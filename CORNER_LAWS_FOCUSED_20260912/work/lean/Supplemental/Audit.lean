import Lean

open Lean Elab Command

namespace Supplemental

private def originOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

private def signature (env : Environment) (info : ConstantInfo) : Json := Id.run do
  let mut body := if info.isTheorem then "" else
    (info.value? true).map reprStr |>.getD ""
  if info.isInductive then
    for ctor in info.inductiveVal!.ctors do
      if let some ctorInfo := env.find? ctor then
        body := body ++ "\n" ++ ctor.toString ++ ":" ++ reprStr ctorInfo.type
  return Json.mkObj [
    ("declaration", toJson info.name.toString),
    ("kind", toJson (if info.isAxiom then "axiom" else if info.isTheorem then "theorem"
                    else if info.isInductive then "inductive"
                    else if info.isDefinition then "definition" else "other")),
    ("type", toJson (reprStr info.type)),
    ("universe_parameters", toJson (info.levelParams.map Name.toString)),
    ("definition_body", toJson body)]

/-- Bind local definitions that give a reviewed type its meaning, including
    unmapped helper definitions. Proof-body changes alone do not change meaning. -/
private def semanticDependencies (env : Environment) (modules : Array Name)
    (root : Name) : Array Json := Id.run do
  let mut pending := [root]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      if modules.contains (originOf env name) then
        let mut used := info.type.getUsedConstants
        if !info.isTheorem then
          if let some value := info.value? true then
            used := used ++ value.getUsedConstants
        if info.isInductive then
          used := used ++ info.inductiveVal!.ctors.toArray
        pending := used.toList ++ pending
  let mut rows := #[]
  for name in seen.toArray.qsort Name.lt do
    if modules.contains (originOf env name) then
      if let some info := env.find? name then
        rows := rows.push (signature env info)
  return rows

/-- Audit every declaration originating in the project's source modules.
    Explicit requests also check that the mapped declarations actually exist. -/
def auditProject (modules allowed requested : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for name in requested do
    unless env.contains name do
      throwError "missing mapped declaration: {name}"
  let mut checked := 0
  let mut rows : Array Json := #[]
  for (name, info) in env.constants do
    let origin := originOf env name
    if modules.contains origin then
      checked := checked + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "unregistered axiom {ax} in {name}"
      if requested.contains name then
        let mut body := if info.isTheorem then "" else
          (info.value? true).map reprStr |>.getD ""
        if info.isInductive then
          for ctor in info.inductiveVal!.ctors do
            if let some ctorInfo := env.find? ctor then
              body := body ++ "\n" ++ ctor.toString ++ ":" ++ reprStr ctorInfo.type
        rows := rows.push <| Json.mkObj [
          ("declaration", toJson name.toString),
          ("module", toJson origin.toString),
          ("kind", toJson (if info.isAxiom then "axiom" else if info.isTheorem then "theorem"
                          else if info.isInductive then "inductive"
                          else if info.isDefinition then "definition" else "other")),
          ("type", toJson (reprStr info.type)),
          ("universe_parameters", toJson (info.levelParams.map Name.toString)),
          ("definition_body", toJson body),
          ("semantic_dependencies", toJson (semanticDependencies env modules name)),
          ("axioms", toJson (axioms.map Name.toString))]
  unless rows.size == requested.size do
    throwError "mapped declarations must originate in project modules"
  let report := Json.mkObj [("checked", toJson checked), ("declarations", toJson rows)]
  liftIO <| IO.println ("HANDOFF_AUDIT " ++ report.compress)

end Supplemental
