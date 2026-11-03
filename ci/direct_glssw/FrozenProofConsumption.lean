import ArmstrongFrozen.Frozen.JointNormalizedHomflyCornerIdentity
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let edges : List (Name × Name) := [
    (`DirectGLSSW.DaughterClosedContainment.daughter_interior_on_parent, `DirectGLSSW.DaughterClosedContainment.daughterSide_endpoint_parameters),
    (`DirectGLSSW.CyclicCarrierClearing.auxiliaryGenericity_of_canonical_universal, `DirectGLSSW.DaughterFirstReturn.daughterCarrier_injective),
    (`DirectGLSSW.ActiveArc.OpenCarrier.openSideCarrier_injective, `DirectGLSSW.ActiveArc.OpenCarrier.retainedCarrier_injective),
    (`DirectGLSSW.ActiveArc.Primitive.before_first_cursor_closed_side_avoidance, `DirectGLSSW.ActiveArc.OpenCarrier.openSideCarrier_injective),
    (`DirectGLSSW.ActiveArc.PhysicalSegments.retained_visit_interval_subsegment, `DirectGLSSW.ActiveArc.PhysicalSegments.retained_side_physical),
    (`DirectGLSSW.ActiveArc.OpenCarrier.openSideCarrier_physical, `DirectGLSSW.ActiveArc.PhysicalSegments.retained_side_physical),
    (`DirectGLSSW.ActiveArc.LiteralTinyParent.selectedCut_eq_actual_tinyParent, `DirectGLSSW.ActiveArc.LiteralTinyParent.tinyParent_GammaM_eq_weighted_approach),
    (`DirectGLSSW.ActiveArc.LiteralTinyParent.selectedCut_eq_actual_tinyParent, `DirectGLSSW.ActiveArc.CompatibleWords.gammaM_selectedCut_before_first),
    (`DirectGLSSW.ActiveArc.LiteralTinyParent.exists_selectedCut_constant_from_actual_tinyParent, `DirectGLSSW.ActiveArc.LiteralTinyParent.selectedCut_eq_actual_tinyParent),
    (`DirectGLSSW.ActiveArc.LiteralTinyParent.exists_selectedCut_constant_from_actual_tinyParent, `DirectGLSSW.ActiveArc.LiteralTinyParent.exists_actual_tinyParent_GammaM_limit),
    (`DirectGLSSW.ActiveArc.CarrierDomainSelectedCut.exists_physical_selectedCut_constant, `DirectGLSSW.ActiveArc.LiteralTinyParent.exists_selectedCut_constant_from_actual_tinyParent),
    (`DirectGLSSW.HOMFLY.positivePolygon_history_canonical_terminal_framed_value_via_general_whitney, `DirectGLSSW.DescendingSpatial.descending_actual_split_triangles_and_normalization),
    (`DirectGLSSW.HOMFLY.MarkedG.terminal_value, `DirectGLSSW.HOMFLY.positivePolygon_history_canonical_terminal_framed_value_via_general_whitney),
    (`DirectGLSSW.HOMFLY.MarkedPolynomial.exists_polynomial_of_detached_witnesses, `DirectGLSSW.HOMFLY.markedParentStep_wellFounded),
    (`DirectGLSSW.SourceWorkingReconstruction.candidate_identity_from_working_chamber, `DirectGLSSW.PolygonGermStability.eventually_polygonAmplitude_stability),
    (`DirectGLSSW.GenericCornerIdentityContinuation.polygonAmplitude_eq_cornerStateSum_of_auxiliaryIdentity, `DirectGLSSW.PolygonGermStability.eventually_polygonAmplitude_stability)]
  for (consumer, producer) in edges do
    let some c := env.find? consumer | throwError "Missing consumer {consumer}"
    let some v := c.value? | throwError "Missing proof value {consumer}"
    unless v.getUsedConstants.contains producer do
      throwError "Missing direct proof edge {consumer} -> {producer}"
    logInfo m!"VERIFIED_DIRECT_EDGE {consumer} -> {producer}"
  logInfo m!"FROZEN_IMPORT_DIRECT_EDGES_OK count={edges.length}"

run_cmd do
  let env ← getEnv
  let root := `DirectGLSSW.joint_normalized_homfly_corner_identity
  let targets := [
    `DirectGLSSW.ActiveArc.LiteralTinyParent.exists_actual_tinyParent_GammaM_limit,
    `DirectGLSSW.ActiveArc.LiteralTinyParent.selectedCut_eq_actual_tinyParent,
    `DirectGLSSW.DescendingSpatial.descending_actual_split_triangles_and_normalization,
    `DirectGLSSW.HOMFLY.markedParentStep_wellFounded,
    `DirectGLSSW.PolygonGermStability.eventually_polygonAmplitude_stability]
  let mut pending : List Name := [root]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      let some c := env.find? n | throwError "Missing reached declaration {n}"
      if let some v := c.value? then
        for u in v.getUsedConstants do
          unless seen.contains u do
            pending := u :: pending
  for target in targets do
    unless seen.contains target do
      throwError "Target is not in frozen theorem proof-term closure: {target}"
    logInfo m!"VERIFIED_FROZEN_PROOF_DEPENDENCY {target}"
  logInfo m!"FROZEN_PROOF_TERM_CLOSURE_OK visited={seen.size} targets={targets.length}"
