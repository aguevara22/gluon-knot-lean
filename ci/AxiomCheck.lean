import SM.CornerLawsAndSoft
/-! CI axiom check: the final theorem must use exactly Lean's three standard axioms and the six
registered literature constants (five literature interfaces; lit:homfly carries two constants).
Run from CORNER_LAWS_FOCUSED_20260912/work/lean:  lake env lean ../../../ci/AxiomCheck.lean -/

#print axioms SM.corner_laws_and_soft

open Lean Elab Command in
run_cmd do
  let axs ← collectAxioms ``SM.corner_laws_and_soft
  let allowed : List Name :=
    [``propext, ``Classical.choice, ``Quot.sound,
     ``SM.lit_homfly, ``SM.lit_homfly_descent, ``SM.lp_lm, ``SM.lp_lm_uniqueness,
     ``SM.ng_finite_word, ``SM.src_contact]
  for a in axs do
    unless allowed.contains a do
      throwError "unexpected axiom in SM.corner_laws_and_soft: {a}"
  if axs.contains ``sorryAx then throwError "sorryAx present"
  logInfo m!"SM.corner_laws_and_soft depends on exactly the registered axioms: {axs}"
