---
name: lean-fixed-target-names
description: "The checker enforces fixed Lean declaration names for the target rows (axiom-policy.json targets); consult before mapping any of them"
metadata:
  type: project
---

`work/lean/axiom-policy.json` has a `targets` block whose rows MUST be mapped to exactly these
declaration names (tools/check_lean.py fails with "fixed declaration name mismatch" otherwise):
Bridge:B1/B2/B3/B4 → Bridge.B1..B4; Bridge:theorem → Bridge.sm_R; CV:ax:R → CV.hyp_R;
R:* rows → RProof.<name> (localization, parity, exterior, fibre_partition, availability_zero_one,
generic_table, generic_selector, generic_transport, generic_selected, extreme_pair_zero,
extreme_transport, extreme_selected, cv_R); SM:corner_laws_and_soft → SM.corner_laws_and_soft;
prop:C-chamber → SM.prop_C_chamber; prop:C-silent → SM.prop_C_silent; thm:C-S3 → SM.thm_C_S3;
thm:C-S5 → SM.thm_C_S5; thm:C-S7 → SM.thm_C_S7; thm:C-soft → SM.thm_C_soft;
thm:comparison → SM.thm_comparison; cor:C-inherits → SM.cor_C_inherits; hyp:R → SM.hyp_R.
The five literature interfaces are fixed too (policy `literature`: SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness, plus the two front/contact interfaces).

**Why:** on 2026-09-13 the prop:C-chamber row was first named SM.C_chamber and the checker
rejected it; renaming cost a rebuild and a remap.
**How to apply:** before fixing a statement for any row in this list, name the main theorem
exactly as above (see [[lean-project-progress]]).
