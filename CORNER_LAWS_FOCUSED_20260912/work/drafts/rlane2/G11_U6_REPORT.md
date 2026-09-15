# G11_U6_REPORT — unit U6 (D8 site + E1 record twist + F1–F3 assembly) of the G11 skeleton

Written 2026-09-14 by the U6 prover (Claude Code) on Mark's RunPod home pod. Plan of record:
`G11_PLAN.md` §3 (leaves D8, E1, F1–F3), §7 (unit table). File: **`work/drafts/rlane2/G11_U6.lean`**
(5 337 lines; the skeleton `G11_Skeleton.lean` is 1 086 lines; the difference is U6 helper material and the
five replaced `sorry` bodies).

Compile (the only allowed command): `cd work/lean && lake env lean ../drafts/rlane2/G11_U6.lean` —
**exit 0, 0 errors, 0 warnings other than the 44 `declaration uses sorry`** of the other units' leaves
(the 44 flagged declarations are exactly the U1–U5 leaves plus X1–X3; none of the five U6 leaves and none of
the U6 helpers is flagged). ~20 s. Nothing under `work/lean` was written.

`grep -c sorry`: skeleton **50** (49 leaves + the word in the header docstring), `G11_U6.lean` **45**
(44 leaves + the header docstring).

Freeze check (script, 2026-09-14): all 128 declaration headers of the skeleton (from the keyword to the
`:= by` / `:=` / `where`) and all 91 docstrings of the skeleton occur verbatim in `G11_U6.lean`; every one of
the 506 added declarations is `gu6_`-prefixed; only the five `sorry` bodies of the U6 leaves were replaced.
`G11_two_crossings_absurd` (X2) is untouched.

## Leaves PROVED (5 of 5)

| leaf | plan | what the proof does |
|---|---|---|
| `G11_twisted_key_lt` (F1) | §3 F1 | `CV.geometricVisitKey_lt_iff` on both sides; `σ_P` and `visitTransport` keep the edge label; on one edge: both local (equal, or `σ_P`-partners, reversed clause of `ExactTriangleVisitOrders`), one local (adjacency `gu6_adj_left/right`, the A7 argument re-proved generically for any edge from `hX` alone, no black box), none local (carried clause). |
| `G11_liftVisit_σD` (F2) | §3 F2 | the parents of the six local occurrences of the lift are the six `G11_v**` (`gu6_lift_six`): the parent's edge is the out-slot edge of the block of `G11_carrierEdge` (`gu6_carrierEdge_outSlot`, from the `geo_mark_block` spec inside the definition, as `liftVisit_edge`), so the two occurrences of one lift crossing have parents on edges `e, g` say, which forces the parent crossing `x_eg` by cardinality — **no black-box leaf is used** (not even `G11_carrierEdge_spec` / `_crossingPoint`); then a six-case + non-local split with `σ` computed on the visits of `X` (`gu6_σ_v**`, `gu6_σ_of_not_local`, `gu6_σD_apply`). |
| `G11_recordIsoData` (F3) | §3 F3 | the `EXT_homfly_wall` / `GT_homfly_wall_gen` assembly with `Φ = Λ ∘ Ψ⁻¹`, (a) via `visitBetween_iff_key`, `hσ`, F1 and `GT_cyc_congr_of_lt`; (b) `liftVisit_twin` + `visitTransport_visitTwin`; (c) `overBit_eq_true_iff_parent` + `hdet`; (d) `geoPositiveLift_sign`. |
| `riii` (D8) | §3 D8 | see below. |
| `exists_Ψ₁` (E1) | §3 E1 | see below. |

Black-box leaves consumed: D8 uses `exists_arcCovers`, `exists_moveMatch`, `disc_isDisc`, `clean_M₀`,
`clean_M₁`, `inner_M₀`, `inner_M₁`, `X₀_generic`, `X₁_generic`, `X₀_cross_*`, `X₁_cross_pC/qB/pq`,
`X₁_sign_pC/qB`, `triangle_sub_interior` and the `G11_Params` fields (`theta_sub`, `disc_clear_vertex`,
`h₁…h₄`, `hlam`) and `G11_Config.trans`; E1 additionally uses `X₁_cross_iff`; F1–F3 use none (F3 uses F1).

### D8 `riii` — what had to be added beyond the plan

The frozen statement of D7 (`exists_arcCovers`) is purely existential: it does **not** say which arc carries
which strand. So D8 recovers the arc/strand identification geometrically:
* the arc through `x_mp` on `mB` also contains `x_mq` on `mC` (`gu6_arc_m_inner_mC`): the traversal points
  strictly between them lie on `mB ∪ mC ⊆ Θ ⊆ interior U`, and an arc leaving the open region would have to
  place its frontier end there (`gu6_arc_inner_of_path_fwd/bwd/start`, from real cyclic-order lemmas
  `gu6_cyc_start_of_outside`, `gu6_cyc_stop_of_outside`, `gu6_cyc_inner_path`);
* the arc through `x_mp` on `p'` contains `x_pq` (the segment of `p` between them is in `Δ`, `triangle_sub_interior`);
* the three arcs are distinct because an arc containing inner points on two different edges contains one of
  the two cyclic paths between them, each of which passes a vertex of `X₀` outside `U` (`gu6_arc_two_paths`,
  `gu6_tb_edge_start`, `gu6_tb_vertex_between`, `gu6_X₀_vertex_not_mem`);
* the start of the `m`-arc is on `mA` (`gu6_arc_m_start`), the start of the `p`-arc on `p'` before the two
  local parameters (`gu6_arc_start_same_edge`, `gu6_arc_start_lt`);
* the `M₁` partner arc (paired by the end equalities of D7) has literally the same start traversal point
  (`gu6_partner_start`, by `clean_M₁.frontier_injOn`), and from that start it contains the two local `M₁`
  occurrences of its strand (`gu6_M₁_inner_m/p/q`, convexity of `U` along an edge:
  `gu6_edge_interior_of_convex`); the three `M₁` arcs are distinct by their start labels; `{Am', Ap', Aq'} = {a', b', c'}` (`gu6_triple_eq`).
* **D9** (the reversal along `p` and `q`) is proved as `gu6_D9_p/q` from `gu6_D9_core_p/q`: in the basis
  `(edge m, edge p)` the exit point `x_mp' = w + μ (p_out − w)` satisfies `x_mp' − x_mp = ρ (z − x_mp)` with
  `ρ = (1−μ)λ`, and `(a − t₂)(1 − ρ) = μ(t₃ − t₂) ≥ 0` with `a < t₂` forces `ρ ≥ 1`, `ρ = 1` forcing `λ = 1`;
  hence `ρ > 1` and `x_pq` is strictly between. Division-free (coefficients by `gu6_coeff_eq`, a 2×2 det
  argument with `linear_combination` on coordinates).
* heights: `¬ IsAlternating` gives the six linear orders; `gu6_riii_of_strands` does the six-case renaming
  (`a, b, c` by height) once, with `gu6_rev_swap` (from `beforeOn_swap_iff`) for the reversal clauses read in
  the other order; `gu6_riii_build` is the `RIIIData` constructor with separations spelled out.

### E1 `exists_Ψ₁` — construction

`Ψ₁ := singleVisitEquiv.trans (ΨX.trans singleVisitEquiv.symm)` with `ΨX := Equiv.sigmaCongr κ (subtypeEquiv σ₁)`,
`σ₁ := Equiv.swap mB mC` on labels and `κ := (Equiv.Finset.congr σ₁).subtypeEquiv gu6_cross_map_iff` on
crossing supports (the crossings of `X₀` through `mB`/`mC` are exactly `{mB,p'}`/`{mC,q'}`, those of `X₁`
exactly `{q',mB}`/`{p',mC}`, by `inner_M₀/M₁`; off `mB, mC` the supports agree by `X₁_cross_iff`).
Twins: `gu6_Ψ₁_twin` (through `singleVisitEquiv_otherVisit`); over bits: `gu6_Ψ₁_overBit` via the positive
diagram's det criterion `gu6_overBit_iff_det` and the sign preservation `gu6_det_sign_iff` at every crossing
(`X₁_sign_pC/qB` at the two moved pairs); signs: all `+1`.
Cyclic order (the gap argument): with `σ₀ := Ψ₀ ∘ σD ∘ Ψ₀⁻¹` (computed on the six local occurrences and the
identity elsewhere, `gu6_σD_v_**`, `gu6_σD_of_not_local`), the strand label of `Ψ₁ x` equals that of `σ₀ x`
(`gu6_label_eq`) and for equal labels the parameters compare alike (`gu6_param_iff`: non-local occurrences keep
label and parameter, `gu6_coord_nonlocal`; the two local parameters of `p'`/`q'` are reversed by D9
(`gu6_D9_p'`, `gu6_D9_q'`); an outside parameter compares alike with every inside parameter by convexity,
`gu6_outside_cmp`). Then `traversalKey_lt_iff` on both sides gives `gu6_key_lt`, `GT_cyc_congr_of_lt` gives
`VisitBetween`, and `h₀` transports to `D₀`.

## Helpers added (506 declarations, all `gu6_`-prefixed)

Blocks, each placed immediately before the leaf that first uses it (file order):
* before `riii` (~1 950 lines): (a) `X₀`/`X₁` vertex and edge values (mirrors of U3's arithmetic:
  `gu6_subdiv_*`, `gu6_X₀_*`, `gu6_X₁_*`, `gu6_lab_*`, `gu6_exists_lab`, vertex-outside facts), the bent
  triangle `gu6_Θ` and the containment of the four inner pieces; (b) traversal-key lemmas
  `gu6_tb_same_edge`, `gu6_tb_span_one/two`, `gu6_tb_edge_start`, `gu6_tb_vertex_between`,
  `gu6_tb_same_edge_of_start`; (c) real cyclic-order lemmas and arc lemmas (`gu6_arc_start_between`,
  `gu6_arc_stop_between'`, `gu6_arc_inner_of_path_*`, `gu6_arc_two_paths`, `gu6_arc_mem_iff`, `gu6_before_iff`);
  (d) occurrences of a positive one-component diagram (`gu6_sv_*`, `gu6_overStrand_eq`, `gu6_overVisit_eq`,
  `gu6_over_under_of_pos/neg`, `gu6_common_eq_single`, `gu6_cp_injective_single`, `gu6_det_ne_zero_single`),
  the six `M₁` occurrences `gu6_w'_*`, the twelve parameters `gu6_s_*`, `gu6_s'_*` with specs, the
  crossing-point identifications `gu6_cp0_*`, `gu6_cp1_pq`; (e) `gu6_coeff_eq`, D9; (f) convexity along an
  edge, the `M₀`/`M₁` arc lemmas; (g) `gu6_riii_build`, `gu6_rev_swap`, `gu6_riii_of_strands`, the inner
  crossings `gu6_y_*`, `gu6_inner0/1`, over relations `gu6_R*_iff`, `gu6_htrans`, `gu6_ov_*`.
* before `exists_Ψ₁` (~900 lines): the generic `Visit`/`σ` lemmas (`gu6_visit_ne_of_edge`, `gu6_swap_edge`,
  `gu6_visit_ext`, `gu6_isCrossing_comm`, `gu6_σ_on_m/p/q`, `gu6_σ_v**`, `gu6_σ_of_not_local`, `gu6_σD_apply`)
  — these live in `namespace RProof.G11_Params` and are referenced as `G11_Params.gu6_…` from the F1/F2
  blocks —, the crossing classification, `gu6_σ₁`, `gu6_κ`, `gu6_ΨX`, `gu6_Ψ₁`, its values on the twelve
  occurrences, twins/over bits/signs, coordinates, non-local facts, `gu6_outside_cmp`, D9 variants,
  `gu6_M₀_cases`, `gu6_σD_v_**`, `gu6_label_eq`, `gu6_param_iff`, `gu6_key_lt`.
* before `G11_twisted_key_lt` (~250 lines): `gu6_σP_*` (edge preservation, six values, involution,
  fixed off the triangle), `gu6_local_cases`, `gu6_local_pair`, `gu6_union_*`, `gu6_crossing_eq_of_param`,
  `gu6_not_between`, `gu6_adj_left/right`, `gu6_mixed_left/right`, `gu6_param_twisted`.
* before `G11_liftVisit_σD` (~190 lines): `gu6_carrierEdge_outSlot`, `gu6_liftVisit_edge_eq`,
  `gu6_liftVisit_fst_eq`, `gu6_liftVisit_symm_eq`, `gu6_lift_six`.
* `G11_recordIsoData`: proof only (first line `have _htri_used := htri` silences the unused-binder lint on the
  frozen hypothesis `htri`, which the proof does not need).

Small definitions added (noncomputable, `gu6_`-prefixed): `gu6_Θ`, `gu6_w'_*` (6), `gu6_s_*`/`gu6_s'_*`
(12), `gu6_a`, `gu6_b`, `gu6_y_*`/`gu6_y'_*` (6), `gu6_σ₁`, `gu6_κ`, `gu6_ΨX`, `gu6_Ψ₁`.

## Pitfalls met (for the other provers / the assembler)

* **Never let the unifier compare two applications of `σ_P`, `σ`, `σD` or `Equiv.swap` with different
  arguments** (`first | exact absurd … | exact iff_of_false (lt_irrefl _) …`, `show`/`change` through `σD`):
  it unfolds the swaps and the `DecidableEq` instance on visits (Finset/Multiset decidability) and hits
  `maxHeartbeats`. Rewrite `σ` away first with the table lemmas, then close; write case analyses as explicit
  bullets, not `first`-chains; prove `σD (sVE.symm x) = sVE.symm (σ x)` from `Equiv.permCongr_apply` as a term.
* **`rw` fails at `instances` transparency across the aliases** `Γ.Crossing` vs `{s // IsCrossing s}`,
  `Visit C.comp.P` vs `Visit C.X`, `TraversalPoint (Γ.comp a.i).k` vs `TraversalPoint (k+3)`, `π.M₁.Γ` vs
  `Shadow.single ⟨…⟩`, and the folded defs `π.p'`, `π.M₁`. Symptom: "Did not find an occurrence … not
  type-correct under the `implicit` transparency level". Cure: apply the lemma by `exact`/`refine`/`Iff.trans`
  (default transparency), or `show`/`unfold` the folded definition first; state path/decoding lemmas over
  `TraversalPoint (k + 3)` and pass the arc-API hypotheses to them by `exact`.
* `Set.Ico` membership proofs written as `⟨_, _⟩` make otherwise identical terms non-matching for `rw`; the
  `⟨0, i⟩ : Fin 1 × ZMod` strand needs the explicit type ascription `(⟨0, i⟩ : (Shadow.single Cp).Strand)`.
* `Finset.map_insert` did not fire on `{s, other x hs}` (instance mismatch through the alias) — proved the
  support equalities membership-wise instead.
* Not in the import chain of `RProof.X1Rows3`: `SM/Smoothing.lean` (`arc_mem_iff_of_same_edge`,
  `traversalBetween_same_edge/span_two`, `Pt_ext`, …) and `SM/CChamber.lean`
  (`crossingGeometry_of_single_generic`) — the needed facts are re-proved here (`gu6_tb_*`,
  `gu6_common_eq_single`). Available and used: `Diagram.beforeOn_iff_before`, `beforeOn_swap_iff`,
  `visit_on_arc_unique`, `inner_of_mem_of_interior`, `Shadow.Arc.inner_mk_iff`, `traversalBetween_total_inner`,
  `GT_cyc_congr_of_lt`, `GT_det_pos_iff_of_sign`, `Equiv.Finset.congr` (`congr_apply` is rfl).
* `push_neg` is deprecated in this Mathlib (`push Not`); `Function.update_same` is `Function.update_self`;
  `Prod.mk.inj_iff` does not exist (use `congrArg Prod.fst`); `ZMod.val_one` needs `Fact (1 < k+3)`.
* Section variables: `omit [NeZero n] in` for the pure-`Finset`/real lemmas; `C` is implicit in the
  `G11_Params` section, so `gu6_a (C := C)`.

## For the assembler

* `G11_U6.lean` is a strict superset of the skeleton: splice the five proof bodies and the four helper blocks
  (the E1 block must precede both F blocks because F1/F2 reference `G11_Params.gu6_visit_ne_of_edge`,
  `G11_Params.gu6_swap_edge`, `G11_Params.gu6_visit_ext`, `G11_Params.gu6_σ_*`, `G11_Params.gu6_σD_apply`;
  the D8 block must precede the E1 block). The pieces and a rebuild script are under `/tmp/g11/` on the pod
  (`build.py`, `d8_all3.lean`, `e1_all.lean`, `f1_helpers_rest.lean`, `f2_helpers_rest.lean`, `*_proof.lean`).
* Compile time of the assembled file with all units is dominated by the `linarith` case bashes in the cyclic
  lemmas (`gu6_cyc_*`, ~5 s) — acceptable.
* No statement was found false; no counterexample. The D7 statement is usable as frozen (the arc/strand
  identification is recoverable, ~600 lines of D8 do exactly that); a future skeleton could add to
  `exists_arcCovers` the six `Inner` clauses and the three start points to shorten D8 by half.
