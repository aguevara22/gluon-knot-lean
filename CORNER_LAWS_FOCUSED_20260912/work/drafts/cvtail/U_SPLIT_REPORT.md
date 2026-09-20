# U_SPLIT_REPORT — unit U-SPLIT (prefix `cvt165s_`), leaf `cvt_singleton_split : SingletonSplitData`

Prover subagent, 2026-09-15 (~19:30 UTC / 3:30pm ET). File: `work/drafts/cvtail/U_SPLIT.lean` (1957 lines; copy of
`Statements_FINAL.lean` with ONE pure insertion and ONE line removed: `diff Statements_FINAL.lean U_SPLIT.lean` =
`691a692,1649` (the helper block, 958 lines, placed in the `noncomputable section` of `namespace CV` immediately
before the leaf's docstring) and `694c1652,1659` (the leaf's `sorry` → 8 proof lines). No statement, name, docstring
or definition of the frozen file was touched; no other unit's `sorry` and no placeholder was touched.

Check (mandated): `cd work/lean && lake env lean ../drafts/cvtail/U_SPLIT.lean` → exit 0, **0 errors, 0 non-sorry
warnings**, 27 s warm; exactly 9 `declaration uses sorry` warnings = the 4 placeholders (`cf_thm_carrierfloor`,
`thm_C_S7`, `thm_C_soft`, `cor_C_inherits`) + `carrier_slot_floor_of_C` (U-SLOT) + `cvt_pair_row_zero_of_singleton`
(U-175) + the 3 fixed-name RA rows 174/176/177. `grep -c sorry`: **11 before → 10 after** (the count includes the
header comment's mention of `sorry` at line 33; the removed line is the leaf body).

`#print axioms CV.cvt_singleton_split` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness]` — standard + the three declarations PLAN_FINAL §0 lists for every use of `P = homfly`
(`SM.lit_homfly` through `homfly`; `SM.lp_lm`, `SM.lp_lm_uniqueness` through `P_eq_homfly`, which lc:single-crossing
needs). The rotation/sign helpers `cvt165s_carrierR_split`, `cvt165s_daughters_alt` are standard-axioms only.
Nothing written under `work/lean`.

## Proved

**Leaf `cvt_singleton_split : SingletonSplitData` — all five conjuncts**, i.e. for a CV-generic `P`,
`S ∈ Ind(G_P)`, a uniform carrier `A` of `S` and a singleton piece `{c}` carried by `A`:
`insert c S ∈ Ind`, two carriers `Λ₁ Λ₂` of `insert c S` with `P_{S,A} = P_{S',Λ₁} P_{S',Λ₂}`,
`w_{S,A} = w_{S',Λ₁} + w_{S',Λ₂} + 1`, `R(A) = R(Λ₁) + R(Λ₂)`, and `UniformOrOneDissentCV` of both daughters' corner
polygons. The daughters are `Λ₁ = geoOwner (insert c S) (inr v)`, `Λ₂ = geoOwner (insert c S) (inr (visitTwin v))`
for the visit `v = ⟨c, i⟩` (`crossing_visits_exist`).

## Interface Props stated

None. Nothing of the unit needed an interface; the leaf is closed from the accepted library alone.

## Helpers added (71, all prefixed `cvt165s_`, in file order; section names in parentheses)

*Polygon side, outside the classical-instance region (`Cvt165sPattern`)*:
`cvt165s_signType_eq_or_neg` (two nonzero signs agree or are opposite, `decide`), `cvt165s_sign_principalTurn`
(`sign (principalTurn L k) = turn L k`, from `SM.principalTurn_sign` + `principalTurn_eq_sm`),
`cvt165s_principalTurn_reversal` (`SM.principalTurn_reversal` in CV's names), `cvt165s_rot_ray` (signed pattern `τ`
⇒ `(τ = 1 → 1 ≤ rot) ∧ (τ = -1 → rot ≤ -1)`; lem:uniformrot's `one_le_rot_of_pos`, `one_le_rot_of_one_dissent`, and
their reversal forms via `rot_reversal`, `regular_reversal'`), `cvt165s_uniformOrOneDissent_of_pattern` (signed
pattern ⇒ `UniformOrOneDissentCV`, the literal reversal form), `cvt165s_abs_add_of_ray` (`|a+b| = |a|+|b|` on one
ray, `omega`).

*Bridge*: `cvt165s_insert_eq` (`insert a s` does not depend on the `DecidableEq` instance; `Subsingleton.elim`).

*(a) Graph part (`Cvt165sGraph`, generic `G : SimpleGraph V`, `t = s ∖ {c}` membership-wise, port of the corner lane's
U103-B)*: `cvt165s_not_reachable_of_isolated`, `cvt165s_reachable_descend`, `cvt165s_compMap` (`ConnectedComponent.map`
of `induceHomOfLE`), `cvt165s_compMap_mk`, `cvt165s_compMap_injective`, `cvt165s_mem_range_compMap_iff`,
`cvt165s_compEquiv : (G.induce t).ConnectedComponent ≃ {C // C ≠ mk ⟨c, _⟩}`, `cvt165s_compEquiv_apply_val`,
`cvt165s_compEquiv_mem_iff`.

*(a) Pieces at `hP : CrossingGeometry P` (`Cvt165sPieces`)*: `cvt165s_not_interlaces` (piece of `c` is `{c}` ⇒ no
`x ∈ U(S)` interlaces `c`), `cvt165s_mem_U_insert_iff` (`U(insert c S) = U(S) ∖ {c}`), `cvt165s_mem_U_set`,
`cvt165s_mem_U_insert_iff_set`, `cvt165s_adj_isolated`, `cvt165s_pieceLabels_eq_singleton_iff`,
**`cvt165s_pieceEquiv : Piece hP (insert c S) ≃ {H : Piece hP S // pieceLabels H ≠ {c}}`**, `cvt165s_pieceEquiv_labels`
(label-preserving), `cvt165s_pieceEmbedding`, `_apply`, `cvt165s_pieceLabels_pieceEmbedding`,
`cvt165s_mem_range_pieceEmbedding_iff`, `cvt165s_pieceOf_notMem_map`, `cvt165s_pieceWrithe_pieceEmbedding`,
`cvt165s_pieceWrithe_singleton` (`w({c}) = 1`).

*(b) Ownership (`Cvt165sOwner`; hypotheses `hc : SingletonPieceOn hP S q v.1`)*: `cvt165s_notMem` (`c ∉ S`),
`cvt165s_owner_visit` (both visits of `c` on `A`), `cvt165s_owner_eq_twin`, `cvt165s_sameCycle`,
`cvt165s_geoIndependent_insert` (`geoIndependent_insert_unselected`), `cvt165s_mem_Ind_insert`, `cvt165s_daughters_ne`
(`geo_selected_visits_separated`), `cvt165s_owner_of_insert` (`geoOwner_insert_eq_imp`), `cvt165s_owner_insert_of`
(`geoComponentForgetSwitch_fiber_affected`), **`cvt165s_owner_iff`** (`owner S m = A ↔ owner S' m = Λ₁ ∨ owner S' m = Λ₂`).

*(c) Products (`Cvt165sProducts`, `Cvt165sHomfly`, `Cvt165sSplitAlgebra`)*: `cvt165s_piecesOn_disjoint`,
`cvt165s_pieceOwner_eq_owner`, `cvt165s_mem_piecesOn_pieceEmbedding_iff`, **`cvt165s_piecesOn_eq`**
(`piecesOn S A = insert (pieceOf c) ((piecesOn S' Λ₁ ∪ piecesOn S' Λ₂).map emb)`),
**`cvt165s_pieceHomfly_eq_of_labels`** (`P_H` is a function of the labels: `homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`
+ `pieceCarrier_geoCarrierCrossings`), **`cvt165s_pieceHomfly_singleton`** (`P_{{c}} = 1`: `single_crossing.one_crossing`
+ `P_eq_homfly` + `pieceShadowCrossingEquiv` + `pieceDiagram_componentCount`), **`cvt165s_groupedPoly_split`**,
**`cvt165s_groupedWrithe_split`**.

*(d)–(e) Rotation (`Cvt165sRot`, `Cvt165sDaughterPattern`, `Cvt165sSplitRot`)*: `cvt165s_markPrincipalTurn` (def:
`principalAngle (edge P (geoInEdge m)) (edge P (geoOutSlot S m).1)`), `cvt165s_markTurn` (def, its sign),
`cvt165s_principalTurn_eq_mark` (`geoCornerPolygon_edge_smul/_edge_pred_smul` + `principalAngle_smul`),
`cvt165s_turn_eq_mark`, `cvt165s_cornerSet` (def), `cvt165s_mem_cornerSet`, `cvt165s_image_cornerMark`,
`cvt165s_sum_corners`, `cvt165s_markPrincipalTurn_insert`, `cvt165s_markTurn_insert` (inherited corners keep their
turn: `geoOutSlot_vertex`, `geoOutSlot_selected`), **`cvt165s_new_turns_cancel`** (`geo_visit_corner_det_ne_zero` +
`principalAngle_swap`), `cvt165s_markTurn_visit_ne_zero`, `cvt165s_isTrueCorner_insert`, `cvt165s_cornerSet_disjoint`,
`cvt165s_cornerSet_union` (corner ledger), `cvt165s_cornerSet_disjoint_visits`, **`cvt165s_daughter_pattern`** (each
daughter is uniform of `A`'s sign or has exactly one dissent), `cvt165s_two_pi_rot` (`two_pi_mul_rot` as a corner-mark
sum), **`cvt165s_rot_add`** (`rot A = rot Λ₁ + rot Λ₂`, real form), `cvt165s_daughter_patterns`,
**`cvt165s_carrierR_split`**, **`cvt165s_daughters_alt`**.

## Unproved

Nothing in this unit.

## Route actually used vs PLAN_FINAL §4

As planned, with two simplifications. (b) needed no list/rotation manipulation: the geo insert layer of
SM/GeoCarrierCount.lean (`geoSmoothingSuccessor_insert*`, `geoOwner_insert_eq_imp`, `geoComponentForgetSwitch_fiber_affected`,
`geo_selected_visits_separated`) gives `cvt165s_owner_iff` directly (≈90 lines instead of the estimated 400–800).
(d) is the corner lane's U103-E route (report `work/drafts/corner/U_SGE_REPORT.md`) ported to the geo layer: the real
principal turn at a corner depends only on the corner MARK and the support (`geoInEdge` is support-free;
`geoOutSlot` at a vertex or at a selected visit is the same at `S` and `insert c S`), so `2π rot` is a sum over the
corner-mark finset and the split is `Finset.sum_union` + `Finset.sum_pair` + the cancellation of the two smoothing
corners — no `TurnLift` rounding and no corner-list surgery. (a)/(c) are the corner lane's U103-B route
(`work/drafts/corner/U_SGB_REPORT.md`) with the isolation of `c` read off `hc.labels` directly. Total 958 lines
(estimate 1500–2500).

## Pitfalls (for the assembler / executor)

1. **`DecidableEq (Crossing P)` instances.** The frozen file imports `RProof.*`, whose global instance
   `RProof.instDecidableEqCrossing` wins over `open Classical`'s low-priority `propDecidable`; so the frozen
   `insert c S` in `SingletonSplitData` is elaborated with the RProof instance, while EVERY CV/SM library lemma
   (`geoIndependent_insert_unselected`, `geoOwner_insert_eq_imp`, `pieceCarrier_geoCarrierCrossings` with `S ∪ K`, …)
   is stated with `fun a b => Classical.propDecidable (a = b)` (their files have `attribute [local instance]
   Classical.propDecidable` and never import RProof). Mismatched instances are not defeq (`Finset.insert`/`∪` unfold to
   `Multiset.ndinsert`/`ndunion` on the instance) and produced "type mismatch" and a **`whnf` heartbeat timeout**
   (the unifier trying to unfold two `∪`s). Fix used: the whole helper region is wrapped in `section Cvt165s` with
   `attribute [local instance high] Classical.propDecidable` (so the helpers reproduce the library's terms
   literally), and the leaf bridges once with `rw [cvt165s_insert_eq c S]` (`insert` is independent of the
   instance by `Subsingleton.elim`; the rewrite's motive over the `∃ hS' : _ ∈ Ind, ∃ q₁ q₂ : GeoComponent _ …` is
   type-correct). A plain `attribute [local instance]` (default priority) did NOT override the RProof instance.
   Any later unit in this lane that consumes library `insert`/`∪` lemmas will hit the same wall; the same two-line
   fix applies. When U-SPLIT is ported to `work/lean/CV/…` (no RProof import), the bridge becomes unnecessary
   (`cvt165s_insert_eq` then rewrites a term to itself and can be dropped).
2. **`omega`/`decide` inside the high-priority-classical region produce kernel-rejected `decide` terms**
   ("application type mismatch: id (Eq.refl true) … decide (… isImpossible = true) = true"): the `Decidable`
   instance chosen for the Bool equalities is `propDecidable`, which the kernel cannot evaluate. Hence
   `cvt165s_signType_eq_or_neg` (`decide`), `cvt165s_rot_ray` (`omega`), `cvt165s_abs_add_of_ray` (`omega`) are placed
   BEFORE the region; inside it only `rw`/`exact`/`ring`/`positivity`/`linarith`-free proofs are used.
3. **Dependent-subtype rewriting.** `rw [hlab] at hy` with `hy : (e y).1 ∈ pieceLabels …`, `e : … ≃ ↥(pieceLabels …)`
   fails ("motive is not type correct": the finset also occurs in the type of `e`). Generalise first
   (`∀ z, z ∈ pieceLabels … → z = c`) and apply.
4. **Section-variable inclusion.** Lean 4 includes a `variable` only if the statement mentions it; `hn : 3 ≤ n`,
   `hS : S ∈ Ind hP`, `hc` are proof-side hypotheses of several lemmas whose statements do not mention them
   (`groupedWrithe` takes no `hn`/`hS`) — explicit `include … in` is required, and the call sites' arities change
   accordingly (`cvt165s_groupedWrithe_split hG hS hc`, no `hn`).
5. **`set hP := hG.crossingGeometry`** in a proof whose context has `Λ : GeoComponent hG.crossingGeometry _`
   creates a shadow `Λ✝` (dependent types); `cvt165s_daughter_pattern` is therefore stated over a plain
   `hP : CrossingGeometry P` and instantiated at `hG.crossingGeometry`.
6. **Visits vs crossings.** The helpers are stated for a visit `v` with `hc : SingletonPieceOn hP S q v.1`, so the
   library's `insert v.1 S` forms match syntactically; the leaf instantiates `v := ⟨c, i⟩`, and `(⟨c, i⟩ : Visit P).1`
   is `c` by `rfl`, so the frozen `insert c S`/`SingletonPieceOn … c` unify with the helpers' `v.1` forms.
7. Names that are NOT in `SM.GeoCarrier`: `geoCornerMark_injective`, `geoOwner_geoCornerMark`,
   `isTrueCorner_geoCornerMark` live in plain `SM` (SM/FlatCarriers.lean:4895–4907, with explicit `hP S`);
   `geoCornerMark_mem` (owner ∧ true corner) is `SM.GeoCarrier`'s (:3158). `principalAngle_smul` (SM/AngleScaling.lean)
   and `principalAngle_swap` (SM/ZeroRotationSeed.lean) ARE in the import closure of the frozen file.

## Statement audit (FR-CV-165-2/-3)

The leaf proves the frozen `SingletonSplitData` exactly: the daughters are carriers of `insert c S`
(`GeoComponent hG.crossingGeometry (insert c S)`), `hS'` is the produced membership `insert c S ∈ Ind`, the
polynomial identity is on `groupedPoly hn hG hS' _`, the writhe identity on `groupedWrithe hG _`, the rotation identity
on `(carrierR hn hG hS q : ℤ)`, and the two alternatives are `UniformOrOneDissentCV` of `geoCornerPolygon` of the
daughters. The docstring's "one loop uniform and the other one-dissent" is stronger than the frozen field (each
daughter uniform-or-one-dissent, both with `A`'s sign `τ`); the stronger form is 5 lines away
(`cvt165s_daughter_pattern` gives the corner at `v` the sign `cvt165s_markTurn (inr v)` and at `visitTwin v` the
opposite sign, `cvt165s_new_turns_cancel`/`geoCornerPolygon_turn_visit_twin`), not needed by `singleton_D_i_of`.
