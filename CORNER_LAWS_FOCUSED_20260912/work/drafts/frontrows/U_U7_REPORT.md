# U_U7_REPORT — unit U7 (L-PL): `PLFront.IsStandardCircles.downCount_eq_c_general`

Written 2026-09-14 07:55 UTC / 3:55am ET by the U7 prover.  File: `work/drafts/frontrows/U_U7.lean` (copy of
`Skeleton_FINAL.lean` with the U7 leaf proved and a helper section added).  Checked with
`cd work/lean && lake env lean ../drafts/frontrows/U_U7.lean` (Lean v4.34.0-rc2, project Mathlib pin).

## 1. Result

| item | value |
|---|---|
| leaf | `PLFront.IsStandardCircles.downCount_eq_c_general (F : PLFront) (h : F.IsStandardCircles) : F.downCount = F.Γ.c` — **PROVED**, statement unchanged |
| compile | 0 errors, 0 non-sorry warnings; 25 `declaration uses sorry` warnings = the other units' 25 leaves |
| `grep -c sorry` | 26 before → 25 after |
| `diff Skeleton_FINAL.lean U_U7.lean` | one deleted line (the leaf's `:= sorry`) + the inserted helper block; no definition, structure, statement, name or docstring touched |
| `#print axioms` (probe in a scratch copy) | `downCount_eq_c_general`, `u7_down_iff_not_down`, `u7_exists_graphFun`: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no new axiom.  `IsStandardCircles.defect_eq_zero` (glue, unchanged) still reaches `sorryAx` through U1's `degAZ_delta` and `lp_lm` through `P`, as PLAN_FINAL §4 predicts |
| size | helper block 640 lines (`section u7_helpers` … `end u7_helpers`, lines 318–957) + 6-line leaf body; estimate was 1.5–2.5k |
| FR-11 fallback | not needed.  (For the record, the realization instance already exists in the accepted library: `SM.realize_downCount_eq_c_of_isStandardCircles`, FrontRealizeStandard.lean:622, and `realize_nil_isStandardCircles`.) |

## 2. Route (the general PL argument; β2's grid argument was not reusable because it walks the word)

Fix a component `i` with its unique left cusp strand `⟨i, ℓ⟩` and unique right cusp strand `⟨i, r⟩`
(from `h.2 i`).  Write `k = (F.Γ.comp i).k`, `P = (F.Γ.comp i).P`, `n = (r − ℓ).val` (so `0 < n < k`),
`m = k − n`.

1. **Runs.**  A vertex where the rightward bit `xdir` changes is a cusp (`u7_isCusp_of_xdir_ne`, from
   `xdir_prev_eq_of_not_isCusp`), and the only cusps of the component are `ℓ` and `r` (uniqueness).  Hence
   (`u7_xdir_run`, an induction along `⟨i, a + j⟩`) the strands `ℓ + j`, `j < n` are rightward and the strands
   `r + j`, `j < m` are leftward.  The index bookkeeping is in `ZMod k` with `ZMod.natCast_zmod_val`,
   `ZMod.natCast_eq_natCast_iff'`, `Nat.mod_eq_of_lt`, `Nat.cast_pred`, `Nat.cast_sub`.
2. **Chains.**  `vA j := P (ℓ + j)` (`j ≤ n`) has strictly increasing x; `vB j := P (r + (m − j))` (`j ≤ m`,
   the leftward arc read backwards) has strictly increasing x too.  `u7_chain v n = ⋃_{j<n} u7_seg (v j) (v (j+1))`
   is compact (`Set.Finite.isCompact_biUnion`), `Prod.fst` is injective on it (`u7_chain_injOn`: x-ranges of the
   pieces are consecutive intervals, a nonvertical segment is determined by x) and its x-projection is exactly
   `Icc (v 0).1 (v n).1` (`u7_chain_fst_image`).  `F.Γ.seg ⟨i, ℓ + j⟩ = u7_seg (vA j) (vA (j+1))` and
   `F.Γ.seg ⟨i, r + (m − (j+1))⟩ = u7_seg (vB j) (vB (j+1))` (`u7_seg_eq`, `u7_seg_symm`).
3. **Graph functions.**  `u7_exists_graphFun`: a compact `K ⊆ ℝ²` with `InjOn fst K` and `fst '' K = Icc a b` is
   the graph of a continuous `f : ℝ → ℝ` (with `(x, f x) ∈ K` on `Icc a b` and `f p.1 = p.2` on `K`).  Proof:
   `fst : K → Icc a b` is a continuous bijection from a compact space to a Hausdorff space, so
   `Continuous.homeoOfEquivCompactToT2` gives a homeomorphism; `f := snd ∘ h.symm ∘ projIcc`.  This replaces the
   plan's "PL graph functions" without ever ordering the pieces by x.
4. **No meeting inside.**  `g := fB − fA` is continuous.  If `g x = 0` with `a < x < b`, the point lies on a
   rightward strand `s = ⟨i, ℓ + j⟩` and a leftward strand `t = ⟨i, r + j'⟩`.  Non-adjacent ⇒
   `Shadow.isCrossing_pair` gives a crossing, contradicting `h.1 : IsEmpty F.Γ.Crossing`.  Adjacent
   (`Shadow.adjacent_mk_iff`, `adjacent` = label difference in `{−1, 0, 1}`): equal labels contradict the bits;
   otherwise one is `prev` of the other, that vertex is a cusp, and `u7_seg_prev_inter_cusp` (the two arms of a
   cusp are not collinear, `cusp_det_ne_zero`, so their segments meet only at the vertex) puts the point at
   `P ℓ` or `P r`, i.e. `x ∈ {a, b}`.  Only `IsEmpty Crossing`, `Regular` (through `cusp_det_ne_zero`) and
   `nonvertical` are used; `tail_off` and `no_triple` are not needed.
5. **Constant sign.**  `isPreconnected_Ioo.intermediate_value` on `Ioo a b`.
6. **Reading the sign at the cusps.**  Near `ℓ`: with `e₁ = eOut`, `e₂ = armIn = −eIn` (both with positive x),
   `δ = min e₁.1 e₂.1 / 2`, the points `P ℓ + (δ/e₁.1) • e₁ ∈ seg ⟨i, ℓ⟩ ⊆ KA` and
   `P ℓ + (δ/e₂.1) • e₂ ∈ seg ⟨i, ℓ − 1⟩ ⊆ KB` give `g (a + δ) = δ · (armHeight e₂ − armHeight e₁)`, so by
   `isDownCusp_iff_armIn_above` the left cusp is downward iff `0 < g` on `(a, b)`.  Near `r` (arms with negative
   x, `δ' = min (−e₃.1) (−e₄.1) / 2`, points on `seg ⟨i, r⟩ ⊆ KB` and `seg ⟨i, r − 1⟩ ⊆ KA`):
   `g (b − δ') = δ' · (armHeight e₃ − armHeight e₄)`, so the right cusp is downward iff `g < 0` on `(a, b)`.
   Hence `IsDownCusp ⟨i, ℓ⟩ ↔ ¬ IsDownCusp ⟨i, r⟩` (`u7_down_iff_not_down`).
7. **Counting** (β2's assembly, `FrontRealizeStandard.lean:557-609`, adapted): every cusp of the component is
   `⟨i, ℓ⟩` or `⟨i, r⟩`, exactly one is downward (`u7_card_down_eq_one`), then `card_subtype_eq_sum_comp` and
   `Finset.card_fin`.

## 3. Helpers added (all in `section u7_helpers`, immediately before the leaf; names `u7_*`, namespace `SM.FrontRows`)

| name | role |
|---|---|
| `u7_seg`, `u7_mem_seg_iff`, `u7_seg_symm`, `u7_seg_isCompact`, `u7_left_mem_seg`, `u7_right_mem_seg`, `u7_seg_fst_mem`, `u7_seg_eq_of_fst_eq` | the closed segment as the image of `[0,1]`; symmetry, compactness, x-range, x determines the point |
| `u7_chain`, `u7_mem_chain_iff`, `u7_chain_isCompact`, `u7_chain_lt`, `u7_chain_strictMono`, `u7_chain_mono`, `u7_chain_injOn`, `u7_chain_fst_subset`, `u7_chain_exists_piece`, `u7_chain_fst_image` | x-monotone polygonal chains: compact, `fst` injective, x-image is the interval |
| `u7_exists_graphFun` | compact graph over `Icc a b` ⇒ continuous graph function (compact→T2 homeomorphism) |
| `u7_seg_eq` | `F.Γ.seg ⟨i, m⟩ = u7_seg (P m) (P (m+1))` |
| `u7_xdir_run` | constant rightward bit along a cusp-free run |
| `u7_isCusp_of_xdir_ne` | a bit change is a cusp |
| `u7_seg_prev_inter_cusp` | the two arms of a cusp meet only at the vertex |
| `u7_down_iff_not_down` | the per-component planarity statement (steps 1–6) |
| `u7_card_down_eq_one` | exactly one downward cusp per component |

## 4. Notes for the reviewer / executor

* The leaf is true as stated and was proved without any additional hypothesis; nothing in Statements_FINAL
  or the skeleton changed.  Row 81 sentences 2–3 (`single_B`, `union_B`) now wait only on U1's `degAZ_delta`
  (through the glue `degAZ_delta_pow` → `IsStandardCircles.defect_eq_zero`).
* The helper block is self-contained (Mathlib + `SM.FrontPL` + `SM.LinkDiagram` API only) and could be ported
  as a library module `SM/FrontPLStandard.lean` if the executor prefers; the section wrapper exists only to
  scope `variable (F : PLFront)`.
* Not used: `Generic.tail_off`, `Generic.no_triple`, any β2 grid tool.  Used from the accepted layer:
  `PLFront.{isCusp_iff, not_isLeftCusp_and_isRightCusp, xdir_eq_true_iff, xdir_eq_false_iff,
  xdir_prev_eq_of_not_isCusp, cusp_det_ne_zero, isDownCusp_iff_armIn_above, card_subtype_eq_sum_comp}`,
  `Shadow.{seg_mk, dir_mk, adjacent_mk_iff, isCrossing_pair}`.
* Scratch development files (not deliverables): `/tmp/u7/dev1..dev4.lean`, `/tmp/u7/U_U7_ax.lean` (axiom probe).
