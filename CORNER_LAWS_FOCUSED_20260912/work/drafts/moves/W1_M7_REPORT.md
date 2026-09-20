# W1_M7_REPORT — unit U-M7 of the moves toolkit (Wave 1): the triangle builder `exists_bigonData_of_triangle`

U-M7 (subagent), 2026-09-15 19:50 UTC / 3:50pm ET.  Inputs: W1_SKELETON_REPORT.md (§1c.0 vocabulary — `no_io_of_succ`,
`param_of_edgePt_eq` —, §2 the U-M7 row, §4 pitfalls, §5 the U-M7 prompt), PLAN_FINAL.md §5–§6, Skeleton_W1.lean (frozen),
SM/LinkDiagram.lean (`Generic`, `crossing_pair_spec`, `crossing_card_two`, `Generic.crossingPoint_injective`,
`Diagram.crossingParam` + `crossingParam_spec/pos/lt_one`), SM/Smoothing.lean §0' (`edgePt`, `edgePt_eq/zero/one`,
`Generic.edgePt_injective`, `mk_add_one_ne`), RProof/GenericTransport.lean 9093–9259 (G11's affine-basis toolkit:
`gu2_det_smul_smul`, `gu2_mem_segment_ab/ac/bc_of_line`).

## 0. Result

| item | result |
|---|---|
| file | `work/drafts/moves/W1_M7.lean` (2056 lines = Skeleton_W1.lean with the ONE U-M7 `sorry` body replaced and 2 helpers `um7_…` inserted immediately before the leaf, in the same section `## 2` / namespace `SM.Link`, under a `/-! ### 2a … -/` heading) |
| compile (`cd work/lean && lake env lean ../drafts/moves/W1_M7.lean`) | exit 0, **0 errors**, **32** `declaration uses sorry` (was 33), 1 cosmetic linter warning (line 565, inherited from the skeleton), ≈ 12 s |
| `grep -c sorry` | Skeleton_W1.lean **34** → W1_M7.lean **33** (the one body; the frozen header comment still counts 1) |
| statement identity | `python3 check_W1_identity.py Statements_FINAL.lean W1_M7.lean` → prefix (1–136) identical: True; **37/37** declarations of Statements_FINAL byte-identical (changed/missing: 0); the third check "suffix identical except the body of `exists_rii_deletion`" reports **False BY CONSTRUCTION**: `exists_bigonData_of_triangle` itself lies in that suffix, so ANY proof of the U-M7 leaf (helpers or not) fails that check — the checker was written for units whose sorries sit in section 1c.  Independent confirmation: `diff Skeleton_W1.lean W1_M7.lean` removes exactly ONE line (`  sorry`, the leaf's body) and adds 191 — every skeleton declaration (docstring, name, statement) is unchanged |
| **proved** | `exists_bigonData_of_triangle` (W1_M7.lean :1652) — the whole of U-M7 (`m7_riiData`, `m7_rii`, `exists_rii_deletion` were already PROVED by U-M0) |
| unproved (of U-M7) | none |
| helpers added | `um7_edgePt_eq_chord` (:1597), `um7_edgePt_mem_segment_iff` (:1605) |
| `#print axioms` (scratch copy = W1_M7.lean + `#print axioms`) | `exists_bigonData_of_triangle`, `um7_edgePt_eq_chord`, `um7_edgePt_mem_segment_iff`: `[propext, Classical.choice, Quot.sound]` — standard only |
| remaining 32 `sorry` declarations | the 3 frozen leaves that stay leaves (`BigonData.reducedRecord_counts` :118, `Record.restrictCrossings_switch` :132, `G11_core_sw` :2008) + the 29 sub-leaves `m1_…m6_…` of the other units (untouched) |
| nothing written under `work/lean` | yes (scratch files under the session scratchpad only) |

No sub-leaf was found false or under-hypothesised.  The leaf's hypotheses used: `hk : 4 ≤ k` (for `hk : 1 + 3 ≤ k`, `omega`),
`hy`, `hz`, `same_over` (verbatim), `clear` (verbatim, the vacuous run clause dropped), `D.generic` (`transverse`,
`crossingPoint_injective`, `edgePt_injective`, `crossingParam_pos/lt_one`).  Nothing else.

## 1. The construction (as prescribed by W1_SKELETON_REPORT §5 U-M7)

`B := { i, a, j := 1, hj := le_rfl, hk := by omega, s, y, z, hy, hz (cast `((1:ℕ) : ZMod k) = 1`), run_free := vacuous
(`1 ≤ m < 1`), no_io := BigonData.no_io_of_succ i a, same_over, ty tz tsy tsz := D.crossingParam y/z (mem), hty … htsz :=
(crossingParam_spec …).2.2.symm (edgePt IS edgePoint, so no rewrite), K := convexHull ℝ {pt y, P (a+1), pt z},
K_convex := convex_convexHull ℝ _, K_compact := (Set.toFinite _).isCompact_convexHull ℝ, run_mem (m = 1: a vertex of the
hull, `subset_convexHull`), in_iff, out_iff, s_iff, clear }`, returned as `⟨B, rfl, rfl, rfl⟩`.

**The one `ZMod` cast.**  The frozen fields read `⟨i, a + ((1 : ℕ) : ZMod k)⟩` once `j := 1`; the leaf's hypotheses read
`⟨i, a + 1⟩`.  One `hcast : ((1 : ℕ) : ZMod (D.Γ.comp i).k) = 1 := Nat.cast_one` and `rw [hcast]` at the start of each affected
field (`hz`, `no_io`, `htz`, `run_mem`, `out_iff`, `clear`) bridges them; no dependent-modulus issue arises because the
component is `D.Γ.comp i` throughout (pitfall §4.1 concerns the REDUCED shadow only).

**Non-degeneracy** (`hdet : det (M₁ − y) (z − y) ≠ 0`, the hypothesis of every `gu2_*` side lemma):
`M₁ − y = (1 − t_y) • dir e_in` (`M₁ = edgePt e_in 1`, `y = edgePt e_in t_y`, `edgePt_eq`, `add_sub_add_left_eq_sub`,
`sub_smul`) and `z − y = (t_sz − t_sy) • dir s` (both on `s`), so `det = (1 − t_y)(t_sz − t_sy) · det (dir e_in) (dir s)`
(`gu2_det_smul_smul`), each factor nonzero: `t_y < 1` (`crossingParam_lt_one`), `t_sy ≠ t_sz` because `pt y ≠ pt z`
(`Generic.crossingPoint_injective` + `y ≠ z`, the latter because `e_in ∈ z.val = {e_out, s}` would force `e_in = e_out`
(`mk_add_one_ne`) or `e_in = s` (`crossing_card_two y` against `{e_in, e_in} = {e_in}`)), and `det (dir e_in) (dir s) ≠ 0` by
`D.generic.transverse` on the non-adjacent meeting pair `crossing_pair_spec y`.  This is exactly "y, M₁, z affinely
independent since z ∉ line(e_in)" of the prompt, read through the two parametrisations of `z − y` rather than through a
line-membership statement.

**The three side lemmas** share one pattern.  `um7_edgePt_eq_chord`: `edgePt e t = edgePt e t₀ + ((t − t₀)/(t₁ − t₀)) •
(edgePt e t₁ − edgePt e t₀)` for `t₀ ≠ t₁` (pure algebra).  `um7_edgePt_mem_segment_iff` (generic shadow): `edgePt e t ∈
segment ℝ (edgePt e t₀) (edgePt e t₁) ↔ min t₀ t₁ ≤ t ∧ t ≤ max t₀ t₁` (`segment_eq_image'`, `Generic.edgePt_injective` to
read the chord parameter back, `nlinarith` for the bounds; the degenerate `t₀ = t₁` case separately).  Then:
* `in_iff` (`e_in ∩ K = [y, M₁]`): `→` `gu2_mem_segment_ab_of_line` with `x = y + ((t − t_y)/(1 − t_y)) • (M₁ − y)` (the chord
  lemma with `t₀ = t_y`, `t₁ = 1`), then the iff with `min t_y 1 = t_y`; `←` `segment_subset_convexHull` on the vertices `y, M₁`
  of `{y, M₁, z}` and the iff with `max t_y 1 = 1 ≥ t`.
* `out_iff` (`e_out ∩ K = [M₁, z]`): the same with `gu2_mem_segment_bc_of_line`, `M₁ = edgePt e_out 0`, `z = edgePt e_out t_z`,
  `t₀ = 0`, `t₁ = t_z` (`0 < t_z` from `crossingParam_pos`), giving `t ≤ t_z`.
* `s_iff` (`s ∩ K = [y, z]`): `gu2_mem_segment_ac_of_line`, `y = edgePt s t_sy`, `z = edgePt s t_sz`; the iff is literally the
  frozen clause `min t_sy t_sz ≤ t ∧ t ≤ max t_sy t_sz` (no ordering assumption between `t_sy`, `t_sz` is needed — the
  frozen statement is min/max for exactly this reason).

## 2. Notes for the executor / consumers

* The leaf is now sorry-free with standard axioms, so the three `j = 1` sites (110, 174, 176) can call
  `exists_bigonData_of_triangle D i a hk s y z hy hz same_over clear` and obtain `B` with `B.i = i`, `B.y = y`, `B.z = z`.
  Their remaining duties are exactly the leaf's hypotheses: the labels, `hk : 4 ≤ k`, `hy`, `hz` (with `⟨i, a + 1⟩`
  literally), `same_over`, and `clear` in the CLOSED-triangle form (PLAN §3 last bullet; `G11_Config.clear_edge`'s shape).
* `check_W1_identity.py`'s third check cannot pass for any file that proves `exists_bigonData_of_triangle` (see §0); the
  meaningful identity evidence for U-M7 is checks 1–2 (pass) plus the one-line `diff` removal.  If the executor wants the
  script to pass literally, the fix is to exempt the leaf's body (`… B.z = z := by\n  sorry`) the same way it exempts
  `exists_rii_deletion`'s — a checker edit, not a statement edit.
* Two tooling notes for other units (Lean 4.34.0-rc2): (i) a multi-line structure instance inside `refine ⟨{ … }, …⟩`
  needs its continuation fields indented at least to the column of the FIRST field (`sepByIndent`); putting `{` at the end of
  the line and every field on its own line (no commas) avoids the "unexpected identifier; expected '}'" parse error;
  (ii) after `rw [segment_eq_image']` add `simp only [Set.mem_image, Set.mem_Icc]` to beta-reduce the image membership before
  `rintro`/`refine`.
* `segment_subset_convexHull (hx : x ∈ s) (hy : y ∈ s)` wants membership in the GENERATING set `{y, M₁, z}`, not in the
  hull (passing hull membership unifies `s` with the hull and leaves `𝕜` stuck).
