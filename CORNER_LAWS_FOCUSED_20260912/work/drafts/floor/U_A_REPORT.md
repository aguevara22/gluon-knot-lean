# U-A report — clause (A) of cf:thm-carrierfloor (rounding record: junction locality, length)

Prover: unit U-A subagent, 2026-09-15. File: `work/drafts/floor/U_A.lean` (byte-identical copy of
`Statements_FINAL.lean` + proofs of the U-A leaves + `ua_`-prefixed helpers; no statement, name,
definition or docstring changed — verified by `diff Statements_FINAL.lean U_A.lean`: the ONLY removed
lines are the three `sorry` bodies, 101 lines added).

Check: `cd work/lean && lake env lean ../drafts/floor/U_A.lean` — **0 errors**, 10 s warm. The 20 remaining
`declaration uses sorry` warnings are exactly the other units' leaves (`CarrierFloorCData.floor_support`,
`ur_P_reverse_all`, `ub_*` ×5, `usw_*` ×5, `ui_mirrorSubstitution`, `urot_exists_rotated`,
`ucurl_exists_curled`, `ul_exists_constants`, `ulift_exists_transverse_lift`,
`cf_thm_carrierfloor_C_of_bound`, `uf_a_floor_of_C`, `uf_z_parity`).
`grep -c sorry`: 25 before (23 leaves + 2 docstring mentions) → **22 after**.

## Leaves proved (3 of 3)

| leaf | file line | route actually used |
|---|---|---|
| `ua_junction_determined` | 495 | `show curveMap C ε (a j + s (b j − a j)) = _` (the record IS `roundedWitness h`: `Lε.γ`, `a`, `b`, `speed` reduce by `rfl`), `curveMap_on_junction h hj ht` (Rounding.lean:1668) with `ht : a j + s(b j − a j) ∈ Icc (a j) (b j)` from `a_lt_b h j` + `nlinarith`; the profile argument `(t − a j) Λ / ℓ_j` collapses to `s` by `add_sub_cancel_left, mul_assoc, mul_div_assoc, G2_arg_b h j, mul_one`; then `A0 C ε j = C.P j − ε • uDir C j` is `rfl`, `principalAngle (uDir C j) (vDir C j) = turn C j` by the helper `ua_principalAngle_uDir_vDir`, and the start angles `θu C j` vs `arg (planeComplex (uDir C j))` are reconciled by `ua_juncArc_congr` from `dirOf (θu C j) = uDir C j` (`dirOf_θu D.regular j`) and `dirOf (arg (uDir C j)) = uDir C j` (`ua_dirOf_arg_uDir`) |
| `ua_length_determined` | 514 | (i) `show Λ C ε * (b − a) = _`, `b_sub_a` (1277), `mul_div_cancel₀ _ (Λ_pos h).ne'`, then `ℓ C ε j = juncLen ε (principalTurn C.P j)` is `rfl` (defs 504/493); (ii) `show curveMap C ε (b C ε j) = _`, `curveMap_b h hj` (1661), `A1 C ε j = C.P j + ε • vDir C j` is `rfl` |
| `CarrierFloorAData.junction_local` | 226 | both junction images are `junctionTemplate q u v ε '' Icc 0 1` (helper `ua_image_junction`, from `hA.junction_determined` + the affine reparametrisation `ua_Icc_eq_image_affine`); then `rw [hq, hu, hv]` |

Hence `cf_thm_carrierfloor_A : CarrierFloorAData` is now COMPLETE (no `sorry` in its transitive closure).

`#print axioms` (checked on a scratch copy with the lines appended, not in the file):
`ua_junction_determined`, `ua_length_determined`, `cf_thm_carrierfloor_A`, `CarrierFloorAData.junction_local`,
`ua_image_junction`, `ua_principalAngle_uDir_vDir` — all `[propext, Classical.choice, Quot.sound]`.
NOTE for the assembler: clause (A) does NOT pull in `SM.lp_lm` (PLAN_FINAL §4 lists `SM.lp_lm` as the expected
axiom set for "(R)(A)(B)" collectively — it comes from `P` in (R)/(B), not from (A)).

## Leaves left

None in this unit.

## Helpers added (all `ua_`, each placed immediately before the leaf that uses it, same section)

Before `CarrierFloorAData.junction_local` (§3):
- `ua_Icc_eq_image_affine {a b : ℝ} (hab : a < b) : Icc a b = (fun s => a + s * (b − a)) '' Icc 0 1` — pure real
  (`div_le_one₀`, `div_mul_cancel₀`, `nlinarith`).
- `ua_image_junction (hA : CarrierFloorAData) … (hj : j < C.k) : (Round C D ε h).Lε.γ '' Icc (a j) (b j) =
  junctionTemplate (C.P j) (uDir C j) (vDir C j) ε '' Icc 0 1` — `Set.image_image`, `Set.image_congr`,
  `(Round C D ε h).a_lt_b j hj`.

Before `ua_junction_determined` (§8.2):
- `ua_dirOf_add_congr : dirOf α = dirOf β → dirOf (α + x) = dirOf (β + x)` — via `planeComplex_injective`,
  `G1_planeComplex_dirOf` (Rounding.lean:1164), `Complex.exp_add`.
- `ua_juncArc_congr : dirOf θ = dirOf θ' → juncArc A0 ε θ ϑ s = juncArc A0 ε θ' ϑ s` — the `2π`-periodicity of
  `juncArc` in `θu`, done WITHOUT `Real.Angle`: `unfold juncArc; congr 2; intervalIntegral.integral_congr`.
- `ua_dirOf_arg_uDir (C) (hreg : Regular C.P) (j : ZMod C.k) : dirOf (arg (planeComplex (uDir C j))) = uDir C j`
  — `G1_smul_dirOf_arg` (1170) + `euclideanLength_normalize (hreg j).1` (TurningNumber.lean:228) + `one_smul`.
- `ua_principalAngle_smul (hr : 0 < r) (hr' : 0 < r') : principalAngle (r • u) (r' • v) = principalAngle u v` —
  `cornerRotor (r•u) (r'•v) = ↑(r r') * cornerRotor u v` (`planeComplex_smul`, `Complex.real_smul`, `star_mul'`,
  `Complex.star_def`, `Complex.conj_ofReal`, `push_cast`, `ring`) then `Complex.arg_real_mul`.
- `ua_principalAngle_uDir_vDir (C) (hreg) (j : ZMod C.k) : principalAngle (uDir C j) (vDir C j) = turn C j` —
  `unfold uDir vDir turn principalTurn normalize` + the previous helper with `inv_pos.mpr (euclideanLength_pos _)`.

The plan's suggested route (`G1_dirOf_arg` 1172 + `Real.Angle` congruence) was replaced by the `dirOf`-level
congruence above (shorter; `dirOf_θu` already gives `dirOf (θu C j) = uDir C j` and only the DIRECTION of the
start angle enters `juncArc`). Total ≈ 100 lines instead of the planned 200.

## Mathlib pitfalls (this pin, Lean v4.34.0-rc2)

- `div_le_one` is gone from the ordered-field API in this pin; use `div_le_one₀ (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b`
  (Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1153). `div_le_iff₀` is the companion.
- `mul_div_cancel₀ (a) (hb : b ≠ 0) : b * (a / b) = a` (GroupWithZero/Units/Basic.lean:458) — the form needed for
  `Λ * (ℓ/Λ) = ℓ`; `div_mul_cancel₀ (a) (hb) : a / b * b = a`.
- `add_sub_cancel_left : a + b - a = b` (current naming; the old `add_sub_cancel'` is deprecated).
- `star_mul'` needs `CommMagma`; ℂ qualifies. `star (↑r : ℂ) = ↑r` is `Complex.star_def` (a function equality
  `star = conj`, rewrite it as `rw [Complex.star_def, Complex.conj_ofReal]`), there is no `Complex.star_ofReal`.
- `show` with a wildcard `_` for the argument does NOT unfold `(Round C D ε h).a j` to `CornerRounding.a C ε j`
  (the `_` unifies with the un-reduced projection and `rw` then fails); spell the whole argument out in the `show`.
- `congr 2` on `A0 + c • ∫ f = A0 + c • ∫ g` stops at `∫ f = ∫ g` as wanted (no descent into `intervalIntegral`).

## For the assembler / executor

- Clause (A) is finished: `cf_thm_carrierfloor_A` and the reviewer corollary `CarrierFloorAData.junction_local`
  have no `sorry` and the standard axioms only. Ready to map as a clause theorem after its own statement review.
- All facts used are `rfl`-level unfoldings of `Round := CornerRounding.roundedWitness` plus the accepted
  Rounding.lean lemmas `curveMap_on_junction`, `curveMap_b`, `b_sub_a`, `G2_arg_b`, `a_lt_b`, `Λ_pos`,
  `dirOf_θu`, `G1_planeComplex_dirOf`, `G1_smul_dirOf_arg`, and `euclideanLength_normalize`,
  `planeComplex_smul`, `planeComplex_injective`, `euclideanLength_pos`. Nothing written under work/lean.
- No leaf of this unit is false or needs a stronger hypothesis. `junction_determined` (stronger than the
  printed "determined by") holds literally of the construction, as FR-FL-A1 claims.
- `ua_principalAngle_smul` / `ua_principalAngle_uDir_vDir` are general enough to be reused by U-B1/U-B3 (the
  `AdmissibleDirection` leaves also compare `principalTurn` with directions of `uDir`); keep the `ua_` names or
  let the assembler promote them to the library section of `SM/CarrierFloor.lean`.
