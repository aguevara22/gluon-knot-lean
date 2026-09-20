# U-ι report — unit IOTA (`ui_`), leaf `ui_mirrorSubstitution`

File: `work/drafts/floor/U_IOTA.lean` (copy of `Statements_FINAL.lean`, frozen text byte-identical — checked by
`diff` after stripping comment/`sorry` lines: nothing removed or altered; only the `ui_` block at lines 577-698 added).
Prover: subagent, 2026-09-15 ~15:30Z. Check: `cd work/lean && lake env lean ../drafts/floor/U_IOTA.lean` — **0 errors**,
12 s warm, 23 `declaration uses sorry` warnings (the 22 leaves of the other units + `ui_mirrorSubstitution`, see §1).
`grep -c sorry`: 25 before, 25 after (23 declarations + 2 doc-comment mentions; my leaf keeps ONE `sorry`, §1).

## 1. Leaf status — `ui_mirrorSubstitution : MirrorSubstitutionData iotaHom`: 5 of 6 fields PROVED; the sixth is FALSE

| field | status | proof |
|---|---|---|
| `ι_a : ι R.a = R.aInv` | proved | `ui_iotaHom_a` |
| `ι_aInv : ι R.aInv = R.a` | proved | `ui_iotaHom_aInv` |
| `ι_z : ι R.z = -R.z` | proved | `ui_iotaHom_z` |
| `coeff : ∀ f d k, coeffAt d k (ι f) = (-1) ^ k.toNat * coeffAt (-d) k f` | **FALSE as stated** | refuted: `ui_coeff_toNat_false` |
| `degAZ_eq : ∀ f, f ≠ 0 → degAZ (ι f) = -mindegAZ f` | proved | `ui_degAZ_iotaHom` |
| `ne_zero : ∀ f, f ≠ 0 → ι f ≠ 0` | proved | `ui_iotaHom_ne_zero` |

The leaf body is `refine ⟨ui_iotaHom_a, ui_iotaHom_aInv, ui_iotaHom_z, ?_, ui_degAZ_iotaHom, ui_iotaHom_ne_zero⟩` with the
`coeff` goal left `sorry` (line 690; the only `sorry` of this unit). Statement not changed (rule 1/4).

**Counterexample (machine-checked, `ui_coeff_toNat_false`, line 642).** `R = ℤ[a^{±1}, z^{±1}]` has negative
`z`-exponents. Take `f = R.zInv = z⁻¹`, `d = 0`, `k = −1`. Then `ι z⁻¹ = (−z)⁻¹ = −z⁻¹`, so the left side is
`coeffAt 0 (−1) (−z⁻¹) = −1`; but `(−1).toNat = 0`, so the right side is `(−1)^0 · coeffAt 0 (−1) z⁻¹ = 1`. The sign
`(-1) ^ k.toNat` is `1` for EVERY negative `k`, while `ι` multiplies the `z^k` row by `(−1)^k`, which is `−1` for odd
negative `k`.

**The fix (one token) and its verification.** Read the sign as `(-1) ^ k.natAbs` — i.e. the field should be
`coeff : ∀ (f : R) (d k : ℤ), coeffAt d k (ι f) = (-1) ^ k.natAbs * coeffAt (-d) k f`
(equivalently `Int.negOnePow k` / `(-1 : ℤˣ) ^ k`; `natAbs` is the cheapest: `Int.natAbs_even`, `Int.natAbs_odd` are
simp lemmas). This is the printed law "`[a^d z^k](ι f) = (−1)^k [a^{−d} z^k] f`" for all `k ∈ ℤ`. I verified in a scratch
copy (`/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/U_IOTA_natAbs_variant.lean`,
= U_IOTA.lean with `k.toNat` → `k.natAbs` in the structure and the leaf body
`exact ⟨ui_iotaHom_a, ui_iotaHom_aInv, ui_iotaHom_z, ui_coeffAt_iotaHom, ui_degAZ_iotaHom, ui_iotaHom_ne_zero⟩`):
0 errors, the leaf's `sorry` warning gone (22 warnings), and
`#print axioms SM.ui_mirrorSubstitution = [propext, Classical.choice, Quot.sound]`. So with the corrected statement the
leaf is FULLY PROVED by the helpers already in the file; the assembler need only make the substitution in the
`MirrorSubstitutionData` structure and use that `exact`.

For `0 ≤ k` the stated `toNat` form IS true: `ui_coeffAt_iotaHom_of_nonneg` (line 635). (For a KNOT diagram `P X` has
only `z`-exponents `≥ 0` by lp:core, so no consumer of the route is hurt by the wrong sign on negative `k`; but the field
quantifies over all `f : R`, so the structure as stated is uninhabited by `iotaHom` — and by ANY ring hom with
`ι z = −z`, since `ι z⁻¹ = −z⁻¹` is forced.)

## 2. Helpers added (all `ui_`, all immediately before the leaf, same section; axioms [propext, Classical.choice, Quot.sound])

| name | line | statement |
|---|---|---|
| `ui_unitPowers_iota` | 581 | `((R.aUnit⁻¹ ^ p * (-R.zUnit) ^ q : Rˣ) : R) = single (-p, q) ((-1) ^ q.natAbs)` |
| `ui_iotaHom_single` | 604 | `iotaHom (single (p, q) c) = single (-p, q) (c * (-1) ^ q.natAbs)` |
| `ui_coeffAt_smul` | 612 | `coeffAt d k (r • f) = r * coeffAt d k f` (`rfl`) |
| `ui_coeffAt_iotaHom` | 616 | the TRUE coefficient law: `coeffAt d k (iotaHom f) = (-1) ^ k.natAbs * coeffAt (-d) k f` |
| `ui_coeffAt_iotaHom_of_nonneg` | 635 | the stated `k.toNat` form under `0 ≤ k` |
| `ui_coeff_toNat_false` | 642 | `¬ ∀ f d k, coeffAt d k (iotaHom f) = (-1) ^ k.toNat * coeffAt (-d) k f` (the refutation) |
| `ui_degAZ_iotaHom` | 652 | `f ≠ 0 → degAZ (iotaHom f) = -mindegAZ f` (via `degAZ_eq_of_spec` + `mindegAZ_spec`) |
| `ui_iotaHom_ne_zero` | 663 | `f ≠ 0 → iotaHom f ≠ 0` |
| `ui_iotaHom_a`, `ui_iotaHom_aInv`, `ui_iotaHom_z`, `ui_iotaHom_zInv` | 670-679 | generator values (`ι z⁻¹ = −z⁻¹` extra) |
| `ui_iotaHom_iotaHom` | 683 | `iotaHom (iotaHom f) = f` — the "`ι ∘ ι = id`" that U-EQ's route (PLAN §3 (C) step 2) needs |

Route: `AddMonoidAlgebra.lift_single` + `unitPowers_apply` reduce `ι` on a monomial to the unit
`aUnit⁻¹ ^ p * (-zUnit) ^ q`; that unit is computed with the accepted `Laurent₂.monoUnit_inv/_zpow/_mul` and
`Even.neg_one_zpow` / `Odd.neg_one_zpow` on `Rˣ` (the `(−1)^q` in ℤ becomes `(-1) ^ q.natAbs` through
`Int.natAbs_even/odd` + `Even/Odd.neg_one_pow`); the coefficient law is `AddMonoidAlgebra.induction_on` (`of`/`add`/
`smul` cases: `coeffAt_single` twice with a case split on `(p, q) = (−d, k)`, `map_add`, `map_zsmul`); degrees by
`degAZ_eq_of_spec` with `d := -mindegAZ f` and `mindegAZ_spec` (both halves), `right_ne_zero_of_mul`, `linarith`.

## 3. Mathlib pitfalls met (this pin: Lean v4.34.0-rc2)

- `AddMonoidAlgebra` is a STRUCTURE here (`Mathlib/Algebra/MonoidAlgebra/Defs.lean:64`), with `.coeff`, `ofCoeff`,
  `coeff_single`, `coeff_smul_apply` (`rfl`s). `coeffAt d k (r • f) = r * coeffAt d k f` is `rfl`.
- `AddMonoidAlgebra.induction_on` (Defs.lean:995) has cases `of m : motive (of R M (ofAdd m))`, `add`, `smul r x`; unfold
  `of` with `AddMonoidAlgebra.of_apply` then `toAdd_ofAdd`. `map_zsmul iotaHom` matches the structure's `ℤ`-smul.
- No `Units.val_zpow` on a `CommRing` (needs `DivisionMonoid`): keep zpow at the `Rˣ` level and land on the accepted
  `Laurent₂.monoUnit_zpow`/`monoUnit_mul`/`val_monoUnit`, then `Units.val_neg`. `mul_zpow` needs the CommGroup `Rˣ`
  (available). After `neg_one_mul` the goal has `u * -v`: `mul_neg` BEFORE `monoUnit_mul`.
- `(-1 : ℤ).toNat = 0` is `decide`, not `norm_num` (norm_num leaves `(-1)^(-1).toNat`). `k.natAbs = k.toNat` for
  `0 ≤ k`: `omega`.
- `Int.natAbs_even : Even n.natAbs ↔ Even n` and `Int.natAbs_odd` (Algebra/Ring/Int/Parity.lean:91ff) exist;
  `Even.neg_one_zpow` (Algebra/Ring/Parity.lean:414), `Odd.neg_one_zpow` (Algebra/Ring/Int/Parity.lean:167).
- The statements file does NOT `open AddMonoidAlgebra` (LinkLaurentRing does): write `AddMonoidAlgebra.single`,
  `AddMonoidAlgebra.smul_single'`, `AddMonoidAlgebra.single_neg` qualified. `coeffAt_single`'s `if` carries its own
  `Decidable` instance; `simp [h1, h2]` with the two inequalities closes it despite `open Classical`.

## 4. For the assembler / executor

1. Fix the statement: in `MirrorSubstitutionData`, `coeff : … = (-1) ^ k.toNat * …` → `(-1) ^ k.natAbs * …`; then the leaf
   is `exact ⟨ui_iotaHom_a, ui_iotaHom_aInv, ui_iotaHom_z, ui_coeffAt_iotaHom, ui_degAZ_iotaHom, ui_iotaHom_ne_zero⟩`
   (verified, §1). Record the change (a FALSE printed-law transcription, not a fidelity issue: the printed proof's
   `(−1)^k` is the integer power for all `k ∈ ℤ`).
2. Until then, consumers should cite the helpers directly rather than the structure's fields: U-C step 7 uses
   `ui_degAZ_iotaHom` (= `.degAZ_eq`) and `P_ne_zero`; U-EQ uses `ui_iotaHom_a/aInv/z` and `ui_iotaHom_iotaHom`
   (`ι ∘ ι = id` on all of `R`, not just the range). None of the route's consumers uses `coeff`.
3. `iotaHom` is an involutive ring automorphism (`ui_iotaHom_iotaHom`), so it is injective: `iotaHom f = iotaHom g → f = g`
   follows by applying `ui_iotaHom_iotaHom` twice — free for U-EQ's `coefficient_transport` step.
4. Nothing was written under `work/lean`; no other unit's `sorry` was touched.
