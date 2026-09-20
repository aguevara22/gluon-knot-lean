# U_SGE_REPORT — unit U103-E (`sge_`), leaf `sg_daughters_rotation`

Prover subagent, 2026-09-15 (~17:00 UTC / 1:00pm ET).  File: `work/drafts/corner/U_SGE.lean` (byte-identical
copy of `Statements_FINAL.lean` plus the helper block and the leaf body; 1155 lines).

Check (mandated): `cd work/lean && lake env lean ../drafts/corner/U_SGE.lean` → exit 0, **0 errors**, 13
`declaration uses sorry` warnings (14 before: the 9 other unit leaves + the 4 row theorems of §6).
`grep -c sorry`: 16 → 15 (one line removed, the `sorry` body of the leaf; the rest are the doc-comment mention at
line 24 and the other units' bodies).  `diff Statements_FINAL.lean U_SGE.lean`: the only removed line is `  sorry`;
the additions are the helper block (inserted at 236a237-601, inside `section Singleton`, immediately before the
U103-E docstring) and the 27-line proof body.  No definition, structure, statement, name or docstring changed.

`#print axioms sg_daughters_rotation` = `[propext, Classical.choice, Quot.sound]` (standard only; same for
`sge_rotation_add`, `sge_daughter_pattern`).  Nothing written under `work/lean`.

## Proved

Leaf: **`sg_daughters_rotation`** (all four conjuncts: the signed patterns of both daughters, the real identity
`r_A = r_{Λ₁} + r_{Λ₂}`, the integer identity `|r_A| = |r_{Λ₁}| + |r_{Λ₂}|`).

Helpers (22 declarations, all prefixed `sge_`, in file order; lines 237-601 of U_SGE.lean):

| name | statement (informal) | proof inputs |
|---|---|---|
| `sge_cornerRotor_smul` | `cornerRotor (a•u) (b•v) = ↑(a*b) * cornerRotor u v` | `Complex.ext`, `cornerRotor_re/_im`, `planeDot`, `det` |
| `sge_principalAngle_smul` | `0<a → 0<b → principalAngle (a•u) (b•v) = principalAngle u v` | `Complex.arg_real_mul` |
| `sge_cornerRotor_swap` | `cornerRotor v u = star (cornerRotor u v)` | `star_mul`, `star_star` |
| `sge_principalAngle_swap` | `det u v ≠ 0 → principalAngle v u = −principalAngle u v` | `Complex.arg_conj`, `Complex.arg_eq_pi_iff`, `cornerRotor_im` |
| `sge_markPrincipalTurn` (def) | `principalAngle (edge P (ccpInEdge m)) (edge P (ccpOutSlot S m).1)` — the real extension of CX1's `markTurn` | — |
| `sge_principalTurn_eq_mark` | `principalTurn (ccpCornerPolygon S q) j = sge_markPrincipalTurn S (ccpCornerMark S q j)` (needs `IsDecomposition`) | `ccpCornerPolygon_edge_pred`, `ccpCornerPolygon_edge` (CarrierCornerPolygon.lean), `sge_principalAngle_smul` |
| `sge_cornerSet` (def), `sge_mem_cornerSet` | `univ.filter (owner S m = q ∧ IsTrueCorner S m)` | — |
| `sge_image_cornerMark` | `univ.image (ccpCornerMark S q) = sge_cornerSet S q` | `ccpCornerMark_mem`, `ccpCornerMark_exists` |
| `sge_sum_corners` | `∑ j, f (ccpCornerMark S q j) = ∑ m ∈ sge_cornerSet S q, f m` | `Finset.sum_image`, `ccpCornerMark_injective` |
| `sge_rotation_eq_sum` | `carrierRotation S q * 2π = ∑ m ∈ sge_cornerSet S q, sge_markPrincipalTurn S m` | the above |
| `sge_markPrincipalTurn_insert` | `IsTrueCorner S m → sge_markPrincipalTurn (insert c S) m = sge_markPrincipalTurn S m` ("inherited corners keep their principal turn") | `ccpOutSlot_vertex`, `ccpOutSlot_selected` |
| `sge_new_turns_cancel` | `v.1 ∈ S → mpt S (inr v) + mpt S (inr (visitTwin v)) = 0` | `ccp_corner_directions_det_ne_zero`, `ccpInEdge_visit`, `ccpOutSlot_selected`, `visitTwin_involutive`, `sge_principalAngle_swap` |
| `sge_isTrueCorner_insert` | `IsTrueCorner (insert c S) m ↔ IsTrueCorner S m ∨ m = inr v₀ ∨ m = inr (visitTwin v₀)` for a visit `v₀` of `c` | `visit_eq_or_twin`, `isTrueCorner_visit` |
| `sge_cornerSet_disjoint` | distinct carriers have disjoint corner sets | — |
| `sge_cornerSet_union` | `sge_cornerSet S' Λ₁ ∪ sge_cornerSet S' Λ₂ = sge_cornerSet S A ∪ {inr v₀, inr (visitTwin v₀)}` (from `hown` and `mem_carrierCrossings`) | — |
| `sge_cornerSet_disjoint_visits` | the two visits of the unselected `c` are not corners of `S` | — |
| `sge_rotation_add` | **`carrierRotation S A = carrierRotation S' Λ₁ + carrierRotation S' Λ₂`** (real form of eq. cb:singleton-rotations) | `Finset.sum_union`, `Finset.sum_pair`, the above |
| `sge_signType_eq_or_neg` | `σ ≠ 0 → τ ≠ 0 → σ = τ ∨ σ = −τ` | `decide` |
| `sge_daughter_visits` | `∃ w₁ w₂` visits of `c` with `owner S' (inr wᵢ) = Λᵢ` | `crossing_visits_exist`, `independent_selected_pair_owners_ne` at `S'`, `hown` |
| `sge_daughter_pattern` | for `Λ ∈ {Λ₁,Λ₂}` owning the visit `w` of `c`: `(∀ j, turn = τ) ∨ (∃ j₀, turn j₀ = −τ ∧ ∀ j ≠ j₀, turn j = τ)` | `turn_ccpCornerPolygon_eq_markTurn`, `markTurn_ne_zero` (CX1), `ccpCornerMark_exists/_owner/_isTrueCorner/_injective`, `independent_selected_pair_owners_ne` |
| `sge_rotation_ray` | signed pattern with `τ` ⇒ `(τ = 1 → 1 ≤ r_Q) ∧ (τ = −1 → r_Q ≤ −1)` | `uniform_rotation` (i)-(iv), `ccpCornerPolygon_regular`, `ccpCornerCount_ge_three`, `ccpCornerPolygon_turn_ne_zero` |

Leaf proof (27 lines): `hA` gives `τ`; `sge_daughter_visits`, `sge_daughter_pattern` ×2 give the two signed patterns
(BOTH with the same `τ` — the assembly only needs `SignedUniformOrOneDissent`, so which daughter is the uniform one
is never decided); `sge_rotation_add` the real sum; `sge_rotation_ray` ×3 + `carrierRotationInt_cast` ×3 +
`Int.cast_injective` + `abs_of_pos/abs_of_neg` + `linarith` the integer identity.

## Left

Nothing in this unit.  (The leaf's docstring says "one daughter is uniform with `A`'s sign and the other has
exactly one dissent"; the frozen statement only asks for `SignedUniformOrOneDissent` of each, which is what is
proved.  The stronger "exactly one is uniform" is true and 5 lines away if anyone needs it: the `c`-visit turns are
`σ, −σ` with `σ ≠ 0`, so exactly one of them equals `τ`.)

## Statement audit

The leaf is TRUE as stated with the given hypotheses; no missing hypothesis found.  Observations for the
assembler / executor:
* The hypothesis `hne : Λ₁ ≠ Λ₂` is used only for the disjointness of the corner sets (`sge_cornerSet_disjoint`)
  in the real rotation sum; the turn patterns and `sge_daughter_visits` do not need it (the latter uses
  `independent_selected_pair_owners_ne` at `insert c S` instead).
* `hS'` (decomposition of `insert c S`) is essential: regularity / nonzero turns / `≥ 3` corners of the
  daughters and the `ρ_{S'}`-separation of the two visits of `c` all come from it.
* The real conjunct `carrierRotation A = r₁ + r₂` holds WITHOUT `hA` (uniformity); only the `|·|` identity uses it.
* Mark-level reading of the turn ledger: `IsTrueCorner (insert c S) m ↔ IsTrueCorner S m ∨ m ∈ {inr v₀, inr (twin v₀)}`
  and `ccpOutSlot (insert c S) m = ccpOutSlot S m` on true corners of `S` are definitional; no orbit/`componentCycle`
  data of CarrierInsertOrbits was needed (the owner-`↔` interface `hown` from U103-D suffices).

## Mathlib / library pitfalls

* `turn_ccpCornerPolygon_eq_markTurn`, `markTurn`, `markTurn_ne_zero`, `markTurn_visitTwin` live in namespace `SM`
  (CX1.lean), not `SM.Carrier`.
* `if_neg` is deprecated in this Mathlib pin → `ite_eq_right` (`¬c → ite c a b = b`); `ite_eq_left` is the `c` case.
* `Complex.arg_conj` is stated for `(starRingEnd ℂ) x`; rewrite `star` with `Complex.star_def` first.
* `Complex.arg_real_mul (x) {r} (hr : 0 < r) : (↑r * x).arg = x.arg` — the real is on the LEFT and cast to `ℂ`.
* `SignType.trichotomy` orders the cases `neg, zero, pos` (`τ = −1`, `τ = 0`, `τ = 1`).
* `IsDecomposition hn hP S` is definitionally `S ∈ independentSupports hn hP`; pass `hS` directly to the
  `independentSupports` lemmas of CarrierCornerPolygon / CarrierIndependentOrder.
* `IsTrueCorner S (inr v)` is definitionally `v.1 ∈ S` (`isTrueCorner_visit` is `Iff.rfl`); `IsTrueCorner S (inl i)`
  is `True` (`trivial`).
* Helper names: prefix `sge_` (lowercase) + Mathlib-style body (`lowerCamelCase` defs, `snake_case` of camelCase
  tokens for theorems), matching the accepted library (`ccpCornerMark_exists`, `markTurn_ne_zero`).  Two helpers are
  `def`s (`sge_markPrincipalTurn`, `sge_cornerSet`), as PLAN_FINAL §4 lists `markPrincipalTurn` as this unit's content.

## Not applicable

U110-G GO/NO-GO on the `RIData`/`RIIData` witnesses: not this unit; no opinion formed.
