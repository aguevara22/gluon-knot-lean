# U_F_REPORT — unit U-F (thm:floor), prefix `uf_`

File: `work/drafts/floor/U_F.lean` (copy of `Statements_FINAL.lean`, statements frozen; only the two U-F
`sorry` bodies replaced, four `uf_` helpers added immediately before `uf_a_floor_of_C` in `section Floor`).
Prover: Claude (subagent), 2026-09-15 ~15:30Z.

Check: `cd work/lean && lake env lean ../drafts/floor/U_F.lean` — **0 errors**, 10 s warm; 21 declarations
report `declaration uses sorry` (the other units' leaves + the two stated corollaries), down from 23.
`grep -c sorry`: Statements_FINAL.lean 25 → U_F.lean 23 (two text occurrences are in comments).
`diff Statements_FINAL.lean U_F.lean`: exactly two `<   sorry` lines removed, 80 lines added — no
statement, definition, name or docstring touched.

## Leaves

| leaf | status | route used |
|---|---|---|
| `uf_z_parity` | **PROVED** | `P_eq_homfly` (so `cornerHomfly = P (positiveLift …)`), `P_support` (`componentCount = 1` is `rfl`, `positiveLift_componentCount`), then `mindegZZ_spec (P_ne_zero _)` gives an attained `z`-exponent, `P_knot_support` makes it `2 * j`, `positivity`. 10 lines. |
| `uf_a_floor_of_C` | **PROVED** | `hC.floor _ _ (uf_carrierFloorCHyp …)`, rewrite `positiveLift_writhe_eq_carrierCrossingCount` and `P_eq_homfly`, `change` to expose `carrierRotation` / `cornerHomfly` (both definitional), cast algebra for the ℝ form, `cornerSlot_cast` + `exact_mod_cast` for the ℤ form. 22 lines. |

No leaf left; both leaves are TRUE as stated. `thm_floor_of_C hC` is now sorry-free given `hC`;
`thm_floor_of_bound` waits only on `cf_thm_carrierfloor_C_of_bound` (U-C).

## Helpers added (all in `section Floor`, right before `uf_a_floor_of_C`)

- `uf_allPosOrOneNeg_of_allLeftOrOneRight {m} [NeZero m] (Q : LabelledTuple m) (hreg : Regular Q) :
  AllLeftOrOneRight Q → AllPosOrOneNeg Q` — `principalTurn_pos_of_left`, and for the one right turn
  `sign_eq_neg_one_iff.mp ((principalTurn_sign hreg j₀).trans hj₀)`.
- `uf_uniformOrOneDissent_of_carrier … (halt : CarrierUniformOrOneDissent hn hP S q) :
  UniformOrOneDissent (carrierPolyComp hn hP S q hS)` — the two alternatives through the helper above, with
  `ccpCornerPolygon_regular hn hP hS q` and `regular_reversal_forward` for the reversal.
- `uf_carrier_principalTurn_ne_zero … (i : ZMod (ccpCornerCount hn hP S q)) :
  principalTurn (carrierPolyComp hn hP S q hS).P i ≠ 0` — `ccpCornerPolygon_turn_ne_zero` (lem:carriers (ii))
  through `principalTurn_sign` and `sign_zero`.
- `uf_carrierFloorCHyp … (halt) : CarrierFloorCHyp (carrierPolyComp hn hP S q hS) (positiveLift hn hP S q hS)` —
  `CarrierFloorCHyp.of_diagram _ _ rfl (positiveLift_isPositive …) (turn_ne helper) (alternative helper)`.

## Axioms (`#print axioms`, no `sorryAx`)

- `uf_z_parity`, `uf_a_floor_of_C`, `thm_floor_of_C`: `[propext, Classical.choice, Quot.sound, SM.lit_homfly,
  SM.lp_lm, SM.lp_lm_uniqueness]`.
- `uf_carrierFloorCHyp`, `uf_allPosOrOneNeg_of_allLeftOrOneRight` (and the other two helpers): `[propext,
  Classical.choice, Quot.sound]`.

**Note for the assembler:** PLAN_FINAL §4 says to expect `[…, SM.lp_lm]` plus `SM.lit_homfly` for the thm:floor
theorems. The actual set also contains `SM.lp_lm_uniqueness`. It is a registered policy axiom
(`work/lean/axiom-policy.json` line 11, `"lp:lm-uniqueness": "SM.lp_lm_uniqueness"`) and it enters ONLY through
the accepted `P_eq_homfly` (PolynomialBlock.lean:667, itself `[…, lit_homfly, lp_lm, lp_lm_uniqueness]`), which
is the lemma the plan's route prescribes for `P X = cornerHomfly`. Unavoidable for any statement about
`cornerHomfly = homfly ∘ positiveLift` proved through `P`; the expected list in §4 should be amended, not the
proof. `P_support`, `P_ne_zero`, `P_knot_support` alone are `[…, lp_lm]`.

## Definitional facts relied on (all checked by `rfl` / `example` in a probe)

- `(positiveLift hn hP S q hS).Γ = Shadow.single (carrierPolyComp hn hP S q hS)` — `positiveLift_Γ` is `rfl` and
  `carrierShadow` is an `abbrev` for `Shadow.single (carrierPolyComp …)` (LinkPositiveLift.lean:218), so the
  `shadow` field of `CarrierFloorCHyp` is literally `rfl`.
- `(carrierPolyComp hn hP S q hS).P = ccpCornerPolygon hn hP S q` (`carrierPolyComp` is an `abbrev`).
- `rotationNumber (carrierPolyComp …).P = carrierRotation hn hP S q` (UniformDefinition.lean:42).
- `SM.P (positiveLift …) = cornerHomfly hn hP S q hS` is `P_eq_homfly _` (`cornerHomfly` unfolds by δ).
- `IsDecomposition hn hP S` is by definition `S ∈ independentSupports hn hP` (DecompositionDefinition.lean:15),
  so `hS` is passed unchanged to `ccpCornerPolygon_turn_ne_zero` / `ccpCornerPolygon_regular`, which are stated
  on `S ∈ independentSupports`.
- `NeZero (ccpCornerCount hn hP S q)` is the instance `ccpCornerCount_neZero` (CarrierCornerPolygon.lean:345);
  `principalTurn_sign` / `principalTurn_pos_of_left` carry `[NeZero n]` (section variable) and find it.

## Mathlib / Lean pitfalls met

1. **Name shadowing.** The leaf binds the parent polygon as `(P : LabelledTuple n)`, which shadows the
   polynomial `SM.P : Diagram → R` inside the proof. Write `SM.P` explicitly when the polynomial must be
   spelled (done in `uf_z_parity`); using `P_eq_homfly` as a `rw` lemma is unaffected. Do NOT rename the
   binder (statement is frozen).
2. `SignType.sign_zero` does not exist; the lemma is the root `sign_zero : SignType.sign 0 = 0`. Likewise
   `sign_eq_one_iff : sign a = 1 ↔ 0 < a`, `sign_eq_neg_one_iff : sign a = -1 ↔ a < 0` are root-namespace.
3. Namespaces for probes: `InSupportM`, `coeffAt`, `mindegZZ_spec`, `positiveLift*`, `carrierPolyComp` live in
   `SM.Link`; a scratch file needs `open Link` (and `open Carrier` for `Component`, `IsDecomposition`) as the
   statements file does.
4. `rw [P_eq_homfly] at hfloor` leaves `homfly (positiveLift …)`, not `cornerHomfly …`; `change` (or a bare
   `exact`) closes the δ-gap. Casting `((1 - (m : ℤ) : ℤ) : ℝ)` to `1 - (m : ℝ)`:
   `rw [Int.cast_sub, Int.cast_one, Int.cast_natCast]`. The ℤ conclusion from the ℝ one: rewrite with
   `cornerSlot_cast hn hP hS q` on the cast of `cornerSlot`, then `exact_mod_cast`.

## For the executor / assembler

- Nothing believed false; no missing hypothesis. Both U-F leaves are cheap and closed; U-F contributes no
  leaf to the critical path.
- The helpers are self-contained (accepted library + the frozen definitions `AllLeftOrOneRight`,
  `AllPosOrOneNeg`, `UniformOrOneDissent`, `CarrierFloorCHyp.of_diagram`); no dependence on any other unit's
  leaf. They can be concatenated verbatim; no name clash with work/lean/SM (`uf_` prefix, grep-clean).
- `uf_carrierFloorCHyp` is reusable by U-C's consumers if they ever need clause (C)'s hypothesis class on the
  positive lift.
