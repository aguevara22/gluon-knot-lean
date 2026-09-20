# W2_EQ_REPORT.md — wave-2 unit U-EQ (helper prefix `ueq_`)

Written 2026-09-15 (UTC) by the U-EQ prover subagent.  File: `work/drafts/floor/W2_EQ.lean`
(= `Wave2_Skeleton.lean` + this unit's proof; every other statement, name and docstring byte-identical).

## 1. Leaf

| leaf (skeleton line) | statement (frozen) | status |
|---|---|---|
| `usw_P_switchAll` (l.1718 of the skeleton; l.1745 of `W2_EQ.lean`) | `(X : Diagram) : P X.switchAll = iotaHom (P X)` | **PROVED** (term proof under the frozen `:= by`, via `exact`) |

The leaf is TRUE as stated; no hypothesis was missing and no counterexample arose.

## 2. Proof route (PLAN_FINAL.md §3 (C) step 2 "mirror", sm-3:4533-4551)

`Q := fun D => ι (P D.switchAll)` is an `RCompetitor` (CoefficientTransport.lean:23), then
`coefficient_transport Q P _ P_rcompetitor` (CoefficientTransport.lean:137, PolynomialBlock.lean:648)
gives `ι (P X.switchAll) = P X` for every `X`; applying `ι` once more and `ui_iotaHom_iotaHom`
(`ι ∘ ι = id`, wave 1) gives `P X.switchAll = ι (P X)`.

The six `RCompetitor` clauses:
- `planar`, `reidemeister_I/II/III`: `usw_switchAllCarries.planar/ri/rii/riii` (wave 1) transport the
  move to the switched diagrams; `P_planar`, `P_reidemeister_I/II/III` (PolynomialBlock.lean:604-607)
  give `P D̄ = P D̄'`; `congrArg iotaHom`.
- `circle`: `usw_switchAllCarries.circle` + `P_circle` (609), then `map_one` for the ring hom `ι`.
- `skein` — the printed "multiplied by −1" (sm-3:4540-4544): for a skein triple `(D₊, D₋, D₀)`,
  `usw_switchAllCarries.skein` gives `IsSkeinTriple D̄₋ D̄₊ D̄₀` (sides exchanged), so `P_skein` (638)
  reads `a·P D̄₋ − a⁻¹·P D̄₊ = z·P D̄₀`.  Applying `ι` (`map_sub`, `map_mul`, `ui_iotaHom_a : ι a = a⁻¹`,
  `ui_iotaHom_aInv : ι a⁻¹ = a`, `ui_iotaHom_z : ι z = −z`) gives
  `a⁻¹·ι(P D̄₋) − a·ι(P D̄₊) = −z·ι(P D̄₀)`; negating (`linear_combination -h1`) is exactly the required
  `a·Q D₊ − a⁻¹·Q D₋ = z·Q D₀`.

## 3. Helpers added (prefix `ueq_`, placed immediately before the leaf, same section)

| helper | statement | lines |
|---|---|---|
| `ueq_iota_switchAll_rcompetitor` | `RCompetitor (fun D : Diagram => iotaHom (P D.switchAll))` | 28 (incl. docstring) |

Wave-1 helpers consumed: `usw_switchAllCarries` (all six fields), `ui_iotaHom_a`, `ui_iotaHom_aInv`,
`ui_iotaHom_z`, `ui_iotaHom_iotaHom`.  Accepted library consumed: `RCompetitor`, `coefficient_transport`,
`P_planar`, `P_reidemeister_I/II/III`, `P_circle`, `P_skein`, `P_rcompetitor`; Mathlib `map_one`,
`map_sub`, `map_mul`, `linear_combination`.  The two `show` lines only beta-reduce the structure-field
goals (`(fun D => …) D` → `iotaHom (P D.switchAll)`) so that `rw`/`linear_combination` see the atoms.

## 4. Fidelity notes

- The printed argument (sm-3:4533-4551) is followed literally: `D ↦ ι(P_{D̄})` satisfies lp:core's
  clauses, the skein clause "multiplied by −1", lp:coefficient-transport identifies it with `P`, and `ι`
  is an involution.  Nothing about supports or coefficients of `Q` is used (lp:coefficient-transport
  imposes no such restriction).
- `ι` is used only through its ring-hom structure and the three generator values; the disputed
  `MirrorSubstitutionData.coeff` field (wave-1 report §5, `ui_mirrorSubstitution`) is NOT touched or used.
- No statement, name or docstring of the skeleton was changed; other units' `sorry`s are untouched.

## 5. Compile

Command: `cd work/lean && lake env lean ../drafts/floor/W2_EQ.lean`.
Development: a scratch file in the session scratchpad stubbing `switchAll`, `SwitchAllCarriesUnit`,
`usw_switchAllCarries`, `iotaHom`, `ui_iotaHom_a/aInv/z/iotaHom` with the frozen statements compiled
with 0 errors on the first attempt (8 s).

`grep -c sorry W2_EQ.lean`: **6 before → 5 after** (the removed one is this leaf).  Remaining
occurrences: two text mentions (l.30, l.418) and the three other units' leaf bodies —
`ub_tangencyCount_of_admissible` (B3, l.967), `ulift_exists_transverse_lift` (LIFT-3, l.2963),
`cf_thm_carrierfloor_C_of_bound` (C, l.2974).  (`ui_mirrorSubstitution` carries no `sorry` in the
D-FL-4-repaired skeleton.)

Full compile of `W2_EQ.lean` (2026-09-15 ~16:45 UTC / 12:45pm ET): **exit 0, 0 errors**, 12 s wall.
Warnings: exactly three `declaration uses sorry` (l.962 B3, l.2959 LIFT-3, l.2973 C — other units) and two
pre-existing unused-variable lints (l.608 `hturn`, l.2243 `hu`, both from wave 1).  No warning at the leaf.

`#print axioms` (on a scratchpad copy of the file with the two lines appended; not in `W2_EQ.lean`):
- `SM.usw_P_switchAll` depends on `[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.lp_lm_uniqueness]`
- `SM.ueq_iota_switchAll_rcompetitor` depends on `[propext, Classical.choice, Quot.sound, SM.lp_lm]`

i.e. the accepted library's axioms only (CoefficientTransport.lean header) — no `sorryAx`.

## 6. Diff against `Wave2_Skeleton.lean`

`diff Wave2_Skeleton.lean W2_EQ.lean`: one insertion of 28 lines (the helper with its docstring) at
skeleton l.1713, and the single line `  sorry` at skeleton l.1718 replaced by 5 lines (comment + `exact`
term).  The `theorem usw_P_switchAll … := by` line is byte-identical to the skeleton.
