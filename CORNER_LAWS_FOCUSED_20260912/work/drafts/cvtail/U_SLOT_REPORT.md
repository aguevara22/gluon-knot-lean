# U-SLOT report — leaf `CV.carrier_slot_floor_of_C` (PLAN_FINAL §4 "CarrierSlotFloor", §6 row U-SLOT)

Prover, 2026-09-15 (~16:40 UTC / 12:40pm ET).  File: `work/drafts/cvtail/U_SLOT.lean`
(byte-identical copy of `Statements_FINAL.lean` except for the additions listed below and the removal of
the one `sorry` of this unit).  Nothing written under `work/lean`.

## Result

* **PROVED**: `CV.carrier_slot_floor_of_C (hC : SM.CarrierFloorCData) : CarrierSlotFloor`.
* Compile: `cd work/lean && lake env lean ../drafts/cvtail/U_SLOT.lean` → exit 0, **0 errors**, 9 warnings
  "declaration uses `sorry`" (the four PLACEHOLDERS `SM.cf_thm_carrierfloor` :160, `SM.thm_C_S7` :194,
  `SM.thm_C_soft` :198, `SM.cor_C_inherits` :1008, and the other units' leaves `cvt_singleton_split` :764,
  `RProof.generic_selected` :809, `cvt_pair_row_zero_of_singleton` :828, `RProof.extreme_transport` :861,
  `RProof.extreme_selected` :874 — untouched).
* `grep -c sorry`: 11 → 10 lines (one of them is the prose line 33 "Every `sorry` is …"; actual `sorry`
  bodies 10 → 9).
* `#print axioms CV.carrier_slot_floor_of_C` (checked on a truncated scratch copy of the file through the
  leaf): `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — no
  `sorryAx`; the three literature axioms enter only through `P_eq_homfly` (lp:core), as PLAN_FINAL's
  deliverables paragraph predicts.  The three helpers depend on the standard axioms only.
* `diff Statements_FINAL.lean U_SLOT.lean`: the single deleted line is `  sorry` of the leaf; every other
  difference is an insertion (helpers + leaf body).  No definition, structure, statement, name or docstring
  changed.

## Proof route (as PLAN_FINAL §4, with two small deviations noted)

`intro n _ hn P hG S hS q halt; by_cases h : (piecesOn hG.crossingGeometry S q).Nonempty`.

**Carrier bearing a piece** — cor:groupedknot (B) + SM (C) on `D(W) = carrierDiagram hn hG hS q`
(`CV/GroupedKnot.lean:778`, an `abbrev` for `geoPositiveLift hn (CarrierGeometry.ofDiagrammatic
(hG.diagrammatic hn)) (geoIndependent_of_mem_Ind hG.crossingGeometry hS) q`):
1. `gk := groupedknot hn hG hS q` (CV/GroupedKnot.lean:883); `(gk.grouped_polynomial h).1 : homfly D(W) =
   groupedPoly`, `(gk.grouped_writhe h).1 : D(W).writhe = groupedWrithe`.
2. `hC.floor C D(W) (cvtS_carrierFloorCHyp hn hG hS q halt)` with `C = geoCarrierPolyComp hn
   (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)) (geoIndependent_of_mem_Ind … hS) q`
   (SM/GeoPositiveLift.lean:91) — gives `((1 - writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P D(W)) : ℝ)`.
3. `rw [P_eq_homfly, h1, h2] at hfloor` (SM/PolynomialBlock.lean:667).
4. `|rotationNumber C.P| = ((carrierR hn hG hS q : ℤ) : ℝ)` is `cvtS_carrierR_real` (from the file's own
   `rotAbs_intCast_real` = `rotAbs_cast` + `Int.cast_abs` + `rot_eq_rotationNumber`); rewritten in a
   restated goal `key`, closed by `exact hfloor` (defeq up to proof irrelevance), then `show 1 -
   groupedWrithe hG q - (carrierR … : ℤ) ≤ mindegAZ (groupedPoly …)` (= `slot`, CV/X1.lean:103 unfolded)
   and `exact_mod_cast key`.

**Piece-free carrier** — clause (D): `carrierfloor_D.floor_D hn hG hS q hemp (cvtS_carrierPolygon_turn_ne hn
hG hS q) halt` gives `mindegAZ groupedPoly = 0 ∧ slot ≤ 0`; `rw [hmin]; exact hle`.

Deviations from the §4 sketch (route only, no statement effect):
* §4 names `geoCornerPolygon_turn_ne_zero` (SM/GeoCornerPolygon.lean:580) for the nonzero turns.  That lemma
  is about the **chirotope sign** `SM.turn … k ≠ 0` (`SignType`, SM/Chirotope.lean:13), not the real
  `principalTurn`.  The clean bridge is its neighbour `geoCornerPolygon_det_ne_zero` (:566, `det(δ_{k−1}, δ_k)
  ≠ 0`) fed to the accepted CV:def:turn sentence `principalTurn_ne_zero_of_det` (CV/Setup.lean:223, "if
  det(δ_{i−1},δ_i) ≠ 0 it is nonzero"), with the regular pair from `geoCornerPolygon_regular hn
  (CarrierGeometry.ofCV hG) …` (SM/GeoCornerPolygon.lean:633).  This is helper `cvtS_carrierPolygon_turn_ne`.
* §4 mentions `carrierR_cast` (CV/X1.lean:120); the file's `rotAbs_intCast_real` (which already composes
  `rotAbs_cast` with `rot_eq_rotationNumber`) applied at `carrierPolygon_cvRegular hn hG hS q` is shorter and
  `carrierR` unfolds to exactly that `rotAbs` (helper `cvtS_carrierR_real`).

## Helpers added (all in `namespace CV`, `noncomputable section`, immediately before the leaf's docstring)

| name | statement | proof |
|---|---|---|
| `cvtS_carrierPolygon_turn_ne` | `∀ j, principalTurn (geoCornerPolygon hG.crossingGeometry S q) j ≠ 0` (binders `hn hG hS q`) | `principalTurn_ne_zero_of_det (geoCornerPolygon_regular hn (CarrierGeometry.ofCV hG) (geoIndependent_of_mem_Ind _ hS) q j) (geoCornerPolygon_det_ne_zero hn hG.weakGeneric (geoIndependent_of_mem_Ind _ hS) q j)` |
| `cvtS_carrierFloorCHyp` | `SM.CarrierFloorCHyp (geoCarrierPolyComp hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)) (geoIndependent_of_mem_Ind _ hS) q) (carrierDiagram hn hG hS q)` given `halt : UniformOrOneDissentCV (geoCornerPolygon …)` | fields: `shadow := rfl` (`geoPositiveLift_Γ`), `positive := geoPositiveLift_isPositive hn _ _ q`, `turn_exists := geoCornerPolygon_regular hn (ofDiagrammatic …) … q`, `turn_ne := cvtS_carrierPolygon_turn_ne …`, `turn_lt_pi := abs_lt.mpr (principalAngle_bounds (geoCornerPolygon_regular … i))`, `generic := geoCarrierShadow_generic hn _ _ q` (SM/GeoPositiveLift.lean:511), `alternative := halt` (defeq: `principalTurn_eq_sm`, `reversal` shared) |
| `cvtS_carrierR_real` | `((carrierR hn hG hS q : ℤ) : ℝ) = \|rotationNumber (geoCarrierPolyComp … q).P\|` | `rotAbs_intCast_real _ (carrierPolygon_cvRegular hn hG hS q)` |

No INTERFACE PROPS were needed (the leaf is unconditional on accepted inputs plus the hypothesis
`hC : SM.CarrierFloorCData`, exactly as stated).  ~75 lines added in total (helpers + leaf body + docstrings).

## The §7-ranked risk 7 ("hypothesis assembly") — how it resolved

* `geoCarrierPolyComp … = polyComp (geoCornerPolygon …) _`: **never needed**.  SM's (C) is applied at the
  component `geoCarrierPolyComp` itself (the shadow of `carrierDiagram` is literally `Shadow.single
  (geoCarrierPolyComp …)`, `rfl`), and `(geoCarrierPolyComp …).P = geoCornerPolygon …` is `rfl`
  (`geoCarrierPolyComp_P`).  No `PolyComp.ext`.
* `CarrierGeometry.ofCV hG` vs `CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)` vs `hG.weakGeneric`:
  all three carrier-geometry / crossing-geometry proofs (`(ofCV hG).cg`, `(ofDiagrammatic …).cg =
  (hG.diagrammatic hn).crossingGeometry`, `weak_crossingGeometry hG.weakGeneric = hG.crossingGeometry`) are
  proofs of the `Prop` `CrossingGeometry P`; Lean's `isDefEq` identifies them by proof irrelevance, so
  `hS : GeoIndependent hG.crossingGeometry S`, `q`, `j : ZMod (geoCornerCount …)` and the corner polygon
  itself transport without any `▸`/cast.  Likewise the `NeZero` instances (`PolyComp.instNeZeroK` vs
  `geoCornerCount_neZero`, `NeZero` is a `Prop` class) inside `rotationNumber`/`rotAbs`.

## Mathlib / Lean pitfalls met

1. **Prop placeholders are not inferred.**  `geoCornerPolygon_regular hn _ _ q` fails with "don't know how to
   synthesize placeholder for argument `hG`/`hS`" even though the expected type determines them up to
   proof irrelevance — the unifier does not assign a `Prop` metavariable from a proof-irrelevant match.
   Pass `CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)` and `geoIndependent_of_mem_Ind
   hG.crossingGeometry hS` explicitly (done in `turn_exists`, `turn_lt_pi`).  The `_ _` in `positive` and
   `generic` *did* resolve because there the metavariables are fixed by the term structure
   `geoPositiveLift hn ?hG ?hS q =?= carrierDiagram …`.
2. `rw [hR] at hfloor` with `hR` stated on `geoCornerPolygon hG.crossingGeometry S q` would not have found
   `|rotationNumber (geoCarrierPolyComp …).P|` syntactically; stating the helper on the `geoCarrierPolyComp`
   form and rewriting in a **restated goal** (`have key : … := by rw [cvtS_carrierR_real …]; exact hfloor`)
   avoids the syntactic-match problem and lets `exact` do the defeq work.
3. `principalTurn` inside `namespace CV` resolves to `CV.principalTurn` (current-namespace declarations
   shadow `open SM`); it is `rfl`-equal to `SM.principalTurn`, so the SM bundle's `turn_ne` field accepts a
   CV-stated helper without `principalTurn_eq_sm`.
4. Timing: with `lake env lean` and warm `.olean`s the 1000-line file elaborates in ~20 s even at load ~20;
   a truncated copy (lines 1 – leaf + `end`/`end CV`) is a convenient scratch and takes the same time.

## For the assembler / executor

* Merge = take `U_SLOT.lean` lines from `/-- U-SLOT helper (`cvtS_`): every principal turn …` through the
  leaf's `exact hle` (they sit between `CarrierSlotFloor.coeff_zero` and the §2 row-165 header, inside
  `namespace CV` / `noncomputable section`).  No import added, no `open` changed.
* When the leaf is ported next to `CarrierSlotFloor` (PLAN §6 U-155 → `CV/CarrierFloor.lean`, or wherever
  `CarrierSlotFloor` lands), the three helpers go with it; `cvtS_carrierPolygon_turn_ne` is general-purpose
  ("all principal turns of a carrier's corner polygon are nonzero", CV vocabulary, tier 2) and may deserve a
  home in `CV/X1.lean` beside `carrierPolygon_cvRegular` — the executor's call; the name prefix is then
  dropped per the repo's conventions.
* Row closure is unchanged: `singleton_D_i := singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C
  SM.cf_thm_carrierfloor.clauseC)` still waits on row 99 (C) and U-SPLIT; the RA units may now consume
  `CarrierSlotFloor` through `carrier_slot_floor_of_C hC` with `hC` as their standing hypothesis.
* No statement was found FALSE and no extra hypothesis is needed.
