# Plan: def:C (corner coefficient and the corner state sum) — work/drafts/CornerStateSum.lean

Source: reference/SM/sm-3-statesum.tex:1688-1700 (def:C); ℓ(P) is def:chirotope, sm-1-polygons.tex:69
("ℓ(P) = #{i : τ_i(P) = 1}"); m_Q, r_Q, uniform: def:uniform (sm-3:242-247); consumer lem:C-X1 at 1787.
Design record: work/reports/design-decision-diagram-record-20260913.md:93, 174, 217, 240
(`cornerCoefficientWith H` then `cornerCoefficient := cornerCoefficientWith homfly`; `cornerStateSum hn hP : ℤ`
with no free hypothesis, summing over `(independentSupports hn hP).filter UniformDecomposition`; integer
rotation "via rotationNumber_integer + carriers regularity").

## Printed symbol -> accepted library name (file:line)

| printed | Lean | where |
|---|---|---|
| generic polygon P, n ≥ 3 | `(hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)`, `[NeZero n]` | convention of UniformDefinition.lean:20 |
| Ind(G_P), "S ∈ Ind(G_P)" | `independentSupports hn hP`, `IsDecomposition hn hP S := S ∈ independentSupports hn hP` | InterlaceSupports.lean:28; DecompositionDefinition.lean:16 |
| subpolygon Q of S | `q : Carrier.Component hn hP S` (Fintype: `componentFintype`) | CarrierSmoothing.lean:124,161 |
| m_Q | `Carrier.carrierCrossingCount hn hP S q : ℕ` | CarrierCrossings.lean:62 |
| r_Q | `carrierRotation hn hP S q : ℝ` (= `rotationNumber (ccpCornerPolygon …)`) | UniformDefinition.lean:42 |
| r_Q ∈ ℤ | `rotationNumber_integer (h : Regular P) : ∃ k : ℤ, rotationNumber P = k`; `Carrier.ccpCornerPolygon_regular hn hP hS q` | RotationNumber.lean:46; CarrierCornerPolygon.lean:678 |
| S uniform | `UniformDecomposition hn hP S` | UniformDefinition.lean:37 |
| ℓ(P) | `leftTurns P : ℕ := (univ.filter fun i => turn P i = 1).card` | Chirotope.lean:16 |
| positive lift of Q | `Link.positiveLift hn hP S q (hS : IsDecomposition hn hP S) : Link.Diagram` | LinkPositiveLift.lean:596 |
| its crossings positive / writhe = m_Q | `Link.positiveLift_isPositive`, `Link.positiveLift_writhe_eq_carrierCrossingCount` | LinkPositiveLift.lean:618,820 |
| H (HOMFLY–PT), ring ℤ[a^{±1},z^{±1}] | `homfly : Link.Diagram → Link.R` (Classical.choose of axiom `lit_homfly`) | LinkInterfaces.lean:131; LinkLaurentRing.lean:76 |
| [a^d z^k] f, "zero if absent" | `Link.coeffAt d k f : ℤ := f.coeff (d, k)`; `coeffAt_eq_zero_of_notMem_support`, `mem_support_iff_coeffAt_ne_zero` | LinkLaurentRing.lean:286,316,320 |

## Rendering decisions

1. r_Q is accepted as a REAL (`carrierRotation : ℝ`); the slot d_Q must be an INTEGER for `coeffAt`. I define
   `carrierRotationInt hn hP S q : ℤ := round (carrierRotation hn hP S q)` (hypothesis-free) and prove
   `carrierRotationInt_cast : IsDecomposition hn hP S → (carrierRotationInt … : ℝ) = carrierRotation …`
   (from `rotationNumber_integer` + `ccpCornerPolygon_regular` + `round_intCast`). Then
   `cornerSlot hn hP S q : ℤ := 1 - m_Q - |carrierRotationInt …|`, with the bundle field
   `((cornerSlot …) : ℝ) = 1 - m_Q - |carrierRotation …|` for decompositions (the printed formula verbatim).
   (`round` rather than `Classical.choose` so that d_Q needs no membership proof; the two agree on decompositions.)
2. c(Q) needs the positive lift, which needs `hS : IsDecomposition hn hP S`; c(Q) is printed only for subpolygons of
   decompositions, so `cornerCoefficientWith (H) hn hP S q hS` and `cornerCoefficient hn hP S q hS` carry `hS`
   explicitly (no junk value off decompositions). H⁺_Q is `cornerHomfly hn hP S q hS := homfly (positiveLift …)`.
3. Threading `hS` through the sum: `uniformDecompositions hn hP := (independentSupports hn hP).filter (UniformDecomposition hn hP)`
   (decidability by `Classical.propDecidable`, the InterlaceSupports convention), and the sum runs over
   `(uniformDecompositions hn hP).attach`, the summand using `(Finset.mem_filter.1 S.2).1 : IsDecomposition`.
   `attach` chosen over `dite`/junk-0 because it keeps every `c(Q)` a genuine coefficient of a genuine positive lift;
   `Finset.sum_attach`/`Finset.sum_filter` convert to consumer-friendly forms (a dite form over `independentSupports.attach`
   is provided as a theorem for lem:C-X1).
4. `cornerProduct hn hP S hS := ∏ q : Component hn hP S, cornerCoefficient …` (Fintype product = "∏_{Q subpolygon of S}").
5. `cornerStateSum hn hP : ℤ := (-1) ^ leftTurns P * ∑ S ∈ (uniformDecompositions hn hP).attach, (-1) ^ S.1.card * cornerProduct hn hP S.1 (…)`.

## Bundle `CornerStateSumDefinitionData` (one field per printed clause)
positive_lift (H⁺_Q := homfly of the def:positive-lift diagram; all crossings positive; writhe = m_Q — cited),
rotation_integer, slot (ℤ unfolding + ℝ printed formula), coefficient (unfolding to `coeffAt`/`coeff`),
coefficient_absent (zero if the monomial is absent, and the converse), coefficient_with (instantiation at `homfly`),
uniform_index_set (S ∈ Ind(G_P) ∧ S uniform), product, state_sum (printed formula, `rfl`).
Ends with `#print axioms SM.corner_state_sum_definition` — expected: propext, Classical.choice, Quot.sound, SM.lit_homfly.

## Result (2026-09-13)
`cd work/lean && lake env lean ../drafts/CornerStateSum.lean`: no errors, no warnings, 0 `sorry`, 308 lines;
`#print axioms SM.corner_state_sum_definition` = [propext, Classical.choice, Quot.sound, SM.lit_homfly].
Toolchain note: `dif_pos/dif_neg/if_pos/if_neg` are deprecated here; use `dite_eq_left/dite_eq_right/ite_eq_left/ite_eq_right`.
