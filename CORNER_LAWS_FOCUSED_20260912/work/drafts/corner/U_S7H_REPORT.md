# U_S7H_REPORT — unit U110-H (two-component row; helper unit, prefix `s7h_`), 2026-09-15

File: `work/drafts/corner/U_S7H.lean` (byte-identical copy of `Statements_FINAL.lean` + 315 added lines, 1079 total).
Check: `cd work/lean && lake env lean ../drafts/corner/U_S7H.lean` — **0 errors, 0 non-sorry warnings**, 14
`declaration uses sorry` warnings (the 10 leaves of the other units + the 4 row theorems of §6), 15 s warm.
`grep -c sorry`: 16 before → 16 after (helper unit: no leaf of its own, no sorry added or removed).
`diff Statements_FINAL.lean U_S7H.lean`: 0 removed lines, 315 added lines — one block inserted inside
`section VertexEdge` immediately before the docstring of `s7_bigon_law_at` (the first leaf that consumes it,
U110-K).  No definition, structure, statement, name or docstring changed; no import added; no new `def`.
Clash scan `grep -rn "s7h_" work/lean/SM work/lean/CV`: empty.

## 0. What the unit renders (PLAN_FINAL §3.3 (3), §4 row U110-H)

PLAN §3.3 (3): "two-component row (U110-H): `homflyrows.two_component_row` (MarkedProducts.lean:323/381,
`two_component_row_of_lowest` :2500) with `twoLinking D_A 0 1 = 2ℓ` (:144), writhe counts
eq. s7c:interlacing-writhe-row / s7c:noninterlacing-writhe from `positiveLift_writhe_eq_carrierCrossingCount`
(LinkPositiveLift.lean:820) + the crossing partition."  The plan gives no fixed Lean statements for this unit;
the ones below are the rendering, chosen so that U110-K can substitute the actual lifts with no geometry:

| printed (sm-4) | lemma | statement |
|---|---|---|
| s7c:crossing-partition rows 1-2, "their actual knot restrictions" | `s7h_writhe_knotRestrict` | `(D.knotRestrict i).writhe = ∑ x ∈ univ.filter (over.1 = i ∧ under.1 = i), sign x` |
| s7c:crossing-partition row 3, `2ℓ = twoLinking` | `s7h_mixedSignSum_eq` | `mixedSignSum D i j = ∑ x ∈ univ.filter (mixed (i,j) or (j,i)), sign x` (`i ≠ j`) |
| "the self crossings contribute `w₁+w₂`, the mixed crossings of `D_A` contribute `2ℓ`" (649-651) | `s7h_writhe_two_component` | `c = 2, i ≠ j ⊢ D.writhe = (D.knotRestrict i).writhe + (D.knotRestrict j).writhe + twoLinking D i j` |
| `ℓ = lk(D_A)` (533, "linking of its named ordered components") | `s7h_twoLinking_even` | `∃ l, twoLinking D i j = 2 l` (mp:zero-link `half_sum_integer`) |
| "the smoothed crossing `q` contributes one" (651) | `s7h_record_writhe_smooth`, `s7h_writhe_of_smooth_iso` | `(ρ.smooth v).writhe = ρ.writhe − sgn v`; `Nonempty (RecordIso D₀.record (D.record.smooth v)) ⊢ D₀.writhe = D.writhe − sign v.1` |
| "one actual ordered two-component diagram `D_A`" (496-497) | `s7h_componentCount_of_smooth_iso`, `s7h_exists_smoothing_two_component` | `c(D) = 1 ⊢ c(D₀) = 2`; `∃ D₀, IsOrientedSmoothing ∧ record clause ∧ c = 2 ∧ w = w(D) − 1` at a positive crossing |
| s7c:interlacing-writhe-row (2nd identity) `w_L = w₁+w₂+2ℓ−1`, s7c:pre-curl-writhe, s7c:noninterlacing-writhe | `s7h_writhe_low` | record clause at a positive occurrence, `c(D_A) = 2`, `w_H = w_L + 2` ⊢ `w_L = w(D_A∣ᵢ) + w(D_A∣ⱼ) + 2ℓ − 1` |
| `w_H = w_L + 2` from def:positive-lift "Its writhe is `m_Q`" | `s7h_lift_writhe_add_two` | `m_{q₊} = m_{q₋} + 2 ⊢ w(positiveLift q₊) = w(positiveLift q₋) + 2` |
| s7c:interlacing-slot `k_L = K − 2ℓ` | `s7h_interlacing_slot` | `ℤ` arithmetic |
| s7c:noninterlacing-slot `K − k_L = 2ℓ + 2` | `s7h_noninterlacing_slot` | `ℤ` arithmetic |
| lem:homflyrows `[z⁻¹]H_D = (a−a⁻¹)a^{−2ℓ}[z⁰](H_{D₁}H_{D₂})`, coefficientwise (666-668) | `s7h_two_component_coeff` (+ `_homfly`) | `coeffAt d (−1) (P D) = coeffAt (d+2ℓ−1) 0 (Q₁Q₂) − coeffAt (d+2ℓ+1) 0 (Q₁Q₂)` |
| s7c:interlacing-extraction / s7c:noninterlacing-extraction before the slot substitution | `s7h_extraction_two_component` | from `Ω_H = Ω_L + [a^{k_L−1}z^{−1}] P D_A` (the conclusion of `s7_universal_extraction` at `FA := P D_A`): `Ω_H − Ω_L = [a^{k_L+2ℓ−2}z⁰](Q₁Q₂) − [a^{k_L+2ℓ}z⁰](Q₁Q₂)` |

Design decision (FR for the executor).  The writhe counts are stated in **`D_A`-component form**: `w(D_A.knotRestrict i)`
rather than the printed `w_i = w(D_i)` of eq. s7c:component-data.  For `ε = 1` these coincide (`D_A^{post} = D_A`).  For
`ε = 0` the printed `w_1` is the writhe AFTER the R-I deletion of the curl `y`; by eq. s7c:pre-curl-writhe
`w(component₁(D_A)) = w₁ + 1`, so `s7h_writhe_low` gives `w_L = (w₁+1) + w₂ + 2ℓ − 1 = w₁ + w₂ + 2ℓ`, exactly
eq. s7c:noninterlacing-writhe — one lemma covers both branches, and the curl deletion (U110-G's NO-GO item) is
consumed only where the printed proof consumes it (`Q₁` after deletion).  Likewise the row is on `P (D_A.knotRestrict i)`;
the identification of these with the half contact carriers' lifts (`Q_i`, eq. s7c:component-polynomial, and the
`ε = 0` curl) is U110-B/G/K material, not this unit's.  `2ℓ` is always `twoLinking D_A i j` (never a half); the printed
`a^{−2ℓ}` reads `aPow (−twoLinking …)` and the coefficient shifts by `± twoLinking` — no division by 2 anywhere.

## 1. Proved (all inside `section VertexEdge`, before `s7_bigon_law_at`; `#print axioms` in a scratch copy)

Standard axioms only (`[propext, Classical.choice, Quot.sound]`): `s7h_writhe_restrict`, `s7h_self_iff`,
`s7h_writhe_knotRestrict`, `s7h_mixedSignSum_eq`, `s7h_comp_eq_or`, `s7h_exists_two_components`,
`s7h_writhe_two_component`, `s7h_twoLinking_even`, `s7h_record_writhe_smooth`, `s7h_writhe_of_smooth_iso`,
`s7h_componentCount_of_smooth_iso`, `s7h_exists_smoothing_two_component`, `s7h_writhe_low`,
`s7h_lift_writhe_add_two`, `s7h_interlacing_slot`, `s7h_noninterlacing_slot`.
`+ lp_lm` (through `SM.P` / `two_component_row_of_lowest`): `s7h_two_component_coeff`, `s7h_extraction_two_component`.
`+ lit_homfly, lp_lm, lp_lm_uniqueness` (through `P_eq_homfly`): `s7h_two_component_coeff_homfly`.
All within the plan's policy set.

Accepted inputs used: `two_component_row_of_lowest` (MarkedProducts.lean:2500), `CV.zRow_zero_mul_of_inSupportM_one`
(CV/Axioms.lean:154), `P_knotRestrict_inSupportM_one` (MarkedProducts.lean:2239), `coeff_T_mul'`, `aPow`,
`coeff_zRow`, `LaurentPolynomial.T_add`, `P_eq_homfly`; `Shadow.restrictCrossingEquiv`, `Diagram.restrict_sign`,
`Diagram.val_eq_pair`, `Diagram.eq_over_under_of_crossing_eq` (MarkedProducts.lean:1873), `Diagram.sign_eq_one_or_neg_one`,
`Diagram.isPositive_iff_sign_eq_one`; `Record.two_mul_writhe`, `Record.smooth_sgn`, `Record.sgn_pair`, `Record.pair_ne`,
`Record.SmoothKeep`, `Record.componentCount_smooth_of_self` (LinkRecordExtras.lean:316), `RecordIso.writhe_eq`,
`RecordIso.componentCount_eq`, `Diagram.record_writhe/record_sgn/record_componentCount/record_isSelfCrossing_iff`,
`exists_smoothing_record_visit` (Smoothing.lean:8185), `zero_link.half_sum_integer` (ZeroLink.lean),
`positiveLift_writhe_eq_carrierCrossingCount` (LinkPositiveLift.lean:820).  No geometry: the smoothing enters only
through its record clause (the same clause U110-G's `s7g_skein_at_positive` returns for its `D₀`, so K applies these
lemmas to G's diagram directly).

## 2. Not proved / left to other units

* Nothing of this unit's content is left.  Not attempted (other units' content): the identification of
  `D_A.knotRestrict i` with the half contact carriers' positive lifts (`Q_i`, `w_i`; U110-B through the CB record
  bridge `positiveLiftRecordIso`), the `ε = 0` curl deletion (`RIData`, U110-G NO-GO), the crossing partition
  `m_H = m_L + 2` feeding `s7h_lift_writhe_add_two` (U110-A/B), the rotation identities `R_L = R₁ + R₂` /
  `R₁ + R₂ − R_L = −1` feeding the slot lemmas (U110-I), the floor reads at `K−2, K` / `K−4, K−2` (U110-J).
* `IsOrientedSmoothing` alone (without the record clause) gives no writhe count here: `OutsideMatch`
  (LinkMoves.lean:316) carries an outer-crossing bijection `ψ` with over/under correspondence but no sign lemma; the
  record clause of `exists_smoothing_record_visit` is the accepted route and is what G's lemma supplies.

## 3. Mathlib / library pitfalls met

* `Finset.sum_subtype {F : Fintype (Subtype p)} (s) (h) (f) : ∑ a ∈ s, f a = ∑ a : Subtype p, f ↑a` has an IMPLICIT
  `Fintype` instance that must be unified from the goal: use it with `exact (Finset.sum_subtype s (fun x => by simp) f).symm`
  giving `s` and `f` explicitly (the `by simp` for `h` is elaborated last); a forward `rw [Finset.sum_subtype …]`
  fails ("did not find pattern", and `F` would stay a metavariable).
* `(ρ.smooth v).M` is only definitionally the subtype `{w // ρ.SmoothKeep v w}`; bridge sums over it with
  `Fintype.sum_equiv (Equiv.refl _ : (ρ.smooth v).M ≃ {w : ρ.M // ρ.SmoothKeep v w}) _ _ (fun w => rfl)` (the two
  `Fintype` instances differ syntactically; `show` may fail under the file's `Classical.propDecidable` local instance).
* `omega` does not beta-reduce: `have h := Finset.sum_filter_add_sum_filter_not univ p (fun w => …)` leaves atoms
  `(fun w => …) x` that never match the other hypotheses — state such a hypothesis with its type written out.
* `dif_pos` / `dif_neg` are deprecated → `dite_eq_left (h : c) : dite c t e = t h`, `dite_eq_right (h : ¬c)`.
* In any lemma with a polygon binder named `P`, write `SM.P` for the polynomial (as in U110-G's report); here the
  lift lemma uses `Pp Pm` to avoid the shadowing altogether.
* Namespaces: `two_component_row_of_lowest`, `mixedSignSum`, `P_knotRestrict_inSupportM_one`, `zero_link` are `SM.…`;
  `twoLinking`, `Diagram.knotRestrict`, `coeff_T_mul'`, `aPow`, `coeffAt_aInv_mul` are `SM.Link.…` (reachable via the
  file's `open Link`); `ZeroLink.mixedPair_iff` is `SM.ZeroLink.…`.
* `(p − q).coeff d = p.coeff d − q.coeff d` on `LaurentPolynomial ℤ` is definitional (`show … - … = _` works;
  `exact?` returns a `rfl`-shaped term); `coeff_zRow` then turns each `(zRow k f).coeff d` into `coeffAt d k f`.
* A sum over ordered strand pairs with a dependent `if h : MixedPair … then … else 0` is best moved to crossings by
  `← Finset.sum_product'` + `Finset.sum_bij_ne_zero` (the crossing `⟨{s,t}, h.2.2⟩` is only needed where the term is
  nonzero, where `MixedPair` is recovered by `by_contra hm; exact hne (dite_eq_right hm)`).

## 4. Notes for the assembler / executor

* Position: the block starts with `/-! ### Unit U110-H …` and ends with `s7h_extraction_two_component`, immediately
  before the docstring `/-- The bigon branch (sm-4:407-874): …` of `s7_bigon_law_at`, inside `section VertexEdge`.
  U110-G's block sits AFTER `s7_bigon_law_at` (before `s7_universal_extraction`); U110-K's proof of `s7_bigon_law_at`
  will need both G's `s7g_*` and this unit's `s7h_*` — the assembler must place K's material after G's block (or move
  the leaf below the two algebra leaves) when concatenating.
* How K composes them (interlacing row, sm-4:638-668): `s7_universal_extraction FH FL (SM.P DA) kL hsk` gives `hext`;
  `s7h_extraction_two_component DA i j h2 hij hext` gives `Ω_H − Ω_L = [a^{k_L+2ℓ−2}](Q₁Q₂) − [a^{k_L+2ℓ}](Q₁Q₂)`;
  `s7h_writhe_low` + `s7h_lift_writhe_add_two` + U110-I's `R_L = R₁ + R₂` + `s7h_interlacing_slot` give
  `k_L + 2ℓ = K`; `s7_corner_product` (U110-J) reads the two coefficients.  Noninterlacing (736-769): the same with
  `w(D_A∣₁) = w₁ + 1` (curl), `s7h_noninterlacing_slot` (`k_L + 2ℓ = K − 2`) and `coeffAt_mul_eq_zero_of_lt_floor` at
  `K−4, K−2`.
* `h2 : DA.componentCount = 2` comes from `s7h_componentCount_of_smooth_iso` with `positiveLift_componentCount`
  (LinkPositiveLift.lean:610, `rfl`) for `D_H`; the two indices `i ≠ j` from `s7h_exists_two_components` (the printed
  "component 1 / component 2" order is fixed by which component contains the `A`-boundary successor — U110-B).
* Diff summary: `+` 315 lines, `−` 0 lines.
