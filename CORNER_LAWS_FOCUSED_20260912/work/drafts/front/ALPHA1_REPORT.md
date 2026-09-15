# Lane α, unit α1 — row 73 ng:front-domain (DEFINE row) — report, 2026-09-14

File: `work/drafts/front/FrontSmooth.lean` (intended home `work/lean/SM/FrontSmooth.lean`), 1338 lines,
185 declarations, **sorry-free** (`grep sorry|admit|native_decide` → none).
Check: `cd work/lean && lake env lean ../drafts/front/FrontSmooth.lean` → no errors, no warnings, exit 0
(Lean v4.34.0-rc2, Mathlib pin of the project; ~17 s).
Main declaration: `SM.front_domain_definition : SM.FrontDomainDefinitionData` (PROVED).
`#print axioms SM.front_domain_definition` → `[propext, Classical.choice, Quot.sound, SM.lp_lm]`
(`SM.lp_lm` enters only through `P` in the `defect` field; every other lemma in the file is on the
standard three axioms — checked for `isDownCusp_xor_isUpCusp`, `isLeftCusp_xor_isRightCusp`,
`det_pos_iff_of_slope_lt`, `germFront_semicubical`, `germFront_cuspDisc`,
`germFront_later_arm_higher_iff`, `crossingPairs_xor_swap`, `downCount_add_upCount`,
`isRounding_iff`, `Marking.componentCount_eq`, `GeomRounding.eq_of_mem_I_of_sameParam`,
`SmoothLoop.toClosedC1Curve`).

Design followed: `work/reports/front-block-design-FINAL-20260913.md` §0-§5, §9 FR-1..FR-4, §11
(TAG B smooth class + graft G2 `GeomRounding`), sketch §1-§5. Namespace: `SM` (class `SM.SmoothFront`,
row theorem `SM.front_domain_definition`, as the brief names them; the sketch's `SM.Front` prefix is
not used). Imports: `SM.PolynomialBlock` (P, degAZ, RecordIso, Diagram.record, IsDisc), `SM.TurningNumber`
(`ClosedC1Curve`, for the reuse bridge), and the Mathlib calculus modules of the sketch plus
`Deriv.Shift` (periodicity of `deriv`).

## 1. Printed clause → bundle field (sm-3:1825-1841)

| # | printed clause | field of `FrontDomainDefinitionData` | Lean content | proof |
|---|---|---|---|---|
| 1 | "A front F is an actual map of a nonempty finite union of parameter circles to the oriented (x,z) plane" | `map` | `0 < F.c ∧ ∀ i, ContDiff ℝ ∞ (F.comp i).γ ∧ Periodic (F.comp i).γ 1` | class fields |
| 2 | "with finitely many transverse double points" | `double_points` | `doubleSet` enumerates the ordered pairs of distinct fundamental-period parameters with equal image; `IsDouble p q → det (vel p) (vel q) ≠ 0` | `mem_doubleSet`, `det_vel_ne_zero_of_isDouble` |
| 3 | "and ordinary semicubical cusps" | `cusps` | `cuspSet` enumerates the zeros of `γ'` in `[0,1)`; `IsCusp p → det (acc p) (jerk p) ≠ 0` (FR-2) | `mem_cuspSet`, `det_acc_jerk_ne_zero_of_isCusp` |
| 4 | "no other singularities" | `no_other_singularities` | `vel p = 0 ↔ IsCusp p` (every non-immersive parameter is a cusp of #3) ∧ no triple point | `Iff.rfl`, class `no_triple` |
| 5 | "and no vertical tangencies on regular arcs" | `no_vertical` | `vel p ≠ 0 → (vel p).1 ≠ 0` | class field |
| 6 | "The limiting tangent at every cusp is also nonvertical: in a semicubical parameter u with cusp at u=0, require x''(0)≠0" | `cusp_nonvertical` | `IsCusp p → (acc p).1 ≠ 0` (FR-2) | class field |
| 7 | "Cusps meet no other strand or singularity." | `cusp_alone` | `¬SameParam p q → IsCusp p → eval p ≠ eval q` | class field |
| 8 | "At a crossing the branch with smaller dz/dx is over." | `over_rule` | `slope = (vel).2/(vel).1`; `IsOverUnder p q ↔ IsDouble p q ∧ slope p < slope q`; `IsDouble p q → Xor (IsOverUnder p q) (IsOverUnder q p)` | `rfl`, `Iff.rfl`, **`isOverUnder_xor`** (slopes of a transverse nonvertical pair differ: `slope_ne_of_isDouble`) |
| 8' | sanity of the over rule vs. the sign convention (sm-3:1908-1912, "the over-first tangent representatives (1,−1),(1,1) have determinant 2, so this crossing is positive") | `over_first_sign` | `det_pos_iff_of_slope_lt` (vector form); `det (1,−1) (1,1) = 2`; on a front `IsOverUnder p q → (crossSign p q = 1 ↔ 0 < (vel p).1 * (vel q).1)` | **proved** (`det_pos_iff_of_slope_lt`, `det_standard_crossing`, `crossSign_eq_one_iff_of_isOverUnder`) |
| 9 | "A downward cusp is traversed from its locally upper arm to its locally lower arm." | `downward_cusp` | `IsDownCusp p ↔ IsCusp p ∧ x''·det(γ'',γ''') < 0`; `IsUpCusp` with `0 <`; `IsCusp p → Xor (IsDownCusp p) (IsUpCusp p)` (FR-2) | `Iff.rfl`, **`isDownCusp_xor_isUpCusp`** |
| 9' | left / right cusp (words of sm-3:1906-1907) | `left_right_cusp` | `IsLeftCusp ↔ IsCusp ∧ 0 < x''`, `IsRightCusp ↔ IsCusp ∧ x'' < 0`, `Xor` | **`isLeftCusp_xor_isRightCusp`** |
| 10 | "Write D(F) for the number of downward cusps" | `D_count` | `downCount = (cuspSet.filter IsDownCusp).card`; `downCount + upCount = cuspSet.card` | `rfl`, **`downCount_add_upCount`** |
| 11 | "w(F) for the sum of the over-first tangent-determinant crossing signs" | `w_sum` | `writhe = ∑ q ∈ crossingPairs, crossSign q.1 q.2`; `crossingPairs = doubleSet.filter (slope q.1 < slope q.2)`; each double point enters exactly once (`Xor (q ∈ crossingPairs) (q.swap ∈ crossingPairs)`); `crossSign p q = sign (det (vel p) (vel q))` in ℤ | `rfl`, `mem_crossingPairs`, **`crossingPairs_xor_swap`**, **`crossSign_eq_sign`** |
| 12 | "and s(F) for the number of crossings plus cusps." | `s_count` | `sCount = crossingPairs.card + cuspSet.card` | `rfl` |
| 13 | "In disjoint clean cusp discs" | `rounding_discs` | for every `GeomRounding F G` and cusp `c`: `IsDisc (U c)`, `eval c ∈ interior (U c)`, pairwise `Disjoint`, `clean` (a front point in `U c` has a parameter in `I c` mod 1 on the cusp's circle) | structure fields |
| 14 | "replace each cusp by a simple regular arc … and no crossing" | `rounding_arc` | `I c = Ioo a b`, `a < cusp < b`, `b − a < 1`; the arc `G` on `I c` lies in `U c`, is regular, `InjOn`, and meets no other point of `G` | structure fields |
| 15 | "with the same oriented attachments" | `rounding_attachments` | `G i = F.comp i` at every `t` whose orbit `t + ℤ` avoids all `I c` on circle `i` (FR-4; same circles, same orientation, literally the same end points) | structure field `agree` |
| 16 | "The resulting ordinary diagram is denoted S(F)." | `resulting_diagram` | `IsRounding F S ↔ ∃ G : SmoothFront, ∃ hc : G.c = F.c, G.CuspFree ∧ Nonempty (GeomRounding F (G.comp ∘ Fin.cast hc.symm)) ∧ Nonempty (G.Marking S)` (FR-1) | **`isRounding_iff`** |
| 16' | the named record read polygonally (FR-1; the items of ng:smoothing-record sm-3:1846-1848) | `named_record` | `S.componentCount = F.c`; occurrence bijection keeps circles, cyclic orders (`cycBetween` ↔ `cycBetween` of `visitCoord`), pairing (`twin`), over/under bits (over = smaller slope), signs (`S.sign = crossSign`) | `Marking` fields + **`Marking.componentCount_eq`** |
| 17 | the printed exact germ `x = x₀+Au², z = z₀+Ay₀u²+⅔Au³` (sm-3:2747) is in the class | `germ` | `ContDiff ℝ ∞ germFront`; for `A ≠ 0`: `γ'(0) = 0`, `det(γ'',γ''')(0) = 8A² ≠ 0`, `x''(0) = 2A ≠ 0`; discriminant `= 16A³`; for `u > 0` the later arm is higher iff `16A³ > 0` | **`germFront_smooth`, `germFront_semicubical`, `germFront_cuspDisc`, `germFront_later_arm_higher_iff`** |
| 18 | display ng:defect (sm-3:1896-1899) `d(F) = deg_a P_{S(F)}`, `B(F) = D − w − d − 1` | `defect` | `dOf F S = degAZ (P S)`; `defect F S = D − w − degAZ (P S) − 1`; `RecordIso S.record S'.record → defect F S = defect F S'` | `rfl`, `rfl`, **`defect_eq_of_recordIso`** (via accepted `presentations`) |

Bold = a genuine theorem (not definitional). Every field of the bundle is discharged in
`front_domain_definition`.

## 2. What is in the file beyond the bundle (for α2 = row 74 and later units)

* `SmoothLoop` API: `continuous`, `differentiable`, `hasDerivAt`, `continuous_deriv`,
  `contDiff_iteratedDeriv`, `deriv_periodic`, `iteratedDeriv_periodic`, `eq_add_int`,
  `deriv_eq_add_int`, `iteratedDeriv_eq_add_int`, `toClosedC1Curve` (a regular circle is the accepted
  `ClosedC1Curve` of TurningNumber.lean — the smooth model is reused, not duplicated; a front
  component cannot be a `ClosedC1Curve` because that class is regular by definition).
* `SameParam`: `refl`, `symm`, `trans`, `eq_of_mem_Ico`, `iff_eq_of_mem_Ico`, `rep`, `rep_mem_Ico`,
  `sameParam_rep` (every parameter has exactly one representative in `[0,1)`).
* `SmoothFront`: invariance of `eval`, `vel`, `acc`, `jerk`, `IsCusp`, `cuspDisc`, `IsDownCusp`,
  `IsUpCusp`, `slope`, `IsOverUnder`, `crossSign` under `SameParam` (the record is read on the
  parameters, FR-3); `acc_ne_zero_of_isCusp`; `vel_ne_zero_of_isDouble` (a double point is not a cusp),
  `vel_fst_ne_zero_of_isDouble`, `slope_ne_of_isDouble`; `crossSign_eq_one_or_neg_one`,
  `crossSign_eq_one_iff`, `crossSign_eq_neg_one_iff`, `crossSign_swap`; `rep_mem_cuspSet`,
  `swap_mem_doubleSet_iff`, `mem_crossingPairs_or_swap`, `not_swap_mem_crossingPairs`,
  `crossingPairs_subset_doubleSet`; `downCount_le_sCount`, `abs_writhe_le` (|w| ≤ #crossings);
  `CuspFree` API (`cuspSet_eq_empty_of_cuspFree`, `cuspFree_iff_cuspSet_eq_empty`,
  `downCount_eq_zero_of_cuspFree`, `sCount_eq_of_cuspFree`, `toClosedC1Curve`); `slNg` (= `w − D`,
  the `sl_Ng` of row 93) with `defect_nonneg_iff` / `defect_nonneg_iff_slNg`: `0 ≤ B(F) ↔ w − D ≤
  −deg_a P_{S(F)} − 1` (the arithmetic identity sm-3:2343 "Substituting ng:defect gives
  ng:front-inequality"; rows 83/93 will state the right-hand side).
* Occurrences: `occSet`, `occSet_finite`, `Occ` (Fintype), `Occ.isDouble_of_ne`,
  `fst/snd_mem_occSet_of_mem_doubleSet`. `Marking`: `c_eq`, `componentCount_eq`, `card_visit_eq`,
  `under_bit`.
* `GeomRounding`: `cusp_mem_I`, `isOpen_I`, `cusp_mem_U`, `cusp_notMem_U_of_ne` (another cusp's point
  is outside this disc), `eq_of_mem_I_of_sameParam` (an arc interval, being shorter than the circle,
  contains at most one representative of each parameter), `inj_arc`, `eval_eq`.
* `Rounding.componentCount_eq`, `IsRounding.componentCount_eq`, `defect_eq_of_P_eq`.

## 3. Readings recorded (printed text over sketch where they differ)

* **FR-1..FR-4** quoted verbatim in the module docstring (from FINAL §9) and cited at `Marking`,
  `Rounding`, `GeomRounding`, the class, and the bundle fields.
* **FR-2 justification** written out in the docstring (why `x''·det(γ'',γ''') < 0` is "upper arm →
  lower arm": Taylor at the cusp, the later arm lies on the `sign det(γ'',γ''')` side of the tangent
  line `ℝγ''`, which is the upper side iff `x'' > 0`), and checked on the printed germ both by the
  derivative values (`16A³`) and by the explicit arm comparison `z(u) − z(−u) = ⁴⁄₃Au³`
  (`germFront_later_arm_higher_iff`).
* The printed germ is taken **with its base point `(x₀, z₀)`** (sm-3:2747); the sketch had translated
  it to the origin.
* "finitely many transverse double points and ordinary semicubical cusps" is read as finitely many
  of each (`doubles_finite`, `cusps_finite`); for a `C^∞` map with the semicubical criterion the
  finiteness of cusps is automatic (isolated zeros of `γ'` on a compact circle), so the field adds no
  strength (documented in the docstring).
* "no other singularities" = every non-immersive parameter is an (ordinary semicubical) cusp and every
  multiple point is a transverse double point (`no_triple`).
* `GeomRounding.interval` asks the replaced arc to be an open parameter interval around the cusp of
  length `< 1` (a proper sub-arc of the circle). This is what "a clean cusp disc" around one cusp
  means (a component with cusps has ≥ 2 of them and the discs are disjoint, so the replaced arc never
  is the whole circle); recorded here as a reading.
* `Rounding.G` is required to be a `SmoothFront` (finitely many transverse doubles, no triple point,
  etc.) and `CuspFree`: this is "ordinary diagram" in the SM's sense (def:positive-lift).
* `IsRounding F S` is an existence statement; **non-vacuity** (that every front has a rounding and
  a polygonal marking of it) is not asserted by the definition and is not proved here (FINAL §8 risk 2:
  it belongs to 76b).

## 4. What is NOT proved / could not be rendered

* The equivalence of the derivative-form cusp criterion with the `(u², u³)` normal form "in a
  semicubical parameter u", and the geometric "locally upper arm" reading of the sign rule for a
  general front (only the germ instance is proved). FINAL §9 FR-2 records this; the optional
  ~500-line Taylor lemma is not attempted in this unit.
* `Fintype.card F.Occ = 2 * F.crossingPairs.card` (each double point has exactly two occurrences; needs
  `no_triple`) — not needed for row 73; useful for row 74 if the crossing count of a marked diagram is
  wanted.
* Nothing about rows 74, 83, 93 is stated here (FINAL §11 puts them in `FrontRecordBridge.lean` /
  `FrontBound.lean`); the only forward-looking items are the arithmetic identity `defect_nonneg_iff`
  and `defect_eq_of_recordIso`.

## 5. Reviewer lenses to expect (pre-empted in the docstrings)

FR-1 (polygonal S(F) via `Marking`), FR-2 (derivative-form cusp criterion and the computed down/up
rule), the `cusps_finite` field, the `b − a < 1` clause of `GeomRounding.interval`, and the reading
of "no other singularities".
