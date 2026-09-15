import CV.Rotation
import SM.TurningNumber

/-! # CV:def:rot, paragraph "Direction loops and smooth curves" (row 144, the remaining part)

Source: reference/R/CV/d1_setup.tex:767–785, inside Definition def:rot (726–787). The polygon part of
the definition (726–765) is BUILT as `CV.Rotation` (`CV.epsRot`, `CV.Admissible`, `CV.rotRay`,
`CV.rot`, `CV.rotAbs`, bundle `CV.RotDefinitionData` / `CV.rot_definition`). This file supplies the
missing paragraph and the combined row-144 declaration `CV.rot_definition_full`.

Decision F6 (work/reports/cv-lane-plan-20260913.md; scout work/reports/turning-number-scout-20260913.md):
the direction-loop, tangent-angle-lift, `tw`, closed-`C¹`-curve and `rot(γ)` notions are defined ONCE,
in the BUILT module `SM.TurningNumber` (row cf:def-turning, sm-3:3514–3541, whose sentences D1–D4, D6, D7
are the same printed text), and re-exported here under CV names:

* `CV.tw L := SM.tw L` — `tw(T) = (θ(1) − θ(0)) / 2π` (773);
* `CV.tangentLoop γ := γ.tangentLoop` — `T_γ = γ'/|γ'|` (778);
* `CV.rotCurve γ := γ.rot` — `rot(γ) = tw(T_γ)` (780) (the name `CV.rot` is the polygon `rot` of 734);
* `CV.Rcurve γ := γ.R` — `R(γ) = |rot(γ)|` (785), the curve case; the polygon case is `CV.rotAbs`.

The types themselves are used under their SM names (`SM.DirectionLoop`, `SM.IsSeamLift`,
`SM.ClosedC1Curve`): a direction loop `T : ℝ/ℤ → S¹` is a 1-periodic continuous `T : ℝ → Plane` of
Euclidean length 1, and a seam lift is a `θ : ℝ → ℝ` continuous on `[0,1]` with
`T s = (cos θ s, sin θ s)` there.

Where CV's wording differs from SM's (scout §1): CV has no D5 sentence ("for a polygon in the regular
locus, rot remains that of Lemma lem:rot") — CV's polygon `rot` is the `ε_i` ray formula of the same
definition, rendered by `RotDefinitionData` — and no transcription note; otherwise the paragraph is
verbatim SM cf:def-turning. The two polygon rotations agree as a theorem (`CV.rot_eq_rotationNumber`,
decision F2, never an identification), which is recorded here as `polygon_R_eq_SM`.

The forward reference "Lemma lem:turnlift constructs the lift and proves that these values do not
depend on its choices, on the seam, or on an orientation-preserving regular reparametrisation" (782–784)
is rendered for the parts that `SM.TurningNumber` proves with the definition (existence of a lift, which
makes `tw` well defined; independence of the lift; independence of the seam). Reparametrisation
invariance is CV lem:turnlift (i) (row 145) and is not part of this row. -/

namespace CV

open SM

/-! ## CV names for the shared definitions (decision F6) -/

/-- `tw(T) = (θ(1) − θ(0)) / 2π` (d1_setup.tex:772–774), for a tangent-angle lift `θ` of the direction
loop `T`: the shared `SM.tw`, evaluated at the chosen lift `SM.DirectionLoop.lift` and equal to the
printed quotient for every seam lift (`SM.tw_eq_of_isSeamLift`). -/
noncomputable abbrev tw (L : SM.DirectionLoop) : ℝ := SM.tw L

/-- `T_γ = γ' / |γ'|` (d1_setup.tex:778), the tangent direction loop of a closed `C¹` regular curve:
the shared `SM.ClosedC1Curve.tangentLoop`. -/
noncomputable abbrev tangentLoop (γ : SM.ClosedC1Curve) : SM.DirectionLoop := γ.tangentLoop

/-- `rot(γ) = tw(T_γ)` (d1_setup.tex:780) for a closed `C¹` regular oriented curve: the shared
`SM.ClosedC1Curve.rot`. (Named `rotCurve` because `CV.rot` is the polygon rotation of 734.) -/
noncomputable abbrev rotCurve (γ : SM.ClosedC1Curve) : ℝ := γ.rot

/-- "For either a polygon or a `C¹` regular closed curve put `R(L) = |rot(L)|`" (d1_setup.tex:784–785),
the curve case: the shared `SM.ClosedC1Curve.R`. The polygon case is `CV.rotAbs` (CV.Rotation). -/
noncomputable abbrev Rcurve (γ : SM.ClosedC1Curve) : ℝ := γ.R

theorem tw_def (L : SM.DirectionLoop) : tw L = (L.lift 1 - L.lift 0) / (2 * Real.pi) := rfl

theorem rotCurve_def (γ : SM.ClosedC1Curve) : rotCurve γ = tw (tangentLoop γ) := rfl

theorem Rcurve_def (γ : SM.ClosedC1Curve) : Rcurve γ = |rotCurve γ| := rfl

/-- The polygon `R(L) = |rot(L)|` of CV (`rotAbs`, cast to `ℝ`) is SM's `polygonR`, by the theorem
`rot_eq_rotationNumber` identifying the two polygon rotations (decision F2). -/
theorem rotAbs_cast_real {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : Regular L) :
    ((rotAbs L hL : ℤ) : ℝ) = polygonR L := by
  rw [rotAbs_cast, Int.cast_abs, rot_eq_rotationNumber hL, polygonR]

/-! ## The row bundle for the paragraph -/

/-- CV def:rot, paragraph "Direction loops and smooth curves" (d1_setup.tex:767–785), clause by clause.
The sentences are those of SM cf:def-turning D1–D4, D6, D7 (sm-3:3514–3535); CV has no D5 sentence
(its polygon `rot` is the `ε_i` formula of `RotDefinitionData`) and no transcription note. -/
structure RotSmoothDefinitionData : Prop where
  /-- (768) "For a continuous loop `T : ℝ/ℤ → S¹`": a direction loop is a continuous, 1-periodic map
  into the unit circle of the oriented plane — `Continuous T`, `T (s + 1) = T s`, `|T s| = 1` — and
  `T s` is the point `planeComplex (T s)` of Mathlib's `Circle` (SM rendering `SM.DirectionLoop`). -/
  direction_loop : ∀ L : SM.DirectionLoop, Continuous L.T ∧ Function.Periodic L.T 1 ∧
    (∀ s, euclideanLength (L.T s) = 1) ∧
    ∀ s, ((L.toCircle s : Circle) : ℂ) = planeComplex (L.T s)
  /-- (768–771) "a tangent-angle lift at a seam is a continuous `θ : [0,1] → ℝ` such that
  `T(s) = (cos θ(s), sin θ(s))`". -/
  tangent_angle_lift : ∀ (T : ℝ → Plane) (θ : ℝ → ℝ), SM.IsSeamLift T θ ↔
    ContinuousOn θ (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, T s = (Real.cos (θ s), Real.sin (θ s))
  /-- (771–774) "Put `tw(T) = (θ(1) − θ(0)) / 2π`": the value for every tangent-angle lift `θ` at
  the seam (`SM.tw_eq_of_isSeamLift`). -/
  tw_eq : ∀ (L : SM.DirectionLoop) (θ : ℝ → ℝ), SM.IsSeamLift L.T θ →
    tw L = (θ 1 - θ 0) / (2 * Real.pi)
  /-- "The integer `tw(T)`" (lem:turnlift (i), 793, where the definition's value is first named an
  integer): the lift increment is a multiple of `2π` because `T 1 = T 0` (`SM.tw_int`). -/
  tw_integer : ∀ L : SM.DirectionLoop, ∃ k : ℤ, tw L = (k : ℝ)
  /-- (775–776) "For a closed `C¹` regular oriented curve `γ : ℝ/ℤ → ℝ²`": 1-periodic, everywhere
  differentiable with continuous derivative `γ'`, and `γ' ≠ 0` everywhere (`γ'` is then 1-periodic
  too). -/
  closed_curve : ∀ γ : SM.ClosedC1Curve, (∀ t, HasDerivAt γ.γ (γ.γ' t) t) ∧ Continuous γ.γ' ∧
    (∀ t, γ.γ' t ≠ 0) ∧ Function.Periodic γ.γ 1 ∧ Function.Periodic γ.γ' 1
  /-- (777–778) "put `T_γ = γ' / |γ'|`", a direction loop (unit length). -/
  tangent_loop : ∀ (γ : SM.ClosedC1Curve) (t : ℝ),
    (tangentLoop γ).T t = (euclideanLength (γ.γ' t))⁻¹ • γ.γ' t ∧
      euclideanLength ((tangentLoop γ).T t) = 1
  /-- (779–780) "`rot(γ) = tw(T_γ)`". -/
  rot_curve : ∀ γ : SM.ClosedC1Curve, rotCurve γ = tw (tangentLoop γ)
  /-- (782–784) "Lemma lem:turnlift constructs the lift and proves that these values do not depend on
  its choices, on the seam, …": the parts proved with the definition — every direction loop has a
  tangent-angle lift at the seam (indeed a global continuous one), so `tw` is well defined; the printed
  quotient is the same for any two seam lifts; and `tw` does not change when the seam is moved
  (`L.shift a` is `s ↦ T (s + a)`). "… or on an orientation-preserving regular reparametrisation" is
  lem:turnlift (i), row 145. -/
  lift_exists_and_independent :
    (∀ L : SM.DirectionLoop, (∃ θ, SM.IsLift L.T θ) ∧ ∃ θ, SM.IsSeamLift L.T θ) ∧
    (∀ (L : SM.DirectionLoop) (θ₁ θ₂ : ℝ → ℝ), SM.IsSeamLift L.T θ₁ → SM.IsSeamLift L.T θ₂ →
      (θ₁ 1 - θ₁ 0) / (2 * Real.pi) = (θ₂ 1 - θ₂ 0) / (2 * Real.pi)) ∧
    ∀ (L : SM.DirectionLoop) (a : ℝ), tw (L.shift a) = tw L
  /-- (784–785) "For either a polygon or a `C¹` regular closed curve put `R(L) = |rot(L)|`": the curve
  case `Rcurve`, and the polygon case `rotAbs` (a natural number, cast to `ℤ`) of `RotDefinitionData`. -/
  R_eq : (∀ γ : SM.ClosedC1Curve, Rcurve γ = |rotCurve γ|) ∧
    ∀ (c : ℕ) [NeZero c] (L : LabelledTuple c) (hL : Regular L), (rotAbs L hL : ℤ) = |rot L hL|
  /-- Where CV's wording differs from SM's: SM's D5 sentence ("for a polygon in the regular locus, `rot`
  remains that of Lemma lem:rot") has no counterpart in CV, whose polygon `rot` is the `ε_i` formula; the
  two agree as a theorem (`rot_eq_rotationNumber`, decision F2), so CV's polygon `R` is SM's `polygonR`. -/
  polygon_R_eq_SM : ∀ (c : ℕ) [NeZero c] (L : LabelledTuple c) (hL : Regular L),
    ((rot L hL : ℤ) : ℝ) = rotationNumber L ∧ ((rotAbs L hL : ℤ) : ℝ) = polygonR L
  /-- Decision F6: the CV names are the SM definitions, definitionally (one definition, two names). -/
  shared_with_SM : (∀ L : SM.DirectionLoop, tw L = SM.tw L) ∧
    ∀ γ : SM.ClosedC1Curve, tangentLoop γ = γ.tangentLoop ∧ rotCurve γ = γ.rot ∧ Rcurve γ = γ.R

theorem rot_smooth_definition : RotSmoothDefinitionData where
  direction_loop := fun L => ⟨L.continuous, L.periodic, L.unit, fun _ => rfl⟩
  tangent_angle_lift := fun _ _ => Iff.rfl
  tw_eq := fun L _ h => SM.tw_eq_of_isSeamLift L h
  tw_integer := SM.tw_int
  closed_curve := fun γ =>
    ⟨γ.hasDerivAt, γ.continuous_deriv, γ.regular, γ.periodic, γ.deriv_periodic⟩
  tangent_loop := fun γ t => ⟨rfl, γ.tangentLoop.unit t⟩
  rot_curve := fun _ => rfl
  lift_exists_and_independent :=
    ⟨fun L => ⟨L.exists_lift, L.exists_seamLift⟩,
      fun L _ _ h₁ h₂ => by rw [L.seamLift_increment_eq h₁ h₂],
      SM.tw_shift⟩
  R_eq := ⟨fun _ => rfl, fun _ _ L hL => rotAbs_cast L hL⟩
  polygon_R_eq_SM := fun _ _ L hL => ⟨rot_eq_rotationNumber hL, rotAbs_cast_real L hL⟩
  shared_with_SM := ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-! ## Row 144 in full -/

/-- Row 144, CV:def:rot (d1_setup.tex:726–787) in full: the polygon part `RotDefinitionData`
(CV.Rotation, 726–765) together with the paragraph "Direction loops and smooth curves"
`RotSmoothDefinitionData` (767–785). -/
structure RotDefinitionFullData : Prop extends RotDefinitionData, RotSmoothDefinitionData

theorem rot_definition_full : RotDefinitionFullData :=
  { rot_definition, rot_smooth_definition with }

end CV

#print axioms CV.rot_smooth_definition
#print axioms CV.rot_definition_full
