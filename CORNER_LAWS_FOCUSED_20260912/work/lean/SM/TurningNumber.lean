import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import SM.RotationContinuity
import SM.RotationTheorem

/-! Ported verbatim 2026-09-13 from work/drafts/TurningNumber.lean (implementer subagent of the pod executor; checked with `lake env lean`, no placeholder, standard axioms); only this header added and `#print axioms` lines removed. Row cf:def-turning → `SM.turning_definition`; the definitions are shared with cf:lem-turnlift (row 96) and CV def:rot / lem:turnlift (rows 144-145, decision F6). Plan: work/drafts/TurningNumber_PLAN.md; scout: work/reports/turning-number-scout-20260913.md. -/

/-! # SM cf:def-turning — direction loops and smooth rotation

Source: reference/SM/sm-3-statesum.tex:3514-3541 (the same text is CV def:rot, paragraph
"Direction loops and smooth curves", reference/R/CV/d1_setup.tex:767-787; decision F6 in
work/reports/cv-lane-plan-20260913.md: defined once here, re-exported by CV).

Printed notation → Lean:
* direction loop `T : ℝ/ℤ → S¹` → `DirectionLoop` (a 1-periodic continuous `T : ℝ → Plane`
  of `euclideanLength` 1; `Plane = ℝ × ℝ` is the oriented plane of the SM library, and the
  unit circle is reached through `planeComplex` as `DirectionLoop.toCircle : C(ℝ, Circle)`);
* tangent-angle lift at a seam `θ : [0,1] → ℝ`, `T s = (cos θ s, sin θ s)` → `IsSeamLift T θ`
  (`ContinuousOn θ (Set.Icc 0 1)`); the global lift `IsLift T θ` on all of `ℝ` is the proof device;
* `tw(T) = (θ(1) − θ(0)) / 2π` → `tw L`, computed from the chosen lift `DirectionLoop.lift`,
  and equal to the printed quotient for every seam lift (`tw_eq_of_isSeamLift`);
* closed `C¹` regular oriented curve `γ : ℝ/ℤ → ℝ²`, `γ' ≠ 0` → `ClosedC1Curve`;
* `T_γ = γ'/|γ'|` → `ClosedC1Curve.tangentLoop`; `rot(γ) = tw(T_γ)` → `ClosedC1Curve.rot`;
* "for a polygon in the regular locus, rot remains that of lem:rot" → the accepted
  `SM.rotationNumber` (RotationNumber.lean) with its lem:rot clauses `SM.rotation_number`;
* `R(L) = |rot(L)|` → `ClosedC1Curve.R` (curves) and `polygonR` (polygons).

The existence of the lift, which the printed definition defers to the lemma that follows
("the lemma that follows constructs the lift"), is proved here so that `tw` is well defined:
`DirectionLoop.exists_lift` uses Mathlib's covering-space lifting through `Circle.exp`
(`IsCoveringMap.existsUnique_continuousMap_lifts`, `ℝ` being simply connected) rather than the
printed atan2 subdivision; the checked object is the printed statement. Independence of the
value from the choice of lift and from the seam is also proved here (`seamLift_increment_eq`,
`tw_shift`); independence under orientation-preserving regular reparametrisation is clause (i)
of cf:lem-turnlift and is not part of this module. -/

namespace SM

/-! ## The unit circle of the oriented plane -/

/-- A unit vector of the plane, as a point of Mathlib's `Circle` (via `planeComplex`). -/
def unitCircle (u : Plane) (hu : euclideanLength u = 1) : Circle :=
  ⟨planeComplex u, mem_sphere_zero_iff_norm.mpr hu⟩

@[simp] theorem coe_unitCircle (u : Plane) (hu : euclideanLength u = 1) :
    ((unitCircle u hu : Circle) : ℂ) = planeComplex u := rfl

theorem continuous_unitCircle {α : Type*} [TopologicalSpace α] {T : α → Plane}
    (hT : Continuous T) (hu : ∀ s, euclideanLength (T s) = 1) :
    Continuous (fun s => unitCircle (T s) (hu s)) :=
  Continuous.subtype_mk (continuous_planeComplex.comp hT) _

/-- `Circle.exp θ` is the point `(cos θ, sin θ)` of the plane. -/
theorem circleExp_planeComplex (θ : ℝ) :
    ((Circle.exp θ : Circle) : ℂ) = planeComplex (Real.cos θ, Real.sin θ) := by
  rw [Circle.coe_exp]
  apply Complex.ext
  · simp [planeComplex]
  · simp [planeComplex]

/-- The printed lift equation `u = (cos θ, sin θ)` is the covering equation `Circle.exp θ = u`. -/
theorem circleExp_eq_unitCircle_iff {u : Plane} (hu : euclideanLength u = 1) (θ : ℝ) :
    Circle.exp θ = unitCircle u hu ↔ u = (Real.cos θ, Real.sin θ) := by
  constructor
  · intro h
    apply planeComplex_injective
    rw [← circleExp_planeComplex, h]
    rfl
  · intro h
    subst h
    exact Subtype.ext (circleExp_planeComplex θ)

/-! ## Direction loops (printed sentence D1) -/

/-- A direction loop: a continuous map `T : ℝ/ℤ → S¹` into the unit circle of the oriented
plane, rendered as a 1-periodic continuous `T : ℝ → Plane` of Euclidean length 1. -/
structure DirectionLoop where
  T : ℝ → Plane
  continuous : Continuous T
  periodic : Function.Periodic T 1
  unit : ∀ s, euclideanLength (T s) = 1

namespace DirectionLoop

/-- The loop as a continuous map into Mathlib's `Circle`. -/
def toCircle (L : DirectionLoop) : C(ℝ, Circle) :=
  ⟨fun s => unitCircle (L.T s) (L.unit s), continuous_unitCircle L.continuous L.unit⟩

@[simp] theorem coe_toCircle (L : DirectionLoop) (s : ℝ) :
    ((L.toCircle s : Circle) : ℂ) = planeComplex (L.T s) := rfl

theorem toCircle_periodic (L : DirectionLoop) : Function.Periodic L.toCircle 1 :=
  fun s => Subtype.ext (congrArg planeComplex (L.periodic s))

/-- The seam moved to `a`: the loop `s ↦ T (s + a)`. -/
def shift (L : DirectionLoop) (a : ℝ) : DirectionLoop where
  T := fun s => L.T (s + a)
  continuous := L.continuous.comp (continuous_add_const a)
  periodic := fun s => by
    show L.T (s + 1 + a) = L.T (s + a)
    rw [add_right_comm]
    exact L.periodic (s + a)
  unit := fun s => L.unit (s + a)

@[simp] theorem shift_T (L : DirectionLoop) (a s : ℝ) : (L.shift a).T s = L.T (s + a) := rfl

end DirectionLoop

/-! ## Tangent-angle lifts (printed sentence D2) -/

/-- A global tangent-angle lift of `T`: continuous on `ℝ` with `T s = (cos θ s, sin θ s)`
for every `s`. Proof device; the printed notion is `IsSeamLift`. -/
def IsLift (T : ℝ → Plane) (θ : ℝ → ℝ) : Prop :=
  Continuous θ ∧ ∀ s, T s = (Real.cos (θ s), Real.sin (θ s))

/-- The printed tangent-angle lift at a seam: a continuous `θ : [0,1] → ℝ` with
`T s = (cos θ s, sin θ s)` for `0 ≤ s ≤ 1`. -/
def IsSeamLift (T : ℝ → Plane) (θ : ℝ → ℝ) : Prop :=
  ContinuousOn θ (Set.Icc 0 1) ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, T s = (Real.cos (θ s), Real.sin (θ s))

theorem IsLift.isSeamLift {T : ℝ → Plane} {θ : ℝ → ℝ} (h : IsLift T θ) : IsSeamLift T θ :=
  ⟨h.1.continuousOn, fun s _ => h.2 s⟩

theorem IsLift.circleExp {L : DirectionLoop} {θ : ℝ → ℝ} (h : IsLift L.T θ) (s : ℝ) :
    Circle.exp (θ s) = L.toCircle s :=
  (circleExp_eq_unitCircle_iff (L.unit s) (θ s)).mpr (h.2 s)

theorem IsSeamLift.circleExp {L : DirectionLoop} {θ : ℝ → ℝ} (h : IsSeamLift L.T θ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : Circle.exp (θ s) = L.toCircle s :=
  (circleExp_eq_unitCircle_iff (L.unit s) (θ s)).mpr (h.2 s hs)

namespace DirectionLoop

/-- Every direction loop has a (global) tangent-angle lift: lifting through the covering map
`Circle.exp : ℝ → Circle`, `ℝ` being simply connected. -/
theorem exists_lift (L : DirectionLoop) : ∃ θ : ℝ → ℝ, IsLift L.T θ := by
  obtain ⟨θ₀, -, hθ₀⟩ := Circle.surjOn_exp_neg_pi_pi (Set.mem_univ (L.toCircle 0))
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts L.toCircle 0 θ₀ hθ₀
  refine ⟨F, F.continuous, fun s => ?_⟩
  exact (circleExp_eq_unitCircle_iff (L.unit s) (F s)).mp (congrFun hF s)

theorem exists_seamLift (L : DirectionLoop) : ∃ θ : ℝ → ℝ, IsSeamLift L.T θ :=
  let ⟨θ, hθ⟩ := L.exists_lift
  ⟨θ, hθ.isSeamLift⟩

/-- The chosen tangent-angle lift `θ` of the loop. -/
noncomputable def lift (L : DirectionLoop) : ℝ → ℝ := Classical.choose L.exists_lift

theorem lift_isLift (L : DirectionLoop) : IsLift L.T L.lift := Classical.choose_spec L.exists_lift

theorem lift_isSeamLift (L : DirectionLoop) : IsSeamLift L.T L.lift := L.lift_isLift.isSeamLift

/-- Two seam lifts differ by a constant on `[0,1]`, so their increments `θ(1) − θ(0)` agree:
the value `tw` does not depend on the choice of the lift. -/
theorem seamLift_increment_eq (L : DirectionLoop) {θ₁ θ₂ : ℝ → ℝ}
    (h₁ : IsSeamLift L.T θ₁) (h₂ : IsSeamLift L.T θ₂) : θ₁ 1 - θ₁ 0 = θ₂ 1 - θ₂ 0 := by
  have := Circle.isCoveringMap_exp.constOn_of_comp (g := fun s => θ₁ s - θ₂ s)
    isPreconnected_Icc (h₁.1.sub h₂.1) (fun a ha a' ha' => ?_) (a := 1) (a' := 0)
    ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
  · have h : θ₁ 1 - θ₂ 1 = θ₁ 0 - θ₂ 0 := this
    linarith
  · show Circle.exp (θ₁ a - θ₂ a) = Circle.exp (θ₁ a' - θ₂ a')
    rw [Circle.exp_sub, Circle.exp_sub, h₁.circleExp ha, h₂.circleExp ha, h₁.circleExp ha',
      h₂.circleExp ha', div_self', div_self']

/-- The increment of a seam lift is an integer multiple of `2π`, since `T 1 = T 0`. -/
theorem seamLift_increment_int (L : DirectionLoop) {θ : ℝ → ℝ} (h : IsSeamLift L.T θ) :
    ∃ m : ℤ, θ 1 - θ 0 = m * (2 * Real.pi) := by
  have h10 : L.T 1 = L.T 0 := by simpa using L.periodic 0
  have : Circle.exp (θ 1) = Circle.exp (θ 0) := by
    rw [h.circleExp ⟨zero_le_one, le_rfl⟩, h.circleExp ⟨le_rfl, zero_le_one⟩]
    exact Subtype.ext (congrArg planeComplex h10)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp this
  exact ⟨m, by linarith⟩

/-- A global lift has the same increment over every seam `[a, a+1]`. -/
theorem lift_add_one_sub {L : DirectionLoop} {θ : ℝ → ℝ} (h : IsLift L.T θ) (a : ℝ) :
    θ (a + 1) - θ a = θ 1 - θ 0 := by
  have := Circle.isCoveringMap_exp.const_of_comp (g := fun s => θ (s + 1) - θ s)
    ((h.1.comp (continuous_add_const 1)).sub h.1) (fun a a' => ?_) a 0
  · simpa using this
  · show Circle.exp (θ (a + 1) - θ a) = Circle.exp (θ (a' + 1) - θ a')
    rw [Circle.exp_sub, Circle.exp_sub, h.circleExp (a + 1), h.circleExp a,
      h.circleExp (a' + 1), h.circleExp a', L.toCircle_periodic a, L.toCircle_periodic a',
      div_self', div_self']

end DirectionLoop

/-! ## The turning number `tw` (printed sentence D3) -/

/-- `tw(T) = (θ(1) − θ(0)) / 2π` for the chosen tangent-angle lift `θ` (equal to the same
quotient for every seam lift: `tw_eq_of_isSeamLift`). -/
noncomputable def tw (L : DirectionLoop) : ℝ := (L.lift 1 - L.lift 0) / (2 * Real.pi)

theorem tw_eq_of_isSeamLift (L : DirectionLoop) {θ : ℝ → ℝ} (h : IsSeamLift L.T θ) :
    tw L = (θ 1 - θ 0) / (2 * Real.pi) := by
  unfold tw
  rw [L.seamLift_increment_eq L.lift_isSeamLift h]

theorem tw_int (L : DirectionLoop) : ∃ k : ℤ, tw L = (k : ℝ) := by
  obtain ⟨m, hm⟩ := L.seamLift_increment_int L.lift_isSeamLift
  refine ⟨m, ?_⟩
  unfold tw
  rw [hm]
  exact mul_div_cancel_right₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))

/-- `tw` does not depend on the seam. -/
theorem tw_shift (L : DirectionLoop) (a : ℝ) : tw (L.shift a) = tw L := by
  obtain ⟨θ, hθ⟩ := L.exists_lift
  have hθa : IsLift (L.shift a).T (fun s => θ (s + a)) :=
    ⟨hθ.1.comp (continuous_add_const a), fun s => hθ.2 (s + a)⟩
  rw [tw_eq_of_isSeamLift (L.shift a) hθa.isSeamLift, tw_eq_of_isSeamLift L hθ.isSeamLift]
  show (θ (1 + a) - θ (0 + a)) / (2 * Real.pi) = (θ 1 - θ 0) / (2 * Real.pi)
  rw [zero_add, add_comm (1 : ℝ) a, DirectionLoop.lift_add_one_sub hθ a]

/-! ## Closed `C¹` regular curves and their rotation (printed sentence D4) -/

/-- Normalisation `v / |v|` (Euclidean length). -/
noncomputable def normalize (v : Plane) : Plane := (euclideanLength v)⁻¹ • v

theorem euclideanLength_normalize {v : Plane} (h0 : v ≠ 0) :
    euclideanLength (normalize v) = 1 := by
  rw [normalize, euclideanLength, planeComplex_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (euclideanLength_pos h0))]
  exact inv_mul_cancel₀ (euclideanLength_pos h0).ne'

theorem continuous_normalize_comp {α : Type*} [TopologicalSpace α] {v : α → Plane}
    (hv : Continuous v) (h0 : ∀ t, v t ≠ 0) : Continuous (fun t => normalize (v t)) := by
  refine Continuous.smul (Continuous.inv₀ ?_ fun t => (euclideanLength_pos (h0 t)).ne') hv
  exact (continuous_planeComplex.comp hv).norm

/-- A closed `C¹` regular oriented curve `γ : ℝ/ℤ → ℝ²`: 1-periodic, everywhere differentiable
with continuous derivative `γ'`, and `γ' ≠ 0` everywhere. -/
structure ClosedC1Curve where
  γ : ℝ → Plane
  γ' : ℝ → Plane
  hasDerivAt : ∀ t, HasDerivAt γ (γ' t) t
  continuous_deriv : Continuous γ'
  regular : ∀ t, γ' t ≠ 0
  periodic : Function.Periodic γ 1

namespace ClosedC1Curve

/-- The derivative of a 1-periodic curve is 1-periodic. -/
theorem deriv_periodic (c : ClosedC1Curve) : Function.Periodic c.γ' 1 := by
  intro t
  have h1 : HasDerivAt (fun s => c.γ (s + 1)) (c.γ' (t + 1)) t := by
    have := (c.hasDerivAt (t + 1)).scomp t ((hasDerivAt_id' t).add_const 1)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun s => c.γ (s + 1)) (c.γ' t) t := by
    have : (fun s => c.γ (s + 1)) = c.γ := funext c.periodic
    rw [this]
    exact c.hasDerivAt t
  exact h1.unique h2

/-- The tangent direction loop `T_γ = γ' / |γ'|`. -/
noncomputable def tangentLoop (c : ClosedC1Curve) : DirectionLoop where
  T := fun t => normalize (c.γ' t)
  continuous := continuous_normalize_comp c.continuous_deriv c.regular
  periodic := fun t => congrArg normalize (c.deriv_periodic t)
  unit := fun t => euclideanLength_normalize (c.regular t)

@[simp] theorem tangentLoop_T (c : ClosedC1Curve) (t : ℝ) :
    c.tangentLoop.T t = (euclideanLength (c.γ' t))⁻¹ • c.γ' t := rfl

/-- `rot(γ) = tw(T_γ)`. -/
noncomputable def rot (c : ClosedC1Curve) : ℝ := tw c.tangentLoop

/-- `R(γ) = |rot(γ)|`. -/
noncomputable def R (c : ClosedC1Curve) : ℝ := |c.rot|

end ClosedC1Curve

/-- `R(L) = |rot(L)|` for a polygon `L`, whose `rot` is the accepted `rotationNumber` of lem:rot
(printed sentence D5: "for a polygon in the regular locus, rot remains that of Lemma lem:rot"). -/
noncomputable def polygonR {n : ℕ} [NeZero n] (P : LabelledTuple n) : ℝ := |rotationNumber P|

/-! ## The definition row -/

/-- One field per printed sentence of cf:def-turning (sm-3:3514-3535). -/
structure TurningDefinitionData : Prop where
  /-- D1: a direction loop is a continuous 1-periodic map into the unit circle of the plane. -/
  direction_loop : ∀ L : DirectionLoop, Continuous L.T ∧ Function.Periodic L.T 1 ∧
    (∀ s, euclideanLength (L.T s) = 1) ∧
    ∀ s, ((L.toCircle s : Circle) : ℂ) = planeComplex (L.T s)
  /-- D2: a tangent-angle lift at a seam is a continuous `θ : [0,1] → ℝ` with
  `T s = (cos θ s, sin θ s)` for `0 ≤ s ≤ 1`. -/
  tangent_angle_lift : ∀ (T : ℝ → Plane) (θ : ℝ → ℝ), IsSeamLift T θ ↔
    ContinuousOn θ (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, T s = (Real.cos (θ s), Real.sin (θ s))
  /-- The existence theorem making `tw` well defined ("the lemma that follows constructs the
  lift"): every direction loop has a tangent-angle lift, indeed a global continuous one. -/
  exists_tangent_angle_lift : ∀ L : DirectionLoop,
    (∃ θ, IsLift L.T θ) ∧ ∃ θ, IsSeamLift L.T θ
  /-- D3: `tw(T) = (θ(1) − θ(0)) / 2π` for every tangent-angle lift `θ` at the seam. -/
  tw_eq : ∀ (L : DirectionLoop) (θ : ℝ → ℝ), IsSeamLift L.T θ →
    tw L = (θ 1 - θ 0) / (2 * Real.pi)
  /-- `tw(T)` is an integer (the lift increment is a multiple of `2π` because `T 1 = T 0`). -/
  tw_integer : ∀ L : DirectionLoop, ∃ k : ℤ, tw L = (k : ℝ)
  /-- D4: a closed `C¹` regular oriented curve is 1-periodic with continuous derivative
  `γ' ≠ 0` everywhere (and `γ'` is then 1-periodic too). -/
  closed_curve : ∀ c : ClosedC1Curve, (∀ t, HasDerivAt c.γ (c.γ' t) t) ∧ Continuous c.γ' ∧
    (∀ t, c.γ' t ≠ 0) ∧ Function.Periodic c.γ 1 ∧ Function.Periodic c.γ' 1
  /-- D4: `T_γ = γ' / |γ'|`, a direction loop. -/
  tangent_loop : ∀ (c : ClosedC1Curve) (t : ℝ),
    c.tangentLoop.T t = (euclideanLength (c.γ' t))⁻¹ • c.γ' t ∧
      euclideanLength (c.tangentLoop.T t) = 1
  /-- D4: `rot(γ) = tw(T_γ)`. -/
  rot_curve : ∀ c : ClosedC1Curve, c.rot = tw c.tangentLoop
  /-- D5: for a polygon in the regular locus, `rot` remains that of lem:rot — the accepted
  `rotationNumber`, `(1/2π) Σ principalTurn`, an integer (`SM.rotation_number`). -/
  polygon_rot : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ P : LabelledTuple n, Regular P →
    rotationNumber P = (1 / (2 * Real.pi)) * (∑ i : ZMod n, principalTurn P i) ∧
      ∃ k : ℤ, rotationNumber P = (k : ℝ)
  /-- D6: `R(L) = |rot(L)|` for a polygon or a `C¹` regular closed curve. -/
  R_eq : (∀ c : ClosedC1Curve, c.R = |c.rot|) ∧
    ∀ {n : ℕ} [NeZero n] (P : LabelledTuple n), polygonR P = |rotationNumber P|
  /-- D7 (the parts proved here): `tw` does not depend on the choice of the lift, nor on the
  seam. Reparametrisation invariance is cf:lem-turnlift (i). -/
  lift_and_seam_independent :
    (∀ (L : DirectionLoop) (θ₁ θ₂ : ℝ → ℝ), IsSeamLift L.T θ₁ → IsSeamLift L.T θ₂ →
      θ₁ 1 - θ₁ 0 = θ₂ 1 - θ₂ 0) ∧
    ∀ (L : DirectionLoop) (a : ℝ), tw (L.shift a) = tw L

theorem turning_definition : TurningDefinitionData where
  direction_loop := fun L => ⟨L.continuous, L.periodic, L.unit, fun _ => rfl⟩
  tangent_angle_lift := fun _ _ => Iff.rfl
  exists_tangent_angle_lift := fun L => ⟨L.exists_lift, L.exists_seamLift⟩
  tw_eq := fun L _ h => tw_eq_of_isSeamLift L h
  tw_integer := tw_int
  closed_curve := fun c =>
    ⟨c.hasDerivAt, c.continuous_deriv, c.regular, c.periodic, c.deriv_periodic⟩
  tangent_loop := fun c t => ⟨rfl, c.tangentLoop.unit t⟩
  rot_curve := fun _ => rfl
  polygon_rot := fun hn P h => ⟨(rotation_number hn P h).1, (rotation_number hn P h).2.1⟩
  R_eq := ⟨fun _ => rfl, fun _ => rfl⟩
  lift_and_seam_independent :=
    ⟨fun L _ _ h₁ h₂ => L.seamLift_increment_eq h₁ h₂, tw_shift⟩

end SM
