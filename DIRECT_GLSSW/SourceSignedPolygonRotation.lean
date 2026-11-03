import SourcePolygonDomain
set_option autoImplicit false
namespace DirectGLSSW.SourcePolygonData
open DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.HOMFLY.PolygonDrawingBridge

/-- Source signed rotation, selected only from the independently audited full
raw existence-and-uniqueness theorem. No default value or genericity domain. -/
noncomputable def signedPolygonRotation {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) : ℤ :=
  Classical.choose (existsUnique_integer_with_global_rounding q hedge hshort)

/-- Complete characterization includes the literal regular positional curve,
its actual derivative, and every continuous real tangent-angle lift. -/
theorem signedPolygonRotation_spec {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) :
    originalCornerTotalTurn q = (signedPolygonRotation hn q hedge hshort:ℝ)*(2*Real.pi) ∧
      ∀ (base : Fin n) (δ : RoundingFraction),
        Function.Periodic (curve q base δ) n ∧
        Continuous (curve q base δ) ∧
        Function.Periodic (curveVelocity q base δ) n ∧
        Continuous (curveVelocity q base δ) ∧
        (∀ t : ℝ, HasDerivAt (curve q base δ) (curveVelocity q base δ t) t ∧
          curveVelocity q base δ t ≠ 0) ∧
        Continuous (tangentLift q base δ) ∧
        (∀ t : ℝ, (tangentLift q base δ t : Real.Angle) =
          ((curveVelocity q base δ t).arg : Real.Angle)) ∧
        (∀ t : ℝ, tangentLift q base δ (t+n)-tangentLift q base δ t = (signedPolygonRotation hn q hedge hshort:ℝ)*(2*Real.pi)) ∧
        (∀ f : ℝ → ℝ, Continuous f →
          (∀ t : ℝ, (f t : Real.Angle) = ((curveVelocity q base δ t).arg : Real.Angle)) →
          f n-f 0 = (signedPolygonRotation hn q hedge hshort:ℝ)*(2*Real.pi)) :=
  (Classical.choose_spec (existsUnique_integer_with_global_rounding q hedge hshort)).1

theorem signedPolygonRotation_total_iff {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) (r : ℤ) :
    originalCornerTotalTurn q = (r:ℝ)*(2*Real.pi) ↔ r = signedPolygonRotation hn q hedge hshort := by
  constructor
  · intro hr
    have hs := (signedPolygonRotation_spec hn q hedge hshort).1
    have hcast := mul_right_cancel₀
      (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero) (hr.symm.trans hs)
    exact_mod_cast hcast
  · intro hr
    subst r
    exact (signedPolygonRotation_spec hn q hedge hshort).1

theorem signedPolygonRotation_characterization {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) (r : ℤ) :
    (originalCornerTotalTurn q = (r:ℝ)*(2*Real.pi) ∧
      ∀ (base : Fin n) (δ : RoundingFraction),
        Function.Periodic (curve q base δ) n ∧
        Continuous (curve q base δ) ∧
        Function.Periodic (curveVelocity q base δ) n ∧
        Continuous (curveVelocity q base δ) ∧
        (∀ t : ℝ, HasDerivAt (curve q base δ) (curveVelocity q base δ t) t ∧
          curveVelocity q base δ t ≠ 0) ∧
        Continuous (tangentLift q base δ) ∧
        (∀ t : ℝ, (tangentLift q base δ t : Real.Angle) =
          ((curveVelocity q base δ t).arg : Real.Angle)) ∧
        (∀ t : ℝ, tangentLift q base δ (t+n)-tangentLift q base δ t = (r:ℝ)*(2*Real.pi)) ∧
        (∀ f : ℝ → ℝ, Continuous f →
          (∀ t : ℝ, (f t : Real.Angle) = ((curveVelocity q base δ t).arg : Real.Angle)) →
          f n-f 0 = (r:ℝ)*(2*Real.pi))) ↔ r = signedPolygonRotation hn q hedge hshort := by
  constructor
  · intro hr
    exact (signedPolygonRotation_total_iff hn q hedge hshort r).mp hr.1
  · intro hr
    subst r
    exact signedPolygonRotation_spec hn q hedge hshort

theorem signedPolygonRotation_proof_irrel {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hn hn' : 0 < n)
    (hedge hedge' : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort hshort' : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) :
    signedPolygonRotation hn q hedge hshort = signedPolygonRotation hn' q hedge' hshort' := by
  apply (signedPolygonRotation_total_iff hn' q hedge' hshort' _).mp
  exact (signedPolygonRotation_spec hn q hedge hshort).1

theorem signedPolygonRotation_any_lift {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane)
    (base : Fin n) (δ : RoundingFraction) (f : ℝ → ℝ) (hf : Continuous f)
    (hangle : ∀ t : ℝ, (f t : Real.Angle) = ((curveVelocity q base δ t).arg : Real.Angle)) :
    f n-f 0 = (signedPolygonRotation hn q hedge hshort:ℝ)*(2*Real.pi) :=
  (any_tangent_lift_increment q hedge hshort base δ f hf hangle).trans
    (signedPolygonRotation_spec hn q hedge hshort).1

theorem signedPolygonRotation_lift_iff {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane)
    (base : Fin n) (δ : RoundingFraction) (f : ℝ → ℝ) (hf : Continuous f)
    (hangle : ∀ t : ℝ, (f t : Real.Angle) = ((curveVelocity q base δ t).arg : Real.Angle))
    (r : ℤ) :
    f n-f 0 = (r:ℝ)*(2*Real.pi) ↔ r = signedPolygonRotation hn q hedge hshort := by
  rw [any_tangent_lift_increment q hedge hshort base δ f hf hangle]
  exact signedPolygonRotation_total_iff hn q hedge hshort r

theorem tangent_degree_base_trim_independent {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane)
    (base base' : Fin n) (δ δ' : RoundingFraction)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfa : ∀ t : ℝ, (f t : Real.Angle) = ((curveVelocity q base δ t).arg : Real.Angle))
    (hga : ∀ t : ℝ, (g t : Real.Angle) = ((curveVelocity q base' δ' t).arg : Real.Angle)) :
    f n-f 0 = g n-g 0 := by
  rw [any_tangent_lift_increment q hedge hshort base δ f hf hfa,
    any_tangent_lift_increment q hedge hshort base' δ' g hg hga]

theorem signedPolygonRotation_generic_eq_turnInteger {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    signedPolygonRotation (by have h := hq.size_ge_three; omega) q
      (generic_edges_ne_zero q hq) (generic_adjacent_ratio_slitPlane q hq) =
      turnInteger (positivePolygonEventDiagram q hq) := by
  symm
  apply (signedPolygonRotation_total_iff _ q _ _ _).mp
  rw [← positivePolygonEventDiagram_totalTurn q hq]
  exact totalTurn_eq_turnInteger _

end DirectGLSSW.SourcePolygonData









