import ImmersedGlobalRegularity
import ImmersedTangentLift

set_option autoImplicit false
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.HOMFLY.PolygonDrawingBridge

/-- Full raw integer characterization with a literal periodic positional
rounding and its actual continuous nonzero derivative. No rotation integer is
chosen, no genericity or remote-incidence premise is present. -/
theorem existsUnique_integer_with_global_rounding
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) :
    ∃! r : ℤ, originalCornerTotalTurn q = (r:ℝ)*(2*Real.pi) ∧
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
          f n-f 0 = (r:ℝ)*(2*Real.pi)) := by
  obtain ⟨r,hr,hunique⟩ := originalCornerTotalTurn_existsUnique_integer_of_edges q hedge
  refine ⟨r,⟨hr,?_⟩,?_⟩
  · intro base δ
    refine ⟨curve_periodic q base δ,curve_continuous q base δ,
      curveVelocity_periodic q base δ,curveVelocity_continuous q base δ,
      fun t => ⟨curve_hasDerivAt q base δ t,curveVelocity_ne_zero q hedge hshort base δ t⟩,
      tangentLift_continuous q hshort base δ,tangentLift_coe q hedge hshort base δ,?_,?_⟩
    · intro t
      exact (tangentLift_shift q hedge hshort base δ t).trans hr
    · intro f hf hangle
      exact (any_tangent_lift_increment q hedge hshort base δ f hf hangle).trans hr
  · intro s hs
    exact hunique s hs.1

/-- On the nonempty source polygon domain, a fixed actual base label supplies
an actual regular closed rounding, with positive period n. -/
theorem source_immersed_global_rounding
    {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane)
    (δ : RoundingFraction) :
    let base : Fin n := ⟨0,hn⟩
    Function.Periodic (curve q base δ) n ∧
    Continuous (curveVelocity q base δ) ∧
    (∀ t : ℝ, HasDerivAt (curve q base δ) (curveVelocity q base δ t) t ∧
      curveVelocity q base δ t ≠ 0) ∧
    Continuous (tangentLift q base δ) ∧
    (∀ t : ℝ, (tangentLift q base δ t : Real.Angle) =
      ((curveVelocity q base δ t).arg : Real.Angle)) ∧
    (∀ t : ℝ, tangentLift q base δ (t+n)-tangentLift q base δ t = originalCornerTotalTurn q) := by
  exact ⟨curve_periodic q _ δ,curveVelocity_continuous q _ δ,
    fun t => ⟨curve_hasDerivAt q _ δ t,curveVelocity_ne_zero q hedge hshort _ δ t⟩,
    tangentLift_continuous q hshort _ δ,tangentLift_coe q hedge hshort _ δ,
    tangentLift_shift q hedge hshort _ δ⟩

end DirectGLSSW.ImmersedGlobalRounding


