import ActualTangentLiftShift
import GlobalRoundingIntersection

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Exact internal aggregate with the corrected v2 proposition verbatim.
Every geometric assertion is a conclusion derived from actual D. -/
def ActualAdmissibleRoundingGoal : Prop :=
  ∀ (D : PLLinkDiagram) (base : Fin D.nArc) (τ : ℝ), τ ∈ Set.Ioo 0 1 →
  ∃ (δ : RoundingFraction) (θ : Fin D.nCrossing → Fin 2 → ℝ) (η : ℝ),
    δ.val < τ ∧ δ.val < 1 - τ ∧ 0 < η ∧
    (∀ c i, θ c i ∈ Set.Ioo 0 (2 * δ.val)) ∧
    (∀ e : Fin D.nArc,
      Function.Periodic (roundedComponentCurve D e δ) (componentArcLength D e : ℝ) ∧
      Continuous (roundedComponentVelocity D e δ) ∧
      (∀ t : ℝ, HasDerivAt (roundedComponentCurve D e δ)
        (roundedComponentVelocity D e δ t) t ∧ roundedComponentVelocity D e δ t ≠ 0) ∧
      Continuous (actualTangentLift D e δ) ∧
      (∀ t : ℝ, (actualTangentLift D e δ t : Real.Angle) =
        ((roundedComponentVelocity D e δ t).arg : Real.Angle)) ∧
      (∀ t : ℝ, actualTangentLift D e δ (t + (componentArcLength D e : ℝ)) -
        actualTangentLift D e δ t = componentTotalTurn D (PermutationOrbits.componentOf D.continuation e))) ∧
    (∀ e : Fin D.nArc, -Real.pi < turn D e ∧ turn D e < Real.pi) ∧
    (∀ u : ℝ, |u| < η →
      τ + δ.val + u ∈ Set.Ioo (2 * δ.val) 1 ∧
      Complex.equivRealProd (roundedComponentCurve D (D.continuation.symm base) δ
        (τ + δ.val + u)) =
        affinePoint (D.vertexPoint (D.arcSource base))
          (D.vertexPoint (D.arcTarget base)) (τ + u)) ∧
    (∀ c i, Complex.equivRealProd
      (roundedComponentCurve D (D.incoming c i) δ (θ c i)) =
        D.vertexPoint (D.crossingVertex c)) ∧
    (∀ c i, ∃ k : ℝ, 0 < k ∧
      Complex.equivRealProd (roundedComponentVelocity D (D.incoming c i) δ (θ c i)) =
        k • strandTangent D c i) ∧
    (let κ : Fin D.nCrossing → ℝ := fun c =>
      planarDet
        (Complex.equivRealProd (roundedComponentVelocity D
          (D.incoming c (D.overBranch c)) δ (θ c (D.overBranch c))))
        (Complex.equivRealProd (roundedComponentVelocity D
          (D.incoming c (otherBranch (D.overBranch c))) δ
          (θ c (otherBranch (D.overBranch c)))))
     ∀ c, ∃ hκ : κ c ≠ 0, nonzeroScalarSign (κ c) hκ = crossingSign D c) ∧
    (∀ (e f : Fin D.nArc) (s t : ℝ),
      roundedComponentCurve D e δ s = roundedComponentCurve D f δ t ↔
      (((D.continuation ^ Int.floor s) e = (D.continuation ^ Int.floor t) f) ∧
        Int.fract s = Int.fract t) ∨
      (∃ (c : Fin D.nCrossing) (i j : Fin 2), i ≠ j ∧
        (D.continuation ^ Int.floor s) e = D.incoming c i ∧
        (D.continuation ^ Int.floor t) f = D.incoming c j ∧
        Int.fract s = θ c i ∧ Int.fract t = θ c j))

/-- The actual globally regular rounding preserves precisely the original
crossings and protected affine basepoint germ, with its actual tangent lift. -/
theorem actual_admissible_rounding : ActualAdmissibleRoundingGoal := by
  intro D base τ hτ
  obtain ⟨δ,θ,η,hleft,hright,hη,hphase,hdet,hgerm,hiff⟩ :=
    exists_global_rounding_intersection D base τ hτ
  refine ⟨δ,θ,η,hleft,hright,hη,fun c i => (hphase c i).1,?_,?_,hgerm,
    fun c i => (hphase c i).2.1,fun c i => (hphase c i).2.2,?_,hiff⟩
  · intro e
    exact ⟨roundedComponentCurve_periodic D e δ,
      roundedComponentVelocity_continuous D e δ,
      fun t => ⟨roundedComponentCurve_hasDerivAt D e δ t,
        roundedComponentVelocity_ne_zero D e δ t⟩,
      actualTangentLift_continuous D e δ,actualTangentLift_coe D e δ,
      actualTangentLift_shift D e δ⟩
  · intro e
    exact turn_mem_open_semicircle D e
  · exact hdet

end DirectGLSSW.HOMFLY.PrincipalTurning

