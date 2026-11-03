import RoundedHalfplane

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Linear-functional multiplier: Re(a*w) = det(q-p,w). -/
def supportingRootNormal (p q : PlanarPoint ℝ) : ℂ :=
  ⟨-(q.2-p.2), -(q.1-p.1)⟩

/-- The point on the root's oriented right side. Epsilon multiplies the right
normal (dy,-dx), so this does not silently assume a unit-length root. -/
def exteriorRootProbe (p q : PlanarPoint ℝ) (τ ε : ℝ) : ℂ :=
  ⟨p.1 + τ*(q.1-p.1) + ε*(q.2-p.2),
    p.2 + τ*(q.2-p.2) - ε*(q.1-p.1)⟩

/-- Actual original-root endpoints cannot coincide in a nonempty actual component. -/
theorem supportingRoot_endpoints_ne (s : MarkedParentState) (p q : PlanarPoint ℝ)
    (h : SupportingRootGeometry s p q) (e : Fin s.1.nArc) : p ≠ q := by
  let C : diagramComponent s.1 := PermutationOrbits.componentOf s.1.continuation e
  intro hpq
  have hv : s.1.vertexPoint (s.1.arcSource (s.2.1.baseArc C).val) =
      s.1.vertexPoint (s.1.arcTarget (s.2.1.baseArc C).val) :=
    (h.1 C).1.trans (hpq.trans (h.1 C).2.symm)
  exact s.1.arc_endpoints_distinct _ (s.1.vertexPoint_injective hv)

theorem supportingRootNormal_ne_zero (p q : PlanarPoint ℝ) (hpq : p ≠ q) :
    supportingRootNormal p q ≠ 0 := by
  intro hz
  have hx := congrArg Complex.re hz
  have hy := congrArg Complex.im hz
  simp only [supportingRootNormal, Complex.zero_re,
    Complex.zero_im, neg_eq_zero] at hx hy
  apply hpq
  apply Prod.ext <;> linarith

/-- Exact signed separation, including its non-unit normal scale. -/
theorem exteriorRootProbe_separation (p q : PlanarPoint ℝ) (τ ε : ℝ) :
    (supportingRootNormal p q * exteriorRootProbe p q τ ε).re =
      (supportingRootNormal p q * (⟨p.1,p.2⟩ : ℂ)).re -
        ε*((q.1-p.1)^2 + (q.2-p.2)^2) := by
  simp only [supportingRootNormal, exteriorRootProbe, Complex.mul_re]
  ring

theorem exteriorRootProbe_strict_exterior (p q : PlanarPoint ℝ) (hpq : p ≠ q)
    (τ ε : ℝ) (hε : 0 < ε) :
    (supportingRootNormal p q * exteriorRootProbe p q τ ε).re <
      (supportingRootNormal p q * (⟨p.1,p.2⟩ : ℂ)).re := by
  have hs : 0 < (q.1-p.1)^2 + (q.2-p.2)^2 := by
    by_contra hn
    have hle := le_of_not_gt hn
    have hx : (q.1-p.1)^2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (q.2-p.2)]) (sq_nonneg _)
    have hy : (q.2-p.2)^2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (q.1-p.1)]) (sq_nonneg _)
    have hx0 := sq_eq_zero_iff.mp hx
    have hy0 := sq_eq_zero_iff.mp hy
    apply hpq
    apply Prod.ext <;> linarith
  rw [exteriorRootProbe_separation]
  exact sub_lt_self _ (mul_pos hε hs)

/-- The exterior probe avoids the literal actual rounded component and has an
explicit periodic positional-angle lift with zero period increment. All geometry
inputs beyond the existing supporting-root condition are discharged here. -/
theorem actual_exterior_root_probe_positional_argument
    (s : MarkedParentState) (p q : PlanarPoint ℝ)
    (h : SupportingRootGeometry s p q) (e : Fin s.1.nArc)
    (δ : RoundingFraction) (τ ε : ℝ) (hε : 0 < ε) :
    (∀ t, roundedComponentCurve s.1 e δ t ≠ exteriorRootProbe p q τ ε) ∧
      ∃ θ : ℝ → ℝ, Continuous θ ∧
        Function.Periodic θ (componentArcLength s.1 e : ℝ) ∧
        (∀ t, (θ t : Real.Angle) =
          ((roundedComponentCurve s.1 e δ t - exteriorRootProbe p q τ ε).arg : Real.Angle)) ∧
        θ (componentArcLength s.1 e : ℝ) - θ 0 = 0 := by
  have hpq := supportingRoot_endpoints_ne s p q h e
  apply actual_rounded_exists_periodic_positional_argument_of_halfplane
    s.1 e δ (supportingRootNormal p q) (exteriorRootProbe p q τ ε)
    (supportingRootNormal p q * (⟨p.1,p.2⟩ : ℂ)).re
    (supportingRootNormal_ne_zero p q hpq)
  · intro t
    exact SupportingRootGeometry.rounded_halfplane s p q h e δ t
  · exact exteriorRootProbe_strict_exterior p q hpq τ ε hε

end DirectGLSSW.HOMFLY.PrincipalTurning


