import RoundingCrossingIntersection

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate1: actual center occurrences are away from both cut endpoints. -/
theorem roundedCorner_crossing_center_interior (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (δ t : ℝ) (hδ : 0 < δ)
    (ht : t ∈ Set.Icc 0 1)
    (hc : roundedCorner D (D.incoming c i) δ t = cornerCenter D (D.incoming c i)) :
    t ∈ Set.Ioo 0 1 := by
  have hzero : t ≠ 0 := by
    intro hz
    subst t
    rw [(roundedCorner_endpoints D (D.incoming c i) δ).1] at hc
    have hv : δ • arcVector D (D.incoming c i) = 0 := by linear_combination -hc
    rcases smul_eq_zero.mp hv with h | h
    · exact (ne_of_gt hδ) h
    · exact arcVector_ne_zero D _ h
  have hone : t ≠ 1 := by
    intro ho
    subst t
    rw [(roundedCorner_endpoints D (D.incoming c i) δ).2] at hc
    have hv : δ • arcVector D (D.continuation (D.incoming c i)) = 0 := by linear_combination hc
    rcases smul_eq_zero.mp hv with h | h
    · exact (ne_of_gt hδ) h
    · exact arcVector_ne_zero D _ h
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero),lt_of_le_of_ne ht.2 hone⟩

end DirectGLSSW.HOMFLY.PrincipalTurning

