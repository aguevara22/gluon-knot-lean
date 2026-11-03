import RoundingCrossingIntersection

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate5: the checked 0/1 crossing classification in either actual branch order. -/
theorem roundedCorner_crossing_distinct_iff_center (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i j : Fin 2) (hij : i ≠ j) (δ s t : ℝ) :
    roundedCorner D (D.incoming c i) δ s = roundedCorner D (D.incoming c j) δ t ↔
      roundedCorner D (D.incoming c i) δ s = cornerCenter D (D.incoming c i) ∧
      roundedCorner D (D.incoming c j) δ t = cornerCenter D (D.incoming c j) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact roundedCorner_crossing_intersection_iff_center D c δ s t
  · constructor
    · intro heq
      have h := (roundedCorner_crossing_intersection_iff_center D c δ t s).mp heq.symm
      exact ⟨h.2,h.1⟩
    · rintro ⟨hs,ht⟩
      exact ((roundedCorner_crossing_intersection_iff_center D c δ t s).mpr ⟨ht,hs⟩).symm
  · exact False.elim (hij rfl)

end DirectGLSSW.HOMFLY.PrincipalTurning

