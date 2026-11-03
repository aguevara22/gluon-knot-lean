import StarCellBoundarySeparation
import StarBoundaryHoleIdentification
import GlobalDiagonalBoundary
import GlobalHoleSignedBalance

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal boundary partition; periodic overlaps contribute zero. -/
theorem actualRetainedRectangle_boundary_three_sums {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleExteriorSide,
      rectangleSideIncrement e) +
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleDiagonalNeighbour,
      rectangleSideIncrement e) +
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleStarNeighbour,
      rectangleSideIncrement e) = 0 := by
  have hpoint : ∀ e : RetainedRectangleSide T C,
      (if rectangleSideReverse e=e then rectangleSideIncrement e else 0) =
      (if rectangleExteriorSide e then rectangleSideIncrement e else 0) +
      (if rectangleDiagonalNeighbour e then rectangleSideIncrement e else 0) +
      (if rectangleStarNeighbour e then rectangleSideIncrement e else 0) := by
    intro e
    by_cases hp : rectanglePeriodicNeighbour e
    · have hz := rectanglePeriodicNeighbour_increment_zero T C e hp
      simp only [hz,ite_self,zero_add]
    · by_cases ho : rectangleExteriorSide e
      · have hd : ¬rectangleDiagonalNeighbour e := fun hd =>
          rectangleDiagonalNeighbour_not_exterior T C e hd ho
        have hs : ¬rectangleStarNeighbour e := fun hs =>
          rectangleStarNeighbour_not_exterior T C e hs ho
        have hf := (fixedRectangleSide_four_reasons T C e).mpr (Or.inl ho)
        simp only [hf,ho,hd,hs,ite_true,ite_false,add_zero]
      · by_cases hd : rectangleDiagonalNeighbour e
        · have hs : ¬rectangleStarNeighbour e := fun hs =>
            rectangleStarNeighbour_not_diagonal T C e hs hd
          have hf := (fixedRectangleSide_four_reasons T C e).mpr (Or.inr (Or.inl hd))
          simp only [hf,ho,hd,hs,ite_true,ite_false,zero_add,add_zero]
        · by_cases hs : rectangleStarNeighbour e
          · have hf := (fixedRectangleSide_four_reasons T C e).mpr
              (Or.inr (Or.inr (Or.inr hs)))
            simp only [hf,ho,hd,hs,ite_true,ite_false,zero_add]
          · have hf : rectangleSideReverse e≠e := by
              intro hf
              rcases (fixedRectangleSide_four_reasons T C e).mp hf with hx | hx | hx | hx
              · exact ho hx
              · exact hd hx
              · exact hp hx
              · exact hs hx
            simp only [hf,ho,hd,hs,ite_false,zero_add]
  have hfixed := actualRetainedRectangle_boundary_balance T C
  rw [Finset.sum_filter] at hfixed
  calc
    _ = ∑ e : RetainedRectangleSide T C,
      ((if rectangleExteriorSide e then rectangleSideIncrement e else 0) +
       (if rectangleDiagonalNeighbour e then rectangleSideIncrement e else 0) +
       (if rectangleStarNeighbour e then rectangleSideIncrement e else 0)) := by
      simp only [Finset.sum_filter,Finset.sum_add_distrib]
    _ = ∑ e : RetainedRectangleSide T C,
      (if rectangleSideReverse e=e then rectangleSideIncrement e else 0) := by
      exact Finset.sum_congr rfl (fun e _ => (hpoint e).symm)
    _ = 0 := hfixed

/-- Actual secant boundary identity, retaining the literal outer chord term.
No exposedness or collar-balance hypothesis is imposed. -/
theorem actualComponent_secantBoundary_formula {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    (∑ e ∈ (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleExteriorSide,
      rectangleSideIncrement e) +
    (∑ k : Fin (componentArcLength D (T.baseArc C).val),
      turn D ((D.continuation ^ (k.val : ℤ)) (T.baseArc C).val)) +
    (2*Real.pi) * (∑ c ∈ actualComponentSelfCrossings T C,
      if 0<complexDet (crossingVector D c (firstVisitedBranch T c))
        (crossingVector D c (otherBranch (firstVisitedBranch T c)))
      then (1 : ℝ) else -1) = 0 := by
  have h := actualRetainedRectangle_boundary_three_sums T C
  rw [actualComponent_diagonalBoundary_regrouping] at h
  have hs : (Finset.univ : Finset (RetainedRectangleSide T C)).filter rectangleStarNeighbour =
      Finset.univ.filter (fun e => ∃ c ∈ actualComponentSelfCrossings T C,
        rectangleTouchesCrossingHole T C c (firstVisitedBranch T c)
          (otherBranch (firstVisitedBranch T c)) e) := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,
      rectangleStarNeighbour_iff_actual_hole T C e]
  rw [hs,actualComponent_holeBoundary_signed_balance] at h
  exact h

end
end DirectGLSSW.HOMFLY.PrincipalTurning


