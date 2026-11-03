import SmoothingOldTurns
import ProcessedConnectorCorners
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Every negative turn in the actual smoothed drawing comes either from an
old negative turn or from one of the two new parent connector endpoints. -/
theorem negative_smoothing_turn_origin (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : badAt T c) (hpos : crossingSign D c = Sign.pos)
    (e : Fin (smoothCrossing D c).nArc) (hneg : turnDet (smoothCrossing D c) e < 0) :
    (∃ x : Fin D.nArc, e = smoothArcEquiv D (Sum.inl x) ∧
      (∀ i : Fin 2, x ≠ D.incoming c i) ∧ turnDet D x < 0) ∨
    e = smoothArcEquiv D (Sum.inl (D.incoming c (firstVisitedBranch T c))) ∨
    e = smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)) := by
  have hleft := (first_under_connector_turns D T c hc hpos).1
  obtain ⟨code,rfl⟩ := (smoothArcEquiv D).surjective e
  rcases code with x | i
  · by_cases hin : ∃ i : Fin 2, x = D.incoming c i
    · obtain ⟨i,rfl⟩ := hin
      have hi : i = firstVisitedBranch T c := by
        by_contra hne
        have hi := Gemini.eq_otherBranch_of_ne i (firstVisitedBranch T c) hne
        rw [hi] at hneg
        exact (not_lt_of_ge (le_of_lt hleft.1)) hneg
      exact Or.inr (Or.inl (congrArg (fun i => smoothArcEquiv D (Sum.inl (D.incoming c i))) hi))
    · have hnot (i : Fin 2) : x ≠ D.incoming c i := fun h => hin ⟨i,h⟩
      obtain ⟨a,ha,hscale⟩ := old_turn_positive_multiple D c x hnot
      rw [hscale] at hneg
      have hold : turnDet D x < 0 := by nlinarith
      exact Or.inl ⟨x,rfl,hnot,hold⟩
  · have hi : i = firstVisitedBranch T c := by
      by_contra hne
      have hi := Gemini.eq_otherBranch_of_ne i (firstVisitedBranch T c) hne
      rw [hi] at hneg
      exact (not_lt_of_ge (le_of_lt hleft.2)) hneg
    exact Or.inr (Or.inr (congrArg (fun i => smoothArcEquiv D (Sum.inr i)) hi))

/-- Incidence at an old regular marked endpoint persists under actual smoothing. -/
theorem old_target_at_regular_mark (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e m : Fin D.nArc)
    (hs : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcSource m)
    (ht : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcTarget m)
    (he : D.arcTarget e = D.arcSource m ∨ D.arcTarget e = D.arcTarget m) :
    (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e)) =
      (smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inl m)) ∨
    (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl e)) =
      (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inl m)) := by
  rcases he with he | he
  · have hr : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcTarget e := by
      rw [he]
      exact hs
    left
    rw [smooth_old_arc_regular_target D c e hr,smooth_old_arc_regular_source D c m hs,he]
  · have hr : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcTarget e := by
      rw [he]
      exact ht
    right
    rw [smooth_old_arc_regular_target D c e hr,smooth_old_arc_regular_target D c m ht,he]

end DirectGLSSW.HOMFLY.SmoothingCornerGeometry
