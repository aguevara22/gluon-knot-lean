import ProcessedParentMarks
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedParentMarks
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
variable {D : PLLinkDiagram} {T : BasedTraversal D}

def liftOldMark (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))))
    (x : {x : Fin D.nArc // x ∈ S.marks}) : Fin R.diagram.nArc :=
  R.arcEquiv.symm ⟨smoothArcEquiv D (Sum.inl x.val), S.mark_continuing_component c hc x⟩

def liftConnector (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) : Fin R.diagram.nArc :=
  R.arcEquiv.symm ⟨smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)),rfl⟩

theorem liftOldMark_map (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))))
    (x : {x : Fin D.nArc // x ∈ S.marks}) :
    (R.arcEquiv (S.liftOldMark c hc R x)).val = smoothArcEquiv D (Sum.inl x.val) :=
  congrArg Subtype.val (R.arcEquiv.apply_symm_apply _)

theorem liftConnector_map (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) :
    (R.arcEquiv (liftConnector D T c R)).val =
      smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)) :=
  congrArg Subtype.val (R.arcEquiv.apply_symm_apply _)

theorem liftOldMark_injective (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) :
    Function.Injective (S.liftOldMark c hc R) := by
  intro x y h
  have hv := congrArg (fun a => (R.arcEquiv a).val) h
  dsimp only at hv
  rw [liftOldMark_map,liftOldMark_map] at hv
  exact Subtype.ext (Sum.inl.inj ((smoothArcEquiv D).injective hv))

theorem liftConnector_ne_oldMark (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))))
    (x : {x : Fin D.nArc // x ∈ S.marks}) :
    liftConnector D T c R ≠ S.liftOldMark c hc R x := by
  intro h
  have hv := congrArg (fun a => (R.arcEquiv a).val) h
  dsimp only at hv
  rw [liftConnector_map,liftOldMark_map] at hv
  have hs := (smoothArcEquiv D).injective hv
  cases hs

theorem liftOldMark_before_connector (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))))
    (x : {x : Fin D.nArc // x ∈ S.marks}) :
    rankBefore
      (visitRank (R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _)))
        (S.liftOldMark c hc R x))
      (visitRank (R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _)))
        (liftConnector D T c R)) := by
  apply (R.basedTraversal_rankBefore _ _ _).2
  rw [liftOldMark_map,liftConnector_map]
  exact S.mark_before_connector c hc x

def smoothedMarks (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) : Finset (Fin R.diagram.nArc) :=
  insert (liftConnector D T c R) (S.marks.attach.image (S.liftOldMark c hc R))

end DirectGLSSW.HOMFLY.ProcessedParentMarks
