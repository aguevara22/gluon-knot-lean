import ProcessedParentMarkMaps
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedParentMarks
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
variable {D : PLLinkDiagram} {T : BasedTraversal D}

/-- Actual extraction discharges both-port membership; no later-cut order is assumed. -/
theorem connector_before_bad (S : ProcessedParentMarks D T) (c : Fin D.nCrossing)
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))))
    (d : Fin R.diagram.nCrossing)
    (hd : badAt (R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _))) d) :
    rankBefore
      (visitRank (R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _)))
        (liftConnector D T c R))
      (visitRank (R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _)))
        (R.diagram.incoming d
          (firstVisitedBranch (R.basedTraversal
            (parentRootSelfSmoothingTraversal D T c (S.connected _ _))) d))) := by
  let U := parentRootSelfSmoothingTraversal D T c (S.connected _ _)
  let d0 := (smoothCrossingEquiv D c).symm (R.crossingEquiv d).val
  have he : smoothCrossingEquiv D c d0 = (R.crossingEquiv d).val :=
    (smoothCrossingEquiv D c).apply_symm_apply _
  have hp : ∀ i : Fin 2, componentOf (smoothCrossing D c).continuation
      ((smoothCrossing D c).incoming (smoothCrossingEquiv D c d0) i) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) := by
    intro i
    rw [he]
    exact (R.crossingEquiv d).property i
  have hb : badAt U (smoothCrossingEquiv D c d0) := by
    rw [he]
    exact (R.basedTraversal_badAt U d).mp hd
  have h := parentRoot_bad_after_connector D T c (S.connected _ _) hgood d0.val d0.property hp hb
  rw [he] at h
  apply (R.basedTraversal_rankBefore U _ _).2
  rw [liftConnector_map,R.incoming_eq,R.basedTraversal_firstVisitedBranch]
  exact h

/-- A literal smoothing-and-extraction step retains every old mark and adds
the actual new connector, preserving the processed-before-bad invariant. -/
def smoothStep (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) :
    ProcessedParentMarks R.diagram
      (R.basedTraversal (parentRootSelfSmoothingTraversal D T c (S.connected _ _))) where
  marks := S.smoothedMarks c hc R
  connected := R.continuation_sameCycle
  beforeBad := by
    intro m hm d hd
    rcases Finset.mem_insert.mp hm with he | hm
    · rw [he]
      exact S.connector_before_bad c hgood R d hd
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hm
      have h₁ := S.liftOldMark_before_connector c hc R x
      have h₂ := S.connector_before_bad c hgood R d hd
      unfold rankBefore at *
      rcases h₁ with h₁ | ⟨he,h₁⟩ <;> rcases h₂ with h₂ | ⟨hf,h₂⟩ <;> omega

theorem liftOldMark_mem_smoothStep (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
    (R : ComponentRestriction (smoothCrossing D c)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))))
    (x : {x : Fin D.nArc // x ∈ S.marks}) :
    S.liftOldMark c hc R x ∈ (S.smoothStep c hc hgood R).marks := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨x,Finset.mem_attach _ _,rfl⟩

end DirectGLSSW.HOMFLY.ProcessedParentMarks
