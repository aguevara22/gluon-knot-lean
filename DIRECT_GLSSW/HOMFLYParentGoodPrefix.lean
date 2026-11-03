import HOMFLYParentPrefixFirstBranch
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Good old prefix crossings remain good in the actual continuing parent.
The good-prefix input is the recursive state, not an assumed new order law. -/
theorem parentRoot_prefix_good (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
    (d : Fin D.nCrossing) (hd : d ≠ c)
    (hparent : ∀ i : Fin 2,
      componentOf (smoothCrossing D c).continuation
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩) i) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))
    (hbefore : rankBefore
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩)
          (firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself)
            (smoothCrossingEquiv D c ⟨d,hd⟩))))
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))) :
    ¬ badAt (parentRootSelfSmoothingTraversal D T c hself)
      (smoothCrossingEquiv D c ⟨d,hd⟩) := by
  let E := smoothCrossing D c
  let U := parentRootSelfSmoothingTraversal D T c hself
  let e := smoothCrossingEquiv D c ⟨d,hd⟩
  let i := firstVisitedBranch T d
  let a := D.incoming c (firstVisitedBranch T c)
  have hi : firstVisitedBranch U e = i :=
    parentRoot_prefix_firstVisitedBranch D T c hself d hd hparent hbefore
  have hp : componentOf E.continuation (smoothArcEquiv D (Sum.inl (D.incoming d i))) =
      componentOf E.continuation (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) := by
    rw [← parentRoot_retained_incoming D c d hd i]
    exact hparent i
  have hn : visitPosition U (E.incoming e i) ≤ visitPosition T a := by
    have h := hbefore
    change rankBefore (visitRank U (E.incoming e (firstVisitedBranch U e)))
      (visitRank U (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))) at h
    rw [hi] at h
    have hlt : visitPosition U (E.incoming e i) <
        visitPosition U (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) := by
      unfold rankBefore visitRank at h
      rw [hparent i] at h
      simpa only [lt_self_iff_false,true_and,false_or] using h
    rw [parentRoot_connector_visitPosition] at hlt
    change visitPosition U (E.incoming e i) < visitPosition T a + 1 at hlt
    omega
  have hr := parentRoot_prefix_visitPosition_reflect D T c hself (D.incoming d i) hp
    (by rw [← parentRoot_retained_incoming D c d hd i];exact hn)
  have hle : visitPosition T (D.incoming d i) ≤ visitPosition T a := by
    rw [hr.1,← parentRoot_retained_incoming D c d hd i]
    exact hn
  have hne : visitPosition T (D.incoming d i) ≠ visitPosition T a := by
    intro he
    have hv : visitRank T (D.incoming d i) = visitRank T a := by
      exact Prod.ext (congrArg T.componentIndex hr.2) he
    have ha := visitRank_injective T hv
    have ht := congrArg D.arcTarget ha
    change D.arcTarget (D.incoming d i) = D.arcTarget (D.incoming c (firstVisitedBranch T c)) at ht
    rw [D.incoming_target,D.incoming_target] at ht
    exact hd (D.crossingVertex_injective ht)
  have hlt : rankBefore (visitRank T (D.incoming d i)) (visitRank T a) := by
    apply Or.inr
    exact ⟨congrArg T.componentIndex hr.2,lt_of_le_of_ne hle hne⟩
  have hg := hgood d hlt
  unfold badAt at hg ⊢
  change firstVisitedBranch U e ≠ E.overBranch e → False
  rw [hi]
  have ho : E.overBranch e = D.overBranch d := by
    change D.overBranch (((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c ⟨d,hd⟩)).val) = _
    rw [Equiv.symm_apply_apply]
  rw [ho]
  exact hg

/-- Every bad self-crossing in the continuing parent is after the new connector,
provided the old traversal had no bad crossing before the cut. -/
theorem parentRoot_bad_after_connector (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
    (d : Fin D.nCrossing) (hd : d ≠ c)
    (hparent : ∀ i : Fin 2,
      componentOf (smoothCrossing D c).continuation
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩) i) =
      componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))
    (hbad : badAt (parentRootSelfSmoothingTraversal D T c hself)
      (smoothCrossingEquiv D c ⟨d,hd⟩)) :
    rankBefore
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))))
      (visitRank (parentRootSelfSmoothingTraversal D T c hself)
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩)
          (firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself)
            (smoothCrossingEquiv D c ⟨d,hd⟩)))) := by
  have hne : visitRank (parentRootSelfSmoothingTraversal D T c hself)
      (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) ≠
      visitRank (parentRootSelfSmoothingTraversal D T c hself)
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩)
          (firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself)
            (smoothCrossingEquiv D c ⟨d,hd⟩))) := by
    intro h
    have ha := visitRank_injective (parentRootSelfSmoothingTraversal D T c hself) h
    rw [parentRoot_retained_incoming] at ha
    have hs := (smoothArcEquiv D).injective ha
    cases hs
  rcases rankBefore_total_of_ne hne with h | h
  · exact h
  · exact (parentRoot_prefix_good D T c hself hgood d hd hparent h hbad).elim

end DirectGLSSW.HOMFLY
