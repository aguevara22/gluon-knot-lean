import HOMFLYParentOldComponent
import HOMFLYParentPrefixReflection
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- A retained parent crossing first encountered in the processed prefix
has the same first branch, with the original parent root retained. -/
theorem parentRoot_prefix_firstVisitedBranch (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
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
    firstVisitedBranch (parentRootSelfSmoothingTraversal D T c hself)
      (smoothCrossingEquiv D c ⟨d,hd⟩) = firstVisitedBranch T d := by
  let E := smoothCrossing D c
  let U := parentRootSelfSmoothingTraversal D T c hself
  let e := smoothCrossingEquiv D c ⟨d,hd⟩
  let j := firstVisitedBranch U e
  let i := firstVisitedBranch T d
  let a := D.incoming c (firstVisitedBranch T c)
  have hp (k : Fin 2) : componentOf E.continuation
      (smoothArcEquiv D (Sum.inl (D.incoming d k))) =
      componentOf E.continuation (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) := by
    rw [← parentRoot_retained_incoming D c d hd k]
    exact hparent k
  have hold (k : Fin 2) : componentOf D.continuation (D.incoming d k) =
      componentOf D.continuation a := parentRoot_old_component D T c hself _ (hp k)
  have hn : visitPosition U (E.incoming e j) ≤ visitPosition T a := by
    have hlt : visitPosition U (E.incoming e j) <
        visitPosition U (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c))) := by
      have h := hbefore
      change rankBefore (visitRank U (E.incoming e j))
        (visitRank U (smoothArcEquiv D (Sum.inr (firstVisitedBranch T c)))) at h
      unfold rankBefore visitRank at h
      rw [hparent j] at h
      simpa only [lt_self_iff_false,true_and,false_or] using h
    rw [parentRoot_connector_visitPosition] at hlt
    change visitPosition U (E.incoming e j) < visitPosition T a + 1 at hlt
    omega
  have hjpos : visitPosition T (D.incoming d j) = visitPosition U (E.incoming e j) := by
    rw [parentRoot_retained_incoming D c d hd j] at hn ⊢
    exact (parentRoot_prefix_visitPosition_reflect D T c hself _ (hp j) hn).1
  change j = i
  apply Classical.byContradiction
  intro hji
  have hoi : otherBranch i = j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have hij : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    simp only [otherBranch]
    omega
  have hoj : otherBranch j = i := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have hij : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    simp only [otherBranch]
    omega
  have hltold : visitPosition T (D.incoming d i) < visitPosition T (D.incoming d j) := by
    have h := firstVisitedBranch_is_first T d
    change rankBefore (visitRank T (D.incoming d i))
      (visitRank T (D.incoming d (otherBranch i))) at h
    rw [hoi] at h
    simpa only [rankBefore,visitRank,hold i,hold j,lt_self_iff_false,true_and,false_or] using h
  have hipos : visitPosition U (E.incoming e i) = visitPosition T (D.incoming d i) := by
    rw [parentRoot_retained_incoming D c d hd i]
    exact parentRoot_prefix_visitPosition D T c hself _ (hold i) (by
      change visitPosition T (D.incoming d i) ≤ visitPosition T a
      omega)
  have hltnew : visitPosition U (E.incoming e j) < visitPosition U (E.incoming e i) := by
    have h := firstVisitedBranch_is_first U e
    change rankBefore (visitRank U (E.incoming e j))
      (visitRank U (E.incoming e (otherBranch j))) at h
    rw [hoj] at h
    unfold rankBefore visitRank at h
    rw [hparent j,hparent i] at h
    simpa only [lt_self_iff_false,true_and,false_or] using h
  omega

end DirectGLSSW.HOMFLY
