import HOMFLYCutProcessedPrefix

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

/-- An actual visit on the cut component, no later than its first cut port,
remains in the actual continuing component. -/
theorem prefix_visit_continuing_component (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (x : Fin D.nArc)
    (hx : componentOf D.continuation x =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))
    (hle : visitPosition T x ≤ visitPosition T (D.incoming c (firstVisitedBranch T c))) :
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl false) := by
  let i := firstVisitedBranch T c
  let a := D.incoming c i
  let b := D.incoming c (otherBranch i)
  let r := (T.baseArc (componentOf D.continuation a)).val
  have hcomp : componentOf D.continuation a = componentOf D.continuation b :=
    (componentOf_eq_iff _ _ _).2 (rootCut_sameCycle D c hself i)
  have ha : componentOf D.continuation a = componentOf D.continuation r :=
    (T.baseArc (componentOf D.continuation a)).property.symm
  have hb : componentOf D.continuation b = componentOf D.continuation r :=
    hcomp.symm.trans ha
  have hxr : componentOf D.continuation x = componentOf D.continuation r := hx.trans ha
  have hpa := visitPosition_eq_orbitPosition_of_baseArc T a r rfl ha
  have hpb := visitPosition_eq_orbitPosition_of_baseArc T b r
    (by dsimp [r]; rw [hcomp]) hb
  have hpx := visitPosition_eq_orbitPosition_of_baseArc T x r
    (by dsimp [r]; rw [hx]) hxr
  have hfirst := firstVisitedBranch_is_first T c
  have hlt : visitPosition T a < visitPosition T b := by
    change rankBefore (visitRank T a) (visitRank T b) at hfirst
    simp only [rankBefore, visitRank, hcomp, lt_self_iff_false, true_and, false_or] at hfirst
    exact hfirst
  have hrx : (rootCutContinuation D c i).SameCycle r x :=
    root_sameCycle_cut_of_position_le D.continuation r a b x ha hb hxr
      (by rw [← hpa, ← hpb]; exact hlt)
      (by rw [← hpx, ← hpa]; exact hle)
  have hra := firstVisited_root_sameCycle_cut D T c hself
  dsimp only at hra
  have hxa : (rootCutContinuation D c i).SameCycle x a := hrx.symm.trans hra
  have hs := congrArg (smoothRootCutComponentEquiv D c i)
    ((componentOf_eq_iff _ _ _).2 hxa)
  rw [smoothRootCutComponentEquiv_old,smoothRootCutComponentEquiv_connector] at hs
  exact hs.trans (rootSelfCutComponents_false D c hself i).symm

/-- Smoothing a self-crossing cannot draw an arc from another original
component into the detached component. No rank or post-cut membership premise. -/
theorem other_component_visit_not_detached (D : PLLinkDiagram)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (x : Fin D.nArc)
    (hx : componentOf D.continuation x ≠ componentOf D.continuation (D.incoming c i)) :
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) ≠
      rootSelfCutComponents D c hself i (Sum.inl true) := by
  intro he
  rw [rootSelfCutComponents_true D c hself i] at he
  have hc : componentOf (rootCutContinuation D c i) x =
      componentOf (rootCutContinuation D c i) (D.incoming c (otherBranch i)) := by
    apply (smoothRootCutComponentEquiv D c i).injective
    rw [smoothRootCutComponentEquiv_old,smoothRootCutComponentEquiv_connector]
    exact he
  have hnew := (componentOf_eq_iff _ _ _).1 hc
  have hold := sameCycle_mul_swap_refines D.continuation
    (rootCut_sameCycle D c hself i) hnew
  exact hx (((componentOf_eq_iff _ _ _).2 hold).trans
    ((componentOf_eq_iff _ _ _).2 (rootCut_sameCycle D c hself i)).symm)

/-- Every actual arc in the processed traversal prefix is outside the
actual detached child, including arcs in earlier original components. -/
theorem before_first_visit_not_detached (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (x : Fin D.nArc)
    (hbefore : rankBefore (visitRank T x)
      (visitRank T (D.incoming c (firstVisitedBranch T c)))) :
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) ≠
      rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true) := by
  by_cases hx : componentOf D.continuation x =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c))
  · have hpos : visitPosition T x <
        visitPosition T (D.incoming c (firstVisitedBranch T c)) := by
      simpa only [rankBefore,visitRank,hx,lt_self_iff_false,true_and,false_or] using hbefore
    have hc := prefix_visit_continuing_component D T c hself x hx (le_of_lt hpos)
    intro he
    have hlabels := (rootSelfCutComponents D c hself (firstVisitedBranch T c)).injective
      (hc.symm.trans he)
    simp only [Sum.inl.injEq,Bool.false_eq_true] at hlabels
  · exact other_component_visit_not_detached D c hself (firstVisitedBranch T c) x hx

/-- The first incoming branch of an earlier visited crossing is outside the
actual detached child, using its actual old-arc image. -/
theorem earlier_crossing_first_old_arc_not_detached
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (d : Fin D.nCrossing)
    (hbefore : rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
      (visitRank T (D.incoming c (firstVisitedBranch T c)))) :
    componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl (D.incoming d (firstVisitedBranch T d)))) ≠
      rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true) :=
  before_first_visit_not_detached D T c hself _ hbefore

/-- The corresponding branch of the actual retained smoothed crossing is
outside the child; the old-arc identification is derived from the constructor. -/
theorem earlier_crossing_first_incoming_not_detached
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (d : Fin D.nCrossing) (hd : d ≠ c)
    (hbefore : rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
      (visitRank T (D.incoming c (firstVisitedBranch T c)))) :
    componentOf (smoothCrossing D c).continuation
      ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩)
        (firstVisitedBranch T d)) ≠
      rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true) := by
  have hi (j : Fin 2) :
      (smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩) j =
        smoothArcEquiv D (Sum.inl (D.incoming d j)) := by
    change smoothArcEquiv D (Sum.inl (D.incoming
      (((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c ⟨d,hd⟩)).val) j)) = _
    rw [Equiv.symm_apply_apply]
  rw [hi]
  exact earlier_crossing_first_old_arc_not_detached D T c hself d hbefore

/-- An earlier visited retained crossing cannot be a self-crossing entirely
inside the actual detached child. -/
theorem earlier_crossing_not_detached_self_crossing
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (d : Fin D.nCrossing) (hd : d ≠ c)
    (hbefore : rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
      (visitRank T (D.incoming c (firstVisitedBranch T c)))) :
    ¬ (componentOf (smoothCrossing D c).continuation
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩) 0) =
        rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true) ∧
      componentOf (smoothCrossing D c).continuation
        ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩) 1) =
        rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true)) := by
  intro h
  have hboth (j : Fin 2) : componentOf (smoothCrossing D c).continuation
      ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d,hd⟩) j) =
      rootSelfCutComponents D c hself (firstVisitedBranch T c) (Sum.inl true) := by
    fin_cases j
    · exact h.1
    · exact h.2
  exact earlier_crossing_first_incoming_not_detached D T c hself d hd hbefore
    (hboth (firstVisitedBranch T d))

end DirectGLSSW.HOMFLY
