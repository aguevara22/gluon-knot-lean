import DirectGLSSW.HOMFLY.HOMFLYInnerTransportInduction

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- Change only the chosen order of continuation components. -/
def reindexTraversalComponents {D : PLLinkDiagram} (T : BasedTraversal D)
    (σ : Fin (diagramComponentCount D) ≃ Fin (diagramComponentCount D)) :
    BasedTraversal D where
  componentIndex := T.componentIndex.trans σ
  baseArc := T.baseArc

@[simp] theorem visitPosition_reindexTraversalComponents
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (σ : Fin (diagramComponentCount D) ≃ Fin (diagramComponentCount D))
    (e : Fin D.nArc) :
    visitPosition (reindexTraversalComponents T σ) e = visitPosition T e := rfl

theorem firstVisitedBranch_reindexTraversalComponents
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (σ : Fin (diagramComponentCount D) ≃ Fin (diagramComponentCount D))
    (c : Fin D.nCrossing)
    (horder :
      rankBefore
          (σ (T.componentIndex
            (PermutationOrbits.componentOf D.continuation (D.incoming c 0))),
            visitPosition T (D.incoming c 0))
          (σ (T.componentIndex
            (PermutationOrbits.componentOf D.continuation (D.incoming c 1))),
            visitPosition T (D.incoming c 1)) ↔
      rankBefore (visitRank T (D.incoming c 0))
        (visitRank T (D.incoming c 1))) :
    firstVisitedBranch (reindexTraversalComponents T σ) c =
      firstVisitedBranch T c := by
  classical
  unfold firstVisitedBranch
  change (if rankBefore
      (σ (T.componentIndex
        (PermutationOrbits.componentOf D.continuation (D.incoming c 0))),
        visitPosition T (D.incoming c 0))
      (σ (T.componentIndex
        (PermutationOrbits.componentOf D.continuation (D.incoming c 1))),
        visitPosition T (D.incoming c 1)) then 0 else 1) = _
  rw [horder]

theorem firstVisitedBranch_reindex_selfCrossing
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (σ : Fin (diagramComponentCount D) ≃ Fin (diagramComponentCount D))
    (c : Fin D.nCrossing)
    (hcomponent :
      PermutationOrbits.componentOf D.continuation (D.incoming c 0) =
      PermutationOrbits.componentOf D.continuation (D.incoming c 1)) :
    firstVisitedBranch (reindexTraversalComponents T σ) c =
      firstVisitedBranch T c := by
  classical
  apply firstVisitedBranch_reindexTraversalComponents
  simp [rankBefore, visitRank, hcomponent]

def InnerSameBranchEvaluatorIH (n k : ℕ) : Prop :=
  ∀ {D : PLLinkDiagram}, D.nCrossing = n →
    ∀ (T U : BasedTraversal D),
      (badCrossings T).card < k →
      (∀ c, firstVisitedBranch T c = firstVisitedBranch U c) →
        descendingLaurentEvaluator D T = descendingLaurentEvaluator D U

theorem innerSameBranchEvaluator_successor {n k : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (ih : InnerSameBranchEvaluatorIH n k) :
    InnerSameBranchEvaluatorIH n (k + 1) := by
  intro D hD T U hcard hbranches
  have hbad : badCrossings T = badCrossings U := by
    ext c
    simp [badCrossings, badAt, hbranches c]
  have hcardEq : (badCrossings U).card = (badCrossings T).card :=
    (congrArg Finset.card hbad).symm
  by_cases hlt : (badCrossings T).card < k
  · exact ih hD T U hlt hbranches
  · have hk : (badCrossings T).card = k := by omega
    by_cases hk0 : k = 0
    · have hEmpty : badCrossings T = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      have hEmptyU : badCrossings U = ∅ := by rw [← hbad]; exact hEmpty
      have hTermT : (badCrossings T).Nonempty = False := by simp [hEmpty]
      have hTermU : (badCrossings U).Nonempty = False := by simp [hEmptyU]
      rw [descendingLaurentEvaluator_terminal D T hTermT,
        descendingLaurentEvaluator_terminal D U hTermU]
    · have hnonempty : (badCrossings T).Nonempty := Finset.card_pos.mp (by omega)
      let c := Classical.choose hnonempty
      have hcMem : c ∈ badCrossings T := Classical.choose_spec hnonempty
      have hcT : badAt T c := by simpa [badCrossings] using hcMem
      have hcU : badAt U c := by
        change firstVisitedBranch U c ≠ D.overBranch c
        rw [← hbranches c]
        exact hcT
      have outerP := innerBadCard_simultaneous_induction outer (k + 1)
      have hEvalT : descendingLaurentEvaluator D T =
          descendingEvaluatorPivotBranch D T c :=
        outerP.1 hD T c (by rw [hk]; omega) hcT
      have hEvalU : descendingLaurentEvaluator D U =
          descendingEvaluatorPivotBranch D U c :=
        outerP.1 hD U c (by rw [hcardEq, hk]; omega) hcU
      have hSwitchCard : (badCrossings (switchTraversal T c)).card < k := by
        have hcTMem : c ∈ badCrossings T := by simpa [badCrossings] using hcT
        have hdrop := badCrossings_switch_card T c hcTMem
        omega
      have hSwitchBranches : ∀ d,
          firstVisitedBranch (switchTraversal T c) d =
            firstVisitedBranch (switchTraversal U c) d := by
        intro d
        simpa using hbranches d
      have hDswitch : (switchCrossing D c).nCrossing = n := by
        simpa [switch_crossing_count] using hD
      have hSwitch := ih hDswitch (switchTraversal T c) (switchTraversal U c)
        hSwitchCard hSwitchBranches
      have hSmoothCount : (smoothCrossing D c).nCrossing < n := by
        have hdrop := smoothCrossing_crossing_count_drop D c
        rw [hD] at hdrop
        omega
      have hSmooth := outer.1 (SignedDiagramIso.refl (smoothCrossing D c))
        hSmoothCount (smoothChildBasedTraversal D c)
        (smoothChildBasedTraversal D c)
      have hBranches :
          descendingEvaluatorPivotBranch D T c =
            descendingEvaluatorPivotBranch D U c := by
        rw [descendingEvaluatorPivotBranch, descendingEvaluatorPivotBranch,
          hSwitch, hSmooth]
      exact hEvalT.trans (hBranches.trans hEvalU.symm)

theorem innerSameBranchEvaluator_all {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n) (k : ℕ) :
    InnerSameBranchEvaluatorIH n k := by
  induction k with
  | zero =>
      intro D hD T U hcard hbranches
      omega
  | succ k ih =>
      exact innerSameBranchEvaluator_successor outer ih

theorem descendingEvaluator_eq_reindexComponents_of_same_branches {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    {D : PLLinkDiagram} (hD : D.nCrossing = n)
    (T : BasedTraversal D)
    (σ : Fin (diagramComponentCount D) ≃ Fin (diagramComponentCount D))
    (hbranches : ∀ c,
      firstVisitedBranch (reindexTraversalComponents T σ) c =
        firstVisitedBranch T c) :
    descendingLaurentEvaluator D (reindexTraversalComponents T σ) =
      descendingLaurentEvaluator D T := by
  have hbound :
      (badCrossings (reindexTraversalComponents T σ)).card ≤
        Fintype.card (Fin D.nCrossing) := Finset.card_le_univ _
  have hlt : (badCrossings (reindexTraversalComponents T σ)).card <
      D.nCrossing + 1 := by simpa using Nat.lt_succ_of_le hbound
  exact innerSameBranchEvaluator_all outer (D.nCrossing + 1)
    hD (reindexTraversalComponents T σ) T hlt hbranches

theorem descendingEvaluator_eq_reindexComponents_of_orderPreserving {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    {D : PLLinkDiagram} (hD : D.nCrossing = n)
    (T : BasedTraversal D)
    (σ : Fin (diagramComponentCount D) ≃ Fin (diagramComponentCount D))
    (horder : ∀ c,
      rankBefore
          (σ (T.componentIndex
            (PermutationOrbits.componentOf D.continuation (D.incoming c 0))),
            visitPosition T (D.incoming c 0))
          (σ (T.componentIndex
            (PermutationOrbits.componentOf D.continuation (D.incoming c 1))),
            visitPosition T (D.incoming c 1)) ↔
      rankBefore (visitRank T (D.incoming c 0))
        (visitRank T (D.incoming c 1))) :
    descendingLaurentEvaluator D (reindexTraversalComponents T σ) =
      descendingLaurentEvaluator D T := by
  apply descendingEvaluator_eq_reindexComponents_of_same_branches outer hD T σ
  intro c
  exact firstVisitedBranch_reindexTraversalComponents T σ c (horder c)

end DirectGLSSW.HOMFLY










