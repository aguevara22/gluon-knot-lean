import HOMFLYRootSelfNormalizedRanks
import HOMFLYOrbitTraversalCoordinates
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

theorem rootSelf_selected_rank_data (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) (i : Fin 2)
    (hroot : (T.baseArc (componentOf D.continuation (D.incoming c i))).val = D.incoming c i)
    (x : Fin D.nArc)
    (hc : componentOf D.continuation x = componentOf D.continuation (D.incoming c i))
    (hxa : x ≠ D.incoming c i) (hxb : x ≠ D.incoming c (otherBranch i)) :
    let k := (cutMarkIndex D.continuation (D.incoming c i)
      (D.incoming c (otherBranch i)) (rootCut_sameCycle D c hself i)).val
    ∃ (b : Bool) (j : ℕ),
      (if b then j < k else k < j) ∧
      visitRank T x = (T.componentIndex (componentOf D.continuation (D.incoming c i)),j) ∧
      visitRank (rootSelfSmoothingTraversal D T c hself i) (smoothArcEquiv D (Sum.inl x)) =
        (rootSelfCutOrder D T c hself i (Sum.inl b), if b then j else j-k) := by
  let e := orbitEnumeration D.continuation (D.incoming c i)
  let j := e.symm ⟨x,hc⟩
  let k := cutMarkIndex D.continuation (D.incoming c i)
    (D.incoming c (otherBranch i)) (rootCut_sameCycle D c hself i)
  have he : (e j).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hc⟩)
  have hj0 : j ≠ 0 := by
    intro h
    apply hxa
    rw [← he, h]
    exact orbitEnumeration_zero _ _
  have hjk : j ≠ k := by
    intro h
    apply hxb
    rw [← he, h]
    exact cutMarkIndex_enumerate _ _ _ _
  have hold : visitRank T x = (T.componentIndex (componentOf D.continuation (D.incoming c i)),j.val) := by
    rw [← he]
    exact visitRank_orbitEnumeration T (D.incoming c i) hroot j
  cases hs : FiniteCycleSplit.cutSide k j with
  | false =>
    refine ⟨false,j.val,?_,hold,?_⟩
    · have hjpos : 0 < j.val := by
        have hn : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        omega
      have hh : ¬ (0 < j.val ∧ j.val ≤ k.val) := by
        simpa only [FiniteCycleSplit.cutSide, decide_eq_false_iff_not] using hs
      change k.val < j.val
      omega
    · have h := rootSelf_tail_visitRank D T c hself i j hs hj0
      rw [he] at h
      exact h
  | true =>
    refine ⟨true,j.val,?_,hold,?_⟩
    · have hh : 0 < j.val ∧ j.val ≤ k.val := by
        simpa only [FiniteCycleSplit.cutSide, decide_eq_true_eq] using hs
      have hn : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      change j.val < k.val
      omega
    · have h := rootSelf_middle_visitRank D T c hself i j hs hjk
      rw [he] at h
      exact h

end
end DirectGLSSW.HOMFLY

