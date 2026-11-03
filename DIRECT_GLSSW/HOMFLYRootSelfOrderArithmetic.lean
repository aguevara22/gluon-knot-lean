import HOMFLYRootSelfOrder
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _

theorem rootSelf_selected_rankBefore_iff (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (b₁ b₂ : Bool) (k j l : ℕ)
    (hj : if b₁ then j < k else k < j)
    (hl : if b₂ then l < k else k < l) :
    rankBefore
      (rootSelfCutOrder D T c hself i (Sum.inl b₁), if b₁ then j else j-k)
      (rootSelfCutOrder D T c hself i (Sum.inl b₂), if b₂ then l else l-k) ↔ j < l := by
  unfold rankBefore
  simp only [Prod.fst, Prod.snd, Fin.lt_def, Fin.ext_iff,
    rootSelfCutOrder_selected_val]
  cases b₁ <;> cases b₂ <;> simp at * <;> omega

theorem rootSelf_selected_other_rankBefore_iff (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (b : Bool)
    (C : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)})
    (j j' l l' : ℕ) :
    rankBefore (rootSelfCutOrder D T c hself i (Sum.inl b),j)
      (rootSelfCutOrder D T c hself i (Sum.inr C),l) ↔
    rankBefore (T.componentIndex (componentOf D.continuation (D.incoming c i)),j')
      (T.componentIndex C.val,l') := by
  simp only [rankBefore, Prod.fst, Prod.snd, Equiv.apply_eq_iff_eq,
    Sum.inl_ne_inr, false_and, or_false, ne_comm.mpr C.property,
    rootSelfCutOrder_lt_iff]
  cases b
  · exact splitSumToFinMiddleFirst_false_lt_other_iff _ _ C
  · exact splitSumToFinMiddleFirst_true_lt_other_iff _ _ C

theorem rootSelf_other_selected_rankBefore_iff (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (b : Bool)
    (C : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)})
    (j j' l l' : ℕ) :
    rankBefore (rootSelfCutOrder D T c hself i (Sum.inr C),j)
      (rootSelfCutOrder D T c hself i (Sum.inl b),l) ↔
    rankBefore (T.componentIndex C.val,j')
      (T.componentIndex (componentOf D.continuation (D.incoming c i)),l') := by
  simp only [rankBefore, Prod.fst, Prod.snd, Equiv.apply_eq_iff_eq,
    Sum.inr_ne_inl, false_and, or_false, C.property,
    rootSelfCutOrder_lt_iff]
  cases b
  · exact splitSumToFinMiddleFirst_other_lt_false_iff _ _ C
  · exact splitSumToFinMiddleFirst_other_lt_true_iff _ _ C

theorem rootSelf_other_other_rankBefore_iff (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2)
    (C E : {C : diagramComponent D // C ≠ componentOf D.continuation (D.incoming c i)})
    (j l : ℕ) :
    rankBefore (rootSelfCutOrder D T c hself i (Sum.inr C),j)
      (rootSelfCutOrder D T c hself i (Sum.inr E),l) ↔
    rankBefore (T.componentIndex C.val,j) (T.componentIndex E.val,l) := by
  simp only [rankBefore, Prod.fst, Prod.snd, Equiv.apply_eq_iff_eq,
    Sum.inr.injEq, Subtype.ext_iff, rootSelfCutOrder_lt_iff,
    splitSumToFinMiddleFirst_other_lt_iff]
  rw [splitSumToFinMiddleFirst_other_lt_iff T.componentIndex
    (componentOf D.continuation (D.incoming c i)) C E]
  rfl

end
end DirectGLSSW.HOMFLY





