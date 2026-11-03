import HOMFLYVisitPositionSuccessor
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Consecutive actual arcs lie in one genuine continuation component. -/
theorem chain_componentOf_eq (D : PLLinkDiagram) {m : ℕ} [NeZero m]
    (g : Fin m → Fin D.nArc)
    (hstep : ∀ (j : Fin m) (hj : j.val+1<m),
      g ⟨j.val+1,hj⟩ = D.continuation (g j)) (i : Fin m) :
    componentOf D.continuation (g i) = componentOf D.continuation (g 0) := by
  have H : ∀ (n : ℕ) (hn : n<m),
      componentOf D.continuation (g ⟨n,hn⟩) = componentOf D.continuation (g 0) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      let j : Fin m := ⟨n,by omega⟩
      rw [hstep j hn,componentOf_apply]
      exact ih j.isLt
  exact H i.val i.isLt

/-- Avoiding the stored root forces actual positions to increase without wrapping. -/
theorem rootFreeChain_visitPosition (D : PLLinkDiagram) (T : BasedTraversal D)
    {m : ℕ} [NeZero m] (g : Fin m → Fin D.nArc)
    (hstep : ∀ (j : Fin m) (hj : j.val+1<m),
      g ⟨j.val+1,hj⟩ = D.continuation (g j))
    (hroot : ∀ j, g j ≠ (T.baseArc (componentOf D.continuation (g j))).val)
    (i : Fin m) : visitPosition T (g i) = visitPosition T (g 0)+i.val := by
  have H : ∀ (n : ℕ) (hn : n<m),
      visitPosition T (g ⟨n,hn⟩) = visitPosition T (g 0)+n := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      let j : Fin m := ⟨n,by omega⟩
      have hs := hstep j hn
      have hc : componentOf D.continuation (g ⟨n+1,hn⟩) =
          componentOf D.continuation (g j) := by
        rw [hs,componentOf_apply]
      have hne : D.continuation (g j) ≠ (T.baseArc (componentOf D.continuation (g j))).val := by
        rw [← hs,← hc]
        exact hroot ⟨n+1,hn⟩
      rw [hs,visitPosition_continuation_of_ne_root D T (g j) hne,ih j.isLt]
      omega
  exact H i.val i.isLt

/-- The derived affine position remains strictly inside the actual component orbit. -/
theorem rootFreeChain_visitPosition_bound (D : PLLinkDiagram) (T : BasedTraversal D)
    {m : ℕ} [NeZero m] (g : Fin m → Fin D.nArc)
    (hstep : ∀ (j : Fin m) (hj : j.val+1<m),
      g ⟨j.val+1,hj⟩ = D.continuation (g j))
    (hroot : ∀ j, g j ≠ (T.baseArc (componentOf D.continuation (g j))).val)
    (i : Fin m) : visitPosition T (g 0)+i.val <
      Fintype.card (Fibre D.continuation (componentOf D.continuation (g 0))) := by
  rw [← rootFreeChain_visitPosition D T g hstep hroot i,
    ← chain_componentOf_eq D g hstep i]
  simpa only [visitPosition,(T.baseArc (componentOf D.continuation (g i))).property] using
    ((orbitEnumeration D.continuation
    (T.baseArc (componentOf D.continuation (g i))).val).symm
      ⟨g i,(T.baseArc (componentOf D.continuation (g i))).property.symm⟩).isLt

/-- Numerical order on a root-free chain is exactly actual rooted visit order. -/
theorem rootFreeChain_visitPosition_lt_iff (D : PLLinkDiagram) (T : BasedTraversal D)
    {m : ℕ} [NeZero m] (g : Fin m → Fin D.nArc)
    (hstep : ∀ (j : Fin m) (hj : j.val+1<m),
      g ⟨j.val+1,hj⟩ = D.continuation (g j))
    (hroot : ∀ j, g j ≠ (T.baseArc (componentOf D.continuation (g j))).val)
    (i j : Fin m) : visitPosition T (g i) < visitPosition T (g j) ↔ i.val<j.val := by
  rw [rootFreeChain_visitPosition D T g hstep hroot i,
    rootFreeChain_visitPosition D T g hstep hroot j]
  omega

/-- Excluding one common-component stored root suffices. -/
theorem rootFreeChain_visitPosition_of_common_root (D : PLLinkDiagram) (T : BasedTraversal D)
    {m : ℕ} [NeZero m] (g : Fin m → Fin D.nArc)
    (hstep : ∀ (j : Fin m) (hj : j.val+1<m),
      g ⟨j.val+1,hj⟩ = D.continuation (g j))
    (hroot : ∀ j, g j ≠ (T.baseArc (componentOf D.continuation (g 0))).val)
    (i : Fin m) : visitPosition T (g i) = visitPosition T (g 0)+i.val := by
  apply rootFreeChain_visitPosition D T g hstep
  intro j
  rw [chain_componentOf_eq D g hstep j]
  exact hroot j

end DirectGLSSW.HOMFLY
