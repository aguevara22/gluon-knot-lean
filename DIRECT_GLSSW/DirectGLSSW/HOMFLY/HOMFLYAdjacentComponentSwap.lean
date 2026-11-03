import DirectGLSSW.HOMFLY.HOMFLYTraversalOrderChanges

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- The adjacent transposition of component ranks `r` and `r+1`. -/
def adjacentComponentSwap {n : ℕ} (r : Fin n) (hr : r.val + 1 < n) : Fin n ≃ Fin n :=
  Equiv.swap r ⟨r.val + 1, hr⟩

theorem adjacentComponentSwap_apply_val {n : ℕ} (r : Fin n) (hr : r.val + 1 < n)
    (i : Fin n) :
    (adjacentComponentSwap r hr i).val =
      if i = r then r.val + 1 else if i = (⟨r.val + 1, hr⟩ : Fin n) then r.val else i.val := by
  classical
  let s : Fin n := ⟨r.val + 1, hr⟩
  have hsr : s ≠ r := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [s] at hv
    omega
  by_cases hir : i = r
  · subst i
    simp [adjacentComponentSwap, s, hsr]
  · by_cases his : i = s
    · subst i
      simp [adjacentComponentSwap, s, hsr]
    · have hir' : i ≠ r := hir
      have his' : i ≠ s := his
      simp [adjacentComponentSwap, s, Equiv.swap_apply_of_ne_of_ne hir' his', hir, his]

theorem adjacentComponentSwap_lt_iff_of_not_pair {n : ℕ}
    (r : Fin n) (hr : r.val + 1 < n) (i j : Fin n)
    (hnot : ¬ ((i = r ∧ j.val = r.val + 1) ∨
      (i.val = r.val + 1 ∧ j = r))) :
    adjacentComponentSwap r hr i < adjacentComponentSwap r hr j ↔ i < j := by
  have hi := adjacentComponentSwap_apply_val r hr i
  have hj := adjacentComponentSwap_apply_val r hr j
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, hi, hj]
  let s : Fin n := ⟨r.val + 1, hr⟩
  have hrn : r.val + 1 < n := hr
  by_cases hir : i = r <;> by_cases his : i = s <;>
    by_cases hjr : j = r <;> by_cases hjs : j = s <;>
      simp_all [s, Fin.ext_iff] <;> omega

theorem rankBefore_adjacentComponentSwap_of_not_pair {n : ℕ}
    (r : Fin n) (hr : r.val + 1 < n) (i j : Fin n) (p q : ℕ)
    (hnot : ¬ ((i = r ∧ j.val = r.val + 1) ∨
      (i.val = r.val + 1 ∧ j = r))) :
    rankBefore (adjacentComponentSwap r hr i, p)
      (adjacentComponentSwap r hr j, q) ↔ rankBefore (i, p) (j, q) := by
  by_cases hij : i = j
  · subst j
    simp [rankBefore]
  · have hswapNe : adjacentComponentSwap r hr i ≠ adjacentComponentSwap r hr j :=
      fun h => hij (Equiv.injective (adjacentComponentSwap r hr) h)
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hlt' : adjacentComponentSwap r hr i < adjacentComponentSwap r hr j :=
        (adjacentComponentSwap_lt_iff_of_not_pair r hr i j hnot).2 hlt
      simp [rankBefore, hij, hswapNe, hlt', hlt]
    · have hgt' : adjacentComponentSwap r hr j < adjacentComponentSwap r hr i := by
        apply (adjacentComponentSwap_lt_iff_of_not_pair r hr j i ?_).2 hgt
        intro h
        apply hnot
        rcases h with h | h
        · exact Or.inr ⟨h.2, h.1⟩
        · exact Or.inl ⟨h.2, h.1⟩
      simp [rankBefore, hij, hswapNe, hgt', hgt] <;> omega

theorem firstVisitedBranch_reindex_adjacent_components_of_not_mixed
    {D : PLLinkDiagram} (T : BasedTraversal D) (r : Fin (diagramComponentCount D))
    (hr : r.val + 1 < diagramComponentCount D) (c : Fin D.nCrossing)
    (hnot : ¬ ((T.componentIndex
        (PermutationOrbits.componentOf D.continuation (D.incoming c 0)) = r ∧
        (T.componentIndex
          (PermutationOrbits.componentOf D.continuation (D.incoming c 1))).val = r.val + 1) ∨
      ((T.componentIndex
          (PermutationOrbits.componentOf D.continuation (D.incoming c 0))).val = r.val + 1 ∧
        T.componentIndex
          (PermutationOrbits.componentOf D.continuation (D.incoming c 1)) = r))) :
    firstVisitedBranch (reindexTraversalComponents T (adjacentComponentSwap r hr)) c =
      firstVisitedBranch T c := by
  apply firstVisitedBranch_reindexTraversalComponents
  simp only [visitRank, reindexTraversalComponents, Equiv.trans_apply,
    visitPosition_reindexTraversalComponents]
  exact rankBefore_adjacentComponentSwap_of_not_pair r hr _ _ _ _ hnot

theorem firstVisitedBranch_reindex_adjacent_components_of_mixed
    {D : PLLinkDiagram} (T : BasedTraversal D) (r : Fin (diagramComponentCount D))
    (hr : r.val + 1 < diagramComponentCount D) (c : Fin D.nCrossing)
    (hforward : T.componentIndex
      (PermutationOrbits.componentOf D.continuation (D.incoming c 0)) = r)
    (hbackward : (T.componentIndex
      (PermutationOrbits.componentOf D.continuation (D.incoming c 1))).val = r.val + 1) :
    firstVisitedBranch (reindexTraversalComponents T (adjacentComponentSwap r hr)) c =
      Equiv.swap (0 : Fin 2) 1 (firstVisitedBranch T c) := by
  classical
  let i := T.componentIndex
    (PermutationOrbits.componentOf D.continuation (D.incoming c 0))
  let j := T.componentIndex
    (PermutationOrbits.componentOf D.continuation (D.incoming c 1))
  let s : Fin (diagramComponentCount D) := ⟨r.val + 1, hr⟩
  have hifin : i = r := hforward
  have hjfin : j = s := Fin.ext hbackward
  have hij : i ≠ j := by rw [hifin, hjfin]; exact (by
    intro h
    have hv := congrArg Fin.val h
    simp [s] at hv)
  have hbefore : rankBefore (i, visitPosition T (D.incoming c 0))
      (j, visitPosition T (D.incoming c 1)) := by
    apply Or.inl
    rw [hifin, hjfin]
    exact Nat.lt_succ_self _
  have hafter : ¬ rankBefore
      (adjacentComponentSwap r hr i, visitPosition T (D.incoming c 0))
      (adjacentComponentSwap r hr j, visitPosition T (D.incoming c 1)) := by
    intro h
    rcases h with hlt | ⟨heq, _⟩
    · have hv : adjacentComponentSwap r hr i < adjacentComponentSwap r hr j := hlt
      rw [hifin, hjfin] at hv
      rw [Fin.lt_iff_val_lt_val] at hv
      simp [adjacentComponentSwap_apply_val, adjacentComponentSwap, s] at hv
    · exact hij (Equiv.injective (adjacentComponentSwap r hr) heq)
  unfold firstVisitedBranch
  simp only [visitRank]
  change (if rankBefore
      ((reindexTraversalComponents T (adjacentComponentSwap r hr)).componentIndex
          (PermutationOrbits.componentOf D.continuation (D.incoming c 0)),
        visitPosition (reindexTraversalComponents T (adjacentComponentSwap r hr))
          (D.incoming c 0))
      ((reindexTraversalComponents T (adjacentComponentSwap r hr)).componentIndex
          (PermutationOrbits.componentOf D.continuation (D.incoming c 1)),
        visitPosition (reindexTraversalComponents T (adjacentComponentSwap r hr))
          (D.incoming c 1)) then 0 else 1) = _
  rw [visitPosition_reindexTraversalComponents, visitPosition_reindexTraversalComponents]
  simp only [reindexTraversalComponents, Equiv.trans_apply]
  have hbefore' : rankBefore
      (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 0)),
        visitPosition T (D.incoming c 0))
      (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 1)),
        visitPosition T (D.incoming c 1)) := by simpa [i, j] using hbefore
  have hafter' : ¬ rankBefore
      ((adjacentComponentSwap r hr
        (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 0))),
        visitPosition T (D.incoming c 0)))
      ((adjacentComponentSwap r hr
        (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 1))),
        visitPosition T (D.incoming c 1))) := by simpa [i, j] using hafter
  rw [if_pos hbefore', if_neg hafter']
  simp

theorem firstVisitedBranch_reindex_adjacent_components_of_mixed_reverse
    {D : PLLinkDiagram} (T : BasedTraversal D) (r : Fin (diagramComponentCount D))
    (hr : r.val + 1 < diagramComponentCount D) (c : Fin D.nCrossing)
    (hforward : (T.componentIndex
      (PermutationOrbits.componentOf D.continuation (D.incoming c 0))).val = r.val + 1)
    (hbackward : T.componentIndex
      (PermutationOrbits.componentOf D.continuation (D.incoming c 1)) = r) :
    firstVisitedBranch (reindexTraversalComponents T (adjacentComponentSwap r hr)) c =
      Equiv.swap (0 : Fin 2) 1 (firstVisitedBranch T c) := by
  classical
  let i := T.componentIndex
    (PermutationOrbits.componentOf D.continuation (D.incoming c 0))
  let j := T.componentIndex
    (PermutationOrbits.componentOf D.continuation (D.incoming c 1))
  let s : Fin (diagramComponentCount D) := ⟨r.val + 1, hr⟩
  have hifin : i = s := Fin.ext hforward
  have hjfin : j = r := hbackward
  have hij : i ≠ j := by rw [hifin, hjfin]; intro h; have hv := congrArg Fin.val h; simp [s] at hv
  have hbefore : ¬ rankBefore (i, visitPosition T (D.incoming c 0))
      (j, visitPosition T (D.incoming c 1)) := by
    intro h
    rcases h with hlt | ⟨heq, _⟩
    · have hv := Fin.lt_iff_val_lt_val.mp hlt
      rw [hifin, hjfin] at hv
      simp [s] at hv
    · exact hij heq
  have hafter : rankBefore
      (adjacentComponentSwap r hr i, visitPosition T (D.incoming c 0))
      (adjacentComponentSwap r hr j, visitPosition T (D.incoming c 1)) := by
    apply Or.inl
    rw [hifin, hjfin]
    have hs : adjacentComponentSwap r hr s = r := by simp [adjacentComponentSwap, s]
    have hr' : adjacentComponentSwap r hr r = s := by simp [adjacentComponentSwap, s]
    rw [hs, hr']
    exact Nat.lt_succ_self _
  unfold firstVisitedBranch
  simp only [visitRank]
  change (if rankBefore
      ((reindexTraversalComponents T (adjacentComponentSwap r hr)).componentIndex
          (PermutationOrbits.componentOf D.continuation (D.incoming c 0)),
        visitPosition (reindexTraversalComponents T (adjacentComponentSwap r hr))
          (D.incoming c 0))
      ((reindexTraversalComponents T (adjacentComponentSwap r hr)).componentIndex
          (PermutationOrbits.componentOf D.continuation (D.incoming c 1)),
        visitPosition (reindexTraversalComponents T (adjacentComponentSwap r hr))
          (D.incoming c 1)) then 0 else 1) = _
  rw [visitPosition_reindexTraversalComponents, visitPosition_reindexTraversalComponents]
  simp only [reindexTraversalComponents, Equiv.trans_apply]
  have hbefore' : ¬ rankBefore
      (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 0)),
        visitPosition T (D.incoming c 0))
      (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 1)),
        visitPosition T (D.incoming c 1)) := by simpa [i, j] using hbefore
  have hafter' : rankBefore
      ((adjacentComponentSwap r hr
        (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 0))),
        visitPosition T (D.incoming c 0)))
      ((adjacentComponentSwap r hr
        (T.componentIndex (PermutationOrbits.componentOf D.continuation (D.incoming c 1))),
        visitPosition T (D.incoming c 1))) := by simpa [i, j] using hafter
  rw [if_neg hbefore', if_pos hafter']
  simp

end DirectGLSSW.HOMFLY








