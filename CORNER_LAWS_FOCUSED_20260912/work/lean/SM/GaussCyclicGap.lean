import SM.SortedCyclicGap
import SM.GaussWord

/-! Adjacency in the actual complete cyclic visit sequence. Cycle.next
includes the last/first cut and is invariant under the choice of list rotation. -/

namespace SM

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem gaussCycle_nodup (hn : 3 ≤ n) (hP : Generic P) : (gaussCycle hn hP).Nodup :=
  gaussList_nodup hn hP

theorem mem_gaussCycle (hn : 3 ≤ n) (hP : Generic P) (v : Visit P) : v ∈ gaussCycle hn hP :=
  mem_gaussList hn hP v

noncomputable def nextGaussVisit (hn : 3 ≤ n) (hP : Generic P) (v : Visit P) : Visit P :=
  (gaussCycle hn hP).next (gaussCycle_nodup hn hP) v (mem_gaussCycle hn hP v)

theorem nextGaussVisit_eq_list_next (hn : 3 ≤ n) (hP : Generic P) (v : Visit P) :
    nextGaussVisit hn hP v = (gaussList hn hP).next v (mem_gaussList hn hP v) := rfl

def GaussVisitsAdjacent (hn : 3 ≤ n) (hP : Generic P) (v w : Visit P) : Prop :=
  nextGaussVisit hn hP v = w ∨ nextGaussVisit hn hP w = v

theorem gauss_next_no_visit_between (hn : 3 ≤ n) (hP : Generic P) {v w : Visit P}
    (hnext : nextGaussVisit hn hP v = w) (u : Visit P) :
    ¬ traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 u)
      (visitPosition hn hP.1 w) := by
  classical
  let d : DecidableEq (Visit P) := inferInstance
  letI := visitLinearOrder hn hP
  rw [nextGaussVisit_eq_list_next] at hnext
  have hnext' : @List.next (Visit P) d (Finset.univ : Finset (Visit P)).sort v
      ((Finset.mem_sort _).mpr (Finset.mem_univ v)) = w := hnext
  have hd : d = (fun a b : Visit P => LinearOrder.toDecidableEq a b) :=
    Subsingleton.elim _ _
  rw [hd] at hnext'
  have hg := sorted_next_no_cyclic_between (Finset.univ : Finset (Visit P))
    (Finset.mem_univ v) (Finset.mem_univ w) hnext' u (Finset.mem_univ u)
  exact hg

theorem gauss_adjacent_empty_arc (hn : 3 ≤ n) (hP : Generic P) {v w : Visit P}
    (h : GaussVisitsAdjacent hn hP v w) :
    (∀ u : Visit P, ¬ traversalBetween (visitPosition hn hP.1 v)
      (visitPosition hn hP.1 u) (visitPosition hn hP.1 w)) ∨
    (∀ u : Visit P, ¬ traversalBetween (visitPosition hn hP.1 w)
      (visitPosition hn hP.1 u) (visitPosition hn hP.1 v)) := by
  rcases h with h | h
  · exact Or.inl (gauss_next_no_visit_between hn hP h)
  · exact Or.inr (gauss_next_no_visit_between hn hP h)

end SM
