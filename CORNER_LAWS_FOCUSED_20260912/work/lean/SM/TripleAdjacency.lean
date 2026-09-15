import SM.TripleParameters
import SM.PairVisits
import SM.SortedAdjacency

/-! The geometric outside-parameter condition implies consecutive indices in
the complete, independently constructed Gauss list of actual visits. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

def VisitsAdjacent (hn : 3 ≤ n) (hP : Generic P) (v w : Visit P) : Prop := by
  classical
  letI := visitLinearOrder hn hP
  letI : DecidableEq (Visit P) := fun a b => LinearOrder.toDecidableEq a b
  exact (gaussList hn hP).idxOf v + 1 = (gaussList hn hP).idxOf w ∨
    (gaussList hn hP).idxOf w + 1 = (gaussList hn hP).idxOf v

theorem gaussList_adjacent_of_no_between (hn : 3 ≤ n) (hP : Generic P)
    {v w : Visit P} (hne : v ≠ w)
    (hgap : ∀ u : Visit P,
      ¬ (visitKey hn hP.1 v < visitKey hn hP.1 u ∧
        visitKey hn hP.1 u < visitKey hn hP.1 w) ∧
      ¬ (visitKey hn hP.1 w < visitKey hn hP.1 u ∧
        visitKey hn hP.1 u < visitKey hn hP.1 v)) :
    VisitsAdjacent hn hP v w := by
  classical
  letI : NeZero n := ⟨by omega⟩
  letI := visitLinearOrder hn hP
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Or.inl
    exact (sorted_indices_adjacent Finset.univ (Finset.mem_univ v)
      (Finset.mem_univ w) hlt (fun u _ => (hgap u).1)).symm
  · apply Or.inr
    exact (sorted_indices_adjacent Finset.univ (Finset.mem_univ w)
      (Finset.mem_univ v) hgt (fun u _ => (hgap u).2)).symm

theorem otherCrossingsOutside_swap [NeZero n] {i j k : ZMod n}
    (h : OtherCrossingsOutside P i j k) : OtherCrossingsOutside P i k j := by
  intro a hai hak haj hc
  rcases h a hai haj hak hc with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact Or.inl ⟨hr, hl⟩
  · exact Or.inr ⟨hr, hl⟩

theorem pairVisits_no_between [NeZero n] (hn : 3 ≤ n) (hP : G1 P)
    {i j k : ZMod n} (hcj : IsCrossing P {i, j}) (hck : IsCrossing P {i, k})
    (hout : OtherCrossingsOutside P i j k) (u : Visit P) :
    ¬ (visitKey hn hP (pairVisit hcj) < visitKey hn hP u ∧
      visitKey hn hP u < visitKey hn hP (pairVisit hck)) := by
  rintro ⟨hl, hr⟩
  obtain ⟨he, hpa, hpb⟩ := visit_between_same_edge hn hP
    (v := pairVisit hcj) (w := pairVisit hck) rfl hl hr
  obtain ⟨h, hhi, hc, rfl⟩ := visit_on_edge_pair u he
  rw [pairVisit_parameter hn hP, pairVisit_parameter hn hP] at hpa hpb
  by_cases hhj : h = j
  · subst h
    exact (lt_irrefl _ hpa).elim
  by_cases hhk : h = k
  · subst h
    exact (lt_irrefl _ hpb).elim
  exact (outsidePair_not_between (hout h hhi hhj hhk hc)).1 ⟨hpa, hpb⟩

theorem pairVisits_adjacent [NeZero n] (hn : 3 ≤ n) (hP : Generic P)
    {i j k : ZMod n} (hjk : j ≠ k)
    (hcj : IsCrossing P {i, j}) (hck : IsCrossing P {i, k})
    (hout : OtherCrossingsOutside P i j k) :
    VisitsAdjacent hn hP (pairVisit hcj) (pairVisit hck) := by
  have hne : pairVisit hcj ≠ pairVisit hck := by
    intro he
    have hp := congrArg visitParameter he
    rw [pairVisit_parameter hn hP.1, pairVisit_parameter hn hP.1] at hp
    exact generic_edgeParameters_ne hn hP hjk hcj hck hp
  apply gaussList_adjacent_of_no_between hn hP hne
  intro u
  exact ⟨pairVisits_no_between hn hP.1 hcj hck hout u,
    pairVisits_no_between hn hP.1 hck hcj (otherCrossingsOutside_swap hout) u⟩

end SM
