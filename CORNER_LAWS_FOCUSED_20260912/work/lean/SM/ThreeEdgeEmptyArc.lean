import SM.ThreeEdgeArcThreads
import SM.GaussCyclicGap

/-! Cyclic adjacency of the actual two newborn visits forces the particular
short arc empty, even when the original cusp is allowed to have threads. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {f : ZMod n}

theorem twoStepArc_no_newborn_visit (hn : 3 ≤ n) (hP : G1 P)
    (h : IsCrossing P {f, f + 2}) (v : Visit P) (hc : v.1.val = {f, f + 2}) :
    ¬ twoStepOpenArc hn hP h (visitPosition hn hP v) := by
  have hv : v.2.val = f ∨ v.2.val = f + 2 := by
    have hm : v.2.val ∈ ({f, f + 2} : Finset (ZMod n)) :=
      (congrArg (fun q : Finset (ZMod n) => v.2.val ∈ q) hc).mp v.2.property
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hv with hv | hv
  · have he : v = twoStepFirstVisit h := visit_ext hc hv
    rw [he]
    change ¬ traversalBetween _ _ _
    unfold traversalBetween
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith
  · have he : v = twoStepLastVisit h := visit_ext hc hv
    rw [he]
    change ¬ traversalBetween _ _ _
    unfold traversalBetween
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith

theorem twoStepArc_empty_of_adjacent (hn : 3 ≤ n) (hP : Generic P)
    (h : IsCrossing P {f, f + 2})
    (ha : GaussVisitsAdjacent hn hP (twoStepFirstVisit h) (twoStepLastVisit h)) :
    ∀ v : Visit P, ¬ twoStepOpenArc hn hP.1 h (visitPosition hn hP.1 v) := by
  rcases gauss_adjacent_empty_arc hn hP ha with hshort | hlong
  · exact hshort
  · intro v hv
    have hc : v.1.val ≠ {f, f + 2} := fun he => twoStepArc_no_newborn_visit hn hP.1 h v he hv
    obtain ⟨w, _, _, hw⟩ := twoStepArc_visit_partner hn hP h v hc hv
    exact hlong w hw

theorem twoStep_middle_edge_no_crossing (hn : 3 ≤ n) (hP : Generic P)
    (h : IsCrossing P {f, f + 2})
    (ha : GaussVisitsAdjacent hn hP (twoStepFirstVisit h) (twoStepLastVisit h)) :
    ∀ c : Crossing P, f + 1 ∉ c.val := by
  intro c hc
  let v : Visit P := ⟨c, f + 1, hc⟩
  have hv : twoStepOpenArc hn hP.1 h (visitPosition hn hP.1 v) :=
    (twoStepOpenArc_iff hn hP.1 h _).mpr (Or.inr (Or.inl rfl))
  exact twoStepArc_empty_of_adjacent hn hP h ha v hv

end SM
