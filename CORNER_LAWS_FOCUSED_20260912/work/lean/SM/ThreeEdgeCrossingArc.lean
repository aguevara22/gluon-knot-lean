import SM.ThreeEdgeArc
import SM.PairVisits
import SM.CrossingPair

/-! The short arc between actual visits of a crossing on edges f and f+2.
Every possible visit in the arc is retained, including threaded crossings. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {f : ZMod n}

def twoStepFirstVisit (h : IsCrossing P {f, f + 2}) : Visit P := pairVisit h

def twoStepLastVisit (h : IsCrossing P {f, f + 2}) : Visit P :=
  ⟨⟨{f, f + 2}, h⟩, f + 2, by simp⟩

def twoStepOpenArc (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (x : TraversalPoint n) : Prop :=
  traversalBetween (visitPosition hn hP (twoStepFirstVisit h)) x
    (visitPosition hn hP (twoStepLastVisit h))

def twoStepClosedArc (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (x : TraversalPoint n) : Prop :=
  x = visitPosition hn hP (twoStepFirstVisit h) ∨ twoStepOpenArc hn hP h x ∨
    x = visitPosition hn hP (twoStepLastVisit h)

theorem twoStepOpenArc_iff (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (x : TraversalPoint n) :
    twoStepOpenArc hn hP h x ↔
      (x.1 = f ∧ visitParameter (twoStepFirstVisit h) < x.2.val) ∨
      x.1 = f + 1 ∨ (x.1 = f + 2 ∧ x.2.val < visitParameter (twoStepLastVisit h)) := by
  exact traversalBetween_two_step hn f _ _ x

theorem twoStepArc_vertex_iff (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (i : ZMod n) :
    twoStepOpenArc hn hP h (traversalVertex i) ↔ i = f + 1 ∨ i = f + 2 := by
  exact three_edge_arc_vertices hn f _ _ (visitPosition_interior hn hP (twoStepLastVisit h)).1 i

theorem twoStepArc_visit_edge (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (v : Visit P) (hv : twoStepOpenArc hn hP h (visitPosition hn hP v)) :
    v.2.val = f ∨ v.2.val = f + 1 ∨ v.2.val = f + 2 := by
  rcases (twoStepOpenArc_iff hn hP h _).mp hv with hv | hv | hv
  · exact Or.inl hv.1
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr hv.1)

theorem twoStepArc_middle_edge (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (t : Set.Ico (0 : ℝ) 1) : twoStepOpenArc hn hP h (f + 1, t) :=
  (twoStepOpenArc_iff hn hP h _).mpr (Or.inr (Or.inl rfl))

theorem remote_three_consecutive_only_ends {i k : ZMod n} (hr : remote i k)
    (hi : i = f ∨ i = f + 1 ∨ i = f + 2)
    (hk : k = f ∨ k = f + 1 ∨ k = f + 2) :
    ({i, k} : Finset (ZMod n)) = {f, f + 2} := by
  rcases hi with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
  · exact (hr (Or.inr (Or.inl (by ring)))).elim
  · exact (hr (Or.inr (Or.inr (by ring)))).elim
  · rfl
  · exact (hr (Or.inl (by ring))).elim
  · exact (hr (Or.inr (Or.inl (by ring)))).elim
  · exact (hr (Or.inr (Or.inr (by ring)))).elim
  · exact Finset.pair_comm _ _
  · exact (hr (Or.inl (by ring))).elim
  · exact (hr (Or.inr (Or.inl (by ring)))).elim

theorem twoStepArc_no_other_double_visit (hn : 3 ≤ n) (hP : G1 P)
    (h : IsCrossing P {f, f + 2}) (c : Crossing P)
    (i k : {l // l ∈ c.val}) (hik : i ≠ k)
    (hi : twoStepOpenArc hn hP h (visitPosition hn hP ⟨c, i⟩))
    (hk : twoStepOpenArc hn hP h (visitPosition hn hP ⟨c, k⟩)) :
    c.val = {f, f + 2} := by
  have hpair : c.val = {i.val, k.val} := by
    apply Finset.eq_of_subset_of_card_le
    · intro l hl
      rcases crossing_visits_exhaust c i k hik ⟨l, hl⟩ with he | he
      · simp [show l = i.val from congrArg Subtype.val he]
      · simp [show l = k.val from congrArg Subtype.val he]
    · have hne : i.val ≠ k.val := fun he => hik (Subtype.ext he)
      simp only [Finset.card_pair hne, crossing_card_two]
      exact le_rfl
  have hr := crossing_pair_remote (hpair ▸ c.property)
  exact hpair.trans (remote_three_consecutive_only_ends hr
    (twoStepArc_visit_edge hn hP h ⟨c, i⟩ hi) (twoStepArc_visit_edge hn hP h ⟨c, k⟩ hk))

end SM
