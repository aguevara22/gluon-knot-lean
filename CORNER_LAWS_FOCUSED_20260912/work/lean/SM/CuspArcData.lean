import SM.CuspEmptyEdge

/-! Complete actual arc data for the newborn crossing. The cyclic word is
the existing visit cycle with its crossing labels; its two occurrences are
exactly the distinct endpoint visits used in the adjacency condition. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {f : ZMod n}

theorem twoStep_newborn_visits_exhaust (h : IsCrossing P {f, f + 2})
    (v : Visit P) (hc : v.1 = (twoStepFirstVisit h).1) :
    v = twoStepFirstVisit h ∨ v = twoStepLastVisit h := by
  have hs : v.1.val = {f, f + 2} := congrArg Subtype.val hc
  have hm : v.2.val ∈ ({f, f + 2} : Finset (ZMod n)) :=
    (congrArg (fun q : Finset (ZMod n) => v.2.val ∈ q) hs).mp v.2.property
  rcases Finset.mem_insert.mp hm with hi | hi
  · exact Or.inl (visit_ext hs hi)
  · exact Or.inr (visit_ext hs (Finset.mem_singleton.mp hi))

structure CuspArcData (hn : 3 ≤ n) (hP : Generic P) (h : IsCrossing P {f, f + 2}) : Prop where
  distinct_visits : twoStepFirstVisit h ≠ twoStepLastVisit h
  same_crossing : (twoStepFirstVisit h).1 = (twoStepLastVisit h).1
  visits_exhaust : ∀ v : Visit P, v.1 = (twoStepFirstVisit h).1 →
    v = twoStepFirstVisit h ∨ v = twoStepLastVisit h
  actual_word : gaussWord hn hP = (gaussCycle hn hP).map Sigma.fst
  closed_arc : ∀ x : TraversalPoint n, twoStepClosedArc hn hP.1 h x ↔
    (x.1 = f ∧ visitParameter (twoStepFirstVisit h) ≤ x.2.val) ∨
    x.1 = f + 1 ∨ (x.1 = f + 2 ∧ x.2.val ≤ visitParameter (twoStepLastVisit h))
  vertices : ∀ i : ZMod n, twoStepClosedArc hn hP.1 h (traversalVertex i) ↔
    i = f + 1 ∨ i = f + 2
  thread_partner : ∀ v : Visit P, v.1.val ≠ {f, f + 2} →
    twoStepOpenArc hn hP.1 h (visitPosition hn hP.1 v) →
    ∃ w : Visit P, w.1 = v.1 ∧ w ≠ v ∧
      traversalBetween (visitPosition hn hP.1 (twoStepLastVisit h))
        (visitPosition hn hP.1 w) (visitPosition hn hP.1 (twoStepFirstVisit h))
  empty_of_adjacent : GaussVisitsAdjacent hn hP (twoStepFirstVisit h) (twoStepLastVisit h) →
    ∀ v : Visit P, ¬ twoStepOpenArc hn hP.1 h (visitPosition hn hP.1 v)

theorem cusp_arc_data (hn : 3 ≤ n) (hP : Generic P) (h : IsCrossing P {f, f + 2}) :
    CuspArcData hn hP h where
  distinct_visits := twoStepFirstVisit_ne_last h
  same_crossing := rfl
  visits_exhaust := twoStep_newborn_visits_exhaust h
  actual_word := rfl
  closed_arc := twoStepClosedArc_iff hn hP.1 h
  vertices := twoStepClosedArc_vertex_iff hn hP.1 h
  thread_partner := twoStepArc_visit_partner hn hP h
  empty_of_adjacent := twoStepArc_empty_of_adjacent hn hP h

end SM
