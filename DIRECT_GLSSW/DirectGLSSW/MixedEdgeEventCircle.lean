import DirectGLSSW.PolygonNonalternation

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeSupportOrder

open FiniteCycleOrder

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

theorem anchor_lt_visit_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (a : Fin n) (v : CrossingVisit q) :
    (letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
     (Sum.inl a : PolygonEvent q) < Sum.inr v) ↔
      a ≤ crossingVisitEdge q v := by
  rw [polygonEvent_lt_iff]
  simp only [polygonEventEdge, polygonEventParameter]
  have hp := (crossingVisitParameter_spec q v).1
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact le_of_lt h
    · exact le_of_eq h
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, hp⟩

theorem visit_lt_anchor_iff (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (v : CrossingVisit q) (a : Fin n) :
    (letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
     (Sum.inr v : PolygonEvent q) < Sum.inl a) ↔
      crossingVisitEdge q v < a := by
  rw [polygonEvent_lt_iff]
  simp only [polygonEventEdge, polygonEventParameter]
  have hp := (crossingVisitParameter_spec q v).1
  constructor
  · rintro (h | ⟨h, hparam⟩)
    · exact h
    · have : ¬ crossingVisitParameter q v < (0 : K) := not_lt_of_gt hp
      exact False.elim (this hparam)
  · exact Or.inl

/-- A visit on any edge other than `e` lies on the actual complementary
event arc from the successor anchor of `e` to the anchor of `e`. -/
theorem crossingVisit_between_successor_anchor_and_edge_anchor
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (e : Fin n) (v : CrossingVisit q)
    (hve : crossingVisitEdge q v ≠ e) :
    (letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
     strictCyclicBetween (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
      (Sum.inr v) (Sum.inl e)) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  let f := crossingVisitEdge q v
  have hfne : f ≠ e := hve
  have hsuccVal : (cyclicSuccessor e).val =
      if e.val + 1 < n then e.val + 1 else 0 := by
    have hn : 0 < n := by have := e.isLt; omega
    unfold cyclicSuccessor
    rw [cyclicVertexIndex_val e (k := 0) hn]
    simp only [Nat.add_zero]
    split_ifs <;> omega
  have hparam : 0 < crossingVisitParameter q v :=
    (crossingVisitParameter_spec q v).1
  by_cases hnxt : e.val + 1 < n
  · have hsuccVal' : (cyclicSuccessor e).val = e.val + 1 := by
      simpa [hsuccVal, hnxt]
    have hB_lt_A : (Sum.inl e : PolygonEvent q) < Sum.inl (cyclicSuccessor e) := by
      rw [polygonEvent_anchor_lt_iff]
      change e.val < (cyclicSuccessor e).val
      omega
    by_cases hfe : f < e
    · have hX_lt_B : (Sum.inr v : PolygonEvent q) < Sum.inl e := by
        exact (visit_lt_anchor_iff q hq v e).2 hfe
      exact Or.inr (Or.inl ⟨hX_lt_B, hB_lt_A⟩)
    · have hef : e < f := lt_of_le_of_ne (le_of_not_gt hfe) (Ne.symm hfne)
      have hA_lt_X' : (Sum.inl (cyclicSuccessor e) : PolygonEvent q) < Sum.inr v := by
        apply (anchor_lt_visit_iff q hq (cyclicSuccessor e) v).2
        change (cyclicSuccessor e).val ≤ f.val
        rw [hsuccVal]
        simp only [if_pos hnxt]
        change e.val + 1 ≤ f.val
        exact Nat.succ_le_of_lt (by exact_mod_cast hef)
      exact Or.inr (Or.inr ⟨hB_lt_A, hA_lt_X'⟩)
  · have hwrap : e.val + 1 = n := by have := e.isLt; omega
    have hsuccVal' : (cyclicSuccessor e).val = 0 := by
      simpa [hsuccVal, hnxt]
    have hA_lt_B : (Sum.inl (cyclicSuccessor e) : PolygonEvent q) < Sum.inl e := by
      apply (polygonEvent_lt_iff q hq _ _).2
      left
      change (cyclicSuccessor e).val < e.val
      omega
    have hA_lt_X : (Sum.inl (cyclicSuccessor e) : PolygonEvent q) < Sum.inr v := by
      apply (anchor_lt_visit_iff q hq (cyclicSuccessor e) v).2
      change (cyclicSuccessor e).val ≤ f.val
      rw [hsuccVal']
      exact Nat.zero_le f.val
    have hX_lt_B_or_same : (Sum.inr v : PolygonEvent q) < Sum.inl e := by
      apply (visit_lt_anchor_iff q hq v e).2
      have hfneVal : f.val ≠ e.val := fun h => hfne (Fin.ext h)
      omega
    exact Or.inl ⟨hA_lt_X, hX_lt_B_or_same⟩

/-- A visit on `e` lies on the complementary short event arc from `e` to its
original successor, including when that interval crosses the Fin wrap. -/
theorem crossingVisit_between_edge_anchor_and_successor_anchor
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (hn : 3 ≤ n) (e : Fin n) (v : CrossingVisit q)
    (hve : crossingVisitEdge q v = e) :
    letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
    strictCyclicBetween (Sum.inl e : PolygonEvent q) (Sum.inr v)
      (Sum.inl (cyclicSuccessor e)) := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  have hA_lt_v : (Sum.inl e : PolygonEvent q) < Sum.inr v := by
    exact (anchor_lt_visit_iff q hq e v).2 (by rw [hve])
  have hv_lt_B : (Sum.inr v : PolygonEvent q) < Sum.inl (cyclicSuccessor e) ↔
      e < cyclicSuccessor e := by
    simpa [hve] using visit_lt_anchor_iff q hq v (cyclicSuccessor e)
  have hsuccVal : (cyclicSuccessor e).val =
      if e.val + 1 < n then e.val + 1 else 0 := by
    have hn0 : 0 < n := by omega
    unfold cyclicSuccessor
    rw [cyclicVertexIndex_val e (k := 0) hn0]
    simp only [Nat.add_zero]
    split_ifs <;> omega
  by_cases hnxt : e.val + 1 < n
  · have hsucc : e < cyclicSuccessor e := by
      change e.val < (cyclicSuccessor e).val
      rw [hsuccVal]
      simp [hnxt]
    exact Or.inl ⟨hA_lt_v, hv_lt_B.mpr hsucc⟩
  · have hwrap : e.val + 1 = n := by have := e.isLt; omega
    have hsucc : cyclicSuccessor e < e := by
      change (cyclicSuccessor e).val < e.val
      rw [hsuccVal]
      have hepos : 0 < e.val := by omega
      simpa [hnxt] using hepos
    have hsuccEvent : (Sum.inl (cyclicSuccessor e) : PolygonEvent q) < Sum.inl e :=
      (polygonEvent_lt_iff q hq _ _).2 (Or.inl hsucc)
    exact Or.inr (Or.inr ⟨hsuccEvent, hA_lt_v⟩)

def complementaryEventRank (e f : Fin n) : ℕ :=
  if (cyclicSuccessor e).val ≤ f.val then
    f.val - (cyclicSuccessor e).val
  else
    n - (cyclicSuccessor e).val + f.val

noncomputable def complementaryVisitKey (q : Fin n → PlanarPoint K) (e : Fin n)
    (v : CrossingVisit q) :=
  toLex (complementaryEventRank e (crossingVisitEdge q v),
    crossingVisitParameter q v)

/-- The strict cyclic order of two actual visits on the complementary arc is
exactly their lexicographic traversal order after cutting at `succ e`. -/
theorem crossingVisit_arcOrder_iff_complementaryKey_lt
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (e : Fin n) (v w : CrossingVisit q)
    (hv : crossingVisitEdge q v ≠ e)
    (hw : crossingVisitEdge q w ≠ e) :
    (letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
     strictCyclicBetween (Sum.inl (cyclicSuccessor e) : PolygonEvent q)
      (Sum.inr v) (Sum.inr w)) ↔ complementaryVisitKey q e v <
        complementaryVisitKey q e w := by
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq
  let f := crossingVisitEdge q v
  let g := crossingVisitEdge q w
  have hanchorV :
      (Sum.inl (cyclicSuccessor e) : PolygonEvent q) < Sum.inr v ↔
        cyclicSuccessor e ≤ f := anchor_lt_visit_iff q hq _ _
  have hWanchor :
      (Sum.inr w : PolygonEvent q) < Sum.inl (cyclicSuccessor e) ↔
        g < cyclicSuccessor e := visit_lt_anchor_iff q hq _ _
  have hVW :
      (Sum.inr v : PolygonEvent q) < Sum.inr w ↔
        f.val < g.val ∨ f.val = g.val ∧
          crossingVisitParameter q v < crossingVisitParameter q w := by
    rw [polygonEvent_lt_iff]
    simp only [polygonEventEdge, polygonEventParameter]
    change (f < g ∨ f = g ∧ crossingVisitParameter q v < crossingVisitParameter q w) ↔ _
    simp only [Fin.lt_def, Fin.ext_iff]
  rw [strictCyclicBetween, hanchorV, hVW, hWanchor]
  change ((cyclicSuccessor e ≤ f ∧
      (f.val < g.val ∨ f.val = g.val ∧ crossingVisitParameter q v < crossingVisitParameter q w)) ∨
    ((f.val < g.val ∨ f.val = g.val ∧ crossingVisitParameter q v < crossingVisitParameter q w) ∧
      g < cyclicSuccessor e) ∨
    (g < cyclicSuccessor e ∧ cyclicSuccessor e ≤ f)) ↔ _
  change _ ↔ toLex (complementaryEventRank e f, crossingVisitParameter q v) <
    toLex (complementaryEventRank e g, crossingVisitParameter q w)
  rw [Prod.Lex.toLex_lt_toLex]
  have hsucc : (cyclicSuccessor e).val =
      if e.val + 1 < n then e.val + 1 else 0 := by
    have hn : 0 < n := by have := e.isLt; omega
    unfold cyclicSuccessor
    rw [cyclicVertexIndex_val e (k := 0) hn]
    simp only [Nat.add_zero]
    split_ifs <;> omega
  have hfne : f ≠ e := hv
  have hgne : g ≠ e := hw
  by_cases hnxt : e.val + 1 < n
  · have hsuccVal : (cyclicSuccessor e).val = e.val + 1 := by
      rw [hsucc]
      simp [hnxt]
    have hAnchorF : cyclicSuccessor e ≤ f ↔ e.val < f.val := by
      change (cyclicSuccessor e).val ≤ f.val ↔ e.val < f.val
      rw [hsuccVal]
      omega
    have hGAnchor : g < cyclicSuccessor e ↔ g.val < e.val := by
      change g.val < (cyclicSuccessor e).val ↔ g.val < e.val
      rw [hsuccVal]
      omega
    rw [hAnchorF, hGAnchor]
    have hFne : f.val ≠ e.val := fun h => hfne (Fin.ext h)
    have hGne : g.val ≠ e.val := fun h => hgne (Fin.ext h)
    have hfbound := f.isLt
    have hgbound := g.isLt
    by_cases hF : e.val < f.val
    · have hFhi : e.val + 1 ≤ f.val := by omega
      by_cases hG : e.val < g.val
      · have hGhi : e.val + 1 ≤ g.val := by omega
        simp only [complementaryEventRank, hsuccVal, if_pos hFhi, if_pos hGhi]
        have hRankLt : f.val - (e.val + 1) < g.val - (e.val + 1) ↔ f.val < g.val := by
          omega
        have hRankEq : f.val - (e.val + 1) = g.val - (e.val + 1) ↔ f.val = g.val := by
          omega
        rw [hRankLt, hRankEq]
        simp [hF, hG, not_lt_of_gt hG]
      · have hG' : g.val < e.val := by omega
        have hGlo : ¬ e.val + 1 ≤ g.val := by omega
        simp only [complementaryEventRank, hsuccVal, if_pos hFhi, if_neg hGlo]
        have hRankLt : f.val - (e.val + 1) < n - (e.val + 1) + g.val := by omega
        have hRankNe : f.val - (e.val + 1) ≠ n - (e.val + 1) + g.val := by omega
        have hGF : g.val < f.val := by omega
        have hGleF : g ≤ f := by change g.val ≤ f.val; omega
        have hValNe : f.val ≠ g.val := by omega
        simp [hF, hG', hRankLt, hRankNe, hGleF, hValNe]
    · have hF' : f.val < e.val := by omega
      have hFlo : ¬ e.val + 1 ≤ f.val := by omega
      by_cases hG : e.val < g.val
      · have hGhi : e.val + 1 ≤ g.val := by omega
        simp only [complementaryEventRank, hsuccVal, if_neg hFlo, if_pos hGhi]
        have hRankGt : n - (e.val + 1) + f.val > g.val - (e.val + 1) := by omega
        have hRankNe : n - (e.val + 1) + f.val ≠ g.val - (e.val + 1) := by omega
        have hRankNotLt : ¬ n - (e.val + 1) + f.val < g.val - (e.val + 1) := by omega
        have hGNotRev : ¬ g.val < e.val := by omega
        simp [hF', hG, hRankGt, hRankNe, hRankNotLt, hGNotRev]
        simp only [Fin.lt_def]
        simp_all
      · have hG' : g.val < e.val := by omega
        have hGlo : ¬ e.val + 1 ≤ g.val := by omega
        simp only [complementaryEventRank, hsuccVal, if_neg hFlo, if_neg hGlo]
        have hRankLt : n - (e.val + 1) + f.val < n - (e.val + 1) + g.val ↔ f.val < g.val := by
          omega
        have hRankEq : n - (e.val + 1) + f.val = n - (e.val + 1) + g.val ↔ f.val = g.val := by
          omega
        rw [hRankLt, hRankEq]
        have hFinF : ¬ e < f := by change ¬ e.val < f.val; omega
        have hFinG : g < e := by change g.val < e.val; exact hG'
        simp [hFinF, hFinG]
  · have hwrap : e.val + 1 = n := by have := e.isLt; omega
    have hsuccVal : (cyclicSuccessor e).val = 0 := by
      rw [hsucc]
      simp [hnxt]
    have hAVisit : cyclicSuccessor e ≤ f := by
      change (cyclicSuccessor e).val ≤ f.val
      rw [hsuccVal]
      omega
    have hWBeforeA : ¬ g < cyclicSuccessor e := by
      change g.val < (cyclicSuccessor e).val → False
      rw [hsuccVal]
      omega
    have hRankF : complementaryEventRank e f = f.val := by
      unfold complementaryEventRank
      rw [hsuccVal]
      simp
    have hRankG : complementaryEventRank e g = g.val := by
      unfold complementaryEventRank
      rw [hsuccVal]
      simp
    rw [hRankF, hRankG]
    have hAVisitTrue : (cyclicSuccessor e ≤ f) = True := propext (iff_true_intro hAVisit)
    have hWBeforeAFalse : (g < cyclicSuccessor e) = False := propext (iff_false_intro hWBeforeA)
    rw [hAVisitTrue, hWBeforeAFalse]
    simp only [true_and, false_and, or_false, false_or, and_false]

end DirectGLSSW.MixedEdgeSupportOrder






