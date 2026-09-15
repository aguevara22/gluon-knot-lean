import SM.ThreeEdgeCrossingArc

/-! The closed short arc includes its two crossing endpoints and exactly
the same two polygon vertices as the corresponding open arc. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {f : ZMod n}

theorem eq_visitPosition_iff (hn : 3 ≤ n) (hP : G1 P) (v : Visit P) (x : TraversalPoint n) :
    x = visitPosition hn hP v ↔ x.1 = v.2.val ∧ x.2.val = visitParameter v := by
  constructor
  · intro he; subst x; exact ⟨rfl, rfl⟩
  · rintro ⟨hi, ht⟩
    exact Prod.ext hi (Subtype.ext ht)

theorem twoStepClosedArc_iff (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (x : TraversalPoint n) :
    twoStepClosedArc hn hP h x ↔
      (x.1 = f ∧ visitParameter (twoStepFirstVisit h) ≤ x.2.val) ∨
      x.1 = f + 1 ∨ (x.1 = f + 2 ∧ x.2.val ≤ visitParameter (twoStepLastVisit h)) := by
  rw [twoStepClosedArc, eq_visitPosition_iff, eq_visitPosition_iff, twoStepOpenArc_iff]
  constructor
  · rintro (⟨hf, hs⟩ | ha | ⟨hg, ht⟩)
    · exact Or.inl ⟨hf, hs.ge⟩
    · rcases ha with ⟨hf, hs⟩ | hm | ⟨hg, ht⟩
      · exact Or.inl ⟨hf, hs.le⟩
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr ⟨hg, ht.le⟩)
    · exact Or.inr (Or.inr ⟨hg, ht.le⟩)
  · rintro (⟨hf, hs⟩ | hm | ⟨hg, ht⟩)
    · rcases hs.eq_or_lt with he | he
      · exact Or.inl ⟨hf, he.symm⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hf, he⟩))
    · exact Or.inr (Or.inl (Or.inr (Or.inl hm)))
    · rcases ht.eq_or_lt with he | he
      · exact Or.inr (Or.inr ⟨hg, he⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hg, he⟩)))

theorem twoStepClosedArc_vertex_iff (hn : 3 ≤ n) (hP : G1 P) (h : IsCrossing P {f, f + 2})
    (i : ZMod n) :
    twoStepClosedArc hn hP h (traversalVertex i) ↔ i = f + 1 ∨ i = f + 2 := by
  rw [twoStepClosedArc_iff]
  have hs := (visitPosition_interior hn hP (twoStepFirstVisit h)).1
  have ht := (visitPosition_interior hn hP (twoStepLastVisit h)).1
  simp only [traversalVertex, not_le.mpr hs, and_false, false_or, ht.le, and_true]

end SM
