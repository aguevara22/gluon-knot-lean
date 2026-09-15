import SM.TraversalArcs

/-! Exact short arcs on the actual half-open polygon traversal. Translation
to a cut at the first edge proves the description for all cyclic indices. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem traversalBetween_of_key_lt {p q r : TraversalPoint n}
    (hpr : traversalKey p < traversalKey r) :
    traversalBetween p q r ↔ traversalKey p < traversalKey q ∧ traversalKey q < traversalKey r := by
  constructor
  · rintro (h | h | h)
    · exact h
    · exact (lt_asymm hpr h.2).elim
    · exact (lt_asymm hpr h.1).elim
  · exact Or.inl

theorem traversalBetween_zero_two (hn : 3 ≤ n) (s t : Set.Ico (0 : ℝ) 1)
    (x : TraversalPoint n) :
    traversalBetween (0, s) x (2, t) ↔
      (x.1 = 0 ∧ s.val < x.2.val) ∨ x.1 = 1 ∨ (x.1 = 2 ∧ x.2.val < t.val) := by
  have hv1 : (1 : ZMod n).val = 1 := by simpa using (ZMod.val_natCast_of_lt (by omega : 1 < n))
  have hv2 : (2 : ZMod n).val = 2 := by simpa using (ZMod.val_natCast_of_lt (by omega : 2 < n))
  have hkp : traversalKey (n := n) (0, s) = s.val := by simp [traversalKey]
  have hkr : traversalKey (n := n) (2, t) = 2 + t.val := by simp [traversalKey, hv2]
  have hpr : traversalKey (n := n) (0, s) < traversalKey (n := n) (2, t) := by
    rw [hkp, hkr]; linarith [s.property.2, t.property.1]
  rw [traversalBetween_of_key_lt hpr, hkp, hkr]
  constructor
  · intro h
    have hv : (x.1.val : ℝ) < 3 := by
      dsimp [traversalKey] at h
      linarith [x.2.property.1, t.property.2]
    have hv' : x.1.val < 3 := by exact_mod_cast hv
    have hc : x.1.val = 0 ∨ x.1.val = 1 ∨ x.1.val = 2 := by omega
    rcases hc with hc | hc | hc
    · have hx : x.1 = 0 := ZMod.val_injective n (by simpa only [ZMod.val_zero] using hc)
      left
      refine ⟨hx, ?_⟩
      simpa only [traversalKey, hx, ZMod.val_zero, Nat.cast_zero, zero_add] using h.1
    · exact Or.inr (Or.inl (ZMod.val_injective n (hc.trans hv1.symm)))
    · have hx : x.1 = 2 := ZMod.val_injective n (hc.trans hv2.symm)
      right; right
      refine ⟨hx, ?_⟩
      simpa only [traversalKey, hx, hv2, Nat.cast_ofNat, add_lt_add_iff_left] using h.2
  · rintro (⟨hx, hp⟩ | hx | ⟨hx, hp⟩)
    · simp only [traversalKey, hx, ZMod.val_zero, Nat.cast_zero, zero_add]
      exact ⟨hp, by linarith [x.2.property.2, t.property.1]⟩
    · simp only [traversalKey, hx, hv1, Nat.cast_one]
      exact ⟨by linarith [s.property.2, x.2.property.1],
        by linarith [x.2.property.2, t.property.1]⟩
    · simp only [traversalKey, hx, hv2, Nat.cast_ofNat]
      exact ⟨by linarith [s.property.2, x.2.property.1], by linarith⟩

theorem traversalBetween_two_step (hn : 3 ≤ n) (f : ZMod n)
    (s t : Set.Ico (0 : ℝ) 1) (x : TraversalPoint n) :
    traversalBetween (f, s) x (f + 2, t) ↔
      (x.1 = f ∧ s.val < x.2.val) ∨ x.1 = f + 1 ∨ (x.1 = f + 2 ∧ x.2.val < t.val) := by
  rw [← traversalBetween_shift f]
  have hl : traversalShift f (f, s) = (0, s) := by simp [traversalShift]
  have hr : traversalShift f (f + 2, t) = (2, t) := by simp [traversalShift]
  rw [hl, hr, traversalBetween_zero_two hn]
  simp only [traversalShift, sub_eq_zero, sub_eq_iff_eq_add, zero_add, add_comm, add_zero]

def traversalVertex (i : ZMod n) : TraversalPoint n := (i, ⟨0, le_rfl, zero_lt_one⟩)

theorem traversalVertex_evaluation (P : LabelledTuple n) (i : ZMod n) :
    traversalEvaluation P (traversalVertex i) = P i := by
  simp [traversalEvaluation, traversalVertex, edgePoint]

theorem three_edge_arc_vertices (hn : 3 ≤ n) (f : ZMod n)
    (s t : Set.Ico (0 : ℝ) 1) (ht : 0 < t.val) (i : ZMod n) :
    traversalBetween (f, s) (traversalVertex i) (f + 2, t) ↔ i = f + 1 ∨ i = f + 2 := by
  rw [traversalBetween_two_step hn]
  simp only [traversalVertex]
  have hs : ¬ s.val < 0 := not_lt.mpr s.property.1
  simp only [hs, and_false, false_or, ht, and_true]

end SM
