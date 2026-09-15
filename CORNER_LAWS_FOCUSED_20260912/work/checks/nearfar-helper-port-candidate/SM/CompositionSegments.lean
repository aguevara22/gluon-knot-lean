import SM.FiniteCompositions

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Every part lies in the original interval. -/
theorem part_bounds (π : IntervalComposition I) (k : Fin π.parts) :
    I.left ≤ (π.part k).left ∧ (π.part k).right ≤ I.right := by
  constructor
  · rw [← π.first]
    exact π.strict.monotone (Fin.zero_le k.castSucc)
  · rw [← π.last]
    exact π.strict.monotone (Fin.le_last k.succ)

/-- Earlier parts end no later than later parts begin. -/
theorem part_order (π : IntervalComposition I) {k l : Fin π.parts} (h : k < l) :
    (π.part k).right ≤ (π.part l).left := by
  apply π.strict.monotone
  change k.val + 1 ≤ l.val
  exact h

/-- Every point before the final endpoint belongs to a unique half-open part;
the proof chooses the largest cut whose position does not exceed that point. -/
theorem exists_halfOpen_part (π : IntervalComposition I) (x : Fin n)
    (hl : I.left ≤ x) (hr : x < I.right) :
    ∃ k : Fin π.parts, (π.part k).left ≤ x ∧ x < (π.part k).right := by
  classical
  let s := Finset.univ.filter (fun j : Fin (π.parts + 1) => π.cut j ≤ x)
  have hs : s.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [π.first] using hl⟩⟩
  let j := s.max' hs
  have hj : π.cut j ≤ x := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hjp : j.val < π.parts := by
    have hn : j ≠ Fin.last π.parts := by
      intro he
      rw [he, π.last] at hj
      exact (not_le_of_gt hr) hj
    have hjb := j.isLt
    have hne : j.val ≠ π.parts := by
      intro he
      exact hn (Fin.ext (by simpa using he))
    omega
  let k : Fin π.parts := ⟨j.val, hjp⟩
  have hk : k.castSucc = j := by apply Fin.ext; rfl
  refine ⟨k, ?_, ?_⟩
  · change π.cut k.castSucc ≤ x
    rw [hk]
    exact hj
  · change x < π.cut k.succ
    by_contra h
    have he : k.succ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
    have hh : k.succ ≤ j := Finset.le_max' s _ he
    change j.val + 1 ≤ j.val at hh
    omega

/-- Closed parts cover both interval endpoints as well as its interior. -/
theorem exists_closed_part (π : IntervalComposition I) (x : Fin n)
    (hl : I.left ≤ x) (hr : x ≤ I.right) :
    ∃ k : Fin π.parts, (π.part k).left ≤ x ∧ x ≤ (π.part k).right := by
  by_cases he : x = I.right
  · let k : Fin π.parts := ⟨π.parts - 1, by have := π.parts_pos; omega⟩
    have hk : k.succ = Fin.last π.parts := by
      apply Fin.ext
      change π.parts - 1 + 1 = π.parts
      have := π.parts_pos
      omega
    have hright : (π.part k).right = I.right := by
      change π.cut k.succ = I.right
      rw [hk, π.last]
    exact ⟨k, by rw [he, ← hright]; exact le_of_lt (π.part k).increasing,
      by rw [he, hright]⟩
  · obtain ⟨k, hk⟩ := π.exists_halfOpen_part x hl (lt_of_le_of_ne hr he)
    exact ⟨k, hk.1, le_of_lt hk.2⟩

/-- Distinct part interiors cannot overlap. Shared endpoints are allowed. -/
theorem part_interior_unique (π : IntervalComposition I) (x : Fin n)
    {k l : Fin π.parts} (hk : (π.part k).left < x ∧ x < (π.part k).right)
    (hl : (π.part l).left < x ∧ x < (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · have hle := π.part_order h
    exact False.elim ((not_lt_of_ge hle) (lt_trans hl.1 hk.2))
  · exact h
  · have hle := π.part_order h
    exact False.elim ((not_lt_of_ge hle) (lt_trans hk.1 hl.2))

end
end SM.IntervalComposition
