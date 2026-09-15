import SM.InsertionIndices

/-! The entire new cyclic index set consists of the injectively retained old
indices and the single inserted index. The sum identity has no geometric input. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem insertion_univ : (Finset.univ : Finset (ZMod (n + 1))) =
    insert (insertedIndex n) (Finset.univ.image (insertIndex (n := n))) := by
  classical
  ext j
  constructor
  · intro _
    rcases insertion_indices_exhaust j with hj | ⟨i, hi⟩
    · exact Finset.mem_insert.mpr (Or.inl hj)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩))
  · intro _
    exact Finset.mem_univ j

theorem insertedIndex_not_mem_old_image : insertedIndex n ∉
    Finset.univ.image (insertIndex (n := n)) := by
  classical
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact insertIndex_ne_inserted i hi

theorem sum_insertion_indices {A : Type*} [AddCommMonoid A] (f : ZMod (n + 1) → A) :
    (∑ j : ZMod (n + 1), f j) = (∑ i : ZMod n, f (insertIndex i)) + f (insertedIndex n) := by
  classical
  rw [insertion_univ, Finset.sum_insert insertedIndex_not_mem_old_image,
    Finset.sum_image (fun _ _ _ _ he => insertIndex_injective he), add_comm]

end SM
