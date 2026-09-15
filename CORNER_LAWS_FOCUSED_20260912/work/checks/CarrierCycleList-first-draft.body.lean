namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The constructed actual cyclic successor is exactly the permutation formed
from the complete sorted mark list, on every actual mark. -/
theorem markSuccessor_eq_formPerm (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) : markSuccessor hn hP = (markList hn hP).formPerm := by
  classical
  ext a
  change (markList hn hP).next a (mem_markList hn hP a) = _
  exact (List.formPerm_apply_mem_eq_next (markList_nodup hn hP) a
    (mem_markList hn hP a)).symm

/-- An actual mark can be made the first entry by rotating the complete list.
The rotation is constructed by splitting at its actual occurrence. -/
theorem markList_rotate_start (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) :
    ∃ k : ℕ, ∃ T : List (Mark P), (markList hn hP).rotate k = a :: T := by
  obtain ⟨L, R, he⟩ := List.mem_iff_append.mp (mem_markList hn hP a)
  refine ⟨L.length, R ++ L, ?_⟩
  rw [he, List.rotate_append_length_eq, List.cons_append]

/-- For any distinct actual marks, the complete marked circle has the literal
split-list presentation used by the source. Either intervening list may be empty. -/
theorem markList_rotate_split (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a b : Mark P) (hab : a ≠ b) :
    ∃ k : ℕ, ∃ A B : List (Mark P),
      (markList hn hP).rotate k = a :: (A ++ b :: B) := by
  obtain ⟨k, T, hrot⟩ := markList_rotate_start hn hP a
  have hb : b ∈ a :: T := hrot ▸ (List.mem_rotate.mpr (mem_markList hn hP b))
  have hbT : b ∈ T := (List.mem_cons.mp hb).resolve_left hab.symm
  obtain ⟨A, B, hT⟩ := List.mem_iff_append.mp hbT
  exact ⟨k, A, B, hT ▸ hrot⟩

/-- The actual original successor admits the source's duplicate-free split-list
presentation for arbitrary distinct actual marks. Rotation retains every vertex
and crossing visit, so no supplied representation or current-carrier premise enters. -/
theorem markSuccessor_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a b : Mark P) (hab : a ≠ b) :
    ∃ A B : List (Mark P),
      (a :: (A ++ b :: B)).Nodup ∧
      (a :: (A ++ b :: B)).formPerm = markSuccessor hn hP ∧
      ∀ m : Mark P, m ∈ a :: (A ++ b :: B) := by
  classical
  obtain ⟨k, A, B, hrot⟩ := markList_rotate_split hn hP a b hab
  refine ⟨A, B, ?_, ?_, ?_⟩
  · rw [← hrot]
    exact List.nodup_rotate.mpr (markList_nodup hn hP)
  · rw [← hrot, List.formPerm_rotate _ (markList_nodup hn hP) k]
    exact (markSuccessor_eq_formPerm hn hP).symm
  · intro m
    rw [← hrot]
    exact List.mem_rotate.mpr (mem_markList hn hP m)

end
end SM.Carrier
