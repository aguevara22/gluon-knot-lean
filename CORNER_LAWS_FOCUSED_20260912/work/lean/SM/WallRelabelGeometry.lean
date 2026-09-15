import SM.NamedWallSides

/-! Actual central supports and geometric quantities under cyclic shifts.
The inverse support translation makes singleton-set equations equivalent. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem wall_sub_add_cancel_right (i r c : ZMod n) : (i - r + c) + r = i + c := by ring

theorem wall_sub_sub_cancel_right (i r c : ZMod n) : (i - r - c) + r = i - c := by ring

theorem wall_translateSupport_injective (r : ZMod n) :
    Function.Injective (translateSupport r) := by
  intro S T he
  have hh := congrArg (translateSupport (-r)) he
  have hS : translateSupport (-r) (translateSupport r S) = S := by
    simpa only [neg_neg] using translateSupport_cancel (-r) S
  have hT : translateSupport (-r) (translateSupport r T) = T := by
    simpa only [neg_neg] using translateSupport_cancel (-r) T
  exact hS.symm.trans (hh.trans hT)

theorem translateSupport_turn (r j : ZMod n) :
    translateSupport (-r) (turnSupport j) = turnSupport (j - r) := by
  simp [translateSupport, turnSupport, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem translateSupport_contact (r M a : ZMod n) :
    translateSupport (-r) (contactSupport M a) = contactSupport (M - r) (a - r) := by
  simp [translateSupport, contactSupport, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem translateSupport_three (r i j k : ZMod n) :
    translateSupport (-r) {i, j, k} = {i - r, j - r, k - r} := by
  simp [translateSupport, sub_eq_add_neg]

theorem contactSeparated_sub (r M a : ZMod n) :
    ContactSeparated (M - r) (a - r) ↔ ContactSeparated M a := by
  have he (c : ZMod n) : a - r + c = (a + c) - r := by ring
  simp [ContactSeparated, show a - r - 1 = (a - 1) - r from by ring, he]

theorem noConsecutive_translate (r : ZMod n) (S : Finset (ZMod n)) :
    NoConsecutive (translateSupport r S) ↔ NoConsecutive S := by
  constructor
  · intro h i hi hn
    exact h (i + r) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (Finset.mem_image.mpr ⟨i + 1, hn, by ring⟩)
  · intro h i hi hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hn
    have hk' : k = j + 1 := by linear_combination he
    exact h j hj (hk' ▸ hk)

theorem edgeParameter_shift (r : ZMod n) (P : LabelledTuple n) (i j : ZMod n) :
    edgeParameter (shift r P) i j = edgeParameter P (i + r) (j + r) := by
  simp only [edgeParameter, edge_shift, shift]

namespace WallGerm

variable (g : WallGerm n)

theorem pointZeros_relabel_singleton (r : ZMod n) (S : Finset (ZMod n)) :
    (g.relabel r).pointZeros = {translateSupport (-r) S} ↔ g.pointZeros = {S} := by
  rw [g.pointZeros_relabel, ← Finset.image_singleton]
  exact Finset.image_inj (wall_translateSupport_injective (-r))

theorem concurrences_relabel_singleton (r : ZMod n) (S : Finset (ZMod n)) :
    (g.relabel r).concurrences = {translateSupport (-r) S} ↔ g.concurrences = {S} := by
  rw [g.concurrences_relabel, ← Finset.image_singleton]
  exact Finset.image_inj (wall_translateSupport_injective (-r))

theorem pointZeros_relabel_empty (r : ZMod n) :
    (g.relabel r).pointZeros = ∅ ↔ g.pointZeros = ∅ := by
  rw [g.pointZeros_relabel, Finset.image_eq_empty]

theorem concurrences_relabel_empty (r : ZMod n) :
    (g.relabel r).concurrences = ∅ ↔ g.concurrences = ∅ := by
  rw [g.concurrences_relabel, Finset.image_eq_empty]

end WallGerm
end SM
