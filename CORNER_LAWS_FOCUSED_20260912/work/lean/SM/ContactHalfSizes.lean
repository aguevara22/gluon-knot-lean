import SM.ContactIndices

/-! The exact sizes of the two source contact halves. The four source
excluded labels force both children to have between three and n-2 vertices. -/

namespace SM

variable {n : ℕ} [NeZero n]

def contactDistance (M a : ZMod n) : ℕ := (a - M).val

def firstHalfSize (M a : ZMod n) : ℕ := contactDistance M a + 1

def secondHalfSize (M a : ZMod n) : ℕ := n - contactDistance M a

theorem contactDistance_cast (M a : ZMod n) : (contactDistance M a : ZMod n) = a - M :=
  ZMod.natCast_zmod_val _

theorem contactDistance_bounds (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a) :
    2 ≤ contactDistance M a ∧ contactDistance M a ≤ n - 3 := by
  have hn5 := contactSeparated_size hn h
  have hd : contactDistance M a < n := ZMod.val_lt _
  have hzero : contactDistance M a ≠ 0 := by
    intro he
    have hh := contactDistance_cast M a
    rw [he, Nat.cast_zero] at hh
    exact h.2.1 (by linear_combination hh)
  have hone : contactDistance M a ≠ 1 := by
    intro he
    have hh := contactDistance_cast M a
    rw [he, Nat.cast_one] at hh
    exact h.1 (by linear_combination hh)
  have hlast : contactDistance M a ≠ n - 1 := by
    intro he
    have hh := contactDistance_cast M a
    rw [he, Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one] at hh
    exact h.2.2.1 (by linear_combination hh)
  have hprev : contactDistance M a ≠ n - 2 := by
    intro he
    have hh := contactDistance_cast M a
    rw [he, Nat.cast_sub (by omega : 2 ≤ n), ZMod.natCast_self, Nat.cast_ofNat] at hh
    exact h.2.2.2 (by linear_combination hh)
  omega

theorem contactHalfSizes_bounds (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a) :
    (3 ≤ firstHalfSize M a ∧ firstHalfSize M a ≤ n - 2) ∧
      (3 ≤ secondHalfSize M a ∧ secondHalfSize M a ≤ n - 2) := by
  have hd := contactDistance_bounds hn h
  have hn5 := contactSeparated_size hn h
  dsimp [firstHalfSize, secondHalfSize]
  omega

theorem contactHalfSizes_sum (M a : ZMod n) :
    firstHalfSize M a + secondHalfSize M a = n + 1 := by
  have hd : contactDistance M a < n := ZMod.val_lt _
  dsimp [firstHalfSize, secondHalfSize]
  omega

theorem contactDistance_relabel (M a r : ZMod n) :
    contactDistance (M - r) (a - r) = contactDistance M a := by
  unfold contactDistance
  congr 1
  ring

theorem contactHalfSizes_relabel (M a r : ZMod n) :
    firstHalfSize (M - r) (a - r) = firstHalfSize M a ∧
      secondHalfSize (M - r) (a - r) = secondHalfSize M a := by
  simp only [firstHalfSize, secondHalfSize, contactDistance_relabel, and_self]

end SM
