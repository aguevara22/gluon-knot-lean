import SM.ContactHalfSizes
import SM.CyclicRangeIndices

/-! The two actual source vertex maps, with the shared contact vertex first.
The second map is a rotation of a consecutive range, not an arbitrary list. -/

namespace SM

variable {n : ℕ} [NeZero n]

instance firstHalfSize_neZero (M a : ZMod n) : NeZero (firstHalfSize M a) :=
  ⟨Nat.succ_ne_zero _⟩

instance secondHalfSize_neZero (M a : ZMod n) : NeZero (secondHalfSize M a) := by
  have hd : contactDistance M a < n := ZMod.val_lt _
  exact ⟨by dsimp [secondHalfSize]; omega⟩

def firstHalfIndex (M a : ZMod n) (i : ZMod (firstHalfSize M a)) : ZMod n :=
  cyclicRangeIndex M i

def secondHalfIndex (M a : ZMod n) (i : ZMod (secondHalfSize M a)) : ZMod n :=
  if i = 0 then M else cyclicRangeIndex a i

def secondHalfEdgeIndex (M a : ZMod n) (i : ZMod (secondHalfSize M a)) : ZMod n :=
  cyclicRangeIndex a i

theorem firstHalfSize_le (M a : ZMod n) : firstHalfSize M a ≤ n := by
  have hd : contactDistance M a < n := ZMod.val_lt _
  dsimp [firstHalfSize]
  omega

theorem secondHalfSize_le (M a : ZMod n) : secondHalfSize M a ≤ n := Nat.sub_le _ _

theorem secondHalfSize_cast (M a : ZMod n) : (secondHalfSize M a : ZMod n) = M - a := by
  have hd : contactDistance M a ≤ n := (ZMod.val_lt _).le
  rw [secondHalfSize, Nat.cast_sub hd, ZMod.natCast_self, contactDistance_cast]
  ring

theorem firstHalfIndex_injective (M a : ZMod n) : Function.Injective (firstHalfIndex M a) :=
  cyclicRangeIndex_injective (firstHalfSize_le M a) M

theorem firstHalfIndex_zero (M a : ZMod n) : firstHalfIndex M a 0 = M :=
  cyclicRangeIndex_zero M

theorem firstHalfIndex_last (M a : ZMod n) : firstHalfIndex M a (-1) = a := by
  rw [firstHalfIndex, cyclicRangeIndex_last, firstHalfSize, Nat.cast_add, Nat.cast_one,
    contactDistance_cast]
  ring

theorem firstHalfIndex_next (M a : ZMod n) {i : ZMod (firstHalfSize M a)} (hi : i ≠ -1) :
    firstHalfIndex M a (i + 1) = firstHalfIndex M a i + 1 := cyclicRangeIndex_next M hi

theorem secondHalfIndex_zero (M a : ZMod n) : secondHalfIndex M a 0 = M := by
  simp [secondHalfIndex]

theorem secondHalfIndex_nonzero (M a : ZMod n) {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    secondHalfIndex M a i = secondHalfEdgeIndex M a i := by
  simp only [secondHalfIndex, hi, ↓reduceIte, secondHalfEdgeIndex]

theorem secondHalfIndex_range (M a : ZMod n) (i : ZMod (secondHalfSize M a)) :
    secondHalfIndex M a i = cyclicRangeIndex (a + 1) (i - 1) := by
  by_cases hi : i = 0
  · subst i
    rw [secondHalfIndex_zero, zero_sub, cyclicRangeIndex_last, secondHalfSize_cast]
    ring
  · rw [secondHalfIndex_nonzero M a hi]
    have hp : i - 1 ≠ -1 := by intro he; apply hi; linear_combination he
    have he := cyclicRangeIndex_next (a + 1) hp
    rw [sub_add_cancel] at he
    dsimp [secondHalfEdgeIndex, cyclicRangeIndex] at he ⊢
    linear_combination he

theorem secondHalfIndex_injective (M a : ZMod n) : Function.Injective (secondHalfIndex M a) := by
  intro i j he
  rw [secondHalfIndex_range, secondHalfIndex_range] at he
  exact sub_left_injective ((cyclicRangeIndex_injective (secondHalfSize_le M a) (a + 1)) he)

theorem secondHalfEdgeIndex_injective (M a : ZMod n) :
    Function.Injective (secondHalfEdgeIndex M a) :=
  cyclicRangeIndex_injective (secondHalfSize_le M a) a

theorem secondHalfEdgeIndex_zero (M a : ZMod n) : secondHalfEdgeIndex M a 0 = a :=
  cyclicRangeIndex_zero a

theorem secondHalfEdgeIndex_last (M a : ZMod n) : secondHalfEdgeIndex M a (-1) = M - 1 := by
  rw [secondHalfEdgeIndex, cyclicRangeIndex_last, secondHalfSize_cast]
  ring

theorem secondHalfIndex_one (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a) :
    secondHalfIndex M a 1 = a + 1 := by
  have hb := contactHalfSizes_bounds hn h
  haveI : Fact (1 < secondHalfSize M a) := ⟨by omega⟩
  rw [secondHalfIndex_nonzero M a one_ne_zero]
  simp only [secondHalfEdgeIndex, cyclicRangeIndex, ZMod.val_one, Nat.cast_one]

theorem secondHalfIndex_last (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a) :
    secondHalfIndex M a (-1) = M - 1 := by
  have hb := contactHalfSizes_bounds hn h
  haveI : Fact (1 < secondHalfSize M a) := ⟨by omega⟩
  rw [secondHalfIndex_nonzero M a (neg_ne_zero.mpr one_ne_zero), secondHalfEdgeIndex_last]

theorem secondHalfIndex_next (M a : ZMod n) {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    secondHalfIndex M a (i + 1) = secondHalfEdgeIndex M a i + 1 := by
  by_cases hl : i = -1
  · subst i
    rw [neg_add_cancel, secondHalfIndex_zero, secondHalfEdgeIndex_last]
    ring
  · have hi' : i + 1 ≠ 0 := fun he => hl (eq_neg_iff_add_eq_zero.mpr he)
    rw [secondHalfIndex_nonzero M a hi']
    exact cyclicRangeIndex_next a hl

end SM
