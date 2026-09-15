import SM.ContactHalfTuples
import Mathlib.Tactic

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/ContactRootPartition.body.lean (prototype ContactHalfRoots, kernel session 90785, receipt
ContactHalfRoots-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Exact representatives when the origin moves from M to a. Both sides
of the cut retain proved natural-subtraction and residue bounds. -/
theorem contact_relative_offset_val (M a g : ZMod n) :
    (g - a).val = if (g - M).val < contactDistance M a then
      (g - M).val + n - contactDistance M a else (g - M).val - contactDistance M a := by
  have hv := ZMod.val_lt (g - M)
  have hd := ZMod.val_lt (a - M)
  change contactDistance M a < n at hd
  by_cases h : (g - M).val < contactDistance M a
  · rw [if_pos h]
    have he : g - a = (((g - M).val + n - contactDistance M a : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
        ZMod.natCast_zmod_val, contactDistance_cast]
      ring
    rw [he, ZMod.val_natCast_of_lt (by omega)]
  · rw [if_neg h]
    have he : g - a = (((g - M).val - contactDistance M a : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val, contactDistance_cast]
      ring
    rw [he, ZMod.val_natCast_of_lt (by omega)]

/-- First-half inherited edges are exactly the original M-to-a arc,
excluding its new closing edge. -/
theorem firstHalf_inherited_root_iff (M a g : ZMod n) :
    (∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) ↔
      (g - M).val < contactDistance M a := by
  constructor
  · rintro ⟨i, hi, he⟩
    have hv := cyclicRangeIndex_offset (firstHalfSize_le M a) M i
    change (firstHalfIndex M a i - M).val = i.val at hv
    rw [he] at hv
    have hn := ZMod.val_lt (i + 1)
    rw [zmod_val_next_of_ne_last hi] at hn
    change i.val + 1 < contactDistance M a + 1 at hn
    omega
  · intro hg
    obtain ⟨i, hi⟩ := (firstHalfIndex_range M a g).mpr
      (by change (g - M).val < contactDistance M a + 1; omega)
    refine ⟨i, ?_, hi⟩
    intro he
    rw [he, firstHalfIndex_last] at hi
    subst g
    exact Nat.lt_irrefl _ hg

theorem secondHalfEdgeIndex_range_iff (M a g : ZMod n) :
    (∃ i : ZMod (secondHalfSize M a), secondHalfEdgeIndex M a i = g) ↔
      (g - a).val < secondHalfSize M a :=
  cyclicRangeIndex_range (secondHalfSize_le M a) a g

/-- Second-half inherited edges are exactly the remaining original arc,
excluding its new opening edge at child label zero. -/
theorem secondHalf_inherited_root_iff (M a g : ZMod n) :
    (∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) ↔
      contactDistance M a < (g - M).val := by
  constructor
  · rintro ⟨i, hi, he⟩
    have hv := cyclicRangeIndex_offset (secondHalfSize_le M a) a i
    change (secondHalfEdgeIndex M a i - a).val = i.val at hv
    rw [he, contact_relative_offset_val M a g] at hv
    have hb := i.val_lt
    change i.val < n - contactDistance M a at hb
    have hpos : 0 < i.val := by
      by_contra h
      have hz : i.val = 0 := by omega
      apply hi
      apply ZMod.val_injective (secondHalfSize M a)
      simpa only [ZMod.val_zero] using hz
    by_cases h : (g - M).val < contactDistance M a
    · rw [if_pos h] at hv
      have hd : contactDistance M a < n := ZMod.val_lt (a - M)
      omega
    · rw [if_neg h] at hv
      omega
  · intro hg
    have hv := ZMod.val_lt (g - M)
    have hr : (g - a).val < secondHalfSize M a := by
      rw [contact_relative_offset_val M a g, if_neg (by omega)]
      unfold secondHalfSize
      omega
    obtain ⟨i, hi⟩ := (secondHalfEdgeIndex_range_iff M a g).mpr hr
    refine ⟨i, ?_, hi⟩
    intro he
    rw [he, secondHalfEdgeIndex_zero] at hi
    subst g
    exact Nat.lt_irrefl _ hg

/-- Every original physical root belongs to one of the source's three
rows. Endpoint incident edges remain included in the two inherited arcs. -/
theorem contact_root_cases (M a g : ZMod n) :
    g = a ∨
      (∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) ∨
      (∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) := by
  rcases lt_trichotomy (g - M).val (contactDistance M a) with h | h | h
  · exact Or.inr (Or.inl ((firstHalf_inherited_root_iff M a g).mpr h))
  · left
    have hc := congrArg (fun x : ℕ => (x : ZMod n)) h
    rw [ZMod.natCast_zmod_val, contactDistance_cast] at hc
    exact sub_left_injective hc
  · exact Or.inr (Or.inr ((secondHalf_inherited_root_iff M a g).mpr h))

/-- The three source root rows are pairwise disjoint, including their
cyclic endpoints. This does not require geometric genericity. -/
theorem contact_root_cases_disjoint (M a g : ZMod n) :
    (g = a → ¬ ∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) ∧
    (g = a → ¬ ∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) ∧
    ((∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) →
      ¬ ∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) := by
  rw [firstHalf_inherited_root_iff, secondHalf_inherited_root_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro hg
    subst g
    exact Nat.lt_irrefl _
  · intro hg
    subst g
    exact Nat.lt_irrefl _
  · omega

end
end SM
