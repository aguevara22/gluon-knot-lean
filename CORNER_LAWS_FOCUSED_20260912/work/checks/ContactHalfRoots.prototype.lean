import SM.ContactHalfTuples
import Mathlib.Tactic

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






namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The physical half-root map: the contacted root splits into the two
new child edges; every other root is retained in exactly one half. -/
def contactHalfRoots (M a g : ZMod n) :
    ZMod (firstHalfSize M a) × ZMod (secondHalfSize M a) :=
  if g = a then (-1, 0)
  else if (g - M).val < contactDistance M a then (((g - M).val : ZMod (firstHalfSize M a)), 0)
  else (-1, ((g - a).val : ZMod (secondHalfSize M a)))

theorem contactHalfRoots_base (M a : ZMod n) : contactHalfRoots M a a = (-1, 0) := by
  simp [contactHalfRoots]

theorem contactHalfRoots_first (M a : ZMod n) {i : ZMod (firstHalfSize M a)} (hi : i ≠ -1) :
    contactHalfRoots M a (firstHalfIndex M a i) = (i, 0) := by
  have hga : firstHalfIndex M a i ≠ a := by
    intro he
    exact hi (firstHalfIndex_injective M a (he.trans (firstHalfIndex_last M a).symm))
  have hf := (firstHalf_inherited_root_iff M a (firstHalfIndex M a i)).mp ⟨i, hi, rfl⟩
  have hv := cyclicRangeIndex_offset (firstHalfSize_le M a) M i
  change (firstHalfIndex M a i - M).val = i.val at hv
  rw [contactHalfRoots, if_neg hga, if_pos hf]
  simp only [hv, ZMod.natCast_zmod_val]

theorem contactHalfRoots_second (M a : ZMod n) {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    contactHalfRoots M a (secondHalfEdgeIndex M a i) = (-1, i) := by
  have hga : secondHalfEdgeIndex M a i ≠ a := by
    intro he
    exact hi (secondHalfEdgeIndex_injective M a (he.trans (secondHalfEdgeIndex_zero M a).symm))
  have hs := (secondHalf_inherited_root_iff M a (secondHalfEdgeIndex M a i)).mp ⟨i, hi, rfl⟩
  have hv := cyclicRangeIndex_offset (secondHalfSize_le M a) a i
  change (secondHalfEdgeIndex M a i - a).val = i.val at hv
  rw [contactHalfRoots, if_neg hga, if_neg (by omega)]
  simp only [hv, ZMod.natCast_zmod_val]

/-- The typed map realizes the source's three exhaustive root rows,
including an actual inherited label whenever a child retains the old root. -/
theorem contactHalfRoots_spec (M a g : ZMod n) :
    (g = a ∧ contactHalfRoots M a g = (-1, 0)) ∨
    (∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g ∧
      contactHalfRoots M a g = (i, 0)) ∨
    (∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g ∧
      contactHalfRoots M a g = (-1, i)) := by
  rcases contact_root_cases M a g with hg | ⟨i, hi, hg⟩ | ⟨i, hi, hg⟩
  · subst g
    exact Or.inl ⟨rfl, contactHalfRoots_base M a⟩
  · subst g
    exact Or.inr (Or.inl ⟨i, hi, rfl, contactHalfRoots_first M a hi⟩)
  · subst g
    exact Or.inr (Or.inr ⟨i, hi, rfl, contactHalfRoots_second M a hi⟩)

/-- Both directed endpoint pairs of the mapped child roots are the actual
source edges. Equality of vectors alone would not establish these endpoints.
The base case produces a-to-M and M-to-a+1; inherited roots keep both endpoints. -/
theorem contactHalfRoots_vertices (hn : 3 ≤ n) {M a : ZMod n} (hc : ContactSeparated M a)
    (P : LabelledTuple n) (g : ZMod n) :
    let r := contactHalfRoots M a g
    ((firstHalf P M a r.1, firstHalf P M a (r.1 + 1)) =
      if (g - M).val < contactDistance M a then (P g, P (g + 1)) else (P a, P M)) ∧
    ((secondHalf P M a r.2, secondHalf P M a (r.2 + 1)) =
      if contactDistance M a < (g - M).val then (P g, P (g + 1)) else (P M, P (a + 1))) := by
  dsimp only
  rcases contact_root_cases M a g with hg | ⟨i, hi, hg⟩ | ⟨i, hi, hg⟩
  · subst g
    rw [contactHalfRoots_base]
    simp only [Prod.fst, Prod.snd, contactDistance, Nat.lt_irrefl, ite_false,
      neg_add_cancel, zero_add, firstHalf_last, firstHalf_zero, secondHalf_zero,
      secondHalf_one hn hc, and_self]
  · subst g
    have hf := (firstHalf_inherited_root_iff M a (firstHalfIndex M a i)).mp ⟨i, hi, rfl⟩
    have hs : ¬ contactDistance M a < (firstHalfIndex M a i - M).val := by omega
    rw [contactHalfRoots_first M a hi]
    simp only [Prod.fst, Prod.snd, if_pos hf, if_neg hs, zero_add,
      secondHalf_zero, secondHalf_one hn hc, firstHalf, firstHalfIndex_next M a hi, and_self]
  · subst g
    have hs := (secondHalf_inherited_root_iff M a (secondHalfEdgeIndex M a i)).mp ⟨i, hi, rfl⟩
    have hf : ¬ (secondHalfEdgeIndex M a i - M).val < contactDistance M a := by omega
    rw [contactHalfRoots_second M a hi]
    simp only [Prod.fst, Prod.snd, if_neg hf, if_pos hs, neg_add_cancel,
      firstHalf_last, firstHalf_zero, secondHalf, secondHalfIndex_nonzero M a hi,
      secondHalfIndex_next M a hi, and_self]

end
end SM

#check SM.contactHalfRoots
#print axioms SM.contactHalfRoots

#check SM.contactHalfRoots_base
#print axioms SM.contactHalfRoots_base

#check SM.contactHalfRoots_first
#print axioms SM.contactHalfRoots_first

#check SM.contactHalfRoots_second
#print axioms SM.contactHalfRoots_second

#check SM.contactHalfRoots_spec
#print axioms SM.contactHalfRoots_spec

#check SM.contactHalfRoots_vertices
#print axioms SM.contactHalfRoots_vertices
