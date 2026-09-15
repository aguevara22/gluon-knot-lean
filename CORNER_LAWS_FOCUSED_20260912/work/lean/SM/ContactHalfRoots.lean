import SM.ContactHalfTuples
import Mathlib.Tactic
import SM.ContactRootPartition

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/ContactHalfRoots.body.lean (prototype ContactHalfRoots, kernel session 90785, receipt
ContactHalfRoots-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

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
