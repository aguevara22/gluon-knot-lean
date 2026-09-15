import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import Mathlib.Tactic
import SM.BoundaryTripleSupports
import SM.CanonicalTripleSigns
import SM.SoftInsertionIndices

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftInsertionSuccessors.body.lean (prototype SoftInsertionTuple, kernel session 84277, receipt
SoftInsertionTuple-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem soft_physical_label_next (a : Fin n) (h : a.val + 1 < n) :
    boundaryIndex 0 (⟨a.val + 1, h⟩ : Fin n) = boundaryIndex 0 a + 1 := by
  simp only [canonical_label, Nat.cast_add, Nat.cast_one]

theorem soft_physical_last_label (a : Fin n) (h : a.val + 1 = n) :
    boundaryIndex 0 a = 0 := by
  rw [canonical_label, h, ZMod.natCast_self]

/-- Every old cyclic successor pair remains consecutive except the one
pair split by the actual soft vertex. This includes the physical wrap. -/
theorem softOldIndex_next (j k : ZMod n) (hk : k ≠ j) :
    softOldIndex j (k + 1) = softOldIndex j k + 1 := by
  let a := canonicalPosition k
  have ha : boundaryIndex 0 a = k := boundaryIndex_canonicalPosition k
  have hne : a.val ≠ (canonicalPosition j).val := by
    intro h
    apply hk
    exact canonicalPosition_injective (Fin.ext h)
  by_cases hw : a.val + 1 < n
  · let b : Fin n := ⟨a.val + 1, hw⟩
    have hb : boundaryIndex 0 b = k + 1 := (soft_physical_label_next a hw).trans (congrArg (· + 1) ha)
    calc
      softOldIndex j (k + 1) = softOldIndex j (boundaryIndex 0 b) := congrArg (softOldIndex j) hb.symm
      _ = softOldIndex j (boundaryIndex 0 a) + 1 := by
        rw [softOldIndex_physical, softOldIndex_physical]
        by_cases hlt : a.val < (canonicalPosition j).val
        · have hb_le : b.val ≤ (canonicalPosition j).val := by dsimp [b]; omega
          rw [if_pos hb_le, if_pos (le_of_lt hlt)]
          simp only [b, Nat.cast_add, Nat.cast_one]
        · have hgt : (canonicalPosition j).val < a.val := by omega
          have hb_gt : ¬ b.val ≤ (canonicalPosition j).val := by dsimp [b]; omega
          rw [if_neg hb_gt, if_neg (not_le_of_gt hgt)]
          simp only [b, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
      _ = softOldIndex j k + 1 := by rw [ha]
  · have hn : a.val + 1 = n := by have := a.isLt; omega
    have hk0 : k = 0 := ha.symm.trans (soft_physical_last_label a hn)
    let first : Fin n := ⟨0, NeZero.pos n⟩
    have hf : boundaryIndex 0 first = 1 := by simp [canonical_label, first]
    have hgt : (canonicalPosition j).val < a.val := by
      have := (canonicalPosition j).isLt
      omega
    calc
      softOldIndex j (k + 1) = softOldIndex j (boundaryIndex 0 first) := by rw [hk0, zero_add, hf]
      _ = 1 := by
        rw [softOldIndex_physical, if_pos (show first.val ≤ (canonicalPosition j).val from Nat.zero_le _)]
        simp [first]
      _ = softOldIndex j (boundaryIndex 0 a) + 1 := by
        rw [softOldIndex_physical, if_neg (not_le_of_gt hgt)]
        have he : a.val + 2 = n + 1 := by omega
        rw [he, ZMod.natCast_self, zero_add]
      _ = softOldIndex j k + 1 := by rw [ha]

/-- The newborn's outgoing edge returns to the original successor of j,
including insertion at the last physical label. -/
theorem softNewIndex_next (j : ZMod n) :
    softNewIndex j + 1 = softOldIndex j (j + 1) := by
  let a := canonicalPosition j
  have ha : boundaryIndex 0 a = j := boundaryIndex_canonicalPosition j
  by_cases hw : a.val + 1 < n
  · let b : Fin n := ⟨a.val + 1, hw⟩
    have hb : boundaryIndex 0 b = j + 1 := (soft_physical_label_next a hw).trans (congrArg (· + 1) ha)
    rw [← hb, softOldIndex_physical, softNewIndex_physical]
    have hgt : ¬ b.val ≤ (canonicalPosition j).val := by dsimp [b, a]; omega
    rw [if_neg hgt]
    simp only [b, a, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  · have hn : a.val + 1 = n := by have := a.isLt; omega
    have hj0 : j = 0 := ha.symm.trans (soft_physical_last_label a hn)
    let first : Fin n := ⟨0, NeZero.pos n⟩
    have hf : boundaryIndex 0 first = 1 := by simp [canonical_label, first]
    calc
      softNewIndex j + 1 = 1 := by
        rw [softNewIndex_physical]
        have he : (canonicalPosition j).val + 2 = n + 1 := by change a.val + 2 = n + 1; omega
        rw [he, ZMod.natCast_self, zero_add]
      _ = softOldIndex j (boundaryIndex 0 first) := by
        rw [softOldIndex_physical, if_pos (show first.val ≤ (canonicalPosition j).val from Nat.zero_le _)]
        simp [first]
      _ = softOldIndex j (j + 1) := by rw [hj0, zero_add, hf]

end
end SM
