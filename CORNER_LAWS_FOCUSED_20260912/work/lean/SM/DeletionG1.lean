import SM.DeletedTuple
import SM.TurnSupports

/-! Every triple of retained vertices avoids the unique central zero triple,
because the latter contains the deleted vertex. No G1 premise on the parent. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

theorem g1_deleteVertex (hz : pointZeroTriples P = {turnSupport j}) :
    G1 (deleteVertex P j) := by
  intro a b c hab hbc hac
  change chi P (deletionIndex j a) (deletionIndex j b) (deletionIndex j c) ≠ 0
  apply chi_nonzero_outside_singleton hz
  · exact fun he => hab (deletionIndex_injective j he)
  · exact fun he => hbc (deletionIndex_injective j he)
  · exact fun he => hac (deletionIndex_injective j he)
  · intro he
    have hj : j ∈ ({deletionIndex j a, deletionIndex j b, deletionIndex j c} : Finset _) := by
      rw [he]
      simp [turnSupport]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj | hj
    · exact deletionIndex_ne_deleted j a hj.symm
    · exact deletionIndex_ne_deleted j b hj.symm
    · exact deletionIndex_ne_deleted j c hj.symm

end SM
