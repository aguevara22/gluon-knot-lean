import MarkedCycleCoordinates
import MarkedGapSuccessor
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Fintype ι] [Nonempty ι]
    (p : Perm α) (mark : ι → α) (hp : p.IsCycleOn Set.univ) (hinj : Function.Injective mark)

/-- Exact conjugacy between the derived gap permutation and physical continuation. -/
theorem gapEquiv_successor (x : Σ m : ι, Fin (gapLength p mark m)) :
    gapEquiv p mark hp hinj
      (gapSuccessor (gapLength p mark) (gapLength_pos p mark) (next p mark hinj) x) =
      p (gapEquiv p mark hp hinj x) := by
  obtain ⟨m,k⟩ := x
  by_cases hk : k.val + 1 < gapLength p mark m
  · rw [gapSuccessor_inner _ _ _ m k hk]
    exact gapEquiv_inner p mark hp hinj m k hk
  · have he : k = ⟨gapLength p mark m - 1,by have := gapLength_pos p mark m; omega⟩ :=
      by
        apply Fin.ext
        change k.val = gapLength p mark m - 1
        omega
    rw [he]
    rw [gapSuccessor_last]
    exact (gapEquiv_continuation_last p mark hp hinj m).symm

/-- Literal backward continuation, obtained from the same actual partition. -/
theorem gapEquiv_predecessor (x : Σ m : ι, Fin (gapLength p mark m)) :
    gapEquiv p mark hp hinj
      ((gapSuccessor (gapLength p mark) (gapLength_pos p mark) (next p mark hinj)).symm x) =
      p.symm (gapEquiv p mark hp hinj x) := by
  apply p.injective
  rw [Equiv.apply_symm_apply]
  rw [← gapEquiv_successor]
  rw [Equiv.apply_symm_apply]

end DirectGLSSW.MarkedCycleGaps
