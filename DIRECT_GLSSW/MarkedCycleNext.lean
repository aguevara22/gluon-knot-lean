import MarkedCyclePartition
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] (p : Perm α) (mark : ι → α)

theorem gapMap_last (hinj : Function.Injective mark) (m : ι) :
    gapMap p mark ⟨m,⟨gapLength p mark m - 1,by have := gapLength_pos p mark m; omega⟩⟩ =
      mark (nextLabel p mark hinj m) := by
  change (p ^ (gapLength p mark m - 1 + 1)) (mark m) = _
  rw [Nat.sub_add_cancel (gapLength_pos p mark m)]
  exact nextLabel_spec p mark hinj m

theorem nextLabel_injective (hinj : Function.Injective mark) :
    Function.Injective (nextLabel p mark hinj) := by
  intro m j h
  have hg : gapMap p mark ⟨m,⟨gapLength p mark m - 1,by have := gapLength_pos p mark m; omega⟩⟩ =
      gapMap p mark ⟨j,⟨gapLength p mark j - 1,by have := gapLength_pos p mark j; omega⟩⟩ := by
    rw [gapMap_last p mark hinj m,gapMap_last p mark hinj j,h]
  exact congrArg Sigma.fst (gapMap_injective p mark hinj hg)

/-- The next marked point is an actual permutation, derived from the gap partition. -/
def next [Fintype ι] (hinj : Function.Injective mark) : Perm ι :=
  Equiv.ofBijective (nextLabel p mark hinj)
    ⟨nextLabel_injective p mark hinj,Finite.surjective_of_injective (nextLabel_injective p mark hinj)⟩

theorem next_apply [Fintype ι] (hinj : Function.Injective mark) (m : ι) :
    next p mark hinj m = nextLabel p mark hinj m := rfl

theorem gapMap_first (m : ι) :
    gapMap p mark ⟨m,⟨0,gapLength_pos p mark m⟩⟩ = p (mark m) := by
  simp only [gapMap,zero_add,pow_one]

theorem gapMap_inner (m : ι) (k : Fin (gapLength p mark m))
    (hk : k.val+1 < gapLength p mark m) :
    gapMap p mark ⟨m,⟨k.val+1,hk⟩⟩ = p (gapMap p mark ⟨m,k⟩) := by
  change (p ^ (k.val+1+1)) (mark m) = p ((p ^ (k.val+1)) (mark m))
  rw [pow_succ']
  rfl

theorem gapMap_continuation_last [Fintype ι] (hinj : Function.Injective mark) (m : ι) :
    p (gapMap p mark ⟨m,⟨gapLength p mark m - 1,by have := gapLength_pos p mark m; omega⟩⟩) =
      gapMap p mark ⟨next p mark hinj m,⟨0,gapLength_pos p mark _⟩⟩ := by
  rw [gapMap_last p mark hinj m,gapMap_first]
  rfl

end DirectGLSSW.MarkedCycleGaps
