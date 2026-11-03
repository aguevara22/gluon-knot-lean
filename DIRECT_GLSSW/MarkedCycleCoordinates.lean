import MarkedCycleNext
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Fintype ι] [Nonempty ι]
    (p : Perm α) (mark : ι → α) (hp : p.IsCycleOn Set.univ) (hinj : Function.Injective mark)

include hp hinj in
/-- The literal positive chain lengths exhaust all arcs, with no unassigned arcs. -/
theorem sum_gapLength_eq_card :
    ∑ m : ι, gapLength p mark m = Fintype.card α := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using
    Fintype.card_congr (gapEquiv p mark hp hinj)

theorem gapEquiv_first (m : ι) :
    gapEquiv p mark hp hinj ⟨m,⟨0,gapLength_pos p mark m⟩⟩ = p (mark m) :=
  gapMap_first p mark m

theorem gapEquiv_last (m : ι) :
    gapEquiv p mark hp hinj ⟨m,⟨gapLength p mark m - 1,by have := gapLength_pos p mark m; omega⟩⟩ =
      mark (next p mark hinj m) := gapMap_last p mark hinj m

theorem gapEquiv_inner (m : ι) (k : Fin (gapLength p mark m))
    (hk : k.val+1 < gapLength p mark m) :
    gapEquiv p mark hp hinj ⟨m,⟨k.val+1,hk⟩⟩ = p (gapEquiv p mark hp hinj ⟨m,k⟩) :=
  gapMap_inner p mark m k hk

theorem gapEquiv_continuation_last (m : ι) :
    p (gapEquiv p mark hp hinj ⟨m,⟨gapLength p mark m - 1,by have := gapLength_pos p mark m; omega⟩⟩) =
      gapEquiv p mark hp hinj ⟨next p mark hinj m,⟨0,gapLength_pos p mark _⟩⟩ :=
  gapMap_continuation_last p mark hinj m

end DirectGLSSW.MarkedCycleGaps
