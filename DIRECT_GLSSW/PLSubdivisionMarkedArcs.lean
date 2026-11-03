import PLArcSubdivisionContraction
import MarkedCycleNext
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open Equiv
attribute [local instance] Classical.propDecidable
variable (D : PLLinkDiagram) (e : Fin D.nArc)

/-- The terminal half represents an old marked incoming arc after subdivision. -/
def markedArcLift (a : Fin D.nArc) : Fin (D.nArc+1) :=
  if a=e then Fin.last D.nArc else a.castSucc

theorem collapse_markedArcLift (a : Fin D.nArc) :
    collapse D e (markedArcLift D e a) = a := by
  by_cases h : a=e
  · subst a
    simp only [markedArcLift,if_pos rfl,ite_true,collapse_new]
  · simp only [markedArcLift,if_neg h,collapse_old]

theorem markedArcLift_injective : Function.Injective (markedArcLift D e) := by
  intro a b h
  have he := congrArg (collapse D e) h
  simpa only [collapse_markedArcLift] using he

theorem markedArcLift_incoming (c : Fin D.nCrossing) (i : Fin 2) :
    markedArcLift D e (D.incoming c i) = incoming D e c i := rfl

theorem continuation_markedArcLift (a : Fin D.nArc) :
    continuation D e (markedArcLift D e a) = (D.continuation a).castSucc := by
  by_cases h : a=e
  · subst a
    simp only [markedArcLift,if_pos rfl,ite_true,continuation,Perm.mul_apply,
      Equiv.swap_apply_right,liftedContinuation_old]
  · have hn : a.castSucc ≠ Fin.last D.nArc := Fin.ne_of_lt (Fin.castSucc_lt_last a)
    have he : a.castSucc ≠ e.castSucc := fun he=>h (Fin.ext (congrArg (fun x : Fin (D.nArc+1)=>x.val) he))
    simp only [markedArcLift,if_neg h,continuation,Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne he hn,liftedContinuation_old]

theorem continuation_markedArcLift_of_next_ne (a : Fin D.nArc) (ha : D.continuation a ≠ e) :
    continuation D e (markedArcLift D e a) = markedArcLift D e (D.continuation a) := by
  rw [continuation_markedArcLift]
  exact (if_neg ha).symm

end DirectGLSSW.HOMFLY.ArcSubdivision
