import PLMarkedRefinementPorts
import PLSubdivisionCycle
import FiniteListMultiplicity
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open Equiv MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {ι : Type*} (D : PLLinkDiagram) (mark : ι → Fin D.nArc)

theorem markedRefinement_isCycleOn (hp : D.continuation.IsCycleOn Set.univ) (l : List ι) :
    (markedRefinementState D mark l).1.continuation.IsCycleOn Set.univ := by
  induction l with
  | nil => exact hp
  | cons sel l ih =>
    exact subdivideArc_isCycleOn (markedRefinementState D mark l).1
      ((markedRefinementState D mark l).2 sel) (1/2:ℝ) (by norm_num) (by norm_num) ih

theorem markedRefinement_next [Fintype ι] (hinj : Function.Injective mark) (l : List ι) :
    next (markedRefinementState D mark l).1.continuation (markedRefinementState D mark l).2
      (markedRefinement_injective D mark hinj l) = next D.continuation mark hinj := by
  ext j
  exact markedRefinement_nextLabel D mark hinj l j

/-- Any prescribed finite nonnegative additions are realized by actual physical subdivisions. -/
theorem exists_prescribed_markedRefinement [Fintype ι] (hinj : Function.Injective mark)
    (extra : ι → ℕ) :
    ∃ l : List ι, ∀ m : ι,
      gapLength (markedRefinementState D mark l).1.continuation (markedRefinementState D mark l).2 m =
        gapLength D.continuation mark m + extra m := by
  obtain ⟨l,hl⟩ := exists_list_count (fun i=>extra ((next D.continuation mark hinj).symm i))
  refine ⟨l,fun m=>?_⟩
  rw [markedRefinement_gapLength D mark hinj l m,hl]
  change _ + extra ((next D.continuation mark hinj).symm (next D.continuation mark hinj m)) = _
  rw [Equiv.symm_apply_apply]

/-- Symmetric target lengths avoid any comparison between the two original gap lengths. -/
theorem exists_common_markedRefinements [Fintype ι] (hinj : Function.Injective mark)
    (E : PLLinkDiagram) (mark' : ι → Fin E.nArc) (hinj' : Function.Injective mark') :
    ∃ l l' : List ι, ∀ m : ι,
      gapLength (markedRefinementState D mark l).1.continuation (markedRefinementState D mark l).2 m =
        gapLength D.continuation mark m + gapLength E.continuation mark' m ∧
      gapLength (markedRefinementState E mark' l').1.continuation (markedRefinementState E mark' l').2 m =
        gapLength D.continuation mark m + gapLength E.continuation mark' m := by
  obtain ⟨l,hl⟩ := exists_prescribed_markedRefinement D mark hinj (gapLength E.continuation mark')
  obtain ⟨l',hl'⟩ := exists_prescribed_markedRefinement E mark' hinj' (gapLength D.continuation mark)
  refine ⟨l,l',fun m=>⟨hl m,?_⟩⟩
  exact (hl' m).trans (Nat.add_comm _ _)

end DirectGLSSW.HOMFLY.ArcSubdivision
