import MarkedSuffixRange
import HOMFLYVisitPositionSuccessor
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

theorem markedOrbitSize_pos (t : MarkedParentState) (a : Fin t.1.nArc) :
    0 < markedOrbitSize t a := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨markedOrbitRoot t a,rfl⟩⟩

theorem markedOrbitSize_eq (t : MarkedParentState) (a b : Fin t.1.nArc) :
    markedOrbitSize t a = markedOrbitSize t b := by
  unfold markedOrbitSize
  rw [markedOrbitRoot_eq t a b]

theorem markedOrbitArc_zero (t : MarkedParentState) (a : Fin t.1.nArc) :
    markedOrbitArc t a ⟨0,markedOrbitSize_pos t a⟩ = markedOrbitRoot t a :=
  orbitEnumeration_zero _ _

theorem markedOrbitRoot_visitPosition (t : MarkedParentState) (a : Fin t.1.nArc) :
    visitPosition t.2.1 (markedOrbitRoot t a) = 0 := by
  rw [← markedOrbitArc_zero t a,markedOrbitArc_visitPosition]

theorem markedOrbitArc_last_continuation (t : MarkedParentState) (a : Fin t.1.nArc) :
    t.1.continuation (markedOrbitArc t a ⟨markedOrbitSize t a-1,by have := markedOrbitSize_pos t a;omega⟩) =
      markedOrbitRoot t a := by
  let j : Fin (markedOrbitSize t a) := ⟨markedOrbitSize t a-1,by have := markedOrbitSize_pos t a;omega⟩
  have hz : cyclicSuccessorPerm (markedOrbitSize t a) j = ⟨0,markedOrbitSize_pos t a⟩ := by
    apply Fin.ext
    change ((markedOrbitSize t a-1)+1+0)%markedOrbitSize t a = 0
    have he : markedOrbitSize t a-1+1=markedOrbitSize t a := by have := markedOrbitSize_pos t a;omega
    rw [Nat.add_zero,he,Nat.mod_self]
  have hh := congrArg Subtype.val (orbitEnumeration_successor t.1.continuation (markedOrbitRoot t a) j)
  change markedOrbitArc t a (cyclicSuccessorPerm (markedOrbitSize t a) j) =
    t.1.continuation (markedOrbitArc t a j) at hh
  rw [hz,markedOrbitArc_zero] at hh
  exact hh.symm

theorem markedSuffixArc_last_continuation (t : MarkedParentState) (a : Fin t.1.nArc) :
    t.1.continuation (markedSuffixArc t a ⟨markedSuffixSize t a-1,by have := markedSuffixSize_pos t a;omega⟩) =
      markedOrbitRoot t a := by
  have he : visitPosition t.2.1 a + (markedSuffixSize t a-1) = markedOrbitSize t a-1 := by
    have := visitPosition_lt_markedOrbitSize t a
    unfold markedSuffixSize
    omega
  have hf : markedSuffixArc t a ⟨markedSuffixSize t a-1,by have := markedSuffixSize_pos t a;omega⟩ =
      markedOrbitArc t a ⟨markedOrbitSize t a-1,by have := markedOrbitSize_pos t a;omega⟩ := by
    unfold markedSuffixArc
    congr 1
    exact Fin.ext he
  rw [hf]
  exact markedOrbitArc_last_continuation t a

/-- The unique predecessor of the stored root is the final actual visit. -/
theorem marked_visitPosition_of_continuation_root (t : MarkedParentState) (a e : Fin t.1.nArc)
    (he : t.1.continuation e = markedOrbitRoot t a) :
    visitPosition t.2.1 e + 1 = markedOrbitSize t a := by
  have hh := markedOrbitArc_last_continuation t a
  have heq := t.1.continuation.injective (he.trans hh.symm)
  rw [heq,markedOrbitArc_visitPosition]
  change markedOrbitSize t a-1+1=markedOrbitSize t a
  have := markedOrbitSize_pos t a
  omega

end DirectGLSSW.HOMFLY
