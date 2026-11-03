import ProcessedArcContinuationTrace
import ProcessedCrossingOriginTrace
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- The stored root of the actual continuation component containing a. -/
def markedOrbitRoot (t : MarkedParentState) (a : Fin t.1.nArc) : Fin t.1.nArc :=
  (t.2.1.baseArc (componentOf t.1.continuation a)).val

def markedOrbitSize (t : MarkedParentState) (a : Fin t.1.nArc) : ℕ :=
  Fintype.card (Fibre t.1.continuation
    (componentOf t.1.continuation (markedOrbitRoot t a)))

def markedOrbitArc (t : MarkedParentState) (a : Fin t.1.nArc)
    (i : Fin (markedOrbitSize t a)) : Fin t.1.nArc :=
  (orbitEnumeration t.1.continuation (markedOrbitRoot t a) i).val

theorem markedOrbitArc_visitPosition (t : MarkedParentState) (a : Fin t.1.nArc)
    (i : Fin (markedOrbitSize t a)) :
    visitPosition t.2.1 (markedOrbitArc t a i) = i.val := by
  have hr := (t.2.1.baseArc (componentOf t.1.continuation a)).property
  have he : componentOf t.1.continuation (markedOrbitArc t a i) =
      componentOf t.1.continuation a :=
    (orbitEnumeration t.1.continuation (markedOrbitRoot t a) i).property.trans hr
  have hb : (t.2.1.baseArc (componentOf t.1.continuation (markedOrbitArc t a i))).val =
      markedOrbitRoot t a := by rw [he]; rfl
  rw [visitPosition_eq_orbitPosition_of_baseArc t.2.1 (markedOrbitArc t a i)
    (markedOrbitRoot t a) hb (orbitEnumeration t.1.continuation (markedOrbitRoot t a) i).property]
  exact congrArg Fin.val ((orbitEnumeration t.1.continuation (markedOrbitRoot t a)).symm_apply_apply i)

theorem visitPosition_lt_markedOrbitSize (t : MarkedParentState) (a : Fin t.1.nArc) :
    visitPosition t.2.1 a < markedOrbitSize t a := by
  exact ((orbitEnumeration t.1.continuation (markedOrbitRoot t a)).symm
    ⟨a,(t.2.1.baseArc (componentOf t.1.continuation a)).property.symm⟩).isLt

theorem markedOrbitArc_at_position (t : MarkedParentState) (a : Fin t.1.nArc) :
    markedOrbitArc t a ⟨visitPosition t.2.1 a,visitPosition_lt_markedOrbitSize t a⟩ = a := by
  exact congrArg Subtype.val ((orbitEnumeration t.1.continuation (markedOrbitRoot t a)).apply_symm_apply
    ⟨a,(t.2.1.baseArc (componentOf t.1.continuation a)).property.symm⟩)

def markedSuffixSize (t : MarkedParentState) (a : Fin t.1.nArc) : ℕ :=
  markedOrbitSize t a - visitPosition t.2.1 a

theorem markedSuffixSize_pos (t : MarkedParentState) (a : Fin t.1.nArc) :
    0 < markedSuffixSize t a := Nat.sub_pos_of_lt (visitPosition_lt_markedOrbitSize t a)

/-- The literal terminal suffix of the actual stored-root orbit, including a. -/
def markedSuffixArc (t : MarkedParentState) (a : Fin t.1.nArc)
    (i : Fin (markedSuffixSize t a)) : Fin t.1.nArc :=
  markedOrbitArc t a ⟨visitPosition t.2.1 a + i.val,by
    have := i.isLt; unfold markedSuffixSize at this; omega⟩

theorem markedSuffixArc_visitPosition (t : MarkedParentState) (a : Fin t.1.nArc)
    (i : Fin (markedSuffixSize t a)) :
    visitPosition t.2.1 (markedSuffixArc t a i) = visitPosition t.2.1 a + i.val :=
  markedOrbitArc_visitPosition t a _

theorem markedSuffixArc_zero (t : MarkedParentState) (a : Fin t.1.nArc) :
    markedSuffixArc t a ⟨0,markedSuffixSize_pos t a⟩ = a := by
  exact markedOrbitArc_at_position t a

theorem markedSuffixArc_successor (t : MarkedParentState) (a : Fin t.1.nArc)
    (i j : Fin (markedSuffixSize t a)) (hij : j.val=i.val+1) :
    t.1.continuation (markedSuffixArc t a i) = markedSuffixArc t a j := by
  unfold markedSuffixArc markedOrbitArc
  rw [orbitEnumeration_apply_val,orbitEnumeration_apply_val]
  change t.1.continuation ((t.1.continuation ^ (visitPosition t.2.1 a + i.val)) (markedOrbitRoot t a)) =
    (t.1.continuation ^ (visitPosition t.2.1 a + j.val)) (markedOrbitRoot t a)
  rw [hij,← Nat.add_assoc,pow_succ',Equiv.Perm.mul_apply]

theorem markedSuffixArc_injective (t : MarkedParentState) (a : Fin t.1.nArc) :
    Function.Injective (markedSuffixArc t a) := by
  intro i j he
  have hh := congrArg (visitPosition t.2.1) he
  rw [markedSuffixArc_visitPosition,markedSuffixArc_visitPosition] at hh
  exact Fin.ext (Nat.add_left_cancel hh)

end DirectGLSSW.HOMFLY
