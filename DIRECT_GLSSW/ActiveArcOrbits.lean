import ActiveArcEvents
import DirectGLSSW.OrbitNormalization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc
open PermutationOrbits

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
variable (h : NoTriple q) (S : Finset (Crossing q))

abbrev OpenCoord := Fin (Fintype.card (Fibre (incoming q h S) (componentOf (incoming q h S) (start q))))

def openEventAt (i : OpenCoord q h S) : Event q :=
  (orbitEnumeration (incoming q h S) (start q) i).val

theorem openEventAt_zero : openEventAt q h S 0=start q := by
  exact orbitEnumeration_zero _ _

def lastCoord : OpenCoord q h S :=
  ⟨Fintype.card (Fibre (incoming q h S) (componentOf (incoming q h S) (start q)))-1,
    Nat.sub_lt (Fintype.card_pos) (by omega)⟩

theorem openEventAt_last : openEventAt q h S (lastCoord q h S)=terminal q := by
  apply (unique_seam_predecessor q h S _).mp
  have hs := congrArg Subtype.val
    (orbitEnumeration_successor (incoming q h S) (start q) (lastCoord q h S))
  have hz : cyclicSuccessorPerm
      (Fintype.card (Fibre (incoming q h S) (componentOf (incoming q h S) (start q))))
      (lastCoord q h S)=0 := by
    apply Fin.ext
    have hn : 0<Fintype.card (Fibre (incoming q h S) (componentOf (incoming q h S) (start q))) := Fintype.card_pos
    simp only [cyclicSuccessorPerm_apply,cyclicSuccessor,cyclicVertexIndex,lastCoord,Nat.add_zero,Fin.val_zero]
    rw [Nat.sub_add_cancel (by omega),Nat.mod_self]
  rw [hz,orbitEnumeration_zero] at hs
  exact hs.symm

/-- Before the terminal coordinate, the actual smoothing follows this linear enumeration. -/
theorem openEventAt_step (i : ℕ)
    (hi : i+1<Fintype.card (Fibre (incoming q h S) (componentOf (incoming q h S) (start q)))) :
    incoming q h S (openEventAt q h S ⟨i,by omega⟩)=
      openEventAt q h S ⟨i+1,hi⟩ := by
  have hs := congrArg Subtype.val
    (orbitEnumeration_successor (incoming q h S) (start q) ⟨i,by omega⟩)
  have hz : cyclicSuccessorPerm
      (Fintype.card (Fibre (incoming q h S) (componentOf (incoming q h S) (start q))))
      ⟨i,by omega⟩=⟨i+1,hi⟩ := by
    apply Fin.ext
    simp only [cyclicSuccessorPerm_apply,cyclicSuccessor,cyclicVertexIndex,Nat.add_zero]
    exact Nat.mod_eq_of_lt hi
  rw [hz] at hs
  exact hs.symm

/-- All open-orbit events occur once, with initial and terminal endpoints distinguished. -/
theorem openEventAt_bijective :
    Function.Bijective (fun i : OpenCoord q h S =>
      (⟨openEventAt q h S i,(orbitEnumeration (incoming q h S) (start q) i).property⟩ :
        Fibre (incoming q h S) (componentOf (incoming q h S) (start q)))) :=
  (orbitEnumeration (incoming q h S) (start q)).bijective

/-- Cutting the sole terminal-to-start seam leaves this actual finite open word. -/
def openEventWord : List (Event q) := orbitWord (incoming q h S) (start q)

theorem openEventWord_nodup : (openEventWord q h S).Nodup := orbitWord_nodup _ _

theorem openEventWord_endpoints :
    openEventAt q h S 0=start q ∧ openEventAt q h S (lastCoord q h S)=terminal q :=
  ⟨openEventAt_zero q h S,openEventAt_last q h S⟩

/-- Closed components use the actual orbit restriction and retain every cyclic step. -/
def closedSuccessor (C : Component (incoming q h S))
    (_hc : C≠openComponent q h S) : Equiv.Perm (Fibre (incoming q h S) C) :=
  fibrePerm (incoming q h S) C

theorem closedSuccessor_isCycle (C : Component (incoming q h S))
    (hc : C≠openComponent q h S) :
    (closedSuccessor q h S C hc).IsCycleOn Set.univ :=
  fibrePerm_isCycleOn _ _

end DirectGLSSW.ActiveArc
