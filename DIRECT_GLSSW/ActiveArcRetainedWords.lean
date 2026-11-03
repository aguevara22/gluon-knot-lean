import ActiveArcClosedCorners
import ActiveArcRegularGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open DirectGLSSW PermutationOrbits ActiveArc

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

abbrev Coord (root : Event q) :=
  Fin (Fintype.card (Fibre (incoming q hR.noTriple S)
    (componentOf (incoming q hR.noTriple S) root)))

def eventAt (root : Event q) (i : Coord q hR S root) : Event q :=
  (orbitEnumeration (incoming q hR.noTriple S) root i).val

abbrev Corner (root : Event q) :=
  {i : Coord q hR S root // retained q S (eventAt q hR S root i)}

instance cornerFintype (root : Event q) : Fintype (Corner q hR S root) := by
  classical
  unfold Corner
  infer_instance

def enumeration (root : Event q) :
    Fin (Fintype.card (Corner q hR S root)) ≃o Corner q hR S root := by
  classical
  exact increasingEnumeration _

def cornerEvent (root : Event q) (i : Fin (Fintype.card (Corner q hR S root))) : Event q :=
  eventAt q hR S root (enumeration q hR S root i).val

def vertex (root : Event q) (i : Fin (Fintype.card (Corner q hR S root))) : PlanarPoint ℝ :=
  eventPoint q (cornerEvent q hR S root i)

theorem eventAt_zero (root : Event q) : eventAt q hR S root 0=root := orbitEnumeration_zero _ _

theorem cornerCount_pos (root : Event q) (hr : retained q S root) :
    0<Fintype.card (Corner q hR S root) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨0,by simpa [eventAt] using hr⟩⟩

theorem enumeration_zero (root : Event q) (hr : retained q S root) :
    enumeration q hR S root ⟨0,cornerCount_pos q hR S root hr⟩ =
      ⟨0,by simpa [eventAt] using hr⟩ := by
  let c₀ : Corner q hR S root := ⟨0,by simpa [eventAt] using hr⟩
  apply le_antisymm
  · have hz : (⟨0,cornerCount_pos q hR S root hr⟩ : Fin (Fintype.card (Corner q hR S root))) ≤
        (enumeration q hR S root).symm c₀ := Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
    simpa [c₀] using (enumeration q hR S root).monotone hz
  · exact Fin.le_iff_val_le_val.mpr (Nat.zero_le _)

theorem cornerEvent_zero (root : Event q) (hr : retained q S root) :
    cornerEvent q hR S root ⟨0,cornerCount_pos q hR S root hr⟩=root := by
  unfold cornerEvent
  rw [enumeration_zero q hR S root hr,eventAt_zero]

abbrev openCount := Fintype.card (Corner q hR S (start q))
def openFirst : Fin (openCount q hR S) := ⟨0,cornerCount_pos q hR S (start q) (endpoints_retained q S).1⟩
def openLast : Fin (openCount q hR S) :=
  ⟨openCount q hR S-1,Nat.sub_lt (cornerCount_pos q hR S (start q) (endpoints_retained q S).1) (by omega)⟩

theorem open_cornerEvent_first : cornerEvent q hR S (start q) (openFirst q hR S)=start q :=
  cornerEvent_zero q hR S (start q) (endpoints_retained q S).1

theorem open_cornerEvent_last : cornerEvent q hR S (start q) (openLast q hR S)=terminal q := by
  let cL : Corner q hR S (start q) :=
    ⟨lastCoord q hR.noTriple S,by
      change retained q S (openEventAt q hR.noTriple S (lastCoord q hR.noTriple S))
      rw [openEventAt_last]
      exact (endpoints_retained q S).2⟩
  have he : enumeration q hR S (start q) (openLast q hR S)=cL := by
    apply le_antisymm
    · change ((enumeration q hR S (start q) (openLast q hR S)).val).val ≤
        Fintype.card (Fibre (incoming q hR.noTriple S) (componentOf (incoming q hR.noTriple S) (start q)))-1
      have hh := (enumeration q hR S (start q) (openLast q hR S)).val.isLt
      omega
    · have hz : (enumeration q hR S (start q)).symm cL≤openLast q hR S := by
        have hh := ((enumeration q hR S (start q)).symm cL).isLt
        change _ ≤Fintype.card (Corner q hR S (start q))-1
        omega
      simpa using (enumeration q hR S (start q)).monotone hz
  unfold cornerEvent
  rw [he]
  exact openEventAt_last q hR.noTriple S

theorem open_vertex_first : vertex q hR S (start q) (openFirst q hR S)=q ⟨0,by omega⟩ := by
  rw [vertex,open_cornerEvent_first]
  rfl

theorem open_vertex_last : vertex q hR S (start q) (openLast q hR S)=q ⟨n+1,by omega⟩ := by
  rw [vertex,open_cornerEvent_last]
  rfl

theorem open_count_ge_two : 2≤openCount q hR S := by
  have hp := cornerCount_pos q hR S (start q) (endpoints_retained q S).1
  by_contra hh
  have he : openFirst q hR S=openLast q hR S := by
    apply Fin.ext
    have h1 := (openFirst q hR S).isLt
    have h2 := (openLast q hR S).isLt
    omega
  have hx := congrArg (cornerEvent q hR S (start q)) he
  rw [open_cornerEvent_first,open_cornerEvent_last] at hx
  exact start_ne_terminal q hx

theorem eventAt_successor (root : Event q) (i : Coord q hR S root) :
    eventAt q hR S root (cyclicSuccessorPerm _ i)=
      incoming q hR.noTriple S (eventAt q hR S root i) := by
  exact congrArg Subtype.val (orbitEnumeration_successor _ root i)

theorem eventAt_iterate (root : Event q) (i : Coord q hR S root) (k : ℕ) :
    eventAt q hR S root ((cyclicSuccessorPerm _ ^ k) i)=
      (incoming q hR.noTriple S ^ k) (eventAt q hR S root i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,eventAt_successor,ih,pow_succ',Equiv.Perm.mul_apply]

def nextCorner (root : Event q) : Equiv.Perm (Corner q hR S root) := by
  classical
  exact orderedCyclicSuccessor _

def cornerGap (root : Event q) (c : Corner q hR S root) : ℕ :=
  FiniteFirstReturn.forwardGap c.val (nextCorner q hR S root c).val

/-- Exact first return to retained events in the actual incoming smoothing orbit. -/
theorem corner_firstReturn (root : Event q) (c : Corner q hR S root) :
    0<cornerGap q hR S root c ∧
    (incoming q hR.noTriple S ^ cornerGap q hR S root c) (eventAt q hR S root c.val)=
      eventAt q hR S root (nextCorner q hR S root c).val ∧
    ∀ k : ℕ, 0<k → k<cornerGap q hR S root c →
      ¬retained q S ((incoming q hR.noTriple S ^ k) (eventAt q hR S root c.val)) := by
  classical
  have hf := FiniteFirstReturn.orderedSubtype_firstReturn
    (fun i : Coord q hR S root => retained q S (eventAt q hR S root i)) c
  change 0<cornerGap q hR S root c ∧
    cornerGap q hR S root c≤_ ∧
    (cyclicSuccessorPerm _ ^ cornerGap q hR S root c) c.val=(nextCorner q hR S root c).val ∧ _ at hf
  refine ⟨hf.1,?_,?_⟩
  · have hi := eventAt_iterate q hR S root c.val (cornerGap q hR S root c)
    rw [hf.2.2.1] at hi
    exact hi.symm
  · intro k hk hd
    have hn := hf.2.2.2 k hk hd
    rw [eventAt_iterate] at hn
    exact hn

end DirectGLSSW.ActiveArc.RetainedWords
