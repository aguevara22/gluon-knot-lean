import ArcSubdivisionIncidence

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
attribute [local instance] Classical.propDecidable
@[simp] private theorem fresh_ne_old {n : ℕ} (a : Fin n) : Fin.last n ≠ a.castSucc :=
  Ne.symm (Fin.ne_of_lt (Fin.castSucc_lt_last a))
@[simp] private theorem old_ne_fresh {n : ℕ} (a : Fin n) : a.castSucc ≠ Fin.last n :=
  Fin.ne_of_lt (Fin.castSucc_lt_last a)
variable (D : PLLinkDiagram) (e : Fin D.nArc)

private theorem original_target_iff (c : Fin D.nCrossing) (a : Fin D.nArc) :
    D.arcTarget a=D.crossingVertex c ↔ a=D.incoming c 0 ∨ a=D.incoming c 1 := by
  constructor
  · intro h
    rcases (D.crossing_incidence_complete c a).mp (Or.inr h) with h0|h1|h0|h1
    · exact Or.inl h0
    · exact Or.inr h1
    · subst a;exact False.elim (D.arc_endpoints_distinct _ ((D.outgoing_source c 0).trans h.symm))
    · subst a;exact False.elim (D.arc_endpoints_distinct _ ((D.outgoing_source c 1).trans h.symm))
  · rintro (rfl|rfl)
    · exact D.incoming_target c 0
    · exact D.incoming_target c 1

private theorem original_source_iff (c : Fin D.nCrossing) (a : Fin D.nArc) :
    D.arcSource a=D.crossingVertex c ↔ a=D.outgoing c 0 ∨ a=D.outgoing c 1 := by
  constructor
  · intro h
    rcases (D.crossing_incidence_complete c a).mp (Or.inl h) with h0|h1|h0|h1
    · subst a;exact False.elim (D.arc_endpoints_distinct _ (h.trans (D.incoming_target c 0).symm))
    · subst a;exact False.elim (D.arc_endpoints_distinct _ (h.trans (D.incoming_target c 1).symm))
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (rfl|rfl)
    · exact D.outgoing_source c 0
    · exact D.outgoing_source c 1

private theorem target_eq_crossing_iff (c : Fin D.nCrossing) (x : Fin (D.nArc+1)) :
    arcTarget D e x=crossingVertex D c ↔ x=incoming D e c 0 ∨ x=incoming D e c 1 := by
  refine Fin.lastCases ?_ (fun a=>?_) x
  · simp only [arcTarget_new,crossingVertex,Fin.castSucc_inj,original_target_iff]
    by_cases h0 : D.incoming c 0=e <;> by_cases h1 : D.incoming c 1=e <;>
      simp_all [incoming]
    exact ⟨Ne.symm h0,Ne.symm h1⟩
  · by_cases ha : a=e
    · subst a
      simp only [arcTarget_old,if_pos rfl,crossingVertex]
      have h0:=selected_first_half_not_incoming D e c 0
      have h1:=selected_first_half_not_incoming D e c 1
      simp [Ne.symm h0,Ne.symm h1]
    · simp only [arcTarget_old,if_neg ha,crossingVertex,Fin.castSucc_inj,original_target_iff]
      by_cases h0 : D.incoming c 0=e <;> by_cases h1 : D.incoming c 1=e <;>
        simp [incoming,h0,h1,ha]

private theorem source_eq_crossing_iff (c : Fin D.nCrossing) (x : Fin (D.nArc+1)) :
    arcSource D x=crossingVertex D c ↔ x=outgoing D c 0 ∨ x=outgoing D c 1 := by
  refine Fin.lastCases ?_ (fun a=>?_) x
  · simp [arcSource_new,crossingVertex,outgoing]
  · simp only [arcSource_old,crossingVertex,outgoing,Fin.castSucc_inj,original_source_iff]

theorem crossing_incidence_complete (c : Fin D.nCrossing) (x : Fin (D.nArc+1)) :
    (arcSource D x=crossingVertex D c ∨ arcTarget D e x=crossingVertex D c) ↔
      (x=incoming D e c 0 ∨ x=incoming D e c 1 ∨ x=outgoing D c 0 ∨ x=outgoing D c 1) := by
  rw [source_eq_crossing_iff,target_eq_crossing_iff]
  tauto

theorem regular_degree_one (v : Fin (D.nVertex+1)) (hv : ∀c,crossingVertex D c≠v) :
    (incomingArcs (arcTarget D e) v).card=1 ∧ (outgoingArcs (arcSource D) v).card=1 := by
  revert hv
  refine Fin.lastCases ?_ (fun v=>?_) v
  · intro _;exact fresh_vertex_degree_one D e
  · intro hv
    have hvo : ∀c,D.crossingVertex c≠v := by
      intro c h;apply hv c;exact congrArg Fin.castSucc h
    obtain ⟨hi,ho⟩:=D.regular_degree_one v hvo
    obtain ⟨a,ha⟩:=Finset.card_eq_one.mp hi
    obtain ⟨b,hb⟩:=Finset.card_eq_one.mp ho
    have hat (x : Fin D.nArc) : D.arcTarget x=v ↔ x=a := by
      have h:=Finset.ext_iff.mp ha x
      simpa only [incomingArcs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using h
    have hbs (x : Fin D.nArc) : D.arcSource x=v ↔ x=b := by
      have h:=Finset.ext_iff.mp hb x
      simpa only [outgoingArcs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using h
    constructor
    · have hs : incomingArcs (arcTarget D e) v.castSucc = {if a=e then Fin.last D.nArc else a.castSucc} := by
        ext x
        simp only [incomingArcs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
        refine Fin.lastCases ?_ (fun x=>?_) x
        · rw [arcTarget_new,Fin.castSucc_inj,hat]
          by_cases hae : a=e <;> simp_all
          exact Ne.symm hae
        · by_cases hxe : x=e <;> by_cases hae : a=e <;> simp_all [arcTarget_old]
          exact Ne.symm hae
      rw [hs];exact Finset.card_singleton _
    · have hs : outgoingArcs (arcSource D) v.castSucc = {b.castSucc} := by
        ext x
        simp only [outgoingArcs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
        refine Fin.lastCases ?_ (fun x=>?_) x
        · simp [arcSource_new]
        · simp only [arcSource_old,Fin.castSucc_inj,hbs]
      rw [hs];exact Finset.card_singleton _
end DirectGLSSW.HOMFLY.ArcSubdivision
