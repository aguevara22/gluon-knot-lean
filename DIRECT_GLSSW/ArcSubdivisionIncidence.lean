import PLArcSubdivisionData

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open DirectGLSSW.HOMFLY Equiv
attribute [local instance] Classical.propDecidable
variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ)

private theorem castSucc_inj_local {n : ℕ} {a b : Fin n} (h : a.castSucc=b.castSucc) : a=b := by
  exact Fin.castSucc_inj.mp h

private theorem cast_ne_last_local {n : ℕ} (a : Fin n) : a.castSucc ≠ Fin.last n := by
  exact Fin.ne_of_lt (Fin.castSucc_lt_last a)

@[simp] theorem crossingVertex_injective : Function.Injective (crossingVertex D) := by
  intro c d h
  apply D.crossingVertex_injective
  exact castSucc_inj_local h

@[simp] theorem incoming_target (c : Fin D.nCrossing) (i : Fin 2) :
    arcTarget D e (incoming D e c i) = crossingVertex D c := by
  by_cases h : D.incoming c i=e
  · have hi := D.incoming_target c i
    rw [h] at hi
    simp [incoming,h,arcTarget_new,crossingVertex,hi]
  · have hi := D.incoming_target c i
    simp [incoming,h,arcTarget_old,crossingVertex,hi]

theorem outgoing_source (c : Fin D.nCrossing) (i : Fin 2) :
    arcSource D (outgoing D c i) = crossingVertex D c := by
  simp [outgoing,arcSource_old,crossingVertex,D.outgoing_source]

theorem four_ports_distinct (c : Fin D.nCrossing) :
    incoming D e c 0 ≠ incoming D e c 1 ∧
      outgoing D c 0 ≠ outgoing D c 1 ∧
      (∀ i j, incoming D e c i ≠ outgoing D c j) := by
  have hp := D.four_ports_distinct c
  constructor
  · intro h
    by_cases h0 : D.incoming c 0=e <;> by_cases h1 : D.incoming c 1=e
    · exact hp.1 (h0.trans h1.symm)
    · have hh : Fin.last D.nArc = (D.incoming c 1).castSucc := by simpa [incoming,h0,h1] using h
      exact cast_ne_last_local (D.incoming c 1) hh.symm
    · have hh : (D.incoming c 0).castSucc = Fin.last D.nArc := by simpa [incoming,h0,h1] using h
      exact cast_ne_last_local (D.incoming c 0) hh
    · have hh : (D.incoming c 0).castSucc=(D.incoming c 1).castSucc := by simpa [incoming,h0,h1] using h
      exact hp.1 (castSucc_inj_local hh)
  constructor
  · intro h
    exact hp.2.1 (castSucc_inj_local (by simpa [outgoing] using h))
  · intro i j h
    by_cases hi : D.incoming c i=e
    · have hh : Fin.last D.nArc=(D.outgoing c j).castSucc := by simpa [incoming,hi,outgoing] using h
      exact cast_ne_last_local (D.outgoing c j) hh.symm
    · have hh : (D.incoming c i).castSucc=(D.outgoing c j).castSucc := by simpa [incoming,hi,outgoing] using h
      exact hp.2.2 i j (castSucc_inj_local hh)

theorem continuation_incidence (x : Fin (D.nArc+1)) :
    arcTarget D e x = arcSource D (continuation D e x) := by
  induction x using Fin.lastCases with
  | last =>
      simp [continuation,Equiv.Perm.mul_apply,liftedContinuation,arcTarget_new,arcSource_old,D.continuation_incidence]
  | cast a =>
      by_cases h : a=e
      · subst a
        simp [continuation,Equiv.Perm.mul_apply,liftedContinuation,arcTarget_old,arcSource_new,arcSource_old]
      · have hne : a.castSucc ≠ e.castSucc := fun hh => h (castSucc_inj_local hh)
        have hlast : a.castSucc ≠ Fin.last D.nArc := cast_ne_last_local _
        rw [continuation,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hne hlast]
        simp [liftedContinuation,arcTarget_old,h,D.continuation_incidence]

theorem continuation_crossing (c : Fin D.nCrossing) (i : Fin 2) :
    continuation D e (incoming D e c i) = outgoing D c (D.through c i) := by
  by_cases h : D.incoming c i=e
  · rw [incoming,if_pos h,continuation,Equiv.Perm.mul_apply,Equiv.swap_apply_right,liftedContinuation_old]
    have hcont := D.continuation_crossing c i
    rw [h] at hcont
    simpa [outgoing] using congrArg Fin.castSucc hcont
  · have hne : (D.incoming c i).castSucc ≠ e.castSucc := fun hh => h (castSucc_inj_local hh)
    have hlast : (D.incoming c i).castSucc ≠ Fin.last D.nArc := cast_ne_last_local _
    rw [incoming,if_neg h,continuation,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hne hlast,liftedContinuation_old]
    have hcont := D.continuation_crossing c i
    simpa [outgoing] using congrArg Fin.castSucc hcont

theorem collapse_surjective : Function.Surjective (collapse D e) := by
  intro a
  exact ⟨a.castSucc,by simp [collapse]⟩

theorem collapse_fiber (a : Fin D.nArc) (x : Fin (D.nArc+1)) :
    collapse D e x=a ↔ x=a.castSucc ∨ (a=e ∧ x=Fin.last D.nArc) := by
  induction x using Fin.lastCases with
  | last => simp [collapse,eq_comm]
  | cast x => simp [collapse,eq_comm]

theorem collapse_selected_fiber (x : Fin (D.nArc+1)) :
    collapse D e x=e ↔ x=e.castSucc ∨ x=Fin.last D.nArc := by
  rw [collapse_fiber]
  constructor
  · rintro (h|⟨_,h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨rfl,h⟩

theorem collapse_other_fiber (a : Fin D.nArc) (ha : a≠e) (x : Fin (D.nArc+1)) :
    collapse D e x=a ↔ x=a.castSucc := by
  rw [collapse_fiber]
  simp [ha]

theorem collapse_incoming (c : Fin D.nCrossing) (i : Fin 2) :
    collapse D e (incoming D e c i)=D.incoming c i := by
  by_cases h : D.incoming c i=e <;> simp [incoming,h,collapse]

theorem collapse_outgoing (c : Fin D.nCrossing) (i : Fin 2) :
    collapse D e (outgoing D c i)=D.outgoing c i := by
  simp [outgoing,collapse]

def throughMap (c : Fin D.nCrossing) : Equiv.Perm (Fin 2) := D.through c

def overMap (c : Fin D.nCrossing) : Fin 2 := D.overBranch c

theorem through_unchanged (c : Fin D.nCrossing) :
    throughMap D c = D.through c := rfl

theorem over_unchanged (c : Fin D.nCrossing) :
    overMap D c = D.overBranch c := rfl

theorem selected_first_half_not_incoming (c : Fin D.nCrossing) (i : Fin 2) :
    incoming D e c i ≠ e.castSucc := by
  by_cases h : D.incoming c i=e
  · have hlast := cast_ne_last_local e
    intro hh
    exact hlast (by simpa [incoming,h] using hh.symm)
  · simp only [incoming,if_neg h]
    exact fun hh => h (castSucc_inj_local hh)

theorem fresh_vertex_degree_one :
    (incomingArcs (arcTarget D e : Fin (D.nArc+1) → Fin (D.nVertex+1)) (Fin.last D.nVertex)).card=1 ∧
    (outgoingArcs (arcSource D : Fin (D.nArc+1) → Fin (D.nVertex+1)) (Fin.last D.nVertex)).card=1 := by
  constructor
  · unfold incomingArcs
    have hset : Finset.univ.filter (fun x : Fin (D.nArc+1) => arcTarget D e x=Fin.last D.nVertex) = {e.castSucc} := by
      ext x
      induction x using Fin.lastCases with
      | last =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          change (arcTarget D e (Fin.last D.nArc)=Fin.last D.nVertex) ↔
            Fin.last D.nArc=e.castSucc
          rw [arcTarget_new]
          constructor
          · intro h; exact False.elim (cast_ne_last_local (D.arcTarget e) h)
          · intro h; exact False.elim (cast_ne_last_local e h.symm)
      | cast a => simp [arcTarget_old]
    rw [hset]
    simp
  · unfold outgoingArcs
    have hset : Finset.univ.filter (fun x : Fin (D.nArc+1) => arcSource D x=Fin.last D.nVertex) = {Fin.last D.nArc} := by
      ext x
      induction x using Fin.lastCases with
      | last => simp [arcSource_new]
      | cast a => simp [arcSource_old]
    rw [hset]
    simp

theorem no_old_crossing_at_fresh_vertex (c : Fin D.nCrossing) :
    crossingVertex D c ≠ Fin.last D.nVertex := by
  change (D.crossingVertex c).castSucc ≠ Fin.last D.nVertex
  exact cast_ne_last_local _

theorem continuation_selected_first :
    continuation D e e.castSucc = Fin.last D.nArc := by
  simp [continuation,Equiv.Perm.mul_apply,Equiv.swap_apply_left,liftedContinuation]

theorem collapse_fibers (a b : Fin (D.nArc+1)) :
    collapse D e a=collapse D e b ↔
      a=b ∨ (a=e.castSucc ∧ b=Fin.last D.nArc) ∨
        (a=Fin.last D.nArc ∧ b=e.castSucc) := by
  induction a using Fin.lastCases with
  | last => induction b using Fin.lastCases <;> simp [collapse,eq_comm]
  | cast a => induction b using Fin.lastCases <;> simp [collapse,eq_comm]

theorem collapse_continuation (x : Fin (D.nArc+1)) (hx : x≠e.castSucc) :
    collapse D e (continuation D e x) = D.continuation (collapse D e x) := by
  induction x using Fin.lastCases with
  | last =>
      simp [continuation,Equiv.Perm.mul_apply,Equiv.swap_apply_right,
        liftedContinuation,collapse]
  | cast a =>
      by_cases h : a=e
      · subst a
        exact False.elim (hx rfl)
      · simp [continuation,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,
          liftedContinuation,collapse,h,cast_ne_last_local]

end DirectGLSSW.HOMFLY.ArcSubdivision
