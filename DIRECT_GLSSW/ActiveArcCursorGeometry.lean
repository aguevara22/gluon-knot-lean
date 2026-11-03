import ActiveArcRegularGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Move only the first endpoint forward on its actual first physical edge. -/
def moveStart (t : ℝ) : Fin (n+2) → PlanarPoint ℝ :=
  Function.update q 0 (affinePoint (q 0) (q 1) t)

@[simp] theorem moveStart_zero (t : ℝ) : moveStart q t 0=affinePoint (q 0) (q 1) t := by
  simp [moveStart]

@[simp] theorem moveStart_succ (t : ℝ) (i : Fin (n+1)) : moveStart q t i.succ=q i.succ := by
  simp [moveStart,Fin.succ_ne_zero]

theorem moveStart_eq (t : ℝ) (i : Fin (n+2)) (hi : i≠0) : moveStart q t i=q i := by
  exact Function.update_of_ne hi _ _

@[simp] theorem moveStart_at_zero : moveStart q 0=q := by
  funext i
  by_cases hi : i=0
  · subst i; simp [affinePoint_zero]
  · exact moveStart_eq q 0 i hi

theorem castSucc_ne_zero {e : Fin (n+1)} (he : e≠0) : e.castSucc≠0 := by
  intro h;apply he;apply Fin.ext;exact congrArg (fun i : Fin (n+2) => i.val) h

theorem edgeInterior_unchanged (t : ℝ) (e : Fin (n+1)) (he : e≠0) (x : PlanarPoint ℝ) :
    edgeInterior (moveStart q t) e x ↔ edgeInterior q e x := by
  unfold edgeInterior
  rw [moveStart_succ,moveStart_eq q t e.castSucc (castSucc_ne_zero he)]

theorem affinePoint_suffix (a b : PlanarPoint ℝ) (t u : ℝ) :
    affinePoint (affinePoint a b t) b u=affinePoint a b (t+(1-t)*u) := by
  ext <;> simp only [affinePoint] <;> ring

/-- The moving first edge is exactly the open parameter interval (t,1). -/
theorem first_edgeInterior_iff (t : ℝ) (ht : t<1) (x : PlanarPoint ℝ) :
    edgeInterior (moveStart q t) 0 x ↔
      ∃ s : ℝ, t<s ∧ s<1 ∧ x=affinePoint (q 0) (q 1) s := by
  change (∃ u : ℝ, 0<u ∧ u<1 ∧ x=affinePoint (moveStart q t 0) (moveStart q t 1) u) ↔ _
  rw [moveStart_zero,moveStart_eq q t 1 (by exact Fin.ne_of_val_ne (by simp))]
  constructor
  · rintro ⟨u,hu0,hu1,hx⟩
    refine ⟨t+(1-t)*u,by nlinarith,by nlinarith,?_⟩
    exact hx.trans (affinePoint_suffix _ _ _ _)
  · rintro ⟨s,hs0,hs1,hx⟩
    refine ⟨(s-t)/(1-t),div_pos (by linarith) (by linarith),?_,?_⟩
    · apply (div_lt_one (by linarith : 0<1-t)).mpr;linarith
    · rw [affinePoint_suffix]
      have hh : t+(1-t)*((s-t)/(1-t))=s := by
        field_simp [ne_of_gt (sub_pos.mpr ht)]
        <;> ring
      rw [hh]
      exact hx

theorem edgeInterior_subset (t : ℝ) (ht0 : 0≤t) (ht1 : t<1)
    (e : Fin (n+1)) (x : PlanarPoint ℝ) :
    edgeInterior (moveStart q t) e x → edgeInterior q e x := by
  by_cases he : e=0
  · subst e
    rintro hx
    obtain ⟨s,hs0,hs1,hsx⟩ := (first_edgeInterior_iff q t ht1 x).mp hx
    exact ⟨s,lt_of_le_of_lt ht0 hs0,hs1,hsx⟩
  · exact (edgeInterior_unchanged q t e he x).mp

/-- All genuine event times are first-edge physical crossing parameters. -/
def criticalParameters : Finset ℝ :=
  (Finset.univ.filter (fun c : Crossing q => c.val.1=0)).image (leftParameter q)

theorem mem_criticalParameters (t : ℝ) : t∈criticalParameters q ↔
    ∃ c : Crossing q, c.val.1=0 ∧ leftParameter q c=t := by
  simp [criticalParameters]

/-- A moving endpoint meets a later edge precisely at an actual crossing time. -/
theorem endpoint_on_later_iff (hR : Regular q) (t : ℝ) (ht0 : 0<t) (ht1 : t<1) :
    (∃ e : Fin (n+1), e≠0 ∧ edgeInterior q e (affinePoint (q 0) (q 1) t)) ↔
      t∈criticalParameters q := by
  constructor
  · rintro ⟨e,he,hx⟩
    have he0 : (0 : Fin (n+1))<e := Fin.pos_iff_ne_zero.mpr he
    let c : Crossing q := ⟨(0,e),he0,affinePoint (q 0) (q 1) t,⟨t,ht0,ht1,rfl⟩,hx⟩
    apply (mem_criticalParameters q t).mpr
    refine ⟨c,rfl,?_⟩
    have hp := crossingPoint_eq_of_mem_regular q hR c (affinePoint (q 0) (q 1) t)
      ⟨t,ht0,ht1,rfl⟩ hx
    apply edge_parameter_unique q hR 0
    exact (leftParameter_spec q c).2.2.symm.trans hp
  · intro ht
    obtain ⟨c,hc,htc⟩ := (mem_criticalParameters q t).mp ht
    have hp : crossingPoint q c=affinePoint (q 0) (q 1) t := by
      simpa only [hc,htc] using (leftParameter_spec q c).2.2
    refine ⟨c.val.2,?_,?_⟩
    · have hh := c.property.1;rw [hc] at hh;exact ne_of_gt hh
    · rw [← hp];exact (crossingPoint_mem q c).2

theorem first_tangent (t : ℝ) :
    moveStart q t 1-moveStart q t 0=(1-t) • (q 1-q 0) := by
  rw [moveStart_zero,moveStart_eq q t 1 (by exact Fin.ne_of_val_ne (by simp))]
  ext <;> simp [affinePoint] <;> ring

/-- Genuine event times cannot be assigned full-word Regular. -/
theorem not_regular_at_critical (t : ℝ) (ht : t∈criticalParameters q) :
    ¬ Regular (moveStart q t) := by
  obtain ⟨c,hc,htc⟩ := (mem_criticalParameters q t).mp ht
  have he : c.val.2≠0 := by have hh:=c.property.1;rw [hc] at hh;exact ne_of_gt hh
  have hp : crossingPoint q c=affinePoint (q 0) (q 1) t := by
    simpa only [hc,htc] using (leftParameter_spec q c).2.2
  intro hR
  apply hR.anchor_avoid c.val.2 0 (Ne.symm (castSucc_ne_zero he)) (Ne.symm (Fin.succ_ne_zero _))
  rw [moveStart_zero,← hp]
  exact (edgeInterior_unchanged q t c.val.2 he _).mpr (crossingPoint_mem q c).2

end DirectGLSSW.ActiveArc.Cursor
