import ActiveArcCursorRegular

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
variable (hR : Regular q) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1)

/-- A first-edge crossing survives exactly when its parameter is ahead of the mark. -/
def Survives (c : Crossing q) : Prop := c.val.1=0 → t<leftParameter q c

def crossingToOriginal (c : Crossing (moveStart q t)) : Crossing q :=
  ⟨c.val,c.property.1,by
    obtain ⟨x,hx,hy⟩ := c.property.2
    exact ⟨x,edgeInterior_subset q t ht0 ht1 c.val.1 x hx,
      edgeInterior_subset q t ht0 ht1 c.val.2 x hy⟩⟩

@[simp] theorem crossingToOriginal_val (c : Crossing (moveStart q t)) :
    (crossingToOriginal q t ht0 ht1 c).val=c.val := rfl

include hR in
theorem crossingToOriginal_point (c : Crossing (moveStart q t)) :
    crossingPoint q (crossingToOriginal q t ht0 ht1 c)=crossingPoint (moveStart q t) c := by
  exact crossingPoint_eq_of_mem_regular q hR _ _
    (edgeInterior_subset q t ht0 ht1 c.val.1 _ (crossingPoint_mem (moveStart q t) c).1)
    (edgeInterior_subset q t ht0 ht1 c.val.2 _ (crossingPoint_mem (moveStart q t) c).2)

include hR in
theorem crossingToOriginal_survives (c : Crossing (moveStart q t)) :
    Survives q t (crossingToOriginal q t ht0 ht1 c) := by
  intro hc
  have hx := (crossingPoint_mem (moveStart q t) c).1
  change c.val.1=0 at hc
  rw [hc] at hx
  obtain ⟨s,hs0,hs1,hsp⟩ := (first_edgeInterior_iff q t ht1 _).mp hx
  have hh : leftParameter q (crossingToOriginal q t ht0 ht1 c)=s := by
    apply edge_parameter_unique q hR 0
    have hp := (leftParameter_spec q (crossingToOriginal q t ht0 ht1 c)).2.2
    rw [crossingToOriginal_point q hR t ht0 ht1] at hp
    simpa only [crossingToOriginal_val,hc] using hp.symm.trans hsp
  exact hh.symm ▸ hs0

def crossingFromOriginal (c : Crossing q) (hc : Survives q t c) : Crossing (moveStart q t) :=
  ⟨c.val,c.property.1,by
    refine ⟨crossingPoint q c,?_,?_⟩
    · by_cases he : c.val.1=0
      · rw [he,first_edgeInterior_iff q t ht1]
        exact ⟨leftParameter q c,hc he,(leftParameter_spec q c).2.1,by
          simpa only [he] using (leftParameter_spec q c).2.2⟩
      · exact (edgeInterior_unchanged q t c.val.1 he _).mpr (crossingPoint_mem q c).1
    · have he : c.val.2≠0 := by
        have hh:=c.property.1
        intro he;rw [he] at hh;exact (not_lt_of_ge (Fin.zero_le _)) hh
      exact (edgeInterior_unchanged q t c.val.2 he _).mpr (crossingPoint_mem q c).2⟩

/-- Literal surviving physical labels, including at the excluded singular event time.
Regularity of the moving word is established separately, only off that time set. -/
def crossingEquiv : Crossing (moveStart q t) ≃ {c : Crossing q // Survives q t c} where
  toFun c := ⟨crossingToOriginal q t ht0 ht1 c,crossingToOriginal_survives q hR t ht0 ht1 c⟩
  invFun c := crossingFromOriginal q t ht1 c.val c.property
  left_inv c := by apply Subtype.ext;rfl
  right_inv c := by apply Subtype.ext;apply Subtype.ext;rfl

@[simp] theorem crossingEquiv_val (c : Crossing (moveStart q t)) :
    (crossingEquiv q hR t ht0 ht1 c).val.val=c.val := rfl

theorem crossingEquiv_point (c : Crossing (moveStart q t)) :
    crossingPoint q (crossingEquiv q hR t ht0 ht1 c).val=crossingPoint (moveStart q t) c :=
  crossingToOriginal_point q hR t ht0 ht1 c

theorem crossingEquiv_rightParameter (c : Crossing (moveStart q t)) :
    rightParameter q (crossingEquiv q hR t ht0 ht1 c).val=rightParameter (moveStart q t) c := by
  have he : c.val.2≠0 := by
    have hh:=c.property.1
    intro he;rw [he] at hh;exact (not_lt_of_ge (Fin.zero_le _)) hh
  apply edge_parameter_unique q hR c.val.2
  have hnew := (rightParameter_spec (moveStart q t) c).2.2
  rw [moveStart_succ,moveStart_eq q t _ (castSucc_ne_zero he)] at hnew
  exact (rightParameter_spec q (crossingEquiv q hR t ht0 ht1 c).val).2.2.symm.trans
    ((crossingEquiv_point q hR t ht0 ht1 c).trans hnew)

theorem crossingEquiv_leftParameter (c : Crossing (moveStart q t)) (he : c.val.1≠0) :
    leftParameter q (crossingEquiv q hR t ht0 ht1 c).val=leftParameter (moveStart q t) c := by
  apply edge_parameter_unique q hR c.val.1
  have hnew := (leftParameter_spec (moveStart q t) c).2.2
  rw [moveStart_succ,moveStart_eq q t _ (castSucc_ne_zero he)] at hnew
  exact (leftParameter_spec q (crossingEquiv q hR t ht0 ht1 c).val).2.2.symm.trans
    ((crossingEquiv_point q hR t ht0 ht1 c).trans hnew)

theorem crossingEquiv_firstParameter (c : Crossing (moveStart q t)) (he : c.val.1=0) :
    leftParameter q (crossingEquiv q hR t ht0 ht1 c).val=
      t+(1-t)*leftParameter (moveStart q t) c := by
  apply edge_parameter_unique q hR 0
  have hp := (leftParameter_spec q (crossingEquiv q hR t ht0 ht1 c).val).2.2
  have hn := (leftParameter_spec (moveStart q t) c).2.2
  rw [he] at hn
  change crossingPoint (moveStart q t) c=affinePoint (moveStart q t 0) (moveStart q t 1) _ at hn
  rw [moveStart_zero,moveStart_eq q t 1 (by exact Fin.ne_of_val_ne (by simp)),affinePoint_suffix] at hn
  simpa only [crossingEquiv_val,he] using hp.symm.trans ((crossingEquiv_point q hR t ht0 ht1 c).trans hn)

end DirectGLSSW.ActiveArc.Cursor
