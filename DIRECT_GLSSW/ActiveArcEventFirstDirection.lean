import ActiveArcVirtualEventGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords

/-- The event-word first side points in a strictly positive multiple of the
actual cursor direction. The multiplier is derived from first-crossing
minimality and exclusion of the crossing from the physical support. -/
theorem eventOpenWord_first_direction_positive
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val) :
    ∃ β : ℝ, 0 < β ∧
      eventOpenWord q hR U c 1 - eventOpenWord q hR U c 0 = β • (q 1 - q 0) := by
  obtain ⟨s,hcs,hs1,hpoint⟩ := openVertex_one_after_unselected_first q hR c hc U hu
  refine ⟨s-leftParameter q c,sub_pos.mpr hcs,?_⟩
  rw [eventOpenWord_zero,eventOpenWord_pos q hR U c 1 (by omega)
    (lt_of_lt_of_le (by decide : 1<2) (open_count_ge_two q hR U.val)),hpoint]
  have hcp := (leftParameter_spec q c).2.2
  rw [hc.1] at hcp
  change crossingPoint q c = affinePoint (q 0) (q 1) (leftParameter q c) at hcp
  rw [hcp]
  ext <;> simp only [affinePoint,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

/-- Once the actual retained crossed side is identified as a positive
subsegment of the original right crossing edge, its event transversality
follows from original Regular. No parent genericity is assumed. -/
theorem eventOpenWord_crossed_subsegment_transverse
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val)
    (k : ℕ) (a b : ℝ) (hab : a < b)
    (ha : eventOpenWord q hR U c k = affinePoint (q c.val.2.castSucc) (q c.val.2.succ) a)
    (hb : eventOpenWord q hR U c (k+1) = affinePoint (q c.val.2.castSucc) (q c.val.2.succ) b) :
    planarDet (eventOpenWord q hR U c 1 - eventOpenWord q hR U c 0)
      (eventOpenWord q hR U c (k+1) - eventOpenWord q hR U c k) ≠ 0 := by
  obtain ⟨β,hβ,hdir⟩ := eventOpenWord_first_direction_positive q hR c hc U hu
  have hdet := hR.transverse c.val.1 c.val.2 (ne_of_lt c.property.1)
    (crossingPoint q c) (crossingPoint_mem q c).1 (crossingPoint_mem q c).2
  rw [hc.1] at hdet
  have he : planarDet (eventOpenWord q hR U c 1 - eventOpenWord q hR U c 0)
      (eventOpenWord q hR U c (k+1) - eventOpenWord q hR U c k) =
      β*(b-a)*planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc) := by
    rw [hdir,ha,hb]
    simp only [planarDet,affinePoint,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (ne_of_gt hβ) (ne_of_gt (sub_pos.mpr hab))) hdet

end DirectGLSSW.ActiveArc.Primitive
