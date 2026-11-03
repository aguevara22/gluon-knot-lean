import ActiveArcRetainedCrossingLocality
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalSegments
open RetainedWords PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- Converse physical incidence: an actual visit strictly between the paired
retained source and its next retained endpoint lies in the strict interior
of that literal retained side. The original edge is derived from order. -/
theorem retained_visit_interval_interior (root : Event q) (z : Corner q hR S root)
    (hz : eventAt q hR S root z.val ≠ terminal q) (v : Visit q)
    (hv0 : (eventOrder q hR.noTriple).lt
      (pairing q S (eventAt q hR S root z.val)) (Sum.inr v))
    (hv1 : (eventOrder q hR.noTriple).lt (Sum.inr v)
      (eventAt q hR S root (nextCorner q hR S root z).val)) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ eventPoint q (Sum.inr v) =
      affinePoint (eventPoint q (eventAt q hR S root z.val))
        (eventPoint q (eventAt q hR S root (nextCorner q hR S root z).val)) t := by
  letI := eventOrder q hR.noTriple
  letI : LinearOrder (Fin (n+2) ⊕ Visit q) := eventOrder q hR.noTriple
  let x := eventAt q hR S root z.val
  let y := pairing q S x
  let w := eventAt q hR S root (nextCorner q hR S root z).val
  have hy : y≠terminal q := pairing_ne_terminal q S x hz
  have hvn : (Sum.inr v : Event q) ≠ terminal q := by intro hh; cases hh
  have hf := corner_firstReturn q hR S root z
  have hb := firstReturn_prefix_bounded q hR S x hz (cornerGap q hR S root z)
    hf.2.2 (cornerGap q hR S root z) hf.1 le_rfl
  rw [hf.2.1] at hb
  have hbound : w ≤ Sum.inl (physicalEdge q y hy).succ := hb.2
  have hvbound : (Sum.inr v : Event q) < Sum.inl (physicalEdge q y hy).succ :=
    lt_of_lt_of_le hv1 hbound
  have htag : edgeTag q (Sum.inr v)=edgeTag q y := by
    have hlo : edgeTag q y≤edgeTag q (Sum.inr v) := by
      rcases (event_lt_iff q hR.noTriple _ _).mp hv0 with h|h
      · exact le_of_lt h
      · exact le_of_eq h.1
    have hhi : edgeTag q (Sum.inr v)<edgeTag q y+1 := by
      by_contra h
      have ha := anchor_le_of_tag_le q hR (physicalEdge q y hy).succ (Sum.inr v)
        (by change edgeTag q y+1≤edgeTag q (Sum.inr v);omega)
      exact (not_le_of_gt hvbound) ha
    omega
  have hedge : physicalEdge q (Sum.inr v) hvn=physicalEdge q y hy := Fin.ext htag
  obtain ⟨b,hab,hb1,hbp,hbu⟩ := bounded_event_physical_spec q hR y w hy hb.1 hbound
  obtain ⟨d,hvd,hd1,hdp,hdu⟩ := bounded_event_physical_spec q hR (Sum.inr v) w hvn hv1
    (by rw [hedge];exact hbound)
  rw [hedge] at hdp
  have hdb : d=b := edge_parameter_unique q hR (physicalEdge q y hy) d b (hdp.symm.trans hbp)
  have hav : parameter q y<visitParameter q v := by
    rcases (event_lt_iff q hR.noTriple _ _).mp hv0 with h|h
    · exact False.elim ((ne_of_lt h) htag.symm)
    · exact h.2
  have hvb : visitParameter q v<b := by simpa only [hdb] using hvd
  have hxpoint : eventPoint q x = affinePoint (q (physicalEdge q y hy).castSucc)
      (q (physicalEdge q y hy).succ) (parameter q y) := by
    rw [← pairing_point q S x]
    exact eventPoint_affine q y hy
  have hvpoint := eventPoint_affine q (Sum.inr v) hvn
  rw [hedge] at hvpoint
  refine ⟨(visitParameter q v-parameter q y)/(b-parameter q y),
    div_pos (sub_pos.mpr hav) (sub_pos.mpr hab),
    (div_lt_one (sub_pos.mpr hab)).mpr (by linarith),?_⟩
  change eventPoint q (Sum.inr v)=affinePoint (eventPoint q x) (eventPoint q w) _
  rw [hxpoint,hbp,affinePoint_subsegment,hvpoint]
  congr 1
  change visitParameter q v = parameter q y + (b-parameter q y)*((visitParameter q v-parameter q y)/(b-parameter q y))
  field_simp [ne_of_gt (sub_pos.mpr hab)] <;> ring

end DirectGLSSW.ActiveArc.PhysicalSegments
