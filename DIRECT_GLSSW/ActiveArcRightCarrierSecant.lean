import ActiveArcEventCarrierDomain
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords OpenCarrier

/-- A retained side on the actual right crossing carrier determines an
adjacent transverse endpoint secant. Its parameters and noncoincidence are
produced from physical side geometry and exclusion of the crossing from U. -/
theorem event_right_carrier_secant
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c∉U.val)
    (k : Fin (openCount q hR U.val-1))
    (hkcar : openSideCarrier q hR U.val k=c.val.2) :
    0<k.val ∧ ∃ τ : ℝ,
      eventOpenWord q hR U c k.val = eventOpenWord q hR U c 0 +
        τ • (eventOpenWord q hR U c (k.val+1)-eventOpenWord q hR U c 0) ∧
      planarDet (eventOpenWord q hR U c k.val-eventOpenWord q hR U c (k.val+1))
        (q 1-q 0)≠0 ∧
      τ≠0 ∧ τ≠1 ∧
      eventOpenWord q hR U c 0≠eventOpenWord q hR U c (k.val+1) := by
  have hk0 : 0<k.val := by
    by_contra hn
    have hkz : k.val=0 := by omega
    have he : k=⟨0,by have := open_count_ge_two q hR U.val;omega⟩ := Fin.ext hkz
    have hzero : openSideCarrier q hR U.val k=0 := by
      rw [he]
      exact openSideCarrier_zero q hR U.val
    have hh := congrArg Fin.val (hzero.symm.trans hkcar)
    have hlt := c.property.1
    rw [hc.1] at hlt
    change 0<c.val.2.val at hlt
    change 0=c.val.2.val at hh
    omega
  have hkn : k.val<openCount q hR U.val := by have := k.isLt;omega
  have hkn1 : k.val+1<openCount q hR U.val := by have := k.isLt;omega
  obtain ⟨s,t,hs,hst,ht,hpa,hpb⟩ := openSideCarrier_physical q hR U.val k
  rw [hkcar] at hpa hpb
  have hpa' : eventOpenWord q hR U c k.val=affinePoint (q c.val.2.castSucc) (q c.val.2.succ) s :=
    (eventOpenWord_pos q hR U c k.val hk0 hkn).trans hpa
  have hpb' : eventOpenWord q hR U c (k.val+1)=affinePoint (q c.val.2.castSucc) (q c.val.2.succ) t :=
    (eventOpenWord_pos q hR U c (k.val+1) (by omega) hkn1).trans hpb
  let u := rightParameter q c
  have hcp : crossingPoint q c=affinePoint (q c.val.2.castSucc) (q c.val.2.succ) u :=
    (rightParameter_spec q c).2.2
  have hne : eventOpenWord q hR U c 0≠eventOpenWord q hR U c (k.val+1) := by
    rw [eventOpenWord_zero,eventOpenWord_pos q hR U c (k.val+1) (by omega) hkn1]
    exact unselected_crossingPoint_ne_vertex q hR U.val c hu (start q) ⟨k.val+1,hkn1⟩
  have htu : t≠u := by
    intro hh
    apply hne
    rw [eventOpenWord_zero,hpb',hh,hcp]
  let τ := (s-u)/(t-u)
  have hcol : eventOpenWord q hR U c k.val=eventOpenWord q hR U c 0+
      τ • (eventOpenWord q hR U c (k.val+1)-eventOpenWord q hR U c 0) := by
    rw [hpa',hpb',eventOpenWord_zero,hcp]
    ext <;> simp only [τ,affinePoint,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> field_simp [sub_ne_zero.mpr htu] <;> ring
  have hdet := hR.transverse c.val.1 c.val.2 (ne_of_lt c.property.1)
    (crossingPoint q c) (crossingPoint_mem q c).1 (crossingPoint_mem q c).2
  rw [hc.1] at hdet
  have he : planarDet (eventOpenWord q hR U c k.val-eventOpenWord q hR U c (k.val+1))
      (q 1-q 0)=(t-s)*planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc) := by
    rw [hpa',hpb']
    simp only [planarDet,affinePoint,Prod.fst_sub,Prod.snd_sub]
    ring
  have htrans : planarDet (eventOpenWord q hR U c k.val-eventOpenWord q hR U c (k.val+1))
      (q 1-q 0)≠0 := by
    rw [he]
    exact mul_ne_zero (ne_of_gt (sub_pos.mpr hst)) hdet
  have ht0 := eventOpenWord_parameter_ne_zero q hR c U hu k.val (k.val+1) hk0 hkn τ hcol
  have ht1 : τ≠1 := by
    intro hh
    have hp : eventOpenWord q hR U c k.val=eventOpenWord q hR U c (k.val+1) := by
      simpa [hh] using hcol
    apply htrans
    rw [hp,sub_self]
    simp [planarDet]
  exact ⟨hk0,τ,hcol,htrans,ht0,ht1,hne⟩

end DirectGLSSW.ActiveArc.Primitive
