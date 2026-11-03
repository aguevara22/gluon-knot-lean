import ActiveArcWordCurrentTransport
import ActiveArcPhysicalEventMotion
import ActiveArcBeforeFirstWords
import ActiveArcAfterFirstWords
import ActiveArcAfterFirstSupports

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)

include hc in
private theorem affinePoint_event (t : ℝ) :
    affinePoint (q 0) (q 1) t = crossingPoint q c +
      (t-leftParameter q c) • (q 1-q 0) := by
  have h := moveStart_event_plus q c hc.1 (t-leftParameter q c)
  rw [show leftParameter q c+(t-leftParameter q c)=t by ring,moveStart_zero] at h
  exact h

/-- Before the first crossing, the actual transported support current is
exactly the current of the physical endpoint curve. -/
theorem before_first_openCurrent_eq_event (t : ℝ) (ht0 : 0≤t)
    (htc : t<leftParameter q c) (U : Support q hR) :
    let hM := before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc
    let V := (BeforeFirst.supportEquiv q hR c hc t ht0 htc).symm U
    openCurrent (moveStart q t) hM V =
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c)
          (q 1-q 0) (t-leftParameter q c))) 0 (openCount q hR U.val-1) := by
  let hM := before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc
  let V := (BeforeFirst.supportEquiv q hR c hc t ht0 htc).symm U
  change openCurrent (moveStart q t) hM V = _
  apply openCurrent_eq_event_of_word q hR U c (moveStart q t) hM V
  have hw := BeforeFirst.open_word q hR c hc t ht0 htc V.val
  have hv : BeforeFirst.selectionEquiv q hR c hc t ht0 htc V.val = U.val :=
    congrArg Subtype.val ((BeforeFirst.supportEquiv q hR c hc t ht0 htc).apply_symm_apply U)
  rw [hv,affinePoint_event q c hc t] at hw
  exact hw

/-- After the first crossing, the actual support inverse excludes precisely
the removed crossing. Survival, nonalternation and word matching are proved
by the predecessor equivalence and word transport. -/
theorem after_first_openCurrent_eq_event (t : ℝ)
    (hct : leftParameter q c<t) (htb : t<afterBound q c)
    (U : {U : Support q hR // c∉U.val}) :
    let ht0 : 0≤t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    let V := (Surviving.afterFirstSupportEquiv q hR c hc t hct htb).symm U
    openCurrent (moveStart q t) hM V =
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U.val c)
          (q 1-q 0) (t-leftParameter q c))) 0 (openCount q hR U.val.val-1) := by
  let ht0 : 0≤t := (lt_trans (leftParameter_spec q c).1 hct).le
  let ht1 : t<1 := lt_of_lt_of_le htb (afterBound_le_one q c)
  let hM : Regular (moveStart q t) :=
    (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
  let V := (Surviving.afterFirstSupportEquiv q hR c hc t hct htb).symm U
  change openCurrent (moveStart q t) hM V = _
  apply openCurrent_eq_event_of_word q hR U.val c (moveStart q t) hM V
  have hw := Surviving.after_first_open_word q hR c hc t hct htb U.val.val U.property
  have hv : V.val = Surviving.movingSelection q t ht0 ht1 U.val.val :=
    Surviving.afterFirstSupportEquiv_symm_val q hR c hc t hct htb U
  change List.ofFn (vertex (moveStart q t) hM V.val (start (moveStart q t))) = _
  rw [hv]
  simpa only [affinePoint_event q c hc t] using hw



end DirectGLSSW.ActiveArc.Primitive
