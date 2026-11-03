import ExtendedReturnEndpointEvents

set_option autoImplicit false

namespace DirectGLSSW.ExtendedReturnEndpointTurns
open DirectGLSSW ExtendedReturnArcGeometry ExtendedReturnEndpointEvents OrderedCapEvents

abbrev Point := PlanarPoint ℝ

private theorem successor_last {n : ℕ} (hn : 3 ≤ n) :
    cyclicSuccessor (lastIndex hn) = zeroIndex hn := by
  apply Fin.ext
  change (n-1+1+0)%n=0
  have h : n-1+1=n := by omega
  rw [h]
  simp

private theorem successor_zero {n : ℕ} (hn : 3 ≤ n) :
    cyclicSuccessor (zeroIndex hn) = firstIndex hn := by
  exact return_successor_eq (zeroIndex hn) (by change 0+1<n; omega)

private theorem successor_penultimate {n : ℕ} (hn : 3 ≤ n) :
    cyclicSuccessor (penultimateIndex hn) = lastIndex hn := by
  rw [return_successor_eq _ (by change n-2+1<n; omega)]
  apply Fin.ext
  change n-2+1=n-1
  omega

/-- Cartesian turns use the incoming tangent followed by the outgoing tangent.
The chosen closing edge is last→zero, hence both determinants have a minus sign. -/
theorem endpoint_turn_determinants {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0) :
    planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) =
      -((P (lastIndex hn)).1-(P (zeroIndex hn)).1)*(P (firstIndex hn)).2 ∧
    planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) =
      -((P (lastIndex hn)).1-(P (zeroIndex hn)).1)*(P (penultimateIndex hn)).2 := by
  constructor <;> simp [cyclicTangent, successor_last, successor_zero, successor_penultimate,
    planarDet, hU, hV] <;> ring

private theorem scalarSignValue_negative_mul (a x : ℝ) (ha : a < 0) :
    scalarSignValue (a*x) = -scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hm := mul_pos_of_neg_of_neg ha hx
    simp [scalarSignValue, ne_of_lt hx, ne_of_gt hm, hx, not_lt_of_gt hm]
  · subst x
    simp [scalarSignValue]
  · have hm := mul_neg_of_neg_of_pos ha hx
    simp [scalarSignValue, ne_of_gt hx, ne_of_lt hm, not_lt_of_gt hx, hm]

/-- The source's two Cartesian endpoint-turn signs, for the leftward closing edge. -/
theorem endpoint_turn_signs {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1) :
    scalarSignValue (planarDet (cyclicTangent P (lastIndex hn))
      (cyclicTangent P (zeroIndex hn))) = -scalarSignValue (P (firstIndex hn)).2 ∧
    scalarSignValue (planarDet (cyclicTangent P (penultimateIndex hn))
      (cyclicTangent P (lastIndex hn))) = -scalarSignValue (P (penultimateIndex hn)).2 := by
  have h := endpoint_turn_determinants hn P hU hV
  rw [h.1,h.2]
  exact ⟨scalarSignValue_negative_mul _ _ (neg_neg_of_pos (sub_pos.mpr hleft)),
    scalarSignValue_negative_mul _ _ (neg_neg_of_pos (sub_pos.mpr hleft))⟩

private theorem scalarSignValue_opposite_iff_mul_neg (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    scalarSignValue x = -scalarSignValue y ↔ x*y<0 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy
  · have hm := mul_pos_of_neg_of_neg hx hy
    norm_num [scalarSignValue, ne_of_lt hx, ne_of_lt hy, hx, hy, not_lt_of_gt hm]
  · have hm := mul_neg_of_neg_of_pos hx hy
    norm_num [scalarSignValue, ne_of_lt hx, ne_of_gt hy, hx, not_lt_of_gt hy, hm]
  · have hm := mul_neg_of_pos_of_neg hx hy
    norm_num [scalarSignValue, ne_of_gt hx, ne_of_lt hy, not_lt_of_gt hx, hy, hm]
  · have hm := mul_pos hx hy
    norm_num [scalarSignValue, ne_of_gt hx, ne_of_gt hy, not_lt_of_gt hx,
      not_lt_of_gt hy, not_lt_of_gt hm]

/-- On G1, the negative-product predicate is exactly the source's opposite nonzero turns. -/
theorem opposite_endpoint_turns_iff_signs {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) :
    planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) *
      planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) < 0 ↔
    scalarSignValue (planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn))) =
      -scalarSignValue (planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn))) := by
  have hu := cyclic_turn_det_ne_zero hn P hP (lastIndex hn)
  rw [successor_last] at hu
  have hv := cyclic_turn_det_ne_zero hn P hP (penultimateIndex hn)
  rw [successor_penultimate] at hv
  exact (scalarSignValue_opposite_iff_mul_neg _ _ hu hv).symm

theorem endpoint_height_signs_of_opposite_turns {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hturn : planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) *
      planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) < 0) :
    scalarSignValue (P (firstIndex hn)).2 = -scalarSignValue (P (penultimateIndex hn)).2 := by
  have ho := (opposite_endpoint_turns_iff_signs hn P hP).mp hturn
  have hs := endpoint_turn_signs hn P hU hV hleft
  rw [hs.1,hs.2] at ho
  linarith

/-- The actual ordered endpoint events have equal signs because the original
Cartesian turns are opposite; no sign-equality field is assumed. -/
theorem endpoint_events_equal_sign {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hturn : planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) *
      planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) < 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cU cV : EventIndex (extendedArc hn P ε) n,
      eventTime (extendedArc hn P ε) n cU = 0 ∧
      eventTime (extendedArc hn P ε) n cV = (P (lastIndex hn)).1-(P (zeroIndex hn)).1 ∧
      eventPair (extendedArc hn P ε) n cU = (1,2) ∧
      eventPair (extendedArc hn P ε) n cV = (n-1,n) ∧ cU<cV ∧
      eventSign (extendedArc hn P ε) n cU = eventSign (extendedArc hn P ε) n cV := by
  obtain ⟨cU,cV,htU,htV,hpU,hpV,horder,hsU,hsV⟩ := endpoint_events hn P hP hU hV hleft ε hε
  refine ⟨cU,cV,htU,htV,hpU,hpV,horder,?_⟩
  rw [hsU,hsV]
  exact endpoint_height_signs_of_opposite_turns hn P hP hU hV hleft hturn

/-- The equality applies to any ordered indices at the endpoint times. -/
theorem endpoint_event_signs_equal_of_times {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hturn : planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) *
      planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) < 0)
    (ε : ℝ) (hε : 0 < ε) (cU cV : EventIndex (extendedArc hn P ε) n)
    (htU : eventTime (extendedArc hn P ε) n cU = 0)
    (htV : eventTime (extendedArc hn P ε) n cV = (P (lastIndex hn)).1-(P (zeroIndex hn)).1) :
    eventSign (extendedArc hn P ε) n cU = eventSign (extendedArc hn P ε) n cV := by
  obtain ⟨dU,dV,hdU,hdV,_,_,_,heq⟩ := endpoint_events_equal_sign hn P hP hU hV hleft hturn ε hε
  have hUeq := (eventTime_strictMono (extendedArc hn P ε) n).injective (htU.trans hdU.symm)
  have hVeq := (eventTime_strictMono (extendedArc hn P ε) n).injective (htV.trans hdV.symm)
  simpa only [hUeq,hVeq] using heq












end DirectGLSSW.ExtendedReturnEndpointTurns
