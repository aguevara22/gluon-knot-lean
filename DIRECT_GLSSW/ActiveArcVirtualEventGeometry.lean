import ActiveArcUnselectedFirstInterior
import DirectGLSSW.EndpointGeometricMatrix

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords

/-- The literal retained open word with its first endpoint at the unselected
crossing. Positive indices are exactly the existing rooted open word. -/
def eventOpenWord {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (U : Support q hR) (c : Crossing q) : ℕ → PlanarPoint ℝ :=
  fun i => if i = 0 then crossingPoint q c else
    rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val) i

@[simp] theorem eventOpenWord_zero {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (U : Support q hR) (c : Crossing q) :
    eventOpenWord q hR U c 0 = crossingPoint q c := by
  rfl

theorem eventOpenWord_pos {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (U : Support q hR) (c : Crossing q)
    (i : ℕ) (hi : 0 < i) (hin : i < openCount q hR U.val) :
    eventOpenWord q hR U c i = OpenVertex q hR U ⟨i,hin⟩ := by
  rw [eventOpenWord,if_neg (Nat.ne_of_gt hi)]
  exact openCurrent_word q hR U i hin

theorem eventOpenWord_parameter_ne_zero {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (U : Support q hR) (hu : c ∉ U.val)
    (k j : ℕ) (hk : 0 < k) (hkn : k < openCount q hR U.val) (τ : ℝ)
    (hcol : eventOpenWord q hR U c k = eventOpenWord q hR U c 0 +
      τ • (eventOpenWord q hR U c j - eventOpenWord q hR U c 0)) : τ ≠ 0 := by
  intro hz
  rw [hz,zero_smul,add_zero,eventOpenWord_zero,eventOpenWord_pos q hR U c k hk hkn] at hcol
  exact unselected_crossingPoint_ne_vertex q hR U.val c hu (start q) ⟨k,hkn⟩ hcol.symm

/-- A transverse endpoint secant event cannot involve the first retained
vertex: that vertex and the crossing lie on the actual direction of motion. -/
theorem eventOpenWord_transverse_index_ne_one {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val)
    (k j : ℕ) (hk : 0 < k) (hkn : k < openCount q hR U.val) (τ : ℝ)
    (hcol : eventOpenWord q hR U c k = eventOpenWord q hR U c 0 +
      τ • (eventOpenWord q hR U c j - eventOpenWord q hR U c 0))
    (htrans : planarDet (eventOpenWord q hR U c k - eventOpenWord q hR U c j)
      (q 1 - q 0) ≠ 0) : k ≠ 1 := by
  have ht := eventOpenWord_parameter_ne_zero q hR c U hu k j hk hkn τ hcol
  intro hk1
  subst k
  let W := eventOpenWord q hR U c
  let v := q 1 - q 0
  obtain ⟨s,hcs,hs,hpoint⟩ := openVertex_one_after_unselected_first q hR c hc U hu
  have hcp := (leftParameter_spec q c).2.2
  rw [hc.1] at hcp
  have hcp' : crossingPoint q c = affinePoint (q 0) (q 1) (leftParameter q c) := by
    simpa using hcp
  have hz : planarDet (W 1 - W 0) v = 0 := by
    dsimp [W,v]
    rw [eventOpenWord_pos q hR U c 1 (by omega) hkn,hpoint,hcp']
    simp only [planarDet,affinePoint,Prod.fst_sub,Prod.snd_sub]
    ring
  have hrel : planarDet (W 1 - W 0) v = τ * planarDet (W j - W 0) v := by
    change W 1 = W 0 + τ • (W j - W 0) at hcol
    rw [hcol]
    dsimp [planarDet]
    ring
  have hzj : planarDet (W j - W 0) v = 0 :=
    (mul_eq_zero.mp (hrel.symm.trans hz)).resolve_left ht
  apply htrans
  change planarDet (W 1 - W j) v = 0
  calc
    _ = planarDet (W 1 - W 0) v - planarDet (W j - W 0) v := by
      simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
      ring
    _ = 0 := by rw [hz,hzj,sub_self]

/-- At a negative-parameter event, adjacent retained vertices would contain
the crossing in their actual side. Incompatible supports exclude this. -/
theorem eventOpenWord_negative_event_not_adjacent {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val)
    (hbad : ∃ d ∈ U.val, ¬ Split.Compatible (a:=n) (b:=0) q hR c d)
    (k j : ℕ) (hk : 0 < k) (hkj : k < j) (hjn : j < openCount q hR U.val)
    (τ : ℝ) (hτ : τ < 0)
    (hcol : eventOpenWord q hR U c k = eventOpenWord q hR U c 0 +
      τ • (eventOpenWord q hR U c j - eventOpenWord q hR U c 0)) : j ≠ k+1 := by
  intro hadj
  subst j
  let W := eventOpenWord q hR U c
  have hd : 0 < 1-τ := by linarith
  have ht0 : 0 < -τ/(1-τ) := div_pos (neg_pos.mpr hτ) hd
  have ht1 : -τ/(1-τ) < 1 := (div_lt_one hd).mpr (by linarith)
  have hp : W 0 = affinePoint (W k) (W (k+1)) (-τ/(1-τ)) := by
    have hx := congrArg Prod.fst hcol
    have hy := congrArg Prod.snd hcol
    change (W k).1 = (W 0).1 + τ*((W (k+1)).1-(W 0).1) at hx
    change (W k).2 = (W 0).2 + τ*((W (k+1)).2-(W 0).2) at hy
    apply Prod.ext
    · simp only [affinePoint]
      field_simp
      nlinarith [hx]
    · simp only [affinePoint]
      field_simp
      nlinarith [hy]
  have hkn : k < openCount q hR U.val := by omega
  have hp' : crossingPoint q c = affinePoint
      (OpenVertex q hR U ⟨k,hkn⟩) (OpenVertex q hR U ⟨k+1,hjn⟩) (-τ/(1-τ)) := by
    simpa only [W,eventOpenWord_zero,eventOpenWord_pos q hR U c k hk hkn,
      eventOpenWord_pos q hR U c (k+1) (by omega) hjn] using hp
  exact Split.incompatible_first_crossing_not_later_side q hR c hc U hu hbad
    ⟨k,hkn⟩ hk hjn (-τ/(1-τ)) ht0 ht1 hp'

end DirectGLSSW.ActiveArc.Primitive
