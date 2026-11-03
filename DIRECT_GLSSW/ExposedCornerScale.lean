import DirectGLSSW.TruncationCommonScale
import DirectGLSSW.TruncationCommonRadius
import SupportingTruncationExposure
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceTruncationSupport

open DirectGLSSW DirectGLSSW.TruncationDirection DirectGLSSW.TruncationCommonScale
open DirectGLSSW.TruncationCommonRadius DirectGLSSW.ExposedOpenPrimitive

private theorem planarDet_scale_sub (s : ℝ) (D U X : PlanarPoint ℝ) :
    planarDet (s • D-U) X = s*planarDet D X-planarDet U X := by
  simp [planarDet,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- A strict exposed-corner normal lies in the positive cone of the two
incident truncation normals at a left turn. The resulting open scale interval
keeps every original vertex strictly to the same side of the short edge. -/
theorem exists_open_strict_support_scale {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a))
    (v : PlanarPoint ℝ)
    (hexposed : ∀ i : Fin n, i ≠ a → 0 < planarDet v (q i-q a)) :
    ∃ lo hi : ℝ, lo < hi ∧ 0 < lo ∧
      ∀ s : ℝ, lo < s → s < hi →
        ∀ i : Fin n, i ≠ a →
          0 < planarDet (s • (q (cyclicSuccessor a)-q a)-(q p-q a)) (q i-q a) := by
  have hna : cyclicSuccessor a ≠ a :=
    cyclicSuccessor_ne_self (by have := hq.size_ge_three; omega) a
  have hpa : p ≠ a := by
    intro h
    subst p
    exact hna hp
  let U : PlanarPoint ℝ := q p-q a
  let D : PlanarPoint ℝ := q (cyclicSuccessor a)-q a
  have hturn' : 0 < planarDet D U := by
    have hh : planarDet (q a-q p) D = planarDet D U := by
      simp [U,D,planarDet]
      ring
    rw [← hh]
    exact hturn
  have hvU : 0 < planarDet v U := by
    simpa [U] using hexposed p hpa
  have hvD : 0 < planarDet v D := by
    simpa [D] using hexposed (cyclicSuccessor a) hna
  obtain ⟨s0,hs0,hsupport0⟩ :=
    positive_scale_of_strict_support (q a) (q p) (q (cyclicSuccessor a)) v
      hturn hvU hvD
  have hstrict0 (i : Fin n) (hi : i ≠ a) :
      0 < planarDet (s0 • D-U) (q i-q a) := by
    simpa [D,U] using hsupport0 (q i) (hexposed i hi)
  let r : Fin n → ℝ := fun i =>
    if hi : i = a then 1 else
      planarDet (s0 • D-U) (q i-q a) /
        (2 * (|planarDet D (q i-q a)|+1))
  have hr : ∀ i, 0 < r i := by
    intro i
    by_cases hi : i=a
    · simp [r,hi]
    · simpa [r,hi] using div_pos (hstrict0 i hi) (by positivity)
  obtain ⟨δ,hδ,hbound⟩ := exists_positive_common_lower_bound r hr
  have hnear (s : ℝ) (hs : |s-s0| < δ) (i : Fin n) (hi : i ≠ a) :
      0 < planarDet (s • D-U) (q i-q a) := by
    have hgap := lt_of_lt_of_le hs (hbound i)
    have hbase : 0 < planarDet (s0 • D-U) (q i-q a) := hstrict0 i hi
    have hri_eq : r i = planarDet (s0 • D-U) (q i-q a) /
        (2 * (|planarDet D (q i-q a)|+1)) := by simp [r,hi]
    have hsmall := mul_lt_mul_of_pos_right hgap
      (show 0 < |planarDet D (q i-q a)|+1 by positivity)
    have hhalf : r i * (|planarDet D (q i-q a)|+1) =
        planarDet (s0 • D-U) (q i-q a) / 2 := by
      rw [hri_eq]
      have hpos : 2 * (|planarDet D (q i-q a)|+1) ≠ 0 := by positivity
      field_simp [hpos]
      <;> ring
    have hvariation : |(s-s0)*planarDet D (q i-q a)| <
        planarDet (s0 • D-U) (q i-q a) := by
      rw [abs_mul]
      calc
        abs (s-s0)*abs (planarDet D (q i-q a)) ≤
            abs (s-s0)*(abs (planarDet D (q i-q a))+1) := by
          have h1 := abs_nonneg (s-s0)
          have h2 := abs_nonneg (planarDet D (q i-q a))
          nlinarith
        _ < r i*(abs (planarDet D (q i-q a))+1) := by simpa using hsmall
        _ = planarDet (s0 • D-U) (q i-q a)/2 := by simpa using hhalf
        _ < planarDet (s0 • D-U) (q i-q a) := by linarith
    have hlinear : planarDet (s • D-U) (q i-q a) =
        planarDet (s0 • D-U) (q i-q a) +
          (s-s0)*planarDet D (q i-q a) := by
      rw [planarDet_scale_sub,planarDet_scale_sub]
      ring
    rw [hlinear]
    have habs := abs_lt.mp hvariation
    linarith
  let δ' := min δ s0
  have hδ' : 0 < δ' := lt_min hδ hs0
  let lo := s0-δ'/2
  let hi := s0+δ'/2
  have hlohi : lo < hi := by dsimp [lo,hi]; linarith
  have hlo : 0 < lo := by
    dsimp [lo]
    have hle := min_le_right δ s0
    linarith
  refine ⟨lo,hi,hlohi,hlo,?_⟩
  intro s hslo hshi i hiA
  have hsabs : |s-s0| < δ := by
    rw [abs_lt]
    have hle : δ' ≤ δ := min_le_left δ s0
    constructor <;> dsimp [lo,hi] at hslo hshi ⊢ <;> linarith [hδ,hle]
  simpa [D,U] using hnear s hsabs i hiA

/-- Choose the short-edge scale inside the actual strict-support cone while
avoiding every source event line; these event points include all daughter
vertices used by the finite first-return construction. -/
theorem exists_exposed_corner_generic_support_scale {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a))
    (v : PlanarPoint ℝ)
    (hexposed : ∀ i : Fin n, i ≠ a → 0 < planarDet v (q i-q a)) :
    ∃ scale : ℝ, 0 < scale ∧
      (∀ i : Fin n, i ≠ a →
        0 < planarDet (scale • (q (cyclicSuccessor a)-q a)-(q p-q a)) (q i-q a)) ∧
      (∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
        planarDet (scale • (q (cyclicSuccessor a)-q a)-(q p-q a))
          (polygonEventPoint q e-q a) ≠ 0) := by
  obtain ⟨lo,hi,hlohi,hlo,hsupport⟩ :=
    exists_open_strict_support_scale q hq a p hp hturn v hexposed
  let U : PlanarPoint ℝ := q p-q a
  let D : PlanarPoint ℝ := q (cyclicSuccessor a)-q a
  let X : PolygonEvent q → PlanarPoint ℝ := fun e => polygonEventPoint q e-q a
  let bad : Finset ℝ := Finset.univ.image fun e =>
    planarDet U (X e) / planarDet D (X e)
  obtain ⟨scale,hscaleI,hscaleBad⟩ :=
    (Set.Ioo_infinite hlohi).exists_not_mem_finset bad
  refine ⟨scale,lt_trans hlo hscaleI.1,?_,?_⟩
  · intro i hi
    exact hsupport scale hscaleI.1 hscaleI.2 i hi
  · intro e he
    by_cases hD : planarDet D (X e)=0
    · have hU : planarDet U (X e) ≠ 0 := by
        exact planarDet_left_ne_zero_of_pair_ne_zero U D (X e)
          (by
            have hh : planarDet U D = -planarDet (q a-q p) D := by
              simp [U,D,planarDet]
              ring
            rw [hh]
            exact neg_ne_zero.mpr (ne_of_gt hturn))
          (sub_ne_zero.mpr he) hD
      have hcalc : planarDet (scale • D-U) (X e) =
          scale*planarDet D (X e)-planarDet U (X e) :=
        planarDet_scale_sub scale D U (X e)
      have hzero : planarDet (scale • D-U) (X e) = -planarDet U (X e) := by
        rw [hcalc,hD]
        ring
      have hnonzero : planarDet (scale • D-U) (X e) ≠ 0 := by
        rw [hzero]
        exact neg_ne_zero.mpr hU
      simpa [D,U,X] using hnonzero
    · intro hz
      have hratio : scale = planarDet U (X e)/planarDet D (X e) := by
        have hcalc : planarDet (scale • D-U) (X e) =
            scale*planarDet D (X e)-planarDet U (X e) :=
          planarDet_scale_sub scale D U (X e)
        rw [hcalc] at hz
        apply (eq_div_iff hD).2
        linarith
      apply hscaleBad
      exact Finset.mem_image.mpr ⟨e,Finset.mem_univ e,hratio.symm⟩

/-- The actual finite truncation is globally exposed on its short edge for all
sufficiently small positive truncation parameters. -/
theorem exists_exposed_corner_small_truncation_leftExposed {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a))
    (v : PlanarPoint ℝ)
    (hexposed : ∀ i : Fin n, i ≠ a → 0 < planarDet v (q i-q a)) :
    ∃ scale : ℝ, 0 < scale ∧
      (∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
        planarDet (scale • (q (cyclicSuccessor a)-q a)-(q p-q a))
          (polygonEventPoint q e-q a) ≠ 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        LeftExposed (truncateCyclicCorner q a p scale ε) a.castSucc := by
  obtain ⟨scale,hscale,hsupport,havoid⟩ :=
    exists_exposed_corner_generic_support_scale q hq a p hp hturn v hexposed
  obtain ⟨δ,hδ,hleft⟩ :=
    exists_small_truncation_leftExposed q a p scale (fun i hi => hsupport i hi)
  exact ⟨scale,hscale,havoid,δ,hδ,hleft⟩





end DirectGLSSW.SourceTruncationSupport
