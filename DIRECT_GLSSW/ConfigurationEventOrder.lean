import ConfigurationCrossingStability
import DirectGLSSW.PolygonEvents

set_option autoImplicit false
namespace DirectGLSSW.ConfigurationEventOrder
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationCrossingStability
open scoped Topology
noncomputable section

/-- Keep the actual crossing edge-pair label and the Boolean visit label. -/
def visitEquiv {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) :
    CrossingVisit P ≃ CrossingVisit Q :=
  Equiv.prodCongr (labelEquiv P Q h) (Equiv.refl Bool)

/-- Anchors retain their vertex labels; visits retain their real edge-pair/side labels. -/
def eventEquiv {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) :
    PolygonEvent P ≃ PolygonEvent Q :=
  Equiv.sumCongr (Equiv.refl (Fin n)) (visitEquiv P Q h)

theorem visitEquiv_labels {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) (v : CrossingVisit P) :
    (visitEquiv P Q h v).1.val = v.1.val ∧ (visitEquiv P Q h v).2 = v.2 :=
  ⟨rfl,rfl⟩

theorem visitEquiv_flip {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) (v : CrossingVisit P) :
    visitEquiv P Q h (crossingVisitFlip P v) = crossingVisitFlip Q (visitEquiv P Q h v) := rfl

theorem eventEquiv_anchor {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) (a : Fin n) :
    eventEquiv P Q h (.inl a) = .inl a := rfl

theorem eventEquiv_visit {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) (c : PolygonCrossing P) (b : Bool) :
    eventEquiv P Q h (.inr (c,b)) = .inr (labelEquiv P Q h c,b) := rfl

theorem eventEquiv_edge {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f) (x : PolygonEvent P) :
    polygonEventEdge Q (eventEquiv P Q h x) = polygonEventEdge P x := by
  cases x <;> rfl

/-- A rational expression with a fixed original event label; it is defined even
outside the incidence-stable neighborhood. -/
def rationalEventParameter {n : ℕ} {P : Configuration n} (Q : Configuration n) : PolygonEvent P → ℝ
  | .inl _ => 0
  | .inr (c,b) => if b then rightParameter Q c.val.1 c.val.2 else leftParameter Q c.val.1 c.val.2

theorem rationalEventParameter_self {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P)
    (x : PolygonEvent P) : rationalEventParameter P x = polygonEventParameter P x := by
  cases x with
  | inl a => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    have h := crossingParameters_eq_of_g1 hP.size_ge_three P hP.g1 c
    cases b
    · exact h.1.symm
    · exact h.2.symm

theorem continuousAt_rationalEventParameter {n : ℕ} (P : Configuration n)
    (hP : CyclicGeneric P) (x : PolygonEvent P) :
    ContinuousAt (fun Q : Configuration n => rationalEventParameter Q x) P := by
  cases x with
  | inl a => exact continuousAt_const
  | inr v =>
    rcases v with ⟨c,b⟩
    have hD : denominator P c.val.1 c.val.2 ≠ 0 := crossing_transverse hP.size_ge_three P hP.g1 c
    cases b
    · exact continuousAt_leftParameter P c.val.1 c.val.2 hD
    · exact continuousAt_rightParameter P c.val.1 c.val.2 hD

theorem eventEquiv_parameter {n : ℕ} (P Q : Configuration n)
    (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f)
    (hD : ∀ c : PolygonCrossing P, denominator Q c.val.1 c.val.2 ≠ 0)
    (x : PolygonEvent P) :
    polygonEventParameter Q (eventEquiv P Q h x) = rationalEventParameter Q x := by
  cases x with
  | inl a => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    have hp := crossingParameters_eq Q (labelEquiv P Q h c) (hD c)
    cases b
    · exact hp.1
    · exact hp.2

private theorem eventually_lt_iff {n : ℕ} (P : Configuration n)
    (f g : Configuration n → ℝ) (hf : ContinuousAt f P) (hg : ContinuousAt g P)
    (hne : f P ≠ g P) : ∀ᶠ Q in 𝓝 P, (f Q < g Q ↔ f P < g P) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpos : ∀ᶠ Q in 𝓝 P, 0 < g Q-f Q :=
      (hg.sub hf).eventually (Ioi_mem_nhds (sub_pos.mpr hlt))
    filter_upwards [hpos] with Q hQ
    exact iff_of_true (sub_pos.mp hQ) hlt
  · have hpos : ∀ᶠ Q in 𝓝 P, 0 < f Q-g Q :=
      (hf.sub hg).eventually (Ioi_mem_nhds (sub_pos.mpr hgt))
    filter_upwards [hpos] with Q hQ
    exact iff_of_false (not_lt.mpr (le_of_lt (sub_pos.mp hQ))) (not_lt.mpr (le_of_lt hgt))

/-- G2 separates parameters of distinct events on the same edge. The finite
intersection here includes every ordered pair, with anchors as parameter zero. -/
theorem eventually_sameEdge_parameter_order {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P) :
    ∀ᶠ Q in 𝓝 P, ∀ x y : PolygonEvent P,
      polygonEventEdge P x = polygonEventEdge P y →
      (rationalEventParameter Q x < rationalEventParameter Q y ↔
        polygonEventParameter P x < polygonEventParameter P y) := by
  classical
  apply Filter.eventually_all.mpr
  intro x
  apply Filter.eventually_all.mpr
  intro y
  by_cases he : polygonEventEdge P x = polygonEventEdge P y
  · by_cases hxy : x = y
    · subst y
      exact Filter.Eventually.of_forall (fun Q _ => by simp)
    · have hne : polygonEventParameter P x ≠ polygonEventParameter P y := by
        intro hp
        exact hxy (polygonEventKey_injective P hP.g2 (Prod.ext he hp))
      have hrne : rationalEventParameter P x ≠ rationalEventParameter P y := by
        simpa only [rationalEventParameter_self P hP] using hne
      have h := eventually_lt_iff P (fun Q => rationalEventParameter Q x)
        (fun Q => rationalEventParameter Q y)
        (continuousAt_rationalEventParameter P hP x) (continuousAt_rationalEventParameter P hP y) hrne
      filter_upwards [h] with Q hQ
      intro _
      simpa only [rationalEventParameter_self P hP] using hQ
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (he h))

/-- One positive coordinate radius preserves all actual edge/parameter comparisons.
There is no assumed event-order stability. -/
theorem exists_orderBox {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ ∃ hBox : StableBox P η,
      (∀ Q, CoordClose η Q P → CyclicGeneric Q) ∧
      ∀ Q (hnear : CoordClose η Q P) (x y : PolygonEvent P),
        polygonEventEdge P x = polygonEventEdge P y →
        (polygonEventParameter Q (eventEquiv P Q (hBox Q hnear).1 x) <
          polygonEventParameter Q (eventEquiv P Q (hBox Q hnear).1 y) ↔
          polygonEventParameter P x < polygonEventParameter P y) := by
  obtain ⟨ηB,hηB,hB,hG⟩ := exists_stableBox P hP
  obtain ⟨ηO,hηO,hO⟩ := exists_coordBox_subset P _ (eventually_sameEdge_parameter_order P hP)
  let η := min ηB ηO
  have hsmallB : ∀ Q, CoordClose η Q P → CoordClose ηB Q P := by
    intro Q hQ i
    exact ⟨lt_of_lt_of_le (hQ i).1 (min_le_left _ _),lt_of_lt_of_le (hQ i).2 (min_le_left _ _)⟩
  have hsmallO : ∀ Q, CoordClose η Q P → CoordClose ηO Q P := by
    intro Q hQ i
    exact ⟨lt_of_lt_of_le (hQ i).1 (min_le_right _ _),lt_of_lt_of_le (hQ i).2 (min_le_right _ _)⟩
  have hBox : StableBox P η := fun Q hQ => hB Q (hsmallB Q hQ)
  refine ⟨η,lt_min hηB hηO,hBox,fun Q hQ => hG Q (hsmallB Q hQ),?_⟩
  intro Q hnear x y he
  rw [eventEquiv_parameter P Q (hBox Q hnear).1 (hBox Q hnear).2 x,
    eventEquiv_parameter P Q (hBox Q hnear).1 (hBox Q hnear).2 y]
  exact hO Q (hsmallO Q hnear) x y he

/-- Every original G1–G2 configuration has a coordinate neighborhood with the
actual traversal order preserved under the exact anchor/edge-pair/Boolean labels.
The equality of underlying equivalences also fixes the visit-flip involution. -/
theorem exists_configuration_event_orderIso {n : ℕ} (P : Configuration n) (hP : CyclicGeneric P) :
    ∃ η : ℝ, 0 < η ∧ ∃ hBox : StableBox P η,
      ∀ Q (hnear : CoordClose η Q P), ∃ hQ : CyclicGeneric Q,
        letI := polygonEventOrder P hP.g2
        letI := polygonEventOrder Q hQ.g2
        ∃ F : PolygonEvent P ≃o PolygonEvent Q,
          F.toEquiv = eventEquiv P Q (hBox Q hnear).1 := by
  obtain ⟨η,hη,hBox,hgeneric,horder⟩ := exists_orderBox P hP
  refine ⟨η,hη,hBox,?_⟩
  intro Q hnear
  let hQ := hgeneric Q hnear
  refine ⟨hQ,?_⟩
  letI := polygonEventOrder P hP.g2
  letI := polygonEventOrder Q hQ.g2
  have hlt : ∀ x y : PolygonEvent P,
      eventEquiv P Q (hBox Q hnear).1 x < eventEquiv P Q (hBox Q hnear).1 y ↔ x < y := by
    intro x y
    rw [polygonEvent_lt_iff Q hQ.g2,polygonEvent_lt_iff P hP.g2,
      eventEquiv_edge,eventEquiv_edge]
    constructor
    · rintro (hl | ⟨he,ht⟩)
      · exact Or.inl hl
      · exact Or.inr ⟨he,(horder Q hnear x y he).mp ht⟩
    · rintro (hl | ⟨he,ht⟩)
      · exact Or.inl hl
      · exact Or.inr ⟨he,(horder Q hnear x y he).mpr ht⟩
  refine ⟨{ toEquiv := eventEquiv P Q (hBox Q hnear).1, map_rel_iff' := ?_ },rfl⟩
  intro x y
  rw [le_iff_lt_or_eq,le_iff_lt_or_eq,hlt]
  exact or_congr Iff.rfl (eventEquiv P Q (hBox Q hnear).1).injective.eq_iff















end
end DirectGLSSW.ConfigurationEventOrder
