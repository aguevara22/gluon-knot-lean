import ChamberContract.Contract
import GeminiChamber.StateSumConstancy
import CrossingIncidenceNeighborhood
import LabelledCrossingContinuity
import ConfigurationEventLocality
import CrossingOrientationLocality
import OriginalLeftTurnLocality
import UniformDaughterSupportLocality
import SharpDaughterRotationLocality
import SharpDaughterSignedIsoOfOrientation

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical Topology
noncomputable section

namespace DirectGLSSW.GeminiChamber

open DirectGLSSW
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW.HOMFLY.SharpDaughterRotation
open DirectGLSSW.HOMFLY.SharpDaughterRotationLocality
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.LocalCrossingTransport
open DirectGLSSW.LocalSupportConjugacy
open DirectGLSSW.UniformDaughterSupportLocality
open DirectGLSSW.CrossingRationalParameters
open DirectGLSSW.CrossingIncidenceNeighborhood
open DirectGLSSW.LabelledCrossingContinuity
open DirectGLSSW.ConfigurationEventLocality
open DirectGLSSW.CrossingOrientationLocality
open DirectGLSSW.OriginalLeftTurnLocality
open Filter Topology

/-!
# Path-Global Combinatorial Invariance in a Generic Chamber

Using `PreconnectedSpace Time` (`time_preconnectedSpace`), any locally constant
value or proposition along `Time` equals its value at `start`. This module
globalizes crossing incidence, canonical label-preserving crossing transport,
event traversal order, crossing orientation determinant signs, `leftCount`,
`polygonNonalternating`, `uniformDaughterSupport`, `sharpDaughterRotationInteger`,
and the combinatorial/vertex part of `DiagramTransport` along any continuous
path `p : Time → Fin n → Plane` in `CyclicGeneric`.
-/

/-- On the preconnected space `Time`, any predicate `P : Time → Prop` that holds
at `start` and is both locally true and locally false holds for all `t : Time`. -/
theorem forall_time_of_locally_constant (P : Time → Prop)
    (h0 : P start)
    (hpos : ∀ t, P t → ∀ᶠ s in 𝓝 t, P s)
    (hneg : ∀ t, ¬ P t → ∀ᶠ s in 𝓝 t, ¬ P s) :
    ∀ t : Time, P t := by
  letI : PreconnectedSpace Time := time_preconnectedSpace
  let U : Set Time := {t | P t}
  let V : Set Time := {t | ¬ P t}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr hpos
  have hV : IsOpen V := isOpen_iff_mem_nhds.mpr hneg
  have hcov : (Set.univ : Set Time) ⊆ U ∪ V := by
    intro t _
    exact em (P t)
  have hU_nonempty : ((Set.univ : Set Time) ∩ U).Nonempty :=
    ⟨start, Set.mem_univ start, h0⟩
  intro t
  by_contra hnt
  have hV_nonempty : ((Set.univ : Set Time) ∩ V).Nonempty :=
    ⟨t, Set.mem_univ t, hnt⟩
  obtain ⟨z, _, hzU, hzV⟩ :=
    PreconnectedSpace.isPreconnected_univ U V hU hV hcov hU_nonempty hV_nonempty
  exact hzV hzU

/-- Any locally constant function `f : Time → α` (into any sort `α`) is globally
constant along `Time`. -/
theorem locally_constant_eq {α : Sort*} (f : Time → α)
    (h : ∀ t : Time, ∀ᶠ s in 𝓝 t, f s = f t) (t : Time) :
    f t = f start := by
  refine forall_time_of_locally_constant (fun s => f s = f start) rfl ?_ ?_ t
  · intro u hu
    filter_upwards [h u] with s hs
    exact hs.trans hu
  · intro u hnu
    filter_upwards [h u] with s hs hcontr
    exact hnu (hs.symm.trans hcontr)

/-- Any locally constant proposition `P : Time → Prop` is globally equivalent to
`P start`. -/
theorem locally_constant_iff (P : Time → Prop)
    (h : ∀ t : Time, ∀ᶠ s in 𝓝 t, P s ↔ P t) (t : Time) :
    P t ↔ P start :=
  iff_of_eq (locally_constant_eq P (fun u => (h u).mono (fun _ hs => propext hs)) t)

/-- Any two label-preserving crossing equivalences between the same polygons are equal. -/
theorem label_preserving_crossingEquiv_unique {n : ℕ} {P Q : Fin n → Plane}
    (E₁ E₂ : PolygonCrossing P ≃ PolygonCrossing Q)
    (h₁ : ∀ c, (E₁ c).val = c.val)
    (h₂ : ∀ c, (E₂ c).val = c.val) :
    E₁ = E₂ := by
  ext c : 1
  exact Subtype.ext ((h₁ c).trans (h₂ c).symm)

/-- Composition of label-preserving crossing equivalences agrees with any
label-preserving crossing equivalence between the endpoints. -/
theorem label_preserving_crossingEquiv_trans {n : ℕ} {P Q R : Fin n → Plane}
    (E₁ : PolygonCrossing P ≃ PolygonCrossing Q)
    (E₂ : PolygonCrossing Q ≃ PolygonCrossing R)
    (E₃ : PolygonCrossing P ≃ PolygonCrossing R)
    (h₁ : ∀ c, (E₁ c).val = c.val)
    (h₂ : ∀ c, (E₂ c).val = c.val)
    (h₃ : ∀ c, (E₃ c).val = c.val) :
    E₁.trans E₂ = E₃ := by
  refine label_preserving_crossingEquiv_unique (E₁.trans E₂) E₃ ?_ h₃
  intro c
  exact (h₂ (E₁ c)).trans (h₁ c)

theorem label_preserving_crossingEquiv_comp_apply {n : ℕ} {P Q R : Fin n → Plane}
    (E₁ : PolygonCrossing P ≃ PolygonCrossing Q)
    (E₂ : PolygonCrossing Q ≃ PolygonCrossing R)
    (E₃ : PolygonCrossing P ≃ PolygonCrossing R)
    (h₁ : ∀ c, (E₁ c).val = c.val)
    (h₂ : ∀ c, (E₂ c).val = c.val)
    (h₃ : ∀ c, (E₃ c).val = c.val)
    (c : PolygonCrossing P) :
    E₂ (E₁ c) = E₃ c := by
  have h := label_preserving_crossingEquiv_trans E₁ E₂ E₃ h₁ h₂ h₃
  exact Equiv.congr_fun h c

theorem label_preserving_eventMap_comp_apply {n : ℕ} {P Q R : Fin n → Plane}
    (E₁ : PolygonCrossing P ≃ PolygonCrossing Q)
    (E₂ : PolygonCrossing Q ≃ PolygonCrossing R)
    (E₃ : PolygonCrossing P ≃ PolygonCrossing R)
    (h₁ : ∀ c, (E₁ c).val = c.val)
    (h₂ : ∀ c, (E₂ c).val = c.val)
    (h₃ : ∀ c, (E₃ c).val = c.val)
    (x : PolygonEvent P) :
    polygonEventMapEquiv E₂ (polygonEventMapEquiv E₁ x) =
      polygonEventMapEquiv E₃ x := by
  cases x with
  | inl i => rfl
  | inr v =>
    rcases v with ⟨c, b⟩
    change Sum.inr (E₂ (E₁ c), b) = Sum.inr (E₃ c, b)
    rw [label_preserving_crossingEquiv_comp_apply E₁ E₂ E₃ h₁ h₂ h₃ c]

theorem label_preserving_supportMap_comp {n : ℕ} {P Q R : Fin n → Plane}
    (E₁ : PolygonCrossing P ≃ PolygonCrossing Q)
    (E₂ : PolygonCrossing Q ≃ PolygonCrossing R)
    (E₃ : PolygonCrossing P ≃ PolygonCrossing R)
    (h₁ : ∀ c, (E₁ c).val = c.val)
    (h₂ : ∀ c, (E₂ c).val = c.val)
    (h₃ : ∀ c, (E₃ c).val = c.val)
    (S : Finset (PolygonCrossing P)) :
    (S.map E₁.toEmbedding).map E₂.toEmbedding = S.map E₃.toEmbedding := by
  rw [Finset.map_map]
  have h := label_preserving_crossingEquiv_trans E₁ E₂ E₃ h₁ h₂ h₃
  ext d
  simp only [Finset.mem_map, Equiv.toEmbedding_apply, Function.Embedding.trans_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, (label_preserving_crossingEquiv_comp_apply E₁ E₂ E₃ h₁ h₂ h₃ c).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, label_preserving_crossingEquiv_comp_apply E₁ E₂ E₃ h₁ h₂ h₃ c⟩

/-- Open-edge intersection is globally invariant along any continuous generic path. -/
theorem path_edgeIntersection_iff {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (t : Time) (e f : Fin n) :
    edgeIntersection (p t) e f ↔ edgeIntersection (p start) e f := by
  refine locally_constant_iff (fun s => edgeIntersection (p s) e f) ?_ t
  intro u
  have hloc := hp.continuousAt.eventually
    (eventually_edgeIntersection_iff (p u) (hg u) e f)
  filter_upwards [hloc] with s hs
  exact hs (hg s).g1

/-- The canonical label-preserving crossing equivalence along a generic path. -/
def pathCrossingEquiv {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t)) (t : Time) :
    PolygonCrossing (p start) ≃ PolygonCrossing (p t) :=
  labelEquiv (p start) (p t) (path_edgeIntersection_iff p hp hg t)

theorem pathCrossingEquiv_labels {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (t : Time) (c : PolygonCrossing (p start)) :
    (pathCrossingEquiv p hp hg t c).val = c.val := rfl

@[simp] theorem pathCrossingEquiv_start {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t)) :
    pathCrossingEquiv p hp hg start = Equiv.refl (PolygonCrossing (p start)) := by
  ext c : 1
  rfl

@[simp] theorem polygonEventMapEquiv_refl_apply {n : ℕ} {q : Fin n → Plane}
    (x : PolygonEvent q) :
    polygonEventMapEquiv (Equiv.refl (PolygonCrossing q)) x = x := by
  cases x <;> rfl

/-- Event traversal order is globally preserved along any continuous generic path. -/
theorem path_eventOrder_iff {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (t : Time) (x y : PolygonEvent (p start)) :
    (polygonEventOrder (p start) (hg start).g2).lt x y ↔
      (polygonEventOrder (p t) (hg t).g2).lt
        (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x)
        (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) y) := by
  symm
  have h := locally_constant_iff
    (fun s => (polygonEventOrder (p s) (hg s).g2).lt
      (polygonEventMapEquiv (pathCrossingEquiv p hp hg s) x)
      (polygonEventMapEquiv (pathCrossingEquiv p hp hg s) y)) ?_ t
  · simpa only [pathCrossingEquiv_start, polygonEventMapEquiv_refl_apply] using h
  · intro u
    have hloc := hp.continuousAt.eventually
      (eventually_configuration_event_order (p u) (hg u))
    filter_upwards [hloc] with s hs
    obtain ⟨hs', E', hlabels', horder'⟩ := hs
    have hx := label_preserving_eventMap_comp_apply
      (pathCrossingEquiv p hp hg u) E' (pathCrossingEquiv p hp hg s)
      (pathCrossingEquiv_labels p hp hg u) hlabels'
      (pathCrossingEquiv_labels p hp hg s) x
    have hy := label_preserving_eventMap_comp_apply
      (pathCrossingEquiv p hp hg u) E' (pathCrossingEquiv p hp hg s)
      (pathCrossingEquiv_labels p hp hg u) hlabels'
      (pathCrossingEquiv_labels p hp hg s) y
    have ho := (horder'
      (polygonEventMapEquiv (pathCrossingEquiv p hp hg u) x)
      (polygonEventMapEquiv (pathCrossingEquiv p hp hg u) y)).symm
    rw [hx, hy] at ho
    exact ho

/-- Crossing tangent determinant sign is globally preserved along any continuous generic path. -/
theorem path_crossingOrientation_iff {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (t : Time) (c : PolygonCrossing (p start)) :
    (0 < planarDet (cyclicTangent (p start) c.val.1) (cyclicTangent (p start) c.val.2)) ↔
      (0 < planarDet (cyclicTangent (p t) (pathCrossingEquiv p hp hg t c).val.1)
        (cyclicTangent (p t) (pathCrossingEquiv p hp hg t c).val.2)) := by
  symm
  have h := locally_constant_iff
    (fun s => 0 < planarDet (cyclicTangent (p s) c.val.1) (cyclicTangent (p s) c.val.2)) ?_ t
  · exact h
  · intro u
    have hloc := hp.continuousAt.eventually
      (eventually_crossing_tangent_pos_iff (p u) (hg u))
    filter_upwards [hloc] with s hs
    exact (hs (pathCrossingEquiv p hp hg u c)).symm

/-- `leftCount` is globally constant along any continuous generic path. -/
theorem path_leftCount_eq {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t)) (t : Time) :
    leftCount (p start) = leftCount (p t) := by
  symm
  refine locally_constant_eq (fun s => leftCount (p s)) ?_ t
  intro u
  exact hp.continuousAt.eventually (eventually_literal_leftTurnCount_eq (p u) (hg u))

/-- `polygonNonalternating` is globally transported along any continuous generic path. -/
theorem path_polygonNonalternating_iff {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (t : Time) (S : Finset (PolygonCrossing (p start))) :
    PolygonNonalternation.polygonNonalternating (p start) (hg start).g2 S ↔
      PolygonNonalternation.polygonNonalternating (p t) (hg t).g2
        (S.map (pathCrossingEquiv p hp hg t).toEmbedding) :=
  polygonNonalternating_map_iff (p start) (p t) (hg start) (hg t)
    (pathCrossingEquiv p hp hg t) (pathCrossingEquiv_labels p hp hg t)
    (path_eventOrder_iff p hp hg t) S

/-- `uniformDaughterSupport` is globally transported along any continuous generic path. -/
theorem path_uniformDaughterSupport_iff {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (t : Time) (S : Finset (PolygonCrossing (p start))) :
    uniformDaughterSupport (p start) (hg start) S ↔
      uniformDaughterSupport (p t) (hg t)
        (S.map (pathCrossingEquiv p hp hg t).toEmbedding) := by
  symm
  have h := locally_constant_iff
    (fun s => uniformDaughterSupport (p s) (hg s)
      (S.map (pathCrossingEquiv p hp hg s).toEmbedding)) ?_ t
  · have hmap0 : S.map (pathCrossingEquiv p hp hg start).toEmbedding = S := by
      ext c
      simp [pathCrossingEquiv_start]
    simpa only [hmap0] using h
  · intro u
    have hloc1 := hp.continuousAt.eventually
      (eventually_configuration_event_order (p u) (hg u))
    have hloc2 := hp.continuousAt.eventually
      (eventually_uniformDaughterSupport_map_iff (p u) (hg u))
    filter_upwards [hloc1, hloc2] with s hs1 hs2
    obtain ⟨_, E', hlabels', horder'⟩ := hs1
    have horder_gs : ∀ x y : PolygonEvent (p u),
        (letI := polygonEventOrder (p u) (hg u).g2; x < y) ↔
        (letI := polygonEventOrder (p s) (hg s).g2;
          polygonEventMapEquiv E' x < polygonEventMapEquiv E' y) := horder'
    have hu := hs2 (hg s) E' hlabels' horder_gs
      (S.map (pathCrossingEquiv p hp hg u).toEmbedding)
    have hsupp := label_preserving_supportMap_comp
      (pathCrossingEquiv p hp hg u) E' (pathCrossingEquiv p hp hg s)
      (pathCrossingEquiv_labels p hp hg u) hlabels'
      (pathCrossingEquiv_labels p hp hg s) S
    rw [hsupp] at hu
    exact hu.symm

/-- `sharpDaughterRotationInteger` is globally preserved along any continuous generic path. -/
theorem path_sharpDaughterRotationInteger_eq {n : ℕ} (p : Time → Fin n → Plane)
    (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (t : Time) (S : Finset (PolygonCrossing (p start)))
    (C : Component (smoothingDartPermutation (p start) (hg start).g2 S))
    (hNA : PolygonNonalternation.polygonNonalternating (p start) (hg start).g2 S) :
    let E := pathCrossingEquiv p hp hg t
    let C' := smoothingComponentMapEquiv (p start) (p t) (hg start) (hg t)
      E (pathCrossingEquiv_labels p hp hg t) (path_eventOrder_iff p hp hg t) S C
    let hNA' := (path_polygonNonalternating_iff p hp hg t S).mp hNA
    sharpDaughterRotationInteger (p start) (hg start) S C hNA =
      sharpDaughterRotationInteger (p t) (hg t) (S.map E.toEmbedding) C' hNA' := by
  let q₀ := p start
  let h₀ := hg start
  let rotAt (s : Time) : ℤ :=
    let E_s := pathCrossingEquiv p hp hg s
    let C_s := smoothingComponentMapEquiv q₀ (p s) h₀ (hg s)
      E_s (pathCrossingEquiv_labels p hp hg s) (path_eventOrder_iff p hp hg s) S C
    let hNA_s := (path_polygonNonalternating_iff p hp hg s S).mp hNA
    sharpDaughterRotationInteger (p s) (hg s) (S.map E_s.toEmbedding) C_s hNA_s
  let F : (Fin n → Plane) → ℝ := fun r =>
    ∑ a : Arc q₀ h₀ S C,
      Complex.arg (polygonEdgeVector r (polygonEventEdge q₀ (P q₀ h₀ S a.val)) /
        polygonEdgeVector r (polygonEventEdge q₀ a.val))
  have hF_eq (s : Time) : F (p s) = (rotAt s : ℝ) * (2 * Real.pi) := by
    let E_s := pathCrossingEquiv p hp hg s
    let C_s := smoothingComponentMapEquiv q₀ (p s) h₀ (hg s)
      E_s (pathCrossingEquiv_labels p hp hg s) (path_eventOrder_iff p hp hg s) S C
    let hNA_s := (path_polygonNonalternating_iff p hp hg s S).mp hNA
    exact (totalTurn_eq_fixed_event_sum q₀ (p s) h₀ (hg s) E_s
      (pathCrossingEquiv_labels p hp hg s) (path_eventOrder_iff p hp hg s) S C hNA).symm.trans
      (sharpDaughterRotationInteger_spec (p s) (hg s) (S.map E_s.toEmbedding) C_s hNA_s).1
  have hF_cont (u : Time) : ContinuousAt F (p u) := by
    let E_u := pathCrossingEquiv p hp hg u
    let S_u := S.map E_u.toEmbedding
    let CE_u := smoothingComponentMapEquiv q₀ (p u) h₀ (hg u)
      E_u (pathCrossingEquiv_labels p hp hg u) (path_eventOrder_iff p hp hg u) S
    let C_u := CE_u C
    let hNA_u := (path_polygonNonalternating_iff p hp hg u S).mp hNA
    let Fu : (Fin n → Plane) → ℝ := fun r =>
      ∑ b : Arc (p u) (hg u) S_u C_u,
        Complex.arg (polygonEdgeVector r (polygonEventEdge (p u) (P (p u) (hg u) S_u b.val)) /
          polygonEdgeVector r (polygonEventEdge (p u) b.val))
    have hFu : ContinuousAt Fu (p u) :=
      continuousAt_fixed_event_turn_sum (p u) (hg u) S_u C_u hNA_u
    have hF_eq_Fu : F = Fu := by
      funext r
      let A : Arc q₀ h₀ S C ≃ Arc (p u) (hg u) S_u C_u :=
        Equiv.subtypeEquiv (polygonEventMapEquiv E_u) (fun x => by
          constructor
          · intro hx
            exact (smoothingComponentMapEquiv_componentOf q₀ (p u) h₀ (hg u) E_u
              (pathCrossingEquiv_labels p hp hg u) (path_eventOrder_iff p hp hg u) S x).symm.trans
              (congrArg CE_u hx)
          · intro hx
            apply CE_u.injective
            exact (smoothingComponentMapEquiv_componentOf q₀ (p u) h₀ (hg u) E_u
              (pathCrossingEquiv_labels p hp hg u) (path_eventOrder_iff p hp hg u) S x).trans hx)
      have hedge (x : PolygonEvent q₀) :
          polygonEventEdge (p u) (polygonEventMapEquiv E_u x) = polygonEventEdge q₀ x := by
        cases x with
        | inl i => rfl
        | inr v =>
          exact crossingVisit_mapEquiv_edge_eq q₀ (p u) E_u
            (pathCrossingEquiv_labels p hp hg u) v
      have hP (x : PolygonEvent q₀) :
          polygonEventMapEquiv E_u (P q₀ h₀ S x) =
            P (p u) (hg u) S_u (polygonEventMapEquiv E_u x) :=
        smoothingDartPermutation_map q₀ (p u) h₀ (hg u) E_u
          (pathCrossingEquiv_labels p hp hg u) (path_eventOrder_iff p hp hg u) S x
      refine Fintype.sum_equiv A _ _ ?_
      intro a
      change _ = Complex.arg (polygonEdgeVector r
        (polygonEventEdge (p u) (P (p u) (hg u) S_u (polygonEventMapEquiv E_u a.val))) /
        polygonEdgeVector r (polygonEventEdge (p u) (polygonEventMapEquiv E_u a.val)))
      rw [← hP, hedge, hedge]
    exact hF_eq_Fu ▸ hFu
  have hrot_const (u : Time) : ∀ᶠ s in 𝓝 u, rotAt s = rotAt u := by
    have h2pi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hcont_p : ContinuousAt (fun s : Time => F (p s)) u :=
      (hF_cont u).comp hp.continuousAt
    have hev : ∀ᶠ s in 𝓝 u, |F (p s) - F (p u)| < 2 * Real.pi :=
      ((hcont_p.sub continuousAt_const).abs).eventually
        (isOpen_Iio.mem_nhds (by simpa using h2pi))
    filter_upwards [hev] with s hnear
    rw [hF_eq s, hF_eq u, ← sub_mul, abs_mul, abs_of_pos h2pi] at hnear
    have hsmall : |(rotAt s : ℝ) - (rotAt u : ℝ)| < 1 := by
      apply (mul_lt_mul_right h2pi).mp
      simpa only [one_mul] using hnear
    have hi : |rotAt s - rotAt u| < (1 : ℤ) := by exact_mod_cast hsmall
    have hi' := abs_lt.mp hi
    omega
  have h0_eq : sharpDaughterRotationInteger q₀ h₀ S C hNA = rotAt start := by
    have h2pi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hsum : PrincipalTurning.totalTurn (sharpDaughterDiagram q₀ h₀ S C hNA) = F q₀ :=
      Fintype.sum_equiv (arcEquiv q₀ h₀ S C) _ _ (actual_turn q₀ h₀ S C hNA)
    have hF0 : F q₀ = (sharpDaughterRotationInteger q₀ h₀ S C hNA : ℝ) * (2 * Real.pi) :=
      hsum.symm.trans (sharpDaughterRotationInteger_spec q₀ h₀ S C hNA).1
    have hF0' := hF_eq start
    have heq_real : (sharpDaughterRotationInteger q₀ h₀ S C hNA : ℝ) = (rotAt start : ℝ) :=
      mul_right_cancel₀ (ne_of_gt h2pi) (hF0.symm.trans hF0')
    exact_mod_cast heq_real
  exact h0_eq.trans (locally_constant_eq rotAt hrot_const t).symm

/-!
## Combinatorial and Vertex Transport of `sharpDaughterDiagram`
-/

section DaughterDiagramTransport

variable {n : ℕ} (q q' : Fin n → Plane) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
variable (E : PolygonCrossing q ≃ PolygonCrossing q')
variable (hlabels : ∀ c, (E c).val = c.val)
variable (horder : ∀ x y : PolygonEvent q,
  (letI := polygonEventOrder q hq.g2; x < y) ↔
  (letI := polygonEventOrder q' hq'.g2; polygonEventMapEquiv E x < polygonEventMapEquiv E y))
variable (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))

def parentVertexEquiv : PolygonDrawing.Vertex q ≃ PolygonDrawing.Vertex q' :=
  Equiv.sumCongr (Equiv.refl (Fin n)) E

@[simp] theorem parentVertexEquiv_eventVertex (x : PolygonEvent q) :
    parentVertexEquiv q q' E (PolygonDrawing.eventVertex q x) =
      PolygonDrawing.eventVertex q' (polygonEventMapEquiv E x) := by
  cases x <;> rfl

def parentVertexFinEquiv :
    Fin (Parent q hq).nVertex ≃ Fin (Parent q' hq').nVertex :=
  (vertexFin q).symm.trans ((parentVertexEquiv q q' E).trans (vertexFin q'))

theorem parentVertexFinEquiv_arcSource (x : PolygonEvent q) :
    parentVertexFinEquiv q q' hq hq' E ((Parent q hq).arcSource (eventFin q x)) =
      (Parent q' hq').arcSource (eventFin q' (polygonEventMapEquiv E x)) := by
  change vertexFin q' (parentVertexEquiv q q' E
    ((vertexFin q).symm (vertexFin q (PolygonDrawing.arcSource q
      ((eventFin q).symm (eventFin q x)))))) =
    vertexFin q' (PolygonDrawing.arcSource q'
      ((eventFin q').symm (eventFin q' (polygonEventMapEquiv E x))))
  rw [(eventFin q).symm_apply_apply, (vertexFin q).symm_apply_apply,
    (eventFin q').symm_apply_apply]
  exact congrArg (vertexFin q') (parentVertexEquiv_eventVertex q q' E x)

def daughterArcCarrierEquiv :
    Arc q hq S C ≃ Arc q' hq' (S.map E.toEmbedding)
      (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) := by
  let CE := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S
  refine Equiv.subtypeEquiv (polygonEventMapEquiv E) ?_
  intro x
  constructor
  · intro hx
    exact (smoothingComponentMapEquiv_componentOf q q' hq hq' E hlabels horder S x).symm.trans
      (congrArg CE hx)
  · intro hx
    apply CE.injective
    exact (smoothingComponentMapEquiv_componentOf q q' hq hq' E hlabels horder S x).trans hx

@[simp] theorem daughterArcCarrierEquiv_val (a : Arc q hq S C) :
    (daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C a).val =
      polygonEventMapEquiv E a.val := rfl

def daughterVertexCarrierEquiv :
    Vertex q hq S C ≃ Vertex q' hq' (S.map E.toEmbedding)
      (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) := by
  refine Equiv.subtypeEquiv (parentVertexFinEquiv q q' hq hq' E) ?_
  intro v
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C a, ?_⟩
    rw [daughterArcCarrierEquiv_val, ← parentVertexFinEquiv_arcSource q q' hq hq' E a.val, ha]
  · rintro ⟨a', ha'⟩
    refine ⟨(daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C).symm a', ?_⟩
    apply (parentVertexFinEquiv q q' hq hq' E).injective
    rw [parentVertexFinEquiv_arcSource q q' hq hq' E]
    have hval : polygonEventMapEquiv E
        ((daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C).symm a').val = a'.val :=
      congrArg Subtype.val
        ((daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C).apply_symm_apply a')
    rw [hval, ha']

def parentCrossingFinEquiv :
    Fin (Parent q hq).nCrossing ≃ Fin (Parent q' hq').nCrossing :=
  (crossingFin q).symm.trans (E.trans (crossingFin q'))

theorem parentCrossingFinEquiv_inv_apply (c : Fin (Parent q hq).nCrossing) :
    (crossingFin q').symm (parentCrossingFinEquiv q q' hq hq' E c) =
      E ((crossingFin q).symm c) :=
  (crossingFin q').symm_apply_apply _

theorem parent_outgoing_event_map (c : Fin (Parent q hq).nCrossing) (i : Fin 2) :
    polygonEventMapEquiv E ((eventFin q).symm ((Parent q hq).outgoing c i)) =
      (eventFin q').symm
        ((Parent q' hq').outgoing (parentCrossingFinEquiv q q' hq hq' E c) i) := by
  rw [outgoing_event q hq c i,
    outgoing_event q' hq' (parentCrossingFinEquiv q q' hq hq' E c) i,
    parentCrossingFinEquiv_inv_apply q q' hq hq' E c]
  rfl

def daughterCrossingCarrierEquiv :
    Crossing q hq S C ≃ Crossing q' hq' (S.map E.toEmbedding)
      (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) := by
  let CE := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S
  refine Equiv.subtypeEquiv (parentCrossingFinEquiv q q' hq hq' E) ?_
  intro c
  have hmem :
      (crossingFin q').symm (parentCrossingFinEquiv q q' hq hq' E c) ∈ S.map E.toEmbedding ↔
        (crossingFin q).symm c ∈ S := by
    rw [parentCrossingFinEquiv_inv_apply q q' hq hq' E c]
    simp
  constructor
  · rintro ⟨hcS, hcC⟩
    refine ⟨fun hcS' => hcS (hmem.mp hcS'), ?_⟩
    intro i
    rw [← parent_outgoing_event_map q q' hq hq' E c i]
    exact (smoothingComponentMapEquiv_componentOf q q' hq hq' E hlabels horder S _).symm.trans
      (congrArg CE (hcC i))
  · rintro ⟨hcS', hcC'⟩
    refine ⟨fun hcS => hcS' (hmem.mpr hcS), ?_⟩
    intro i
    apply CE.injective
    exact (smoothingComponentMapEquiv_componentOf q q' hq hq' E hlabels horder S _).trans
      ((congrArg (componentOf (P q' hq' (S.map E.toEmbedding)))
        (parent_outgoing_event_map q q' hq hq' E c i)).trans (hcC' i))

variable (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
variable (hNA' : PolygonNonalternation.polygonNonalternating q' hq'.g2 (S.map E.toEmbedding))

def daughterVertexIndexEquiv :
    Fin (sharpDaughterDiagram q hq S C hNA).nVertex ≃
      Fin (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA').nVertex :=
  (vertexEquiv q hq S C).trans
    ((daughterVertexCarrierEquiv q q' hq hq' E hlabels horder S C).trans
      (vertexEquiv q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)).symm)

def daughterArcIndexEquiv :
    Fin (sharpDaughterDiagram q hq S C hNA).nArc ≃
      Fin (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA').nArc :=
  (arcEquiv q hq S C).trans
    ((daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C).trans
      (arcEquiv q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)).symm)

def daughterCrossingIndexEquiv :
    Fin (sharpDaughterDiagram q hq S C hNA).nCrossing ≃
      Fin (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA').nCrossing :=
  (crossingEquiv q hq S C).trans
    ((daughterCrossingCarrierEquiv q q' hq hq' E hlabels horder S C).trans
      (crossingEquiv q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)).symm)

theorem daughterArcIndexEquiv_apply
    (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    arcEquiv q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a) =
      daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C (arcEquiv q hq S C a) :=
  (arcEquiv q' hq' (S.map E.toEmbedding)
    (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)).apply_symm_apply _

theorem daughterCrossingIndexEquiv_apply
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) :
    crossingEquiv q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterCrossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c) =
      daughterCrossingCarrierEquiv q q' hq hq' E hlabels horder S C (crossingEquiv q hq S C c) :=
  (crossingEquiv q' hq' (S.map E.toEmbedding)
    (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)).apply_symm_apply _

theorem daughter_arcEquiv_incoming
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) (i : Fin 2) :
    arcEquiv q hq S C ((sharpDaughterDiagram q hq S C hNA).incoming c i) =
      inc q hq S C (crossingEquiv q hq S C c) i :=
  (arcEquiv q hq S C).apply_symm_apply _

theorem daughter_arcEquiv_outgoing
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) (i : Fin 2) :
    arcEquiv q hq S C ((sharpDaughterDiagram q hq S C hNA).outgoing c i) =
      out q hq S C (crossingEquiv q hq S C c) i :=
  (arcEquiv q hq S C).apply_symm_apply _

theorem daughterVertexIndexEquiv_oldVertex
    (v : Fin (sharpDaughterDiagram q hq S C hNA).nVertex) :
    oldVertex q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterVertexIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' v) =
      parentVertexFinEquiv q q' hq hq' E (oldVertex q hq S C v) := by
  exact congrArg Subtype.val
    ((vertexEquiv q' hq' (S.map E.toEmbedding)
      (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)).apply_symm_apply _)

theorem daughterArcIndexEquiv_oldArc
    (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    oldArc q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a) =
      eventFin q' (polygonEventMapEquiv E
        ((eventFin q).symm (oldArc q hq S C a))) := by
  have h := congrArg Subtype.val
    (daughterArcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA' a)
  unfold oldArc
  rw [h, daughterArcCarrierEquiv_val, (eventFin q).symm_apply_apply]

theorem daughterCrossingIndexEquiv_oldCrossing
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) :
    oldCrossing q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterCrossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c) =
      crossingFin q' (E ((crossingFin q).symm (oldCrossing q hq S C c))) := by
  exact congrArg Subtype.val
    (daughterCrossingIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA' c)

theorem daughterArcCarrierEquiv_next (a : Arc q hq S C) :
    daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C
        (fibrePerm (P q hq S) C a) =
      fibrePerm (P q' hq' (S.map E.toEmbedding))
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C a) := by
  apply Subtype.ext
  exact smoothingDartPermutation_map q q' hq hq' E hlabels horder S a.val

theorem daughterArcCarrierEquiv_out (c : Crossing q hq S C) (i : Fin 2) :
    daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C (out q hq S C c i) =
      out q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterCrossingCarrierEquiv q q' hq hq' E hlabels horder S C c) i := by
  apply Subtype.ext
  exact parent_outgoing_event_map q q' hq hq' E c.val i

theorem daughterArcCarrierEquiv_inc (c : Crossing q hq S C) (i : Fin 2) :
    daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C (inc q hq S C c i) =
      inc q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
        (daughterCrossingCarrierEquiv q q' hq hq' E hlabels horder S C c) i := by
  apply (fibrePerm (P q' hq' (S.map E.toEmbedding))
    (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)).injective
  apply Subtype.ext
  change P q' hq' (S.map E.toEmbedding)
      (polygonEventMapEquiv E ((eventFin q).symm ((Parent q hq).incoming c.val i))) =
    P q' hq' (S.map E.toEmbedding)
      ((eventFin q').symm ((Parent q' hq').incoming
        (daughterCrossingCarrierEquiv q q' hq hq' E hlabels horder S C c).val i))
  rw [← smoothingDartPermutation_map q q' hq hq' E hlabels horder S]
  rw [p_incoming q hq S c.val c.property.1 i,
      p_incoming q' hq' (S.map E.toEmbedding)
        (daughterCrossingCarrierEquiv q q' hq hq' E hlabels horder S C c).val
        (daughterCrossingCarrierEquiv q q' hq hq' E hlabels horder S C c).property.1 i]
  exact parent_outgoing_event_map q q' hq hq' E c.val i

/-- Explicit signed diagram isomorphism with public `daughterArcIndexEquiv` and
`daughterCrossingIndexEquiv`. -/
def daughterSignedDiagramIso
    (hpos : ∀ c : PolygonCrossing q,
      (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)) ↔
      (0 < planarDet (cyclicTangent q' (E c).val.1)
        (cyclicTangent q' (E c).val.2))) :
    SignedDiagramIso (sharpDaughterDiagram q hq S C hNA)
      (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA') where
  arcEquiv := daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
  crossingEquiv := daughterCrossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
  incoming_map := by
    let S' := S.map E.toEmbedding
    let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
    intro c i
    apply (arcEquiv q' hq' S' C').injective
    rw [daughterArcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA',
      daughter_arcEquiv_incoming q hq S C hNA,
      daughter_arcEquiv_incoming q' hq' S' C' hNA',
      daughterCrossingIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA']
    exact daughterArcCarrierEquiv_inc q q' hq hq' E hlabels horder S C
      (crossingEquiv q hq S C c) i
  outgoing_map := by
    let S' := S.map E.toEmbedding
    let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
    intro c i
    apply (arcEquiv q' hq' S' C').injective
    rw [daughterArcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA',
      daughter_arcEquiv_outgoing q hq S C hNA,
      daughter_arcEquiv_outgoing q' hq' S' C' hNA',
      daughterCrossingIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA']
    exact daughterArcCarrierEquiv_out q q' hq hq' E hlabels horder S C
      (crossingEquiv q hq S C c) i
  continuation_map := by
    let S' := S.map E.toEmbedding
    let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
    intro a
    apply (arcEquiv q' hq' S' C').injective
    change arcEquiv q' hq' S' C'
        (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
          (next q hq S C a)) =
      arcEquiv q' hq' S' C'
        (next q' hq' S' C'
          (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a))
    rw [daughterArcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA',
      arcEquiv_next, arcEquiv_next,
      daughterArcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA']
    exact daughterArcCarrierEquiv_next q q' hq hq' E hlabels horder S C
      (arcEquiv q hq S C a)
  through_map := fun _ => rfl
  overBranch_map := by
    let S' := S.map E.toEmbedding
    let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
    intro c
    have hindex := daughterCrossingIndexEquiv_oldCrossing q q' hq hq' E hlabels horder S C hNA hNA' c
    change (Parent q hq).overBranch (oldCrossing q hq S C c) =
      (Parent q' hq').overBranch
        (oldCrossing q' hq' S' C'
          (daughterCrossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c))
    rw [hindex]
    let c₀ := (crossingFin q).symm (oldCrossing q hq S C c)
    have hleft : crossingFin q c₀ = oldCrossing q hq S C c :=
      (crossingFin q).apply_symm_apply _
    change (positivePolygonEventDiagram q hq).overBranch (oldCrossing q hq S C c) =
      (positivePolygonEventDiagram q' hq').overBranch (crossingFin q' (E c₀))
    rw [← hleft,
      positivePolygonEventDiagram_overBranch q hq c₀,
      positivePolygonEventDiagram_overBranch q' hq' (E c₀)]
    by_cases hdet : 0 < planarDet (cyclicTangent q c₀.val.1) (cyclicTangent q c₀.val.2)
    · rw [if_pos hdet, if_pos ((hpos c₀).mp hdet)]
    · have hdet' : ¬ 0 < planarDet (cyclicTangent q' (E c₀).val.1)
          (cyclicTangent q' (E c₀).val.2) := fun h' => hdet ((hpos c₀).mpr h')
      rw [if_neg hdet, if_neg hdet']
  crossingSign_map := by
    let S' := S.map E.toEmbedding
    let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
    intro c
    rw [sharpDaughterDiagram_crossingSign q hq S C hNA c,
      sharpDaughterDiagram_crossingSign q' hq' S' C' hNA'
        (daughterCrossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' c)]

theorem daughterVertexIndexEquiv_arcSource
    (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    daughterVertexIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
        ((sharpDaughterDiagram q hq S C hNA).arcSource a) =
      (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA').arcSource
        (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a) := by
  let S' := S.map E.toEmbedding
  let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
  apply oldVertex_injective q' hq' S' C'
  rw [daughterVertexIndexEquiv_oldVertex q q' hq hq' E hlabels horder S C hNA hNA']
  change parentVertexFinEquiv q q' hq hq' E (oldVertex q hq S C (sourceIndex q hq S C a)) =
    oldVertex q' hq' S' C' (sourceIndex q' hq' S' C'
      (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a))
  rw [old_source q hq S C a,
    old_source q' hq' S' C' (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a),
    daughterArcIndexEquiv_oldArc q q' hq hq' E hlabels horder S C hNA hNA' a]
  simpa only [oldArc, (eventFin q).symm_apply_apply] using
    parentVertexFinEquiv_arcSource q q' hq hq' E (arcEquiv q hq S C a).val

theorem daughterVertexIndexEquiv_arcTarget
    (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    daughterVertexIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
        ((sharpDaughterDiagram q hq S C hNA).arcTarget a) =
      (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA').arcTarget
        (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a) := by
  let D := sharpDaughterDiagram q hq S C hNA
  let S' := S.map E.toEmbedding
  let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
  let D' := sharpDaughterDiagram q' hq' S' C' hNA'
  have hcont : daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
      (D.continuation a) =
    D'.continuation (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a) := by
    apply (arcEquiv q' hq' S' C').injective
    change arcEquiv q' hq' S' C'
        (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
          (next q hq S C a)) =
      arcEquiv q' hq' S' C'
        (next q' hq' S' C'
          (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a))
    rw [daughterArcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA',
      arcEquiv_next, arcEquiv_next,
      daughterArcIndexEquiv_apply q q' hq hq' E hlabels horder S C hNA hNA']
    exact daughterArcCarrierEquiv_next q q' hq hq' E hlabels horder S C
      (arcEquiv q hq S C a)
  rw [D.continuation_incidence a,
    daughterVertexIndexEquiv_arcSource q q' hq hq' E hlabels horder S C hNA hNA' (D.continuation a),
    hcont, ← D'.continuation_incidence]

theorem daughterDiagram_nCrossing_eq :
    (sharpDaughterDiagram q hq S C hNA).nCrossing =
      (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA').nCrossing :=
  Fin.equiv_iff_eq.mp ⟨daughterCrossingIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'⟩

theorem daughterVertexPoint_image (F : Plane → Plane)
    (hvert : ∀ i : Fin n, F (q i) = q' i)
    (hcross : ∀ c : PolygonCrossing q, F (crossingPoint q c) = crossingPoint q' (E c))
    (v : Fin (sharpDaughterDiagram q hq S C hNA).nVertex) :
    F ((sharpDaughterDiagram q hq S C hNA).vertexPoint v) =
      (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA').vertexPoint
        (daughterVertexIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' v) := by
  let S' := S.map E.toEmbedding
  let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
  change F ((Parent q hq).vertexPoint (oldVertex q hq S C v)) =
    (Parent q' hq').vertexPoint
      (oldVertex q' hq' S' C'
        (daughterVertexIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' v))
  rw [daughterVertexIndexEquiv_oldVertex q q' hq hq' E hlabels horder S C hNA hNA' v]
  change F (PolygonDrawing.vertexPoint q ((vertexFin q).symm (oldVertex q hq S C v))) =
    PolygonDrawing.vertexPoint q'
      ((vertexFin q').symm (vertexFin q'
        (parentVertexEquiv q q' E ((vertexFin q).symm (oldVertex q hq S C v)))))
  rw [(vertexFin q').symm_apply_apply]
  cases u : (vertexFin q).symm (oldVertex q hq S C v) with
  | inl i => exact hvert i
  | inr c => exact hcross c

theorem daughter_diagramArc_eq_event_trace
    (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    diagramArc (sharpDaughterDiagram q hq S C hNA) a =
      trace (polygonEventPoint q ((arcEquiv q hq S C a).val))
        (polygonEventPoint q (polygonEventSuccessor q hq.g2 ((arcEquiv q hq S C a).val))) := by
  unfold diagramArc
  change trace ((Parent q hq).vertexPoint (oldVertex q hq S C (sourceIndex q hq S C a)))
    ((Parent q hq).vertexPoint (oldVertex q hq S C (targetIndex q hq S C a))) = _
  rw [old_source, old_target]
  unfold oldArc
  rw [source_point q hq (arcEquiv q hq S C a).val,
    target_point q hq (arcEquiv q hq S C a).val]

/-- If a planar homeomorphism `F` transports original vertices, crossings, and
every parent event sub-segment trace, it induces a `DiagramTransport` between
`sharpDaughterDiagram`s. -/
def daughterDiagramTransport
    (hpos : ∀ c : PolygonCrossing q,
      (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)) ↔
      (0 < planarDet (cyclicTangent q' (E c).val.1)
        (cyclicTangent q' (E c).val.2)))
    (F : Plane ≃ₜ Plane)
    (hvert : ∀ i : Fin n, F (q i) = q' i)
    (hcross : ∀ c : PolygonCrossing q, F (crossingPoint q c) = crossingPoint q' (E c))
    (harcs : ∀ x : PolygonEvent q,
      F '' trace (polygonEventPoint q x) (polygonEventPoint q (polygonEventSuccessor q hq.g2 x)) =
        trace (polygonEventPoint q' (polygonEventMapEquiv E x))
          (polygonEventPoint q' (polygonEventSuccessor q' hq'.g2 (polygonEventMapEquiv E x)))) :
    DiagramTransport F (sharpDaughterDiagram q hq S C hNA)
      (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
        (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C) hNA') where
  signed := daughterSignedDiagramIso q q' hq hq' E hlabels horder S C hNA hNA' hpos
  vertex := daughterVertexIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA'
  vertex_image := daughterVertexPoint_image q q' hq hq' E hlabels horder S C hNA hNA' F hvert hcross
  source_image := daughterVertexIndexEquiv_arcSource q q' hq hq' E hlabels horder S C hNA hNA'
  target_image := daughterVertexIndexEquiv_arcTarget q q' hq hq' E hlabels horder S C hNA hNA'
  arc_image := by
    let S' := S.map E.toEmbedding
    let C' := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C
    intro a
    rw [daughter_diagramArc_eq_event_trace q hq S C hNA a]
    change F '' _ = diagramArc (sharpDaughterDiagram q' hq' S' C' hNA')
      (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a)
    rw [daughter_diagramArc_eq_event_trace q' hq' S' C' hNA']
    have hval : (arcEquiv q' hq' S' C'
        (daughterArcIndexEquiv q q' hq hq' E hlabels horder S C hNA hNA' a)).val =
        polygonEventMapEquiv E (arcEquiv q hq S C a).val :=
      congrArg Subtype.val
        ((arcEquiv q' hq' S' C').apply_symm_apply
          (daughterArcCarrierEquiv q q' hq hq' E hlabels horder S C (arcEquiv q hq S C a)))
    rw [hval]
    exact harcs (arcEquiv q hq S C a).val

end DaughterDiagramTransport

section EdgeDecompositionAndReduction

variable {n : ℕ}

theorem affinePoint_eq_add_smul (a b : Plane) (t : ℝ) :
    affinePoint a b t = a + t • (b - a) := by
  ext <;> simp [affinePoint, smul_eq_mul]

theorem trace_eq_image_affinePoint (a b : Plane) :
    trace a b = (affinePoint a b) '' Set.Icc (0 : ℝ) 1 := by
  ext x
  simp only [trace, Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc, affinePoint_eq_add_smul]
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨t, ht0, ht1, rfl⟩

theorem image_trace_of_affinePoint_eq (F : Plane → Plane) (a b a' b' : Plane)
    (h : ∀ α ∈ Set.Icc (0 : ℝ) 1, F (affinePoint a b α) = affinePoint a' b' α) :
    F '' trace a b = trace a' b' := by
  rw [trace_eq_image_affinePoint, trace_eq_image_affinePoint, ← Set.image_comp]
  exact Set.image_congr h

theorem subarcPoint_event_eq (q : Fin n → Plane) (hq : CyclicGeneric q)
    (x : PolygonEvent q) (t : ℝ) :
    affinePoint (polygonEventPoint q x)
        (polygonEventPoint q (polygonEventSuccessor q hq.g2 x)) t =
      affinePoint (q (polygonEventEdge q x))
        (q (cyclicSuccessor (polygonEventEdge q x)))
        (PolygonDrawing.subarcParameter q hq x t) := by
  have h := PolygonDrawing.subarcPoint_eq q hq x t
  unfold PolygonDrawing.arcSource PolygonDrawing.arcTarget at h
  rwa [PolygonDrawing.vertexPoint_eventVertex, PolygonDrawing.vertexPoint_eventVertex] at h

theorem originalEdge_eq_biUnion_event_trace
    (q : Fin n → Plane) (hq : CyclicGeneric q) (e : Fin n) :
    originalEdge q e = ⋃ (x : PolygonEvent q) (_ : polygonEventEdge q x = e),
      trace (polygonEventPoint q x) (polygonEventPoint q (polygonEventSuccessor q hq.g2 x)) := by
  classical
  ext p
  simp only [originalEdge, Set.mem_iUnion, trace_eq_image_affinePoint, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
    letI : LinearOrder (PolygonEvent q) := by
      change LinearOrder (Fin n ⊕ CrossingVisit q)
      exact polygonEventOrder q hq.g2
    let F : Finset (PolygonEvent q) :=
      Finset.univ.filter (fun x : PolygonEvent q =>
        polygonEventEdge q x = e ∧ polygonEventParameter q x ≤ s)
    have hmem0 : (Sum.inl e : PolygonEvent q) ∈ F := by
      simp [F, polygonEventEdge, polygonEventParameter, hs0]
    let x : PolygonEvent q := F.max' ⟨Sum.inl e, hmem0⟩
    have hxF : x ∈ F := Finset.max'_mem F ⟨Sum.inl e, hmem0⟩
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hxF
    rcases hxF with ⟨hxe, hxs⟩
    have hgt : ∀ z : PolygonEvent q, polygonEventEdge q z = e →
        polygonEventParameter q x < polygonEventParameter q z →
        s < polygonEventParameter q z := by
      intro z hze hlt
      by_contra hnot
      have hzs : polygonEventParameter q z ≤ s := le_of_not_gt hnot
      have hzF : z ∈ F := by simp [F, hze, hzs]
      have hzx : z ≤ x := Finset.le_max' F z hzF
      have hxz : x < z :=
        (polygonEvent_sameEdge_lt_iff q hq.g2 x z (hxe.trans hze.symm)).2 hlt
      exact (not_lt_of_ge hzx) hxz
    let u := EventSegmentGeometry.polygonEventSuccessorTerminalParameter
      q hq.g2 hq.size_ge_three x
    have hbounds := EventSegmentGeometry.polygonEventSuccessorTerminalParameter_bounds
      q hq.g2 hq.size_ge_three x
    have hsu : s ≤ u := by
      have hclass := EventSegmentGeometry.polygonEventSuccessor_sameEdge_next_or_nextAnchor
        q hq.g2 hq.size_ge_three x
      dsimp at hclass
      rcases hclass with ⟨hey, hxy, _⟩ | ⟨hy, _⟩
      · have hu := (EventSegmentGeometry.polygonEventSuccessorTerminalParameter_spec
          q hq.g2 hq.size_ge_three x).1 hey
        change u = _ at hu
        rw [hu]
        exact le_of_lt (hgt (polygonEventSuccessor q hq.g2 x) (hey.trans hxe) hxy)
      · have hu := (EventSegmentGeometry.polygonEventSuccessorTerminalParameter_spec
          q hq.g2 hq.size_ge_three x).2 hy
        change u = 1 at hu
        rw [hu]
        exact hs1
    have hpos : 0 < u - polygonEventParameter q x := sub_pos.mpr hbounds.1
    let t : ℝ := (s - polygonEventParameter q x) / (u - polygonEventParameter q x)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hxs) (le_of_lt hpos)
    have ht1 : t ≤ 1 := (div_le_one hpos).mpr (by linarith)
    refine ⟨x, hxe, t, ⟨ht0, ht1⟩, ?_⟩
    rw [subarcPoint_event_eq q hq x t, hxe]
    congr 1
    dsimp [PolygonDrawing.subarcParameter, t, u]
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
    ring
  · rintro ⟨x, hxe, t, ⟨ht0, ht1⟩, rfl⟩
    have hbounds := EventSegmentGeometry.polygonEventSuccessorTerminalParameter_bounds
      q hq.g2 hq.size_ge_three x
    have hstart := polygonEventParameter_bounds q x
    refine ⟨PolygonDrawing.subarcParameter q hq x t, ⟨?_, ?_⟩, ?_⟩
    · dsimp [PolygonDrawing.subarcParameter]
      nlinarith [hstart.1, hbounds.1]
    · dsimp [PolygonDrawing.subarcParameter]
      nlinarith [hbounds.1, hbounds.2]
    · have hpt := (subarcPoint_event_eq q hq x t).symm
      rwa [hxe] at hpt

theorem polygonEventEdge_mapEquiv
    (q q' : Fin n → Plane) (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val) (x : PolygonEvent q) :
    polygonEventEdge q' (polygonEventMapEquiv E x) = polygonEventEdge q x := by
  cases x with
  | inl e => rfl
  | inr v =>
    rcases v with ⟨c, b⟩
    cases b
    · exact congrArg Prod.fst (hlabels c)
    · exact congrArg Prod.snd (hlabels c)

theorem originalEdge_image_of_event_traces
    (q q' : Fin n → Plane) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (F : Plane → Plane)
    (harcs : ∀ x : PolygonEvent q,
      F '' trace (polygonEventPoint q x) (polygonEventPoint q (polygonEventSuccessor q hq.g2 x)) =
        trace (polygonEventPoint q' (polygonEventMapEquiv E x))
          (polygonEventPoint q' (polygonEventSuccessor q' hq'.g2 (polygonEventMapEquiv E x))))
    (e : Fin n) :
    F '' originalEdge q e = originalEdge q' e := by
  rw [originalEdge_eq_biUnion_event_trace q hq e,
    originalEdge_eq_biUnion_event_trace q' hq' e, Set.image_iUnion]
  ext p
  simp only [Set.mem_iUnion, Set.image_iUnion]
  constructor
  · rintro ⟨x, hxe, hp⟩
    rw [harcs x] at hp
    refine ⟨polygonEventMapEquiv E x, ?_, hp⟩
    rw [polygonEventEdge_mapEquiv q q' E hlabels x, hxe]
  · rintro ⟨y, hye, hp⟩
    let x := (polygonEventMapEquiv E).symm y
    have hxy : polygonEventMapEquiv E x = y := (polygonEventMapEquiv E).apply_symm_apply y
    refine ⟨x, ?_, ?_⟩
    · have hed := polygonEventEdge_mapEquiv q q' E hlabels x
      rw [hxy] at hed
      exact hed.symm.trans hye
    · rw [harcs x, hxy]
      exact hp

/-- Master reduction theorem for `full_chamber_geometry`: any `AmbientPlaneIsotopy`
that transports every event sub-segment affine parameterization along the path
automatically satisfies the entire `full_chamber_geometry` contract. -/
theorem full_chamber_geometry_of_event_affinePoint_isotopy
    (p : Time → Fin n → Plane) (hp : Continuous p) (hg : ∀ t, CyclicGeneric (p t))
    (I : AmbientPlaneIsotopy)
    (haff : ∀ (t : Time) (x : PolygonEvent (p start)) (α : ℝ),
      α ∈ Set.Icc (0 : ℝ) 1 →
      I.motion t (affinePoint (polygonEventPoint (p start) x)
        (polygonEventPoint (p start) (polygonEventSuccessor (p start) (hg start).g2 x)) α) =
      affinePoint
        (polygonEventPoint (p t) (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))
        (polygonEventPoint (p t) (polygonEventSuccessor (p t) (hg t).g2
          (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))) α) :
    let q₀ := p start
    let h₀ : CyclicGeneric q₀ := hg start
    ∃ I : AmbientPlaneIsotopy,
      (∀ t i, I.motion t (q₀ i) = p t i) ∧
      (∀ t e, I.motion t '' originalEdge q₀ e = originalEdge (p t) e) ∧
      ∀ t, ∃ E : PolygonCrossing q₀ ≃ PolygonCrossing (p t),
        (∀ c, (E c).val = c.val) ∧
        (∃ ht : CyclicGeneric (p t),
          (∀ x y : PolygonEvent q₀,
            (polygonEventOrder q₀ h₀.g2).lt x y ↔
              (polygonEventOrder (p t) ht.g2).lt
                (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) ∧
          (∀ c, I.motion t (crossingPoint q₀ c) = crossingPoint (p t) (E c)) ∧
          leftCount q₀ = leftCount (p t) ∧
          (∀ S : Finset (PolygonCrossing q₀),
            PolygonNonalternation.polygonNonalternating q₀ h₀.g2 S ↔
              PolygonNonalternation.polygonNonalternating (p t) ht.g2
                (S.map E.toEmbedding)) ∧
          (∀ S : Finset (PolygonCrossing q₀),
            uniformDaughterSupport q₀ h₀ S ↔
              uniformDaughterSupport (p t) ht (S.map E.toEmbedding)) ∧
          ∀ (S : Finset (PolygonCrossing q₀))
            (C : Component (smoothingDartPermutation q₀ h₀.g2 S))
            (hNA : PolygonNonalternation.polygonNonalternating q₀ h₀.g2 S),
            ∃ C' : Component (smoothingDartPermutation (p t) ht.g2 (S.map E.toEmbedding)),
            ∃ hNA' : PolygonNonalternation.polygonNonalternating (p t) ht.g2
              (S.map E.toEmbedding),
            ∃ J : DiagramTransport (I.motion t)
              (sharpDaughterDiagram q₀ h₀ S C hNA)
              (sharpDaughterDiagram (p t) ht (S.map E.toEmbedding) C' hNA'),
              (∀ x : PolygonEvent q₀,
                componentOf (smoothingDartPermutation q₀ h₀.g2 S) x = C →
                componentOf (smoothingDartPermutation (p t) ht.g2 (S.map E.toEmbedding))
                  (polygonEventMapEquiv E x) = C') ∧
              (sharpDaughterDiagram q₀ h₀ S C hNA).nCrossing =
                (sharpDaughterDiagram (p t) ht (S.map E.toEmbedding) C' hNA').nCrossing ∧
              sharpDaughterRotationInteger q₀ h₀ S C hNA =
                sharpDaughterRotationInteger (p t) ht (S.map E.toEmbedding) C' hNA' ∧
              (∀ c : Fin (sharpDaughterDiagram q₀ h₀ S C hNA).nCrossing,
                oldCrossing (p t) ht (S.map E.toEmbedding) C' (J.signed.crossingEquiv c) =
                  crossingFin (p t) (E
                    ((crossingFin q₀).symm (oldCrossing q₀ h₀ S C c)))) ∧
              (∀ a : Fin (sharpDaughterDiagram q₀ h₀ S C hNA).nArc,
                oldArc (p t) ht (S.map E.toEmbedding) C' (J.signed.arcEquiv a) =
                  eventFin (p t) (polygonEventMapEquiv E
                    ((eventFin q₀).symm (oldArc q₀ h₀ S C a))))) := by
  let q₀ := p start
  let h₀ : CyclicGeneric q₀ := hg start
  have hvert : ∀ t (i : Fin n), I.motion t (q₀ i) = p t i := by
    intro t i
    have h0 := haff t (Sum.inl i) 0 ⟨le_rfl, zero_le_one⟩
    simpa only [affinePoint_zero, polygonEventMapEquiv, Equiv.sumCongr_apply,
      Equiv.refl_apply, Sum.map_inl, polygonEventPoint] using h0
  have hcross : ∀ t (c : PolygonCrossing q₀),
      I.motion t (crossingPoint q₀ c) = crossingPoint (p t) (pathCrossingEquiv p hp hg t c) := by
    intro t c
    have h0 := haff t (Sum.inr (c, false)) 0 ⟨le_rfl, zero_le_one⟩
    simpa only [affinePoint_zero, polygonEventMapEquiv, Equiv.sumCongr_apply,
      Equiv.prodCongr_apply, Equiv.refl_apply, Sum.map_inr, Prod.map_apply,
      polygonEventPoint, crossingVisitPoint] using h0
  have harcs : ∀ t (x : PolygonEvent q₀),
      I.motion t '' trace (polygonEventPoint q₀ x)
        (polygonEventPoint q₀ (polygonEventSuccessor q₀ h₀.g2 x)) =
      trace (polygonEventPoint (p t) (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))
        (polygonEventPoint (p t) (polygonEventSuccessor (p t) (hg t).g2
          (polygonEventMapEquiv (pathCrossingEquiv p hp hg t) x))) := by
    intro t x
    exact image_trace_of_affinePoint_eq (I.motion t) _ _ _ _ (haff t x)
  refine ⟨I, hvert, ?_, ?_⟩
  · intro t e
    exact originalEdge_image_of_event_traces q₀ (p t) h₀ (hg t)
      (pathCrossingEquiv p hp hg t) (pathCrossingEquiv_labels p hp hg t)
      (I.motion t) (harcs t) e
  · intro t
    let E := pathCrossingEquiv p hp hg t
    have hlabels := pathCrossingEquiv_labels p hp hg t
    have horder := path_eventOrder_iff p hp hg t
    have hpos := path_crossingOrientation_iff p hp hg t
    refine ⟨E, hlabels, hg t, horder, hcross t, path_leftCount_eq p hp hg t,
      path_polygonNonalternating_iff p hp hg t,
      path_uniformDaughterSupport_iff p hp hg t, ?_⟩
    intro S C hNA
    let C' := smoothingComponentMapEquiv q₀ (p t) h₀ (hg t) E hlabels horder S C
    have hNA' : PolygonNonalternation.polygonNonalternating (p t) (hg t).g2
        (S.map E.toEmbedding) :=
      (path_polygonNonalternating_iff p hp hg t S).mp hNA
    refine ⟨C', hNA',
      daughterDiagramTransport q₀ (p t) h₀ (hg t) E hlabels horder S C hNA hNA' hpos
        (I.motion t) (hvert t) (hcross t) (harcs t),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      dsimp [C']
      rw [← hx]
      exact (smoothingComponentMapEquiv_componentOf q₀ (p t) h₀ (hg t) E hlabels horder S x).symm
    · exact daughterDiagram_nCrossing_eq q₀ (p t) h₀ (hg t) E hlabels horder S C hNA hNA'
    · exact path_sharpDaughterRotationInteger_eq p hp hg t S C hNA
    · intro c
      exact daughterCrossingIndexEquiv_oldCrossing q₀ (p t) h₀ (hg t)
        E hlabels horder S C hNA hNA' c
    · intro a
      exact daughterArcIndexEquiv_oldArc q₀ (p t) h₀ (hg t)
        E hlabels horder S C hNA hNA' a

end EdgeDecompositionAndReduction

end DirectGLSSW.GeminiChamber

