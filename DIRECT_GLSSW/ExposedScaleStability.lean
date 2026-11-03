import ExposedCornerScale
import DirectGLSSW.TruncationPointGeometry
import PolygonGermStability
import LocalCarrierLineAlgebra
import ExposedEdgeGeometry

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceTruncationScaleStability

open DirectGLSSW DirectGLSSW.TruncationDirection
  DirectGLSSW.SourceTruncationSupport Filter Topology

/-- The strict original support inequalities and the finite event-line
avoidance selected by the exposed-corner scale construction persist on a
neighborhood of that same scale. This is the raw fixed-scale input needed
when a later good carrier line recovers a nearby, possibly different scale. -/
theorem exists_exposed_scale_support_and_avoidance_neighborhood {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a))
    (v : PlanarPoint ℝ)
    (hexposed : ∀ i : Fin n, i ≠ a → 0 < planarDet v (q i-q a)) :
    ∃ s0 : ℝ, 0 < s0 ∧
      (∀ i : Fin n, i ≠ a →
        0 < planarDet (s0 • (q (cyclicSuccessor a)-q a)-(q p-q a)) (q i-q a)) ∧
      (∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
        planarDet (s0 • (q (cyclicSuccessor a)-q a)-(q p-q a))
          (polygonEventPoint q e-q a) ≠ 0) ∧
      ∀ᶠ s : ℝ in 𝓝 s0,
        (∀ i : Fin n, i ≠ a →
          0 < planarDet (s • (q (cyclicSuccessor a)-q a)-(q p-q a)) (q i-q a)) ∧
        (∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
          planarDet (s • (q (cyclicSuccessor a)-q a)-(q p-q a))
            (polygonEventPoint q e-q a) ≠ 0) := by
  obtain ⟨s0,hs0,hsupport,havoid⟩ :=
    exists_exposed_corner_generic_support_scale q hq a p hp hturn v hexposed
  let U : PlanarPoint ℝ := q p-q a
  let D : PlanarPoint ℝ := q (cyclicSuccessor a)-q a
  have hsupportEvent : ∀ᶠ s : ℝ in 𝓝 s0,
      ∀ i : Fin n, i ≠ a → 0 < planarDet (s • D-U) (q i-q a) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i=a
    · filter_upwards [] with s
      intro hne
      exact (hne hi).elim
    · have hpos : 0 < planarDet (s0 • D-U) (q i-q a) := by
        simpa [U,D] using hsupport i hi
      have hcont : ContinuousAt (fun s : ℝ => planarDet (s • D-U) (q i-q a)) s0 := by
        unfold planarDet
        fun_prop
      filter_upwards [hcont.eventually (isOpen_Ioi.mem_nhds hpos)] with s hs
      intro _
      exact hs
  have havoidEvent : ∀ᶠ s : ℝ in 𝓝 s0,
      ∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
        planarDet (s • D-U) (polygonEventPoint q e-q a) ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : polygonEventPoint q e = q a
    · filter_upwards [] with s
      intro hne
      exact (hne he).elim
    · have hnonzero : planarDet (s0 • D-U) (polygonEventPoint q e-q a) ≠ 0 := by
        simpa [U,D] using havoid e he
      have hcont : ContinuousAt
          (fun s : ℝ => planarDet (s • D-U) (polygonEventPoint q e-q a)) s0 := by
        unfold planarDet
        fun_prop
      filter_upwards [hcont.eventually (isOpen_ne.mem_nhds hnonzero)] with s hs
      intro _
      exact hs
  have hboth := hsupportEvent.and havoidEvent
  refine ⟨s0,hs0,?_,?_,?_⟩
  · intro i hi
    simpa [U,D] using hsupport i hi
  · intro e he
    simpa [U,D] using havoid e he
  · filter_upwards [hboth] with s hs
    rcases hs with ⟨hsupportS,havoidS⟩
    constructor
    · intro i hi
      simpa [U,D] using hsupportS i hi
    · intro e he
      simpa [U,D] using havoidS e he

end DirectGLSSW.SourceTruncationScaleStability

