import PolygonGermStability

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace DirectGLSSW.PolygonGermStability
open Filter
open scoped Topology

theorem eventually_scalarSignValue {α : Type*} [TopologicalSpace α] {a : α}
    (f : α → ℝ) (hf : ContinuousAt f a) (h0 : f a ≠ 0) :
    ∀ᶠ x in 𝓝 a, scalarSignValue (f x) = scalarSignValue (f a) := by
  by_cases hp : 0 < f a
  · have he := hf.eventually (isOpen_Ioi.mem_nhds hp)
    filter_upwards [he] with x hx
    have hx' : 0 < f x := hx
    simp [scalarSignValue, ne_of_gt hp, ne_of_gt hx',
      not_lt_of_ge (le_of_lt hp), not_lt_of_ge (le_of_lt hx')]
  · have hn : f a < 0 := lt_of_le_of_ne (le_of_not_gt hp) h0
    have he := hf.eventually (isOpen_Iio.mem_nhds hn)
    filter_upwards [he] with x hx
    have hx' : f x < 0 := hx
    simp [scalarSignValue, ne_of_lt hn, ne_of_lt hx', hn, hx']

theorem eventually_orderedSign_stability {α : Type*} [TopologicalSpace α] {a : α} {n : ℕ}
    (Q : α → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, ContinuousAt (fun x => Q x v) a) (h0 : cyclicNoncollinear (Q a)) :
    ∀ᶠ x in 𝓝 a, ∀ i k j : Fin n, i ≠ k → k ≠ j → i ≠ j →
      scalarSignValue (planarDet (Q x k - Q x j) (Q x i - Q x j)) =
      scalarSignValue (planarDet (Q a k - Q a j) (Q a i - Q a j)) := by
  classical
  have he : ∀ i k j : Fin n, ∀ᶠ x in 𝓝 a, i ≠ k → k ≠ j → i ≠ j →
      scalarSignValue (planarDet (Q x k - Q x j) (Q x i - Q x j)) =
      scalarSignValue (planarDet (Q a k - Q a j) (Q a i - Q a j)) := by
    intro i k j
    by_cases hd : i ≠ k ∧ k ≠ j ∧ i ≠ j
    · have hc : ContinuousAt (fun x => planarDet (Q x k - Q x j) (Q x i - Q x j)) a := by
        unfold planarDet
        exact (((hQ k).fst.sub (hQ j).fst).mul ((hQ i).snd.sub (hQ j).snd)).sub
          (((hQ k).snd.sub (hQ j).snd).mul ((hQ i).fst.sub (hQ j).fst))
      have h := eventually_scalarSignValue _ hc (h0 i k j hd.1 hd.2.1 hd.2.2)
      exact h.mono (fun x hx _ _ _ => hx)
    · exact Filter.Eventually.of_forall (fun _ hi hk hj => False.elim (hd ⟨hi,hk,hj⟩))
  exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun k =>
    Filter.eventually_all.mpr (fun j => he i k j)))

theorem eventually_polygonAmplitude_stability {α : Type*} [TopologicalSpace α] {a : α} {n : ℕ}
    (Q : α → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, ContinuousAt (fun x => Q x v) a) (h0 : CyclicGeneric (Q a)) :
    ∀ᶠ x in 𝓝 a, ∃ hx : CyclicGeneric (Q x),
      polygonAmplitude (Q x) hx = polygonAmplitude (Q a) h0 := by
  filter_upwards [eventually_cyclicGeneric Q hQ h0,
    eventually_orderedSign_stability Q hQ h0.g1] with x hx hs
  refine ⟨hx, ?_⟩
  exact polygonAmplitude_eq_of_oriented_triple_signs (Q x) (Q a) hx h0 hs

theorem exists_local_polygonAmplitude_stability_of_continuousAt {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, ContinuousAt (fun t => Q t v) 0) (h0 : CyclicGeneric (Q 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ ht : CyclicGeneric (Q t), polygonAmplitude (Q t) ht = polygonAmplitude (Q 0) h0 := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (eventually_polygonAmplitude_stability Q hQ h0)
  refine ⟨δ,hδ,?_⟩
  intro t ht
  exact hball (by simpa [Metric.mem_ball,Real.dist_eq] using ht)

end DirectGLSSW.PolygonGermStability





