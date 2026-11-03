import DirectGLSSW.EndpointGenericStability
import DirectGLSSW.EndpointActualRecurrence
import DirectGLSSW.OpenMarkedCurrent
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorEndpointStability
open Filter Set Topology ShortEdgeSignStability
private theorem scalar_stable (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 ≠ 0) :
    ∀ᶠ η in 𝓝 (0 : ℝ), f η ≠ 0 ∧ scalarSignValue (f η) = scalarSignValue (f 0) := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · have hh : ∀ᶠ η in 𝓝 (0 : ℝ), f η < 0 :=
      hf.continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds hn)
    filter_upwards [hh] with η hη
    exact ⟨ne_of_lt hη, by simp [scalarSignValue, ne_of_lt hη, h0, hη, hn]⟩
  · have hh : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < f η :=
      hf.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hp)
    filter_upwards [hh] with η hη
    exact ⟨ne_of_gt hη, by simp [scalarSignValue, ne_of_gt hη, h0, not_lt.mpr (le_of_lt hη), not_lt.mpr (le_of_lt hp)]⟩

/-- Finite sorted-triple genericity and signs persist for any continuous actual
word family, with no claim about unbounded labels. -/
theorem eventually_continuous_word_signs
    (W : ℝ → ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcont : ∀ i, i ≤ N → Continuous (fun η => W η i))
    (hcore : CoreHGeneric (W 0) N) :
    ∀ᶠ η in 𝓝 (0 : ℝ), CoreHGeneric (W η) N ∧
      ∀ i k j, i < k → k < j → j ≤ N →
        polygonSignArray (W η) i k j = polygonSignArray (W 0) i k j := by
  have hh : ∀ᶠ η in 𝓝 (0 : ℝ), ∀ i k j : Fin (N+1),
      i.val < k.val → k.val < j.val →
        polygonHDet (W η) i.val k.val j.val ≠ 0 ∧
        polygonSignArray (W η) i.val k.val j.val =
          polygonSignArray (W 0) i.val k.val j.val := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro j
    by_cases hh : i.val < k.val ∧ k.val < j.val
    · have hi := hcont i.val (by omega)
      have hk := hcont k.val (by omega)
      have hj := hcont j.val (by omega)
      have hc : Continuous (fun η => polygonHDet (W η) i.val k.val j.val) := by
        unfold polygonHDet planarDet
        fun_prop
      exact (scalar_stable _ hc (hcore _ _ _ hh.1 hh.2 (by omega))).mono
        (fun η hη _ _ => hη)
    · exact Filter.Eventually.of_forall (fun _ hik hkj => (hh ⟨hik,hkj⟩).elim)
  filter_upwards [hh] with η hη
  have H (i k j : ℕ) (hik : i<k) (hkj : k<j) (hj : j≤N) :=
    hη ⟨i,by omega⟩ ⟨k,by omega⟩ ⟨j,by omega⟩ hik hkj
  exact ⟨fun i k j hik hkj hj => (H i k j hik hkj hj).1,
    fun i k j hik hkj hj => (H i k j hik hkj hj).2⟩

theorem open_entry_congr_sorted_signs (H K : TripleArray) (N : ℕ) (hN : 0<N)
    (hs : ∀ i k j, i<k → k<j → j≤N → H i k j = K i k j) :
    OpenMarkedCurrent.entry H 0 N = OpenMarkedCurrent.entry K 0 N := by
  unfold OpenMarkedCurrent.entry
  apply EndpointCurrent.weightedCutSum_congr_of_branch_eq _ hN
  intro a b _ hab hb
  apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
  intro i k j _ hik hkj hj
  exact hs i k j hik hkj (le_trans hj hb)

/-- Full endpoint value stability, derived through the finite actual sign array. -/
theorem exists_continuous_word_current_radius
    (W : ℝ → ℕ → PlanarPoint ℝ) (N : ℕ) (hN : 0<N)
    (hcont : ∀ i, i ≤ N → Continuous (fun η => W η i))
    (hcore : CoreHGeneric (W 0) N) :
    ∃ δ : ℝ, 0<δ ∧ ∀ η : ℝ, |η|<δ →
      CoreHGeneric (W η) N ∧
      (∀ i k j, i<k → k<j → j≤N →
        polygonSignArray (W η) i k j = polygonSignArray (W 0) i k j) ∧
      OpenMarkedCurrent.entry (polygonSignArray (W η)) 0 N =
        OpenMarkedCurrent.entry (polygonSignArray (W 0)) 0 N := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (eventually_continuous_word_signs W N hcont hcore)
  refine ⟨δ,hδ,?_⟩
  intro η hη
  have hmem : η ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hη
  obtain ⟨hc,hs⟩ := hball hmem
  exact ⟨hc,hs,open_entry_congr_sorted_signs _ _ N hN hs⟩
end DirectGLSSW.CursorEndpointStability


