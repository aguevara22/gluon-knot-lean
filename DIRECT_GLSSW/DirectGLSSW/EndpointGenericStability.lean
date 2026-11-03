import DirectGLSSW.EndpointEventGeometry
import DirectGLSSW.EndpointCurrent

set_option autoImplicit false

namespace DirectGLSSW.EndpointGenericStability
open DirectGLSSW
open DirectGLSSW.EndpointEventGeometry
open DirectGLSSW.EndpointCurrent
open DirectGLSSW.ShortEdgeSignStability

private theorem scalarSignValue_congr_of_neg_iff {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hneg : x < 0 ↔ y < 0) :
    scalarSignValue x = scalarSignValue y := by
  simp only [scalarSignValue, hx, hy, if_false]
  exact if_congr hneg rfl rfl

private theorem exists_two_sided_affine_sign_radius (d c : ℝ) (hd : d ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, |t| < ρ →
      d + t * c ≠ 0 ∧ (d + t * c < 0 ↔ d < 0) := by
  obtain ⟨ρp, hρp, hp⟩ := ShortEdgeSignStability.exists_affine_sign_radius d c hd
  obtain ⟨ρm, hρm, hm⟩ := ShortEdgeSignStability.exists_affine_sign_radius d (-c) hd
  refine ⟨min ρp ρm, lt_min hρp hρm, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    constructor
    · simpa using hd
    · simpa only [zero_mul, add_zero]
  · rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · have hε : 0 < -t := by linarith
      have hbound : -t < ρm := by
        have habs : |t| = -t := abs_of_neg hneg
        rw [habs] at ht
        exact lt_of_lt_of_le ht (min_le_right _ _)
      have hgood := hm (-t) hε hbound
      have hrewrite : d + t * c = d + (-t) * (-c) := by ring
      rw [hrewrite]
      exact hgood
    · have hbound : t < ρp := by
        have habs : |t| = t := abs_of_pos hpos
        rw [habs] at ht
        exact lt_of_lt_of_le ht (min_le_left _ _)
      exact hp t hpos hbound

private theorem exists_one_triple_endpoint_sign_radius
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    {i k j n : ℕ} (hik : i < k) (hkj : k < j) (hjn : j ≤ n)
    (hgeneric : ShortEdgeSignStability.CoreHGeneric q n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, |t| < ρ →
      polygonHDet (EndpointEventGeometry.moveEndpoint q v t) i k j ≠ 0 ∧
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v t) i k j =
        polygonSignArray q i k j := by
  have hd : polygonHDet q i k j ≠ 0 := hgeneric i k j hik hkj hjn
  by_cases hi : i = 0
  · subst i
    let d := polygonHDet q 0 k j
    let c := planarDet (q k - q j) v
    have hd' : d ≠ 0 := hd
    obtain ⟨ρ, hρ, hgood⟩ := exists_two_sided_affine_sign_radius d c hd'
    refine ⟨ρ, hρ, ?_⟩
    intro t ht
    have hdet : polygonHDet (EndpointEventGeometry.moveEndpoint q v t) 0 k j = d + t * c := by
      rw [EndpointEventGeometry.moveEndpoint_farDet q v (by omega) hkj]
    obtain ⟨hnew, hneg⟩ := hgood t ht
    refine ⟨?_, ?_⟩
    · rw [hdet]
      exact hnew
    · change scalarSignValue _ = scalarSignValue _
      rw [hdet]
      exact scalarSignValue_congr_of_neg_iff hnew hd' hneg
  · have hk : k ≠ 0 := by omega
    have hj : j ≠ 0 := by omega
    have hdet : ∀ t : ℝ,
        polygonHDet (EndpointEventGeometry.moveEndpoint q v t) i k j =
          polygonHDet q i k j := by
      intro t
      simp [polygonHDet, EndpointEventGeometry.moveEndpoint, hi, hk, hj]
    refine ⟨1, by norm_num, ?_⟩
    intro t _
    refine ⟨?_, ?_⟩
    · rw [hdet]
      exact hd
    · simp [polygonSignArray, hdet]

/-- A common two-sided radius preserves all endpoint words' current entries. -/
theorem exists_endpoint_current_stability_radius
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (n : ℕ)
    (hgeneric : ShortEdgeSignStability.CoreHGeneric q n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, |t| < ρ →
      ShortEdgeSignStability.CoreHGeneric
        (EndpointEventGeometry.moveEndpoint q v t) n ∧
      ∀ d : ℕ → ℚ, ∀ a i : Fin n,
        EndpointCurrent.endpointCurrent d
          (polygonSignArray (EndpointEventGeometry.moveEndpoint q v t)) a.val i.val =
        EndpointCurrent.endpointCurrent d (polygonSignArray q) a.val i.val := by
  classical
  let triples := ShortEdgeSignStability.boundedTriples n
  let P : (ℕ × ℕ × ℕ) → ℝ → Prop := fun t ε =>
    (t.1 < t.2.1 → t.2.1 < t.2.2 → t.2.2 ≤ n →
      (polygonHDet (EndpointEventGeometry.moveEndpoint q v ε) t.1 t.2.1 t.2.2 ≠ 0 ∧
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v ε) t.1 t.2.1 t.2.2 =
          polygonSignArray q t.1 t.2.1 t.2.2) ∧
      (polygonHDet (EndpointEventGeometry.moveEndpoint q v (-ε)) t.1 t.2.1 t.2.2 ≠ 0 ∧
        polygonSignArray (EndpointEventGeometry.moveEndpoint q v (-ε)) t.1 t.2.1 t.2.2 =
          polygonSignArray q t.1 t.2.1 t.2.2))
  have hlocal : ∀ t, t ∈ triples → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ε < ρ → P t ε := by
    intro t _
    by_cases hh : t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 ≤ n
    · obtain ⟨ρ, hρ, hstable⟩ := exists_one_triple_endpoint_sign_radius q v
        hh.1 hh.2.1 hh.2.2 hgeneric
      refine ⟨ρ, hρ, ?_⟩
      intro ε hε hερ hik hkj hjn
      have habs : |ε| = ε := abs_of_pos hε
      have hnegs : |-ε| = ε := by rw [abs_neg, habs]
      exact ⟨hstable ε (by simpa [habs] using hερ),
        hstable (-ε) (by simpa [hnegs] using hερ)⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro ε hε hερ hik hkj hjn
      exact False.elim (hh ⟨hik, hkj, hjn⟩)
  obtain ⟨ρ, hρ, hgood⟩ := ShortEdgeSignStability.exists_finset_common_radius triples P hlocal
  have htriple (t : ℝ) (ht : |t| < ρ) {i k j : ℕ}
      (hik : i < k) (hkj : k < j) (hjn : j ≤ n) :
      polygonHDet (EndpointEventGeometry.moveEndpoint q v t) i k j ≠ 0 ∧
      polygonSignArray (EndpointEventGeometry.moveEndpoint q v t) i k j =
        polygonSignArray q i k j := by
    have hmem : (i, k, j) ∈ triples := by
      simp [triples, ShortEdgeSignStability.boundedTriples]
      omega
    by_cases ht0 : t = 0
    · subst t
      have hbase := hgeneric i k j hik hkj hjn
      have hmove : EndpointEventGeometry.moveEndpoint q v 0 = q := by
        funext x
        by_cases hx : x = 0
        · simp [EndpointEventGeometry.moveEndpoint, hx]
        · simp [EndpointEventGeometry.moveEndpoint, hx]
      rw [hmove]
      exact ⟨hbase, rfl⟩
    · rcases lt_or_gt_of_ne ht0 with htneg | htpos
      · have hε : 0 < -t := by linarith
        have hεbound : -t < ρ := by
          have habs : |t| = -t := abs_of_neg htneg
          rw [habs] at ht
          exact ht
        have hpair := hgood (-t) hε hεbound (i, k, j) hmem hik hkj hjn
        simpa using hpair.2
      · have hεbound : t < ρ := by
          have habs : |t| = t := abs_of_pos htpos
          rw [habs] at ht
          exact ht
        exact hgood t htpos hεbound (i, k, j) hmem hik hkj hjn |>.1
  refine ⟨ρ, hρ, ?_⟩
  intro t ht
  refine ⟨?_, ?_⟩
  · intro i k j hik hkj hjn
    exact (htriple t ht hik hkj hjn).1
  · intro d a i
    by_cases hai : a.val ≤ i.val
    · simp only [EndpointCurrent.endpointCurrent, if_pos hai]
      apply ordinaryCurrent_congr_interval_fixed_near
        (fun _ k _ => d k) _ _ (by omega)
      intro x y z hax hxy hyz hzb
      have hzN : z ≤ n := le_trans hzb (by omega : i.val + 1 ≤ n)
      by_cases hxa : x = a.val
      · simp [EndpointCurrent.endpointFar, hxa]
        exact (htriple t ht (i := 0) (k := y) (j := z) (by omega) hyz hzN).2
      · simp [EndpointCurrent.endpointFar, hxa]
        exact (htriple t ht (i := x) (k := y) (j := z) hxy hyz hzN).2
    · have hnot : ¬ a.val ≤ i.val := by omega
      simp [EndpointCurrent.endpointCurrent, hnot]






end DirectGLSSW.EndpointGenericStability
