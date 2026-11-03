import DirectGLSSW.EndpointGeometricMatrix

set_option autoImplicit false

namespace DirectGLSSW.EndpointEventSourceAdapter
open DirectGLSSW
open DirectGLSSW.EndpointEventGeometry
open DirectGLSSW.EndpointCurrent

/-- One geometric endpoint event, split into the three source regimes. The
endpoint values are the literal polygon sign arrays before/after moving only
q(0); the output is the full actual endpoint-current matrix jump. Pairwise
distinctness derives the excluded endpoint parameters τ=0 and τ=1 from the
collinearity equation. The existing source-geometric event isolation binder
is the only isolated-event premise. -/
theorem exists_endpoint_event_matrix_all_regimes
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hqDistinct : ∀ a b, a ≤ n → b ≤ n → a ≠ b → q a ≠ q b)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v ε) n ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v (-ε)) n ∧
      ∀ a i : Fin n,
        endpointCurrent d (polygonSignArray (moveEndpoint q v ε)) a.val i.val -
          endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε))) a.val i.val =
        if τ < 0 then
          scalarSignValue (planarDet (q k - q j) v) *
            endpointMarked d (polygonSignArray (moveEndpoint q v (-ε))) a.val (k - 1) *
            source k j *
            endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε)))
              (j - 1) i.val
        else if 1 < τ then
          scalarSignValue (planarDet (q k - q j) v) * source a.val k *
            markedAmplitude (fun _ l _ => d l)
              (polygonSignArray (moveEndpoint q v (-ε))) k j *
            endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε)))
              (j - 1) i.val
        else
          scalarSignValue (planarDet (q k - q j) v) * source a.val k * source k j *
            endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε)))
              (j - 1) i.val := by
  have hqk0 : q k ≠ q 0 := by
    intro he
    exact (hqDistinct 0 k (by omega) (by omega) (by omega) he.symm)
  have hqkj : q k ≠ q j := by
    intro he
    exact hqDistinct k j (by omega) (by omega) (by omega) he
  have hτ : τ ≠ 0 := by
    intro hzero
    apply hqk0
    rw [hcollinear, hzero]
    simp
  have hτ1 : 1 - τ ≠ 0 := by
    intro hzero
    have hτeq : τ = 1 := by linarith
    apply hqkj
    rw [hcollinear, hτeq]
    simp
  by_cases hneg : τ < 0
  · obtain ⟨ρ, hρ, hdata⟩ :=
      exists_endpoint_current_matrix_event_negative_positive q v d n hk hkj hjn τ
        hcollinear htransverse hisolated hneg
    refine ⟨ρ, hρ, ?_⟩
    intro ε hε hερ
    obtain ⟨hplus, hminus, hjump⟩ := hdata ε hε hερ
    refine ⟨hplus, hminus, ?_⟩
    intro a i
    simpa [hneg] using hjump a i
  · by_cases hgt : 1 < τ
    · obtain ⟨ρ, hρ, hdata⟩ :=
        exists_endpoint_current_matrix_event_positive_negative q v d n hk hkj hjn τ
          hcollinear htransverse hisolated hgt
      refine ⟨ρ, hρ, ?_⟩
      intro ε hε hερ
      obtain ⟨hplus, hminus, hjump⟩ := hdata ε hε hερ
      refine ⟨hplus, hminus, ?_⟩
      intro a i
      simpa [hneg, hgt] using hjump a i
    · have hpos : 0 < τ := by
        rcases lt_or_gt_of_ne hτ with h | h
        · exact False.elim (hneg h)
        · exact h
      have hτne1 : τ ≠ 1 := by
        intro hEq
        apply hτ1
        linarith
      have hτlt1 : τ < 1 := lt_of_le_of_ne (le_of_not_gt hgt) hτne1
      have hpos1 : 0 < 1 - τ := by linarith
      obtain ⟨ρ, hρ, hdata⟩ :=
        exists_endpoint_current_matrix_event_positive_positive q v d n hk hkj hjn τ
          hcollinear htransverse hisolated hpos hpos1
      refine ⟨ρ, hρ, ?_⟩
      intro ε hε hερ
      obtain ⟨hplus, hminus, hjump⟩ := hdata ε hε hερ
      refine ⟨hplus, hminus, ?_⟩
      intro a i
      simpa [hneg, hgt] using hjump a i


/-- The ordinary-source factors in the three regimes are literal adjacency
indicators. Hence every nonadjacent source case has zero jump, coordinatewise. -/
theorem endpoint_event_vanishing_source_cases
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (d : ℕ → ℚ) (n : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjn : j ≤ n) (τ : ℝ)
    (hqDistinct : ∀ a b, a ≤ n → b ≤ n → a ≠ b → q a ≠ q b)
    (hcollinear : q k = q 0 + τ • (q j - q 0))
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ n →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ∀ a i : Fin n,
        (τ < 0 ∧ j ≠ k + 1) ∨
        (0 < τ ∧ τ < 1 ∧ (j ≠ k + 1 ∨ k ≠ a.val + 1)) ∨
        (1 < τ ∧ k ≠ a.val + 1) →
        endpointCurrent d (polygonSignArray (moveEndpoint q v ε)) a.val i.val -
          endpointCurrent d (polygonSignArray (moveEndpoint q v (-ε))) a.val i.val = 0 := by
  obtain ⟨ρ, hρ, hdata⟩ := exists_endpoint_event_matrix_all_regimes q v d n
    hk hkj hjn τ hqDistinct hcollinear htransverse hisolated
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ a i hvan
  obtain ⟨_, _, hjump⟩ := hdata ε hε hερ
  rcases hvan with hneg | hmid | hpos
  · simpa [hneg.1, source, hneg.2] using hjump a i
  · rcases hmid with ⟨hτpos, hτlt, hsource⟩
    have hnotneg : ¬ τ < 0 := not_lt_of_ge (le_of_lt hτpos)
    have hnotgt : ¬ 1 < τ := not_lt_of_ge (le_of_lt hτlt)
    rcases hsource with hjneq | hkneq
    · simpa [hnotneg, hnotgt, source, hjneq] using hjump a i
    · simpa [hnotneg, hnotgt, source, hkneq] using hjump a i
  · have hτpos : 0 < τ := lt_trans (by norm_num : (0 : ℝ) < 1) hpos.1
    have hnotneg : ¬ τ < 0 := not_lt_of_ge (le_of_lt hτpos)
    simpa [hnotneg, hpos.1, source, hpos.2] using hjump a i




end DirectGLSSW.EndpointEventSourceAdapter


