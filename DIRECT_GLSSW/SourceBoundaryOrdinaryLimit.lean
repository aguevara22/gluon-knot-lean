import SourceBoundaryOrdinaryRow
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceBoundaryCurrent
open DirectGLSSW EndpointCurrent EndpointEventGeometry
/-- A common radius gives the literal event-prefix coefficient and event-parent
ordinary suffix for every endpoint j, with zero entries before the crossed edge. -/
theorem exists_adjacent_ordinary_row_limit
    (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N k : ℕ)
    (hk : 0 < k) (hKN : k + 1 ≤ N) (τ : ℝ)
    (hcollinear : W k = W 0 + τ • (W (k + 1) - W 0))
    (htransverse : planarDet (W k - W (k + 1)) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ N →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ k + 1) → polygonHDet W a b c ≠ 0)
    (hτ : τ < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v (-ε)) N ∧
      ∀ j, 0<j → j≤N →
      ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W v ε)) 0 j -
        ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W v (-ε))) 0 j =
      if k<j then
        (scalarSignValue (planarDet (W k-W (k+1)) v) *
          markedAmplitude (fun _ _ _ => -1) (polygonSignArray W) 0 k) *
        ordinaryCurrent (fun _ _ _ => -1) (endpointFar k (polygonSignArray W)) k j
      else 0 := by
  obtain ⟨ρjump, hjumpPos, hjump⟩ :=
    exists_adjacent_ordinary_row_jump W v N k hk hKN τ
      hcollinear htransverse hisolated hτ
  have hzero : polygonHDet W 0 k (k + 1) = 0 := by
    simp [polygonHDet, planarDet, hcollinear]
    ring
  obtain ⟨ρsign, hsignPos, hsign⟩ :=
    EndpointEventGeometry.exists_endpoint_event_radius W v N hk (by omega)
      (by omega) hzero htransverse hisolated
  refine ⟨min ρjump ρsign, lt_min hjumpPos hsignPos, ?_⟩
  intro ε hε hερ
  have hερJump : ε < ρjump := lt_of_lt_of_le hερ (min_le_left _ _)
  have hερSign : ε < ρsign := lt_of_lt_of_le hερ (min_le_right _ _)
  obtain ⟨hgenericPlus, hgenericMinus, hjumpEq⟩ := hjump ε hε hερJump
  obtain ⟨_, _, hstable, _⟩ := hsign ε hε hερSign
  let Hminus : TripleArray := polygonSignArray (moveEndpoint W v (-ε))
  let Hzero : TripleArray := polygonSignArray W
  have hmarkedEq :
      endpointMarked (fun _ : ℕ => -1) Hminus 0 (k - 1) =
        markedAmplitude (fun _ _ _ : ℕ => -1) Hzero 0 k := by
    have hFarZero : endpointFar 0 Hminus = Hminus := by
      funext a b c
      by_cases ha : a = 0 <;> simp [endpointFar, ha]
    rw [EndpointCurrent.endpointMarked, if_pos (by omega)]
    change markedAmplitude (fun _ l _ => -1) (endpointFar 0 Hminus) 0
        ((k - 1) + 1) = _
    rw [hFarZero, Nat.sub_add_cancel (show 1 ≤ k by omega)]
    apply markedAmplitude_congr_interval _ _ Hminus Hzero (by omega)
    intro a b c hab hab' hbc hc
    have hnot : a ≠ 0 ∨ b ≠ k ∨ c ≠ k + 1 :=
      Or.inr (Or.inr (by omega))
    exact (hstable a b c hab' hbc (by omega) hnot).2
  have hFarSigns : ∀ a b c, k ≤ a → a < b → b < c → c ≤ N →
      endpointFar k Hminus a b c = endpointFar k Hzero a b c := by
    intro a b c hka hab hbc hc
    by_cases hak : a = k
    · subst a
      have hnot : 0 ≠ 0 ∨ b ≠ k ∨ c ≠ k + 1 :=
        Or.inr (Or.inl (by omega))
      simpa [endpointFar] using
        (hstable 0 b c (by omega) (by omega) (by omega) hnot).2
    · have hnot : a ≠ 0 ∨ b ≠ k ∨ c ≠ k + 1 :=
        Or.inl (by omega)
      simpa [endpointFar, hak] using
        (hstable a b c hab hbc (by omega) hnot).2
  refine ⟨hgenericPlus,hgenericMinus,?_⟩
  intro j hj hjN
  have hrow := hjumpEq j hj hjN
  rw [hmarkedEq] at hrow
  by_cases hkj : k<j
  · have hparent : ordinaryCurrent (fun _ _ _ => -1) (endpointFar k Hminus) k j =
        ordinaryCurrent (fun _ _ _ => -1) (endpointFar k Hzero) k j := by
      apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hkj
      intro a b c hka hab hbc hcj
      exact hFarSigns a b c hka hab hbc (by omega)
    simp only [if_pos hkj] at hrow ⊢
    rw [hparent] at hrow
    exact hrow
  · simpa only [if_neg hkj] using hrow

end DirectGLSSW.SourceBoundaryCurrent
