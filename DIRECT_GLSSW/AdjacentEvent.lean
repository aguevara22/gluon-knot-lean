import DirectGLSSW.EndpointGeometricMatrix
import FirstRowJump

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW
open DirectGLSSW.EndpointCurrent
open DirectGLSSW.EndpointEventGeometry

/-- An isolated adjacent negative event gives the signed-cut jump through
its actual endpoint-matrix propagation, followed by first-row propagation.
The geometric collinearity, transversality, and isolation conditions remain
explicit inputs. -/
theorem exists_openMarkedCurrent_adjacent_negative_event_jump
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
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v ε)) 0 N -
          OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v (-ε))) 0 N =
        (scalarSignValue (planarDet (W k - W (k + 1)) v) *
          endpointMarked (fun _ : ℕ => -1)
            (polygonSignArray (moveEndpoint W v (-ε))) 0 (k - 1)) *
          OpenMarkedCurrent.entry
            (endpointFar k (polygonSignArray (moveEndpoint W v (-ε)))) k N := by
  obtain ⟨ρ, hρ, hEvent⟩ :=
    exists_endpoint_current_matrix_event_negative_positive W v
      (fun _ : ℕ => -1) N hk (by omega) (by omega) τ
      hcollinear htransverse hisolated hτ
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  obtain ⟨hgenericPlus, hgenericMinus, hmatrix⟩ := hEvent ε hε hερ
  let Hminus : TripleArray := polygonSignArray (moveEndpoint W v (-ε))
  let Hplus : TripleArray := polygonSignArray (moveEndpoint W v ε)
  let D : TripleArray := fun _ _ _ => -1
  let bMinus : IntervalArray := ordinaryCurrent D Hminus
  let bPlus : IntervalArray := ordinaryCurrent D Hplus
  let bParent : IntervalArray := ordinaryCurrent D (endpointFar k Hminus)
  let A : ℚ := scalarSignValue (planarDet (W k - W (k + 1)) v) *
    endpointMarked (fun _ : ℕ => -1) Hminus 0 (k - 1)
  have hkN : k < N := by omega
  have hSuffix : ∀ i j, 0 < i → i < j → j ≤ N → bPlus i j = bMinus i j := by
    intro i j hi hij hj
    dsimp [bPlus, bMinus, D]
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hij
    intro a b c hia hab hbc hcj
    have ha : a ≠ 0 := by omega
    have hb : b ≠ 0 := by omega
    have hc : c ≠ 0 := by omega
    simp [Hplus, Hminus, polygonSignArray, polygonHDet, moveEndpoint,
      EndpointEventGeometry.moveEndpoint, ha, hb, hc]
  have hParentSuffix : ∀ i j, k < i → i < j → j ≤ N →
      bParent i j = bMinus i j := by
    intro i j hki hij hj
    dsimp [bParent, bMinus, D]
    apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hij
    intro a b c hia hab hbc hcj
    have hak : a ≠ k := ne_of_gt (lt_of_lt_of_le hki hia)
    simp [EndpointCurrent.endpointFar, endpointFar, hak]
  have endpointFar_zero (H : TripleArray) : endpointFar 0 H = H := by
    funext a b c
    by_cases ha : a = 0 <;> simp [endpointFar, ha]
  have htop (H : TripleArray) (j : ℕ) (hj : 0 < j) :
      endpointCurrent (fun _ : ℕ => -1) H 0 (j - 1) =
        ordinaryCurrent D H 0 j := by
    have h0 : 0 ≤ j - 1 := by omega
    rw [EndpointCurrent.endpointCurrent, if_pos h0]
    change ordinaryCurrent D (endpointFar 0 H) 0 ((j - 1) + 1) = _
    rw [endpointFar_zero, Nat.sub_add_cancel (show 1 ≤ j by omega)]
  have hparentCurrent (j : ℕ) (hj : 0 < j) :
      endpointCurrent (fun _ : ℕ => -1) Hminus k (j - 1) =
        if k < j then bParent k j else 0 := by
    by_cases hkj : k < j
    · have hkrow : k ≤ j - 1 := by omega
      rw [EndpointCurrent.endpointCurrent, if_pos hkrow]
      change ordinaryCurrent D (endpointFar k Hminus) k ((j - 1) + 1) = _
      rw [Nat.sub_add_cancel (show 1 ≤ j by omega)]
      simp [hkj, bParent]
    · have hbelow : j - 1 < k := by omega
      rw [EndpointCurrent.endpointCurrent_below (fun _ : ℕ => -1) Hminus hbelow]
      simp [hkj]
  have hrow : ∀ j, 0 < j → j ≤ N →
      bPlus 0 j - bMinus 0 j = if k < j then A * bParent k j else 0 := by
    intro j hj hjN
    let i : Fin N := ⟨j - 1, by omega⟩
    let a : Fin N := ⟨0, by omega⟩
    have hmat := hmatrix a i
    have htopPlus := htop Hplus j hj
    have htopMinus := htop Hminus j hj
    change ordinaryCurrent D Hplus 0 j - ordinaryCurrent D Hminus 0 j = _
    rw [← htopPlus, ← htopMinus]
    calc
      endpointCurrent (fun _ : ℕ => -1) Hplus a.val i.val -
          endpointCurrent (fun _ : ℕ => -1) Hminus a.val i.val =
        scalarSignValue (planarDet (W k - W (k + 1)) v) *
          endpointMarked (fun _ : ℕ => -1) Hminus a.val (k - 1) *
          source k (k + 1) *
          endpointCurrent (fun _ : ℕ => -1) Hminus k i.val := by
        simpa [a, i, Nat.add_sub_cancel] using hmat
      _ = if k < j then A * bParent k j else 0 := by
        rw [hparentCurrent j hj]
        simp [A, source, a, i, Nat.sub_add_cancel (show 1 ≤ j by omega),
          Nat.add_sub_cancel]
  have hsum := weightedCutSum_firstRow_jump bMinus bPlus bParent A hkN
    hSuffix hParentSuffix hrow
  have hentry :
      OpenMarkedCurrent.entry Hplus 0 N - OpenMarkedCurrent.entry Hminus 0 N =
        A * OpenMarkedCurrent.entry (endpointFar k Hminus) k N := by
    simpa [OpenMarkedCurrent.entry, bPlus, bMinus, bParent, D, A] using hsum
  exact ⟨hgenericPlus, hgenericMinus, by simpa [Hplus, Hminus, A] using hentry⟩



end DirectGLSSW
