import ActiveArcVirtualEventGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry EndpointCurrent

private theorem endpointCurrent_zero_eq (d : ℕ → ℚ) (H : TripleArray)
    (b : ℕ) (hb : 0 < b) :
    endpointCurrent d H 0 (b-1) = ordinaryCurrent (fun _ k _ => d k) H 0 b := by
  rw [endpointCurrent,if_pos (Nat.zero_le _),Nat.sub_add_cancel (by omega)]
  have hfar : endpointFar 0 H = H := by
    funext x y z
    by_cases hx : x = 0 <;> simp [endpointFar,hx]
  rw [hfar]

/-- Conditional actual-support application of the endpoint-event theorem.
The isolated secant/transversality data are explicit internal hypotheses;
the incompatible support and physical first-side geometry discharge all
zero-source factors. The conclusion is the ACTUAL signed-cut open current.
Production of isolated retained-word charts is a separate missing consumer
input; this theorem claims no unconditional source-node closure. -/
theorem incompatible_isolated_event_openCurrent_eq
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val)
    (hbad : ∃ d ∈ U.val, ¬ Split.Compatible (a:=n) (b:=0) q hR c d)
    (k j : ℕ) (hk : 0 < k) (hkj : k < j)
    (hjn : j ≤ openCount q hR U.val - 1) (τ : ℝ)
    (hcol : eventOpenWord q hR U c k = eventOpenWord q hR U c 0 +
      τ • (eventOpenWord q hR U c j - eventOpenWord q hR U c 0))
    (htrans : planarDet (eventOpenWord q hR U c k - eventOpenWord q hR U c j)
      (q 1 - q 0) ≠ 0)
    (hisolated : ∀ a b d, a < b → b < d → d ≤ openCount q hR U.val - 1 →
      (a ≠ 0 ∨ b ≠ k ∨ d ≠ j) → polygonHDet (eventOpenWord q hR U c) a b d ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric
        (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) ε)
        (openCount q hR U.val - 1) ∧
      ShortEdgeSignStability.CoreHGeneric
        (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) (-ε))
        (openCount q hR U.val - 1) ∧
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) ε))
        0 (openCount q hR U.val - 1) =
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1-q 0) (-ε)))
        0 (openCount q hR U.val - 1) := by
  let W := eventOpenWord q hR U c
  let v := q 1-q 0
  let N := openCount q hR U.val - 1
  have hcount := open_count_ge_two q hR U.val
  have hN : 0 < N := by dsimp [N]; omega
  have hkn : k < openCount q hR U.val := by omega
  have hjlt : j < openCount q hR U.val := by omega
  have ht0 := eventOpenWord_parameter_ne_zero q hR c U hu k j hk hkn τ hcol
  have hk1 := eventOpenWord_transverse_index_ne_one q hR c hc U hu k j hk hkn τ hcol htrans
  have ht1 : τ ≠ 1 := by
    intro ht
    have hp : W k = W j := by simpa [W,ht] using hcol
    apply htrans
    change planarDet (W k-W j) v = 0
    rw [hp,sub_self]
    simp [planarDet]
  have hs0 : source 0 k = 0 := by simp [source,hk1]
  have hrow : ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v (-ε)) N ∧
      ∀ i : Fin N,
        endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v ε)) 0 i.val -
        endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v (-ε))) 0 i.val = 0 := by
    rcases lt_or_gt_of_ne ht0 with ht | ht
    · have hgap := eventOpenWord_negative_event_not_adjacent q hR c hc U hu hbad
        k j hk hkj hjlt τ ht hcol
      have hs : source k j = 0 := by simp [source,hgap]
      obtain ⟨ρ,hρ,hdata⟩ := exists_endpoint_current_matrix_event_negative_positive
        W v (fun _ => -1) N hk hkj hjn τ hcol htrans hisolated ht
      refine ⟨ρ,hρ,?_⟩
      intro ε hε hερ
      obtain ⟨hg1,hg0,hmat⟩ := hdata ε hε hερ
      refine ⟨hg1,hg0,?_⟩
      intro i
      simpa [hs] using hmat ⟨0,hN⟩ i
    · rcases lt_or_gt_of_ne ht1 with hlt | hgt
      · obtain ⟨ρ,hρ,hdata⟩ := exists_endpoint_current_matrix_event_positive_positive
          W v (fun _ => -1) N hk hkj hjn τ hcol htrans hisolated ht (by linarith)
        refine ⟨ρ,hρ,?_⟩
        intro ε hε hερ
        obtain ⟨hg1,hg0,hmat⟩ := hdata ε hε hερ
        refine ⟨hg1,hg0,?_⟩
        intro i
        simpa [hs0] using hmat ⟨0,hN⟩ i
      · obtain ⟨ρ,hρ,hdata⟩ := exists_endpoint_current_matrix_event_positive_negative
          W v (fun _ => -1) N hk hkj hjn τ hcol htrans hisolated hgt
        refine ⟨ρ,hρ,?_⟩
        intro ε hε hερ
        obtain ⟨hg1,hg0,hmat⟩ := hdata ε hε hερ
        refine ⟨hg1,hg0,?_⟩
        intro i
        simpa [hs0] using hmat ⟨0,hN⟩ i
  obtain ⟨ρ,hρ,hdata⟩ := hrow
  refine ⟨ρ,hρ,?_⟩
  intro ε hε hερ
  obtain ⟨hg1,hg0,hrow⟩ := hdata ε hε hερ
  refine ⟨hg1,hg0,?_⟩
  change OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v ε)) 0 N =
    OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v (-ε))) 0 N
  unfold OpenMarkedCurrent.entry
  apply weightedCutSum_congr_of_branch_eq _ hN
  intro a b ha hab hbN
  by_cases ha0 : a = 0
  · subst a
    have he := hrow ⟨b-1,by omega⟩
    change endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v ε)) 0 (b-1) -
      endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v (-ε))) 0 (b-1) = 0 at he
    rw [endpointCurrent_zero_eq _ _ b hab,endpointCurrent_zero_eq _ _ b hab] at he
    exact sub_eq_zero.mp he
  · apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
    intro x y z hax hxy hyz hzb
    have hx : x ≠ 0 := by omega
    have hy : y ≠ 0 := by omega
    have hz : z ≠ 0 := by omega
    simp only [polygonSignArray,polygonHDet,moveEndpoint,if_neg hx,if_neg hy,if_neg hz]

end DirectGLSSW.ActiveArc.Primitive
