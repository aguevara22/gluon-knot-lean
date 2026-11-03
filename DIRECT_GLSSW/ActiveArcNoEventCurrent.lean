import ActiveArcVirtualEventGeometry
import DirectGLSSW.EndpointGenericStability

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords EndpointEventGeometry EndpointCurrent

private theorem endpointCurrent_zero_eq (d : ℕ → ℚ) (H : TripleArray)
    (b : ℕ) (hb : 0 < b) :
    endpointCurrent d H 0 (b - 1) = ordinaryCurrent (fun _ k _ => d k) H 0 b := by
  rw [endpointCurrent, if_pos (Nat.zero_le _), Nat.sub_add_cancel (by omega)]
  have hfar : endpointFar 0 H = H := by
    funext x y z
    by_cases hx : x = 0 <;> simp [endpointFar, hx]
  rw [hfar]

/-- Conditional stability of the literal signed-cut current in an event-free
word. The genericity premise is supplied explicitly, not deduced here. -/
theorem generic_word_openCurrent_eq
    (W : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N : ℕ) (hN : 0 < N)
    (hCore : ShortEdgeSignStability.CoreHGeneric W N) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W v (-ε)) N ∧
      OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v ε)) 0 N =
        OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W v (-ε))) 0 N := by
  obtain ⟨ρ, hρ, hstable⟩ :=
    EndpointGenericStability.exists_endpoint_current_stability_radius W v N hCore
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  have hp := hstable ε (by simpa [abs_of_pos hε] using hερ)
  have hm := hstable (-ε) (by simpa [abs_neg, abs_of_pos hε] using hερ)
  refine ⟨hp.1, hm.1, ?_⟩
  unfold OpenMarkedCurrent.entry
  apply weightedCutSum_congr_of_branch_eq _ hN
  intro a b ha hab hbN
  by_cases ha0 : a = 0
  · subst a
    have he := (hp.2 (fun _ => -1) ⟨0, hN⟩ ⟨b - 1, by omega⟩).trans
      (hm.2 (fun _ => -1) ⟨0, hN⟩ ⟨b - 1, by omega⟩).symm
    change endpointCurrent (fun _ => -1) (polygonSignArray (moveEndpoint W v ε))
        0 (b - 1) = endpointCurrent (fun _ => -1)
        (polygonSignArray (moveEndpoint W v (-ε))) 0 (b - 1) at he
    rw [endpointCurrent_zero_eq _ _ b hab, endpointCurrent_zero_eq _ _ b hab] at he
    exact he
  · apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
    intro x y z hax hxy hyz hzb
    have hx : x ≠ 0 := by omega
    have hy : y ≠ 0 := by omega
    have hz : z ≠ 0 := by omega
    simp only [polygonSignArray, polygonHDet, moveEndpoint, if_neg hx, if_neg hy, if_neg hz]

/-- Actual retained-word application for the no-event branch. `hCore` remains
an explicit conditional input; Regular alone does not imply this condition. -/
theorem generic_eventOpenWord_openCurrent_eq
    {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (U : Support q hR)
    (hCore : ShortEdgeSignStability.CoreHGeneric
      (eventOpenWord q hR U c) (openCount q hR U.val - 1)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric
        (moveEndpoint (eventOpenWord q hR U c) (q 1 - q 0) ε)
        (openCount q hR U.val - 1) ∧
      ShortEdgeSignStability.CoreHGeneric
        (moveEndpoint (eventOpenWord q hR U c) (q 1 - q 0) (-ε))
        (openCount q hR U.val - 1) ∧
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1 - q 0) ε))
        0 (openCount q hR U.val - 1) =
      OpenMarkedCurrent.entry
        (polygonSignArray (moveEndpoint (eventOpenWord q hR U c) (q 1 - q 0) (-ε)))
        0 (openCount q hR U.val - 1) := by
  have hcount := open_count_ge_two q hR U.val
  exact generic_word_openCurrent_eq (eventOpenWord q hR U c) (q 1 - q 0)
    (openCount q hR U.val - 1) (by omega) hCore




end DirectGLSSW.ActiveArc.Primitive
