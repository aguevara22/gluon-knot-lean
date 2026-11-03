import DirectGLSSW.HorizontalCapCore
import DirectGLSSW.CapActualBranches

set_option autoImplicit false

namespace DirectGLSSW.HorizontalShortEdge

open DirectGLSSW.CapActualBranches

/-- The concrete F S (I-BS)⁻¹ G matrix on the internal labels of a cap core. -/
noncomputable def horizontalCapPairing {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ) : Matrix (Fin n) (Fin n) ℚ :=
  let w := horizontalComplementWord q 0
  let d := fun k => scalarSignValue (w k).2
  globalCapPairing (capEndpointMatrix w (w 0) d n)
    (capInternalMatrix w d n)
    (capTerminalMatrix w d n) (fun r => d (r.val + 1))

theorem horizontal_cap_pairing_first_last (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin (n + 1) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hzero : (q ⟨0, by omega⟩).2 = 0)
    (hothers : ∀ x : Fin (n + 1), x ≠ ⟨0, by omega⟩ → (q x).2 ≠ 0) :
    horizontalCapPairing q
      ⟨0, by have := hq.size_ge_three; omega⟩
      ⟨n - 1, by have := hq.size_ge_three; omega⟩ =
      ((scalarSignValue (q ⟨n, by omega⟩).2 +
        scalarSignValue (q ⟨1, by have := hq.size_ge_three; omega⟩).2) / 2) *
        polygonAmplitude q hq := by
  have hn : 2 ≤ n := by have := hq.size_ge_three; omega
  let w := horizontalComplementWord q 0
  let d := fun k => scalarSignValue (w k).2
  have hgeneric : ShortEdgeSignStability.CoreHGeneric w n :=
    horizontalComplementWord_core_generic q hq.g1 hzero
  obtain ⟨rho, hrho, hstable⟩ :=
    EndpointGenericStability.exists_endpoint_current_stability_radius w (-1, 0) n hgeneric
  obtain ⟨delta, hdelta, hcap⟩ := exists_horizontal_capExpansion hRI q hq hzero hothers
  let epsilon := min rho delta / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hepsilon_rho : epsilon < rho := by
    have := min_le_left rho delta
    have := lt_min hrho hdelta
    dsimp [epsilon]
    linarith
  have hepsilon_delta : epsilon < delta := by
    have := min_le_right rho delta
    have := lt_min hrho hdelta
    dsimp [epsilon]
    linarith
  obtain ⟨_, hvalue⟩ := hcap epsilon hepsilon hepsilon_delta
  have hcurrent := (hstable epsilon (by rw [abs_of_pos hepsilon]; exact hepsilon_rho)).2
  let p' := horizontalComplementWord q epsilon 0
  have hcomplement : capComplement w p' = horizontalComplementWord q epsilon := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [capComplement, p']
    · simp [capComplement, w, horizontalComplementWord, hk]
  have hbase : capComplement w (w 0) = w := by
    funext k
    by_cases hk : k = 0 <;> simp [capComplement, hk]
  have hmatrix : capEndpointMatrix w p' d n = capEndpointMatrix w (w 0) d n := by
    funext a b
    unfold capEndpointMatrix
    rw [hcomplement, hbase, horizontalComplementWord_eq_moveEndpoint]
    exact hcurrent d a b
  have hword : capWord w p' n = horizontalComplementWord q epsilon := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [capWord, p']
    · by_cases hlast : k = n + 1
      · subst k
        simp [capWord, w, horizontalComplementWord]
        apply Prod.ext
        · rfl
        · exact hzero.symm
      · simp [capWord, w, horizontalComplementWord, hk, hlast]
  have hsum := weightedCutSumNonempty_cap_actual_eq_globalCapPairing w p' d (by omega : 0 < n)
  unfold capActualBranch at hsum
  rw [hword, hmatrix] at hsum
  simp only [horizontalComplementWord_height] at hvalue
  change capCutExpansion (j := n + 1) d
    (ordinaryCurrent (fun _ k _ => d k)
      (polygonSignArray (horizontalComplementWord q epsilon))) 0 = _ at hvalue
  rw [← weightedCutSumNonempty_eq_capCutExpansion d _ (by omega : 0 < n + 1)] at hvalue
  rw [hsum] at hvalue
  exact hvalue




end DirectGLSSW.HorizontalShortEdge
