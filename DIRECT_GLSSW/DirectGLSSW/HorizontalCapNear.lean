import DirectGLSSW.HorizontalCapPairing
import DirectGLSSW.HorizontalCapPolygon
import DirectGLSSW.HorizontalCapCore
import DirectGLSSW.EndpointGenericStability
import DirectGLSSW.NearData
import DirectGLSSW.CapMarkedPairing
import DirectGLSSW.HorizontalComplement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.HorizontalShortEdge

open DirectGLSSW.CapActualBranches
open DirectGLSSW.ShortEdgeCyclicAdapter

/-- The concrete first/last cap pairing with caller-specified internal near data. -/
noncomputable def horizontalCapPairingWithNear {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ) (d : ℕ → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let w := horizontalComplementWord q 0
  globalCapPairing (capEndpointMatrix w (w 0) d n)
    (capInternalMatrix w d n) (capTerminalMatrix w d n)
    (fun r => d (r.val + 1))

/-- The horizontal complementary word's top far gates agree with any near data
that agrees with the original internal vertex heights. -/
private theorem horizontal_top_gate_eq_of_near_data
    {n : ℕ} (q : Fin (n + 1) → PlanarPoint ℝ) (epsilon : ℝ)
    (hzero : (q ⟨0, by omega⟩).2 = 0) (hepsilon : 0 < epsilon)
    (d : ℕ → ℚ)
    (hnear : ∀ r : Fin n,
      d (r.val + 1) =
        scalarSignValue (q ⟨r.val + 1, by omega⟩).2)
    {k : ℕ} (hk : k ∈ Finset.Ioo 0 (n + 1)) :
    polygonSignArray (horizontalComplementWord q epsilon) 0 k (n + 1) = d k := by
  have hk' := Finset.mem_Ioo.mp hk
  have hstart : horizontalComplementWord q epsilon 0 =
      ((q ⟨0, by omega⟩).1 - epsilon, 0) := by
    simp [horizontalComplementWord]
  have hfinish : horizontalComplementWord q epsilon (n + 1) =
      ((q ⟨0, by omega⟩).1, 0) := by
    simp [horizontalComplementWord, ← hzero]
  have htop := horizontal_word_top_sign (horizontalComplementWord q epsilon)
    (n + 1) (q ⟨0, by omega⟩).1 epsilon hepsilon hstart hfinish k
  have hheight := horizontalComplementWord_height q epsilon k
  have hcore := horizontalComplementWord_zero_eq_core q hzero k (by omega)
  let r : Fin n := ⟨k - 1, by omega⟩
  have hr : r.val + 1 = k := by simp [r]; omega
  calc
    polygonSignArray (horizontalComplementWord q epsilon) 0 k (n + 1) =
        scalarSignValue (horizontalComplementWord q epsilon k).2 := htop
    _ = scalarSignValue (horizontalComplementWord q 0 k).2 := by rw [hheight]
    _ = scalarSignValue (q ⟨k, by omega⟩).2 := by rw [hcore]
    _ = d k := by
      have hidx : (⟨k, by omega⟩ : Fin (n + 1)) =
          ⟨r.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [hr]
      calc
        scalarSignValue (q ⟨k, by omega⟩).2 =
            scalarSignValue (q ⟨r.val + 1, by omega⟩).2 := by rw [hidx]
        _ = d (r.val + 1) := (hnear r).symm
        _ = d k := by rw [hr]

/-- The arbitrary-near cut expansion evaluates to the same geometric endpoint
pairing as the height-defined near data. -/
theorem exists_horizontal_capExpansion_withNear
    (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin (n + 1) → PlanarPoint ℝ)
    (hq : CyclicGeneric q)
    (hzero : (q ⟨0, by omega⟩).2 = 0)
    (hothers : ∀ x : Fin (n + 1),
      x ≠ ⟨0, by omega⟩ → (q x).2 ≠ 0)
    (d : ℕ → ℚ)
    (hnear : ∀ r : Fin n,
      d (r.val + 1) =
        scalarSignValue (q ⟨r.val + 1, by omega⟩).2) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < delta →
        ∃ hp : CyclicGeneric
          (insertCyclicAfter q ⟨0, by omega⟩ epsilon (-1, 0)),
          capCutExpansion (j := n + 1) d
            (ordinaryCurrent (fun _ k _ => d k)
              (polygonSignArray (horizontalComplementWord q epsilon))) 0 =
            ((scalarSignValue (q ⟨n, by omega⟩).2 +
              scalarSignValue
                (q ⟨1, by have := hq.size_ge_three; omega⟩).2) / 2) *
              polygonAmplitude q hq := by
  obtain ⟨delta, hdelta, hcap⟩ :=
    exists_horizontal_capExpansion hRI q hq hzero hothers
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon hepsilon hlt
  obtain ⟨hp, hgeometric⟩ := hcap epsilon hepsilon hlt
  refine ⟨hp, ?_⟩
  let H := polygonSignArray (horizontalComplementWord q epsilon)
  let dGeo := fun k => scalarSignValue (horizontalComplementWord q epsilon k).2
  have htopD : ∀ k, k ∈ Finset.Ioo 0 (n + 1) → H 0 k (n + 1) = d k := by
    intro k hk
    exact horizontal_top_gate_eq_of_near_data q epsilon hzero hepsilon d hnear hk
  have htopGeo : ∀ k, k ∈ Finset.Ioo 0 (n + 1) → H 0 k (n + 1) = dGeo k := by
    intro k hk
    have hstart : horizontalComplementWord q epsilon 0 =
        ((q ⟨0, by omega⟩).1 - epsilon, 0) := by
      simp [horizontalComplementWord]
    have hfinish : horizontalComplementWord q epsilon (n + 1) =
        ((q ⟨0, by omega⟩).1, 0) := by
      simp [horizontalComplementWord, ← hzero]
    exact horizontal_word_top_sign (horizontalComplementWord q epsilon)
      (n + 1) (q ⟨0, by omega⟩).1 epsilon hepsilon hstart hfinish k
  have hn : 2 ≤ n := by have := hq.size_ge_three; omega
  have hgap : 0 + 1 < n + 1 := by omega
  have hcutD := markedAmplitude_eq_capCutExpansion_middleNear d H hgap htopD
  have hcutGeo := markedAmplitude_eq_capCutExpansion_middleNear dGeo H hgap htopGeo
  have hmarked := markedAmplitude_near_independent
    (fun _ k _ => d k) (fun _ k _ => dGeo k) H (i := 0) (j := n + 1) (by omega)
  change capCutExpansion d (ordinaryCurrent (fun _ k _ => d k) H) 0 = _
  calc
    capCutExpansion d (ordinaryCurrent (fun _ k _ => d k) H) 0 =
        markedAmplitude (fun _ k _ => d k) H 0 (n + 1) := hcutD.symm
    _ = markedAmplitude (fun _ k _ => dGeo k) H 0 (n + 1) := hmarked
    _ = capCutExpansion dGeo (ordinaryCurrent (fun _ k _ => dGeo k) H) 0 := hcutGeo
    _ = ((scalarSignValue (q ⟨n, by omega⟩).2 +
          scalarSignValue (q ⟨1, by have := hq.size_ge_three; omega⟩).2) / 2) *
          polygonAmplitude q hq := by
      exact hgeometric

/-- The arbitrary-near first/last pairing has the geometric endpoint value. -/
theorem horizontal_cap_pairing_withNear_first_last
    (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin (n + 1) → PlanarPoint ℝ)
    (hq : CyclicGeneric q)
    (hzero : (q ⟨0, by omega⟩).2 = 0)
    (hothers : ∀ x : Fin (n + 1),
      x ≠ ⟨0, by omega⟩ → (q x).2 ≠ 0)
    (d : ℕ → ℚ)
    (hnear : ∀ r : Fin n,
      d (r.val + 1) =
        scalarSignValue (q ⟨r.val + 1, by omega⟩).2) :
    horizontalCapPairingWithNear q d
      ⟨0, by have := hq.size_ge_three; omega⟩
      ⟨n - 1, by have := hq.size_ge_three; omega⟩ =
      ((scalarSignValue (q ⟨n, by omega⟩).2 +
        scalarSignValue (q ⟨1, by have := hq.size_ge_three; omega⟩).2) / 2) *
        polygonAmplitude q hq := by
  have hn : 2 ≤ n := by have := hq.size_ge_three; omega
  let w := horizontalComplementWord q 0
  have hgeneric : ShortEdgeSignStability.CoreHGeneric w n :=
    horizontalComplementWord_core_generic q hq.g1 hzero
  obtain ⟨rho, hrho, hstable⟩ :=
    EndpointGenericStability.exists_endpoint_current_stability_radius w (-1, 0) n hgeneric
  obtain ⟨delta, hdelta, hcap⟩ :=
    exists_horizontal_capExpansion_withNear hRI q hq hzero hothers d hnear
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
  change capCutExpansion (j := n + 1) d
    (ordinaryCurrent (fun _ k _ => d k)
      (polygonSignArray (horizontalComplementWord q epsilon))) 0 = _ at hvalue
  rw [← weightedCutSumNonempty_eq_capCutExpansion d _ (by omega : 0 < n + 1)] at hvalue
  rw [hsum] at hvalue
  exact hvalue






end DirectGLSSW.HorizontalShortEdge
