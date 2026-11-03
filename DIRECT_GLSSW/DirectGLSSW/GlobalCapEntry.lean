import DirectGLSSW.GlobalCapAlgebra
import DirectGLSSW.CapSubwordBridge
import DirectGLSSW.HorizontalCapNear

set_option autoImplicit false

namespace DirectGLSSW.GlobalCapEntry
open DirectGLSSW.GlobalCapAlgebra DirectGLSSW.CapSubwordBridge
open DirectGLSSW.CapMatrixRestriction DirectGLSSW.HorizontalShortEdge

def lineCapCore {n : ℕ} (q : ℕ → PlanarPoint ℝ) (a b : Fin n) :
    Fin (b.val - a.val + 1 + 1) → PlanarPoint ℝ :=
  capSubwordFin q a.val (b.val - a.val + 1)

private theorem subword_eq_horizontal (q : ℕ → PlanarPoint ℝ)
    (offset m : ℕ) (hzero : (q 0).2 = 0) :
    capSubwordNat q offset m =
      horizontalComplementWord (capSubwordFin q offset m) 0 := by
  funext k
  by_cases hk0 : k = 0
  · subst k
    apply Prod.ext <;>
      simp [capSubwordNat, capSubwordFin, horizontalComplementWord, hzero]
  · by_cases hkm : k ≤ m
    · have hlt : k < m + 1 := by omega
      simp [capSubwordNat, capSubwordFin, horizontalComplementWord, hk0, hkm, hlt]
    · have hlt : ¬ k < m + 1 := by omega
      simp [capSubwordNat, capSubwordFin, horizontalComplementWord, hk0, hkm, hlt]

theorem lineCapPairing_entry (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ k : ℕ, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (a b : Fin n) (hab : a.val < b.val)
    (hcap : CyclicGeneric (lineCapCore q a b)) :
    lineCapPairing q n a b =
      ((lineCapHeights q n a + lineCapHeights q n b) / 2) *
        polygonAmplitude (lineCapCore q a b) hcap := by
  let m := b.val - a.val + 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hbound : a.val + m ≤ n := by dsimp [m]; have := b.isLt; omega
  let Q := capSubwordFin q a.val m
  let d := fun k => scalarSignValue (q k).2
  let e := consecutiveBlockEmbedding a.val hbound
  have hQ : CyclicGeneric Q := hcap
  have hQzero : (Q ⟨0, by omega⟩).2 = 0 := by
    simpa [Q, capSubwordFin] using hzero
  have hQothers : ∀ x : Fin (m + 1), x ≠ ⟨0, by omega⟩ → (Q x).2 ≠ 0 := by
    intro x hx
    have hx0 : x.val ≠ 0 := fun h => hx (Fin.ext h)
    have hpoint : Q x = q (a.val + x.val) := by simp [Q, capSubwordFin, hx0]
    rw [hpoint]
    apply hothers
    · omega
    · have := x.isLt; omega
  have hnear : ∀ k : Fin m, capSubwordNear d a.val (k.val + 1) =
      scalarSignValue (Q ⟨k.val + 1, by omega⟩).2 := by
    intro k
    simp [capSubwordNear, d, Q, capSubwordFin]
  have hvalue := horizontal_cap_pairing_withNear_first_last hRI Q hQ
    hQzero hQothers (capSubwordNear d a.val) hnear
  have hword : capSubwordNat q a.val m = horizontalComplementWord Q 0 :=
    subword_eq_horizontal q a.val m hzero
  have hstart : horizontalComplementWord Q 0 0 = q 0 := by
    apply Prod.ext <;> simp [horizontalComplementWord, Q, capSubwordFin, hzero]
  have hblock := capPairing_submatrix_consecutive q (q 0) d hbound
  rw [hword] at hblock
  have hblock' : (lineCapPairing q n).submatrix e e =
      horizontalCapPairingWithNear Q (capSubwordNear d a.val) := by
    simpa only [lineCapPairing, lineCapHeights, horizontalCapPairingWithNear, hstart]
      using hblock
  have hfirst : e ⟨0, by omega⟩ = a := by
    apply Fin.ext
    simp [e, consecutiveBlockEmbedding]
  have hlast : e ⟨m - 1, by omega⟩ = b := by
    apply Fin.ext
    dsimp [e, consecutiveBlockEmbedding, m]
    omega
  have hentry := congrArg (fun M : Matrix (Fin m) (Fin m) ℚ =>
      M ⟨0, by omega⟩ ⟨m - 1, by omega⟩) hblock'
  change lineCapPairing q n (e ⟨0, by omega⟩) (e ⟨m - 1, by omega⟩) = _ at hentry
  rw [hfirst, hlast] at hentry
  dsimp only at hentry
  rw [hentry, hvalue]
  have hQlast : Q ⟨m, by omega⟩ = q (b.val + 1) := by
    have hm0 : m ≠ 0 := by omega
    simp only [Q, capSubwordFin, Fin.val_mk, if_neg hm0]
    congr 1
    dsimp [m]
    omega
  have hQfirst : Q ⟨1, by omega⟩ = q (a.val + 1) := by simp [Q, capSubwordFin]
  rw [hQlast, hQfirst]
  have hAmp : polygonAmplitude Q hQ = polygonAmplitude (lineCapCore q a b) hcap := rfl
  rw [hAmp]
  dsimp only [lineCapHeights]
  ring

private theorem scalarSignValue_sq_one (x : ℝ) (hx : x ≠ 0) :
    scalarSignValue x ^ 2 = 1 := by
  by_cases hneg : x < 0 <;> simp [scalarSignValue, hx, hneg]

theorem lineCapPairing_commutes (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ k : ℕ, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (hcaps : ∀ a b : Fin n, a.val < b.val → CyclicGeneric (lineCapCore q a b)) :
    Matrix.diagonal (lineCapHeights q n) * lineCapPairing q n =
      lineCapPairing q n * Matrix.diagonal (lineCapHeights q n) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : a.val < b.val
  · rw [lineCapPairing_entry hRI q n hzero hothers a b hab (hcaps a b hab)]
    have ha : lineCapHeights q n a ^ 2 = 1 :=
      scalarSignValue_sq_one _ (hothers (a.val + 1) (by omega) (by have := a.isLt; omega))
    have hb : lineCapHeights q n b ^ 2 = 1 :=
      scalarSignValue_sq_one _ (hothers (b.val + 1) (by omega) (by have := b.isLt; omega))
    apply sub_eq_zero.mp
    calc
      _ = ((lineCapHeights q n a) ^ 2 - (lineCapHeights q n b) ^ 2) *
          polygonAmplitude (lineCapCore q a b) (hcaps a b hab) / 2 := by ring
      _ = 0 := by rw [ha, hb]; ring
  · by_cases heq : a = b
    · subst b
      exact mul_comm _ _
    · have hne : a.val ≠ b.val := fun h => heq (Fin.ext h)
      have hba : b.val < a.val := by omega
      rw [lineCapPairing_below q n a b hba]
      simp







end DirectGLSSW.GlobalCapEntry
