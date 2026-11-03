import DirectGLSSW.GlobalCapEntry
import DirectGLSSW.EndpointActualPropagation

set_option autoImplicit false

namespace DirectGLSSW.GlobalCapIntertwining

open DirectGLSSW
open DirectGLSSW.CapActualBranches
open DirectGLSSW.GlobalCapAlgebra
open DirectGLSSW.GlobalCapEntry

noncomputable def lineCapNear (q : ℕ → PlanarPoint ℝ) (n : ℕ) : ℕ → ℚ :=
  fun k => scalarSignValue (q k).2

noncomputable def lineCapF (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  capEndpointMatrix q (q 0) (lineCapNear q n) n

noncomputable def lineCapC (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  EndpointPropagation.finiteKernel
    (EndpointCurrent.endpointCoefficient (lineCapNear q n) (polygonSignArray q)) n

noncomputable def lineCapS (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (GlobalCapAlgebra.lineCapHeights q n)

noncomputable def lineCapU (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  lineCapS q n * DirectGLSSW.globalCapResolvent
      (capInternalMatrix q (lineCapNear q n) n)
      (GlobalCapAlgebra.lineCapHeights q n) *
    capTerminalMatrix q (lineCapNear q n) n

noncomputable def lineCapJ (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (1 + lineCapC q n) * lineCapS q n * lineCapF q n

private theorem capComplement_self (q : ℕ → PlanarPoint ℝ) :
    capComplement q (q 0) = q := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [capComplement]
  · simp [capComplement, hx]

private theorem lineCapC_strictUpper (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    StrictUpper (lineCapC q n) := by
  intro i j hji
  simp [lineCapC, EndpointPropagation.finiteKernel, Nat.not_lt.mpr hji]

theorem lineCapF_eq_finiteInverse (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    lineCapF q n = DirectGLSSW.finiteInverse (lineCapC q n) n := by
  change (fun a b : Fin n => EndpointCurrent.endpointCurrent
      (lineCapNear q n)
      (polygonSignArray (capComplement q (q 0))) a.val b.val) =
    DirectGLSSW.finiteInverse
      (EndpointPropagation.finiteKernel
        (EndpointCurrent.endpointCoefficient (lineCapNear q n) (polygonSignArray q)) n) n
  rw [capComplement_self]
  exact EndpointCurrent.endpointCurrent_eq_finiteInverse
    (lineCapNear q n) (polygonSignArray q) n

theorem lineCapF_left_inverse (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    (1 + lineCapC q n) * lineCapF q n = 1 := by
  rw [lineCapF_eq_finiteInverse]
  exact (DirectGLSSW.strictUpper_finiteInverse (lineCapC q n)
    (lineCapC_strictUpper q n)).2

theorem lineCapF_right_inverse (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    lineCapF q n * (1 + lineCapC q n) = 1 := by
  rw [lineCapF_eq_finiteInverse]
  exact (DirectGLSSW.strictUpper_finiteInverse (lineCapC q n)
    (lineCapC_strictUpper q n)).1

theorem lineCapPairing_eq_FU (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    GlobalCapAlgebra.lineCapPairing q n = lineCapF q n * lineCapU q n := by
  change
    (capEndpointMatrix q (q 0) (lineCapNear q n) n *
      Matrix.diagonal (GlobalCapAlgebra.lineCapHeights q n) *
      DirectGLSSW.globalCapResolvent (capInternalMatrix q (lineCapNear q n) n)
        (GlobalCapAlgebra.lineCapHeights q n) *
      capTerminalMatrix q (lineCapNear q n) n) =
    capEndpointMatrix q (q 0) (lineCapNear q n) n *
      (Matrix.diagonal (GlobalCapAlgebra.lineCapHeights q n) *
        DirectGLSSW.globalCapResolvent (capInternalMatrix q (lineCapNear q n) n)
          (GlobalCapAlgebra.lineCapHeights q n) *
        capTerminalMatrix q (lineCapNear q n) n)
  simp [mul_assoc]

theorem lineCap_FJ_eq_SF (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    lineCapF q n * lineCapJ q n = lineCapS q n * lineCapF q n := by
  change lineCapF q n *
      ((1 + lineCapC q n) * lineCapS q n * lineCapF q n) =
    lineCapS q n * lineCapF q n
  calc
    _ = ((lineCapF q n * (1 + lineCapC q n)) * lineCapS q n) * lineCapF q n := by
      simp [mul_assoc]
    _ = lineCapS q n * lineCapF q n := by
      rw [lineCapF_right_inverse]
      simp

theorem lineCap_JU_eq_US (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ k, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (hcaps : ∀ a b : Fin n, a.val < b.val →
      CyclicGeneric (GlobalCapEntry.lineCapCore q a b)) :
    lineCapJ q n * lineCapU q n = lineCapU q n * lineCapS q n := by
  let F := lineCapF q n
  let C := lineCapC q n
  let S := lineCapS q n
  let U := lineCapU q n
  let W := GlobalCapAlgebra.lineCapPairing q n
  have hleft : (1 + C) * F = 1 := by
    dsimp [F, C]
    exact lineCapF_left_inverse q n
  have hfu : W = F * U := by
    dsimp [F, U, W]
    exact lineCapPairing_eq_FU q n
  have hcomm : S * W = W * S := by
    dsimp [S, W]
    exact GlobalCapEntry.lineCapPairing_commutes hRI q n hzero hothers hcaps
  change ((1 + C) * S * F) * U = U * S
  calc
    ((1 + C) * S * F) * U = (1 + C) * (S * (F * U)) := by simp [mul_assoc]
    _ = (1 + C) * (S * W) := by rw [hfu]
    _ = (1 + C) * (W * S) := by rw [hcomm]
    _ = U * S := by
      rw [hfu]
      calc
        (1 + C) * ((F * U) * S) = ((1 + C) * F) * U * S := by simp [mul_assoc]
        _ = U * S := by rw [hleft]; simp
















end DirectGLSSW.GlobalCapIntertwining
