import DirectGLSSW.GlobalCapIntertwining
import DirectGLSSW.CapCrossingEventStability

set_option autoImplicit false
namespace DirectGLSSW.SourceLineTransferMeaning
open GlobalCapIntertwining GlobalCapAlgebra GlobalCapEntry CapActualBranches

theorem actual_F_inverse_existsUnique (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    ∃! V : Matrix (Fin n) (Fin n) ℚ,
      V * lineCapF q n = 1 ∧ lineCapF q n * V = 1 := by
  refine ⟨1 + lineCapC q n,
    ⟨lineCapF_left_inverse q n, lineCapF_right_inverse q n⟩, ?_⟩
  intro V hV
  calc
    V = V * (lineCapF q n * (1 + lineCapC q n)) := by
      rw [lineCapF_right_inverse, mul_one]
    _ = (V * lineCapF q n) * (1 + lineCapC q n) := (mul_assoc _ _ _).symm
    _ = 1 + lineCapC q n := by rw [hV.1, one_mul]

theorem J_characterization (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    lineCapJ q n = (1 + lineCapC q n) * lineCapS q n * lineCapF q n ∧
    (1 + lineCapC q n) * lineCapF q n = 1 ∧
    lineCapF q n * (1 + lineCapC q n) = 1 :=
  ⟨rfl, lineCapF_left_inverse q n, lineCapF_right_inverse q n⟩

theorem U_literal (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    lineCapU q n =
      lineCapS q n * globalCapResolvent
        (capInternalMatrix q (lineCapNear q n) n) (lineCapHeights q n) *
      capTerminalMatrix q (lineCapNear q n) n := rfl

theorem wronskian_entry (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ k, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (a b : Fin n) (hab : a.val < b.val)
    (hcap : CyclicGeneric (lineCapCore q a b)) :
    lineCapPairing q n a b =
      ((lineCapHeights q n a + lineCapHeights q n b) / 2) *
        polygonAmplitude (lineCapCore q a b) hcap :=
  lineCapPairing_entry hRI q n hzero hothers a b hab hcap

theorem wronskian_diagonal (q : ℕ → PlanarPoint ℝ) (n : ℕ) (a : Fin n) :
    lineCapPairing q n a a = lineCapHeights q n a :=
  lineCapPairing_diagonal q n a

theorem wronskian_commutes (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ k, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (hcaps : ∀ a b : Fin n, a.val < b.val → CyclicGeneric (lineCapCore q a b)) :
    lineCapS q n * lineCapPairing q n = lineCapPairing q n * lineCapS q n :=
  lineCapPairing_commutes hRI q n hzero hothers hcaps

theorem actual_intertwining (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (hothers : ∀ k, 0 < k → k ≤ n → (q k).2 ≠ 0)
    (hcaps : ∀ a b : Fin n, a.val < b.val → CyclicGeneric (lineCapCore q a b)) :
    lineCapJ q n * lineCapU q n = lineCapU q n * lineCapS q n ∧
    lineCapF q n * lineCapJ q n = lineCapS q n * lineCapF q n :=
  ⟨lineCap_JU_eq_US hRI q n hzero hothers hcaps, lineCap_FJ_eq_SF q n⟩

end DirectGLSSW.SourceLineTransferMeaning

