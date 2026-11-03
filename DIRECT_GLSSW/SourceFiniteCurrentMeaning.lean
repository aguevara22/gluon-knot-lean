import DirectGLSSW.GlobalCapAlgebra
import DirectGLSSW.SpinorVertices

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceFiniteCurrentMeaning
open DirectGLSSW.CapActualBranches DirectGLSSW.GlobalCapAlgebra

theorem far_sign_literal (q : ℕ → PlanarPoint ℝ) (i k j : ℕ) :
    polygonSignArray q i k j =
      scalarSignValue (planarDet (q k - q j) (q i - q j)) := rfl

theorem far_sign_negative_turn (q : ℕ → PlanarPoint ℝ) (i k j : ℕ) :
    polygonSignArray q i k j =
      scalarSignValue (-planarDet (q k - q i) (q j - q k)) := by
  simp only [polygonSignArray, polygonHDet_eq_neg_turn, polygonChord]

theorem first_current_literal (q : ℕ → PlanarPoint ℝ) (p : PlanarPoint ℝ)
    (d : ℕ → ℚ) (n : ℕ) (a b : Fin n) (hab : a ≤ b) :
    capEndpointMatrix q p d n a b =
      ordinaryCurrent (fun _ k _ => d k)
        (polygonSignArray (EndpointCurrent.endpointWord (capComplement q p) a.val))
        a.val (b.val + 1) :=
  EndpointCurrent.endpointCurrent_polygon_eq (capComplement q p) d hab

theorem first_current_diagonal (q : ℕ → PlanarPoint ℝ) (p : PlanarPoint ℝ)
    (d : ℕ → ℚ) (n : ℕ) (a : Fin n) : capEndpointMatrix q p d n a a = 1 :=
  EndpointCurrent.endpointCurrent_diagonal d _ a.val

theorem first_current_below (q : ℕ → PlanarPoint ℝ) (p : PlanarPoint ℝ)
    (d : ℕ → ℚ) (n : ℕ) (a b : Fin n) (hba : b < a) :
    capEndpointMatrix q p d n a b = 0 :=
  EndpointCurrent.endpointCurrent_below d _ hba

theorem fixed_internal_current_literal (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) :
    capInternalMatrix q (fun k => scalarSignValue (q k).2) n a b =
      if a.val < b.val then ordinaryCurrent (fun _ k _ => scalarSignValue (q k).2)
        (polygonSignArray q) (a.val+1) (b.val+1) else 0 := rfl

theorem fixed_resolvent_two_sided (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    let B := capInternalMatrix q (fun k => scalarSignValue (q k).2) n
    let S := Matrix.diagonal (lineCapHeights q n)
    let R := globalCapResolvent B (lineCapHeights q n)
    R * (1 - B * S) = 1 ∧ (1 - B * S) * R = 1 := by
  dsimp only
  let B := capInternalMatrix q (fun k => scalarSignValue (q k).2) n
  let S := Matrix.diagonal (lineCapHeights q n)
  have hB : StrictUpper B := cap_internalMatrix_strictUpper q _ n
  have hX : StrictUpper (-(B * S)) := by
    intro i j hji
    simp only [Matrix.neg_apply, Matrix.mul_diagonal, hB i j hji, zero_mul, neg_zero, S]
  simpa only [globalCapResolvent, sub_eq_add_neg, B, S] using
    strictUpper_finiteInverse (-(B * S)) hX

theorem fixed_resolvent_existsUnique (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    let B := capInternalMatrix q (fun k => scalarSignValue (q k).2) n
    let S := Matrix.diagonal (lineCapHeights q n)
    ∃! R : Matrix (Fin n) (Fin n) ℚ,
      R * (1 - B * S) = 1 ∧ (1 - B * S) * R = 1 := by
  dsimp only
  let B := capInternalMatrix q (fun k => scalarSignValue (q k).2) n
  let S := Matrix.diagonal (lineCapHeights q n)
  let R := globalCapResolvent B (lineCapHeights q n)
  have hR : R * (1-B*S) = 1 ∧ (1-B*S) * R = 1 :=
    fixed_resolvent_two_sided q n
  refine ⟨R, hR, ?_⟩
  intro X hX
  calc
    X = X * ((1-B*S) * R) := by rw [hR.2, mul_one]
    _ = (X * (1-B*S)) * R := (mul_assoc _ _ _).symm
    _ = R := by rw [hX.1, one_mul]

theorem terminal_current_literal (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ)
    (n : ℕ) (a b : Fin n) (hab : a ≤ b) :
    capTerminalMatrix q d n a b =
      ordinaryCurrent (fun _ k _ => d k)
        (polygonSignArray (TerminalEndpoint.terminalWord q (b.val+2)))
        (a.val+1) (b.val+2) :=
  TerminalEndpoint.terminalCurrent_polygon_eq q d hab

theorem terminal_current_diagonal (q : ℕ → PlanarPoint ℝ) (d : ℕ → ℚ)
    (n : ℕ) (a : Fin n) : capTerminalMatrix q d n a a = 1 :=
  TerminalEndpoint.terminalCurrent_diagonal d _ a.val

theorem pairing_literal (q : ℕ → PlanarPoint ℝ) (n : ℕ) :
    let d := fun k => scalarSignValue (q k).2
    let F := capEndpointMatrix q (q 0) d n
    let B := capInternalMatrix q d n
    let G := capTerminalMatrix q d n
    let S := Matrix.diagonal (lineCapHeights q n)
    lineCapPairing q n = F * S * globalCapResolvent B (lineCapHeights q n) * G := rfl

end DirectGLSSW.SourceFiniteCurrentMeaning
