import ActiveArcGammaM
import DirectGLSSW.OpenMarkedCurrent

set_option autoImplicit false
open scoped BigOperators
namespace DirectGLSSW.SourceOpenCurrentMeaning
open OpenMarkedCurrent

theorem interval_matrix_literal (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (i j : Fin n) :
    intervalMatrix (polygonSignArray q) n i j =
      if i.val < j.val then ordinaryCurrent (fun _ _ _ => -1)
        (polygonSignArray q) i.val j.val else 0 := rfl

theorem finite_inverse_two_sided (H : TripleArray) (n : ℕ) :
    let B := intervalMatrix H n
    finiteInverse B n * (1+B) = 1 ∧ (1+B) * finiteInverse B n = 1 := by
  apply strictUpper_finiteInverse
  intro i j hji
  simp [intervalMatrix, Nat.not_lt.mpr hji]

theorem finite_inverse_existsUnique (H : TripleArray) (n : ℕ) :
    let B := intervalMatrix H n
    ∃! R : Matrix (Fin n) (Fin n) ℚ, R*(1+B)=1 ∧ (1+B)*R=1 := by
  dsimp only
  let B := intervalMatrix H n
  let R := finiteInverse B n
  have hR : R*(1+B)=1 ∧ (1+B)*R=1 := finite_inverse_two_sided H n
  refine ⟨R,hR,?_⟩
  intro X hX
  calc
    X = X*((1+B)*R) := by rw [hR.2,mul_one]
    _ = (X*(1+B))*R := (mul_assoc _ _ _).symm
    _ = R := by rw [hX.1,one_mul]

theorem resolvent_finite_series (H : TripleArray) (n : ℕ) :
    literalResolvent H n = intervalMatrix H n *
      ∑ k ∈ Finset.range n, (-intervalMatrix H n)^k := rfl

theorem entry_signed_cut_cardinality (H : TripleArray) (i j : ℕ) :
    entry H i j = ∑ S ∈ (Finset.Ioo i j).powerset,
      (-1 : ℚ)^S.card * branchProduct (ordinaryCurrent (fun _ _ _ => -1) H)
        (cutVertices i j S) := by
  simp only [entry_eq_signedCutExpansion, Finset.prod_const]

theorem actual_open_word_resolvent {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : ActiveArc.Regular q)
    (S : ActiveArc.Primitive.Support q hR) :
    let m := ActiveArc.RetainedWords.openCount q hR S.val
    let H := polygonSignArray (rootedPolygonWord
      (ActiveArc.Primitive.OpenVertex q hR S) (ActiveArc.RetainedWords.openLast q hR S.val))
    ActiveArc.Primitive.openCurrent q hR S =
      literalResolvent H m
        ⟨0, by have := ActiveArc.RetainedWords.open_count_ge_two q hR S.val; omega⟩
        ⟨m-1, by have := ActiveArc.RetainedWords.open_count_ge_two q hR S.val; omega⟩ := by
  dsimp only
  unfold ActiveArc.Primitive.openCurrent
  have hm := ActiveArc.RetainedWords.open_count_ge_two q hR S.val
  exact entry_eq_literalResolvent
    (n := ActiveArc.RetainedWords.openCount q hR S.val) _
    ⟨0, by omega⟩ ⟨ActiveArc.RetainedWords.openCount q hR S.val-1, by omega⟩
    (by change 0 < ActiveArc.RetainedWords.openCount q hR S.val-1; omega)

end DirectGLSSW.SourceOpenCurrentMeaning
