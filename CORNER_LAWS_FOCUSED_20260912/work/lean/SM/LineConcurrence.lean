import SM.PolynomialAvoidance
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FunProp

/-! Actual homogeneous edge-line rows and their 3x3 concurrence determinant.
A common finite point forces this determinant to vanish. -/

namespace SM

open Polynomial

variable {n : ℕ}

def edgeLineA (P : LabelledTuple n) (i : ZMod n) : ℝ := (P i).2 - (P (i + 1)).2

def edgeLineB (P : LabelledTuple n) (i : ZMod n) : ℝ := (P (i + 1)).1 - (P i).1

def edgeLineC (P : LabelledTuple n) (i : ZMod n) : ℝ :=
  (P i).1 * (P (i + 1)).2 - (P (i + 1)).1 * (P i).2

def edgeLineRow (P : LabelledTuple n) (i : ZMod n) : Fin 3 → ℝ :=
  ![edgeLineA P i, edgeLineB P i, edgeLineC P i]

def concurrenceMatrix (P : LabelledTuple n) (i j k : ZMod n) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![edgeLineRow P i, edgeLineRow P j, edgeLineRow P k]

noncomputable def concurrenceDet (P : LabelledTuple n) (i j k : ZMod n) : ℝ :=
  (concurrenceMatrix P i j k).det

theorem concurrenceDet_formula (P : LabelledTuple n) (i j k : ZMod n) :
    concurrenceDet P i j k =
      edgeLineA P i * edgeLineB P j * edgeLineC P k -
      edgeLineA P i * edgeLineC P j * edgeLineB P k -
      edgeLineB P i * edgeLineA P j * edgeLineC P k +
      edgeLineB P i * edgeLineC P j * edgeLineA P k +
      edgeLineC P i * edgeLineA P j * edgeLineB P k -
      edgeLineC P i * edgeLineB P j * edgeLineA P k := by
  unfold concurrenceDet
  rw [Matrix.det_fin_three]
  rfl

@[continuity, fun_prop] theorem continuous_edgeLineA (i : ZMod n) :
    Continuous (fun P : LabelledTuple n => edgeLineA P i) :=
  (continuous_vertex i).snd.sub (continuous_vertex (i + 1)).snd

@[continuity, fun_prop] theorem continuous_edgeLineB (i : ZMod n) :
    Continuous (fun P : LabelledTuple n => edgeLineB P i) :=
  (continuous_vertex (i + 1)).fst.sub (continuous_vertex i).fst

@[continuity, fun_prop] theorem continuous_edgeLineC (i : ZMod n) :
    Continuous (fun P : LabelledTuple n => edgeLineC P i) :=
  ((continuous_vertex i).fst.mul (continuous_vertex (i + 1)).snd).sub
    ((continuous_vertex (i + 1)).fst.mul (continuous_vertex i).snd)

theorem continuous_concurrenceDet (i j k : ZMod n) :
    Continuous (fun P : LabelledTuple n => concurrenceDet P i j k) := by
  simp only [concurrenceDet_formula]
  fun_prop

theorem edgePoint_line_equation (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    edgeLineA P i * (edgePoint P i t).1 + edgeLineB P i * (edgePoint P i t).2 +
      edgeLineC P i = 0 := by
  dsimp [edgeLineA, edgeLineB, edgeLineC, edgePoint, edge]
  ring

theorem edgeSegment_line_equation (P : LabelledTuple n) (i : ZMod n) {x : Plane}
    (hx : x ∈ edgeSegment P i) :
    edgeLineA P i * x.1 + edgeLineB P i * x.2 + edgeLineC P i = 0 := by
  obtain ⟨t, _, _, rfl⟩ := hx
  exact edgePoint_line_equation P i t

theorem concurrenceDet_eq_zero_of_common_point (P : LabelledTuple n) (i j k : ZMod n)
    (x : Plane)
    (hi : edgeLineA P i * x.1 + edgeLineB P i * x.2 + edgeLineC P i = 0)
    (hj : edgeLineA P j * x.1 + edgeLineB P j * x.2 + edgeLineC P j = 0)
    (hk : edgeLineA P k * x.1 + edgeLineB P k * x.2 + edgeLineC P k = 0) :
    concurrenceDet P i j k = 0 := by
  rw [concurrenceDet_formula]
  linear_combination
    (edgeLineA P j * edgeLineB P k - edgeLineB P j * edgeLineA P k) * hi +
    (edgeLineB P i * edgeLineA P k - edgeLineA P i * edgeLineB P k) * hj +
    (edgeLineA P i * edgeLineB P j - edgeLineB P i * edgeLineA P j) * hk

theorem concurrenceDet_eq_zero_of_closedTriple (P : LabelledTuple n) (i j k : ZMod n)
    (h : ClosedTripleMeet P i j k) : concurrenceDet P i j k = 0 := by
  obtain ⟨x, hi, hj, hk⟩ := h
  exact concurrenceDet_eq_zero_of_common_point P i j k x
    (edgeSegment_line_equation P i hi) (edgeSegment_line_equation P j hj)
    (edgeSegment_line_equation P k hk)

noncomputable def lineAPolynomial (P Q : LabelledTuple n) (i : ZMod n) : ℝ[X] :=
  lineYPolynomial P Q i - lineYPolynomial P Q (i + 1)

noncomputable def lineBPolynomial (P Q : LabelledTuple n) (i : ZMod n) : ℝ[X] :=
  lineXPolynomial P Q (i + 1) - lineXPolynomial P Q i

noncomputable def lineCPolynomial (P Q : LabelledTuple n) (i : ZMod n) : ℝ[X] :=
  lineXPolynomial P Q i * lineYPolynomial P Q (i + 1) -
    lineXPolynomial P Q (i + 1) * lineYPolynomial P Q i

@[simp] theorem eval_lineAPolynomial (P Q : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    (lineAPolynomial P Q i).eval t = edgeLineA (tupleLine P Q t) i := by
  simp [lineAPolynomial, edgeLineA]

@[simp] theorem eval_lineBPolynomial (P Q : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    (lineBPolynomial P Q i).eval t = edgeLineB (tupleLine P Q t) i := by
  simp [lineBPolynomial, edgeLineB]

@[simp] theorem eval_lineCPolynomial (P Q : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    (lineCPolynomial P Q i).eval t = edgeLineC (tupleLine P Q t) i := by
  simp [lineCPolynomial, edgeLineC]

noncomputable def concurrenceLinePolynomial (P Q : LabelledTuple n) (i j k : ZMod n) : ℝ[X] :=
  lineAPolynomial P Q i * lineBPolynomial P Q j * lineCPolynomial P Q k -
  lineAPolynomial P Q i * lineCPolynomial P Q j * lineBPolynomial P Q k -
  lineBPolynomial P Q i * lineAPolynomial P Q j * lineCPolynomial P Q k +
  lineBPolynomial P Q i * lineCPolynomial P Q j * lineAPolynomial P Q k +
  lineCPolynomial P Q i * lineAPolynomial P Q j * lineBPolynomial P Q k -
  lineCPolynomial P Q i * lineBPolynomial P Q j * lineAPolynomial P Q k

theorem concurrence_polynomial_on_lines (i j k : ZMod n) :
    PolynomialOnTupleLines (fun P : LabelledTuple n => concurrenceDet P i j k) := by
  intro P Q
  refine ⟨concurrenceLinePolynomial P Q i j k, ?_⟩
  intro t
  simp [concurrenceLinePolynomial, concurrenceDet_formula]

end SM
