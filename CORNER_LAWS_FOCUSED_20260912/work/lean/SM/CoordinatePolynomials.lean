import SM.Polygon
import SM.PolynomialShear
import SM.DeterminantPolynomial

/-! Actual scalar vertex polynomials for the polynomial-controls lemma.
The scalar assignments and labelled tuples are inverse presentations of the
same unrestricted coordinate space. The area determinant is transported by an
explicit automorphism of the entire coordinate ring, including unused variables.
This module proves the Δ irreducibility clause, not the complete source lemma. -/

namespace SM

open MvPolynomial

noncomputable section

abbrev ScalarCoordinate (n : ℕ) := ZMod n × Fin 2
abbrev CoordinatePolynomial (n : ℕ) := MvPolynomial (ScalarCoordinate n) ℝ

variable {n : ℕ}

def scalarCoordinates (P : LabelledTuple n) (c : ScalarCoordinate n) : ℝ :=
  if c.2 = 0 then (P c.1).1 else (P c.1).2

def tupleOfScalarCoordinates (x : ScalarCoordinate n → ℝ) : LabelledTuple n :=
  fun i => (x (i, 0), x (i, 1))

@[simp] theorem tupleOf_scalarCoordinates (P : LabelledTuple n) :
    tupleOfScalarCoordinates (scalarCoordinates P) = P := by
  funext i
  simp [tupleOfScalarCoordinates, scalarCoordinates]

@[simp] theorem scalarCoordinates_tupleOf (x : ScalarCoordinate n → ℝ) :
    scalarCoordinates (tupleOfScalarCoordinates x) = x := by
  funext c
  obtain ⟨i, c⟩ := c
  fin_cases c <;> simp [scalarCoordinates, tupleOfScalarCoordinates]

def scalarCoordinateEquiv (n : ℕ) : LabelledTuple n ≃ (ScalarCoordinate n → ℝ) where
  toFun := scalarCoordinates
  invFun := tupleOfScalarCoordinates
  left_inv := tupleOf_scalarCoordinates
  right_inv := scalarCoordinates_tupleOf

def coordinateX (i : ZMod n) : CoordinatePolynomial n := X (i, 0)
def coordinateY (i : ZMod n) : CoordinatePolynomial n := X (i, 1)

@[simp] theorem eval_coordinateX (P : LabelledTuple n) (i : ZMod n) :
    eval (scalarCoordinates P) (coordinateX i) = (P i).1 := by
  simp [coordinateX, scalarCoordinates]

@[simp] theorem eval_coordinateY (P : LabelledTuple n) (i : ZMod n) :
    eval (scalarCoordinates P) (coordinateY i) = (P i).2 := by
  simp [coordinateY, scalarCoordinates]

def areaPolynomial (i j k : ZMod n) : CoordinatePolynomial n :=
  (coordinateX j - coordinateX i) * (coordinateY k - coordinateY i) -
    (coordinateY j - coordinateY i) * (coordinateX k - coordinateX i)

@[simp] theorem eval_areaPolynomial (P : LabelledTuple n) (i j k : ZMod n) :
    eval (scalarCoordinates P) (areaPolynomial i j k) = det (P j - P i) (P k - P i) := by
  simp [areaPolynomial, det]

/-- Translate every other vertex by minus the fixed base vertex, retaining the
base vertex itself. The generic shear supplies the inverse by addition. -/
def vertexCoordinateTranslation (i : ZMod n) :
    CoordinatePolynomial n ≃ₐ[ℝ] CoordinatePolynomial n := by
  classical
  exact polynomialShear (fun c : ScalarCoordinate n => c.1 ≠ i)
    (fun c => (i, c.2)) (by intro c hc; simp)

theorem vertexCoordinateTranslation_X (i j : ZMod n) (hji : j ≠ i) :
    vertexCoordinateTranslation i (coordinateX j) = coordinateX j - coordinateX i := by
  classical
  simp [vertexCoordinateTranslation, coordinateX, hji]

theorem vertexCoordinateTranslation_Y (i j : ZMod n) (hji : j ≠ i) :
    vertexCoordinateTranslation i (coordinateY j) = coordinateY j - coordinateY i := by
  classical
  simp [vertexCoordinateTranslation, coordinateY, hji]

theorem areaPolynomial_irreducible (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Irreducible (areaPolynomial i j k) := by
  have hq : Irreducible (coordinateX j * coordinateY k - coordinateY j * coordinateX k) :=
    determinantPolynomial_irreducible (j, 0) (k, 1) (j, 1) (k, 0)
      (by simp) (by simp) (by simpa using hjk) (by simpa using hjk.symm) (by simp)
  have ht := (MulEquiv.irreducible_iff (vertexCoordinateTranslation i)).mpr hq
  simpa only [map_sub, map_mul, vertexCoordinateTranslation_X i j hij.symm,
    vertexCoordinateTranslation_Y i j hij.symm, vertexCoordinateTranslation_X i k hik.symm,
    vertexCoordinateTranslation_Y i k hik.symm, areaPolynomial] using ht

theorem areaPolynomial_ne_zero (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : areaPolynomial i j k ≠ 0 :=
  (areaPolynomial_irreducible i j k hij hik hjk).ne_zero

end

end SM
