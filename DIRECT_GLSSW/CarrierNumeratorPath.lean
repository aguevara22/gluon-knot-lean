import CarrierWitnessEvaluation
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CarrierNumeratorPath
open DirectGLSSW.AuxiliaryCarrierChart DirectGLSSW.CarrierWitnessEvaluation

def scalarPath (x y t : ℝ) : ℝ := x + t * (y - x)
def carrierPath (L M : CarrierLine) (t : ℝ) : CarrierLine :=
  ((scalarPath L.1.1 M.1.1 t, scalarPath L.1.2 M.1.2 t),
    scalarPath L.2 M.2 t)

def scalarPolynomial (x y : ℝ) : Polynomial ℝ :=
  Polynomial.C x + Polynomial.X * Polynomial.C (y - x)
abbrev PolynomialCarrier := (Polynomial ℝ × Polynomial ℝ) × Polynomial ℝ
def carrierPolynomial (L M : CarrierLine) : PolynomialCarrier :=
  ((scalarPolynomial L.1.1 M.1.1, scalarPolynomial L.1.2 M.1.2),
    scalarPolynomial L.2 M.2)
def polynomialDenominator (L M : PolynomialCarrier) : Polynomial ℝ :=
  L.1.1 * M.1.2 - L.1.2 * M.1.1
def polynomialNumerator (L M : PolynomialCarrier) : Polynomial ℝ × Polynomial ℝ :=
  (M.2 * L.1.1 - L.2 * M.1.1, M.2 * L.1.2 - L.2 * M.1.2)
def polynomialTriple (A B C D E F : PolynomialCarrier) : Polynomial ℝ :=
  (polynomialNumerator A B).1 *
      ((polynomialNumerator C D).2 * polynomialDenominator E F -
        polynomialDenominator C D * (polynomialNumerator E F).2) -
    (polynomialNumerator A B).2 *
      ((polynomialNumerator C D).1 * polynomialDenominator E F -
        polynomialDenominator C D * (polynomialNumerator E F).1) +
    polynomialDenominator A B *
      ((polynomialNumerator C D).1 * (polynomialNumerator E F).2 -
        (polynomialNumerator C D).2 * (polynomialNumerator E F).1)

def numeratorPathPolynomial {α : Type*} (L M : α → CarrierLine)
    (a b c d e f : α) : Polynomial ℝ :=
  polynomialTriple (carrierPolynomial (L a) (M a)) (carrierPolynomial (L b) (M b))
    (carrierPolynomial (L c) (M c)) (carrierPolynomial (L d) (M d))
    (carrierPolynomial (L e) (M e)) (carrierPolynomial (L f) (M f))

theorem numeratorPathPolynomial_eval {α : Type*} (L M : α → CarrierLine)
    (a b c d e f : α) (t : ℝ) :
    (numeratorPathPolynomial L M a b c d e f).eval t =
      carrierTripleNumerator (carrierPath (L a) (M a) t) (carrierPath (L b) (M b) t)
        (carrierPath (L c) (M c) t) (carrierPath (L d) (M d) t)
        (carrierPath (L e) (M e) t) (carrierPath (L f) (M f) t) := by
  simp [numeratorPathPolynomial, polynomialTriple, polynomialNumerator,
    polynomialDenominator, carrierPolynomial, scalarPolynomial,
    carrierTripleNumerator, lineNumerator, lineDenominator, planarDet,
    carrierPath, scalarPath]

theorem numeratorPathPolynomial_eval_one {α : Type*} (L M : α → CarrierLine)
    (a b c d e f : α) :
    (numeratorPathPolynomial L M a b c d e f).eval 1 =
      carrierTripleNumerator (M a) (M b) (M c) (M d) (M e) (M f) := by
  rw [numeratorPathPolynomial_eval]
  simp [carrierPath, scalarPath]

theorem numeratorPathPolynomial_ne_zero {α : Type*} (L M : α → CarrierLine)
    (a b c d e f : α)
    (hM : carrierTripleNumerator (M a) (M b) (M c) (M d) (M e) (M f) ≠ 0) :
    numeratorPathPolynomial L M a b c d e f ≠ 0 := by
  intro hz
  apply hM
  rw [← numeratorPathPolynomial_eval_one L M a b c d e f, hz, Polynomial.eval_zero]

theorem daughter_exists_nonzero_path_polynomial
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i j k : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ M : Fin n → CarrierLine, ∀ L : Fin n → CarrierLine,
      let m := Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)
      let prev : Fin m → Fin m := fun v => (cyclicSuccessorPerm m)⁻¹ v
      let car := DaughterFirstReturn.daughterCarrier q hG2 S root
      numeratorPathPolynomial L M (car (prev i)) (car i)
        (car (prev j)) (car j) (car (prev k)) (car k) ≠ 0 := by
  obtain ⟨M, hM⟩ := daughterCarrierTriple_has_nonzero_numerator
    q hG2 S hn hG1 hNA root hroot i j k hij hjk hik
  refine ⟨M, ?_⟩
  intro L
  dsimp only
  apply numeratorPathPolynomial_ne_zero
  exact hM

end DirectGLSSW.CarrierNumeratorPath






