import SM.PolynomialControlRepresentatives
import SM.GeometricCoordinateSpecialization

/-! Full source-facing polynomial-controls statement. The finite family has
one representative per unordered source name. Every algebraic hypothesis for
the coefficient certificates is discharged for this actual concrete family. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

structure PolynomialControlsStatement (n : ℕ) [NeZero n] : Prop where
  family_exact : ∀ p : CoordinatePolynomial n,
    p ∈ polynomialControlFamily n ↔ ∃ name : PolynomialControlName n,
      namedControlPolynomial name = p
  one_per_name : Function.Injective (namedControlPolynomial (n := n))
  vertex_coverage : ∀ (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    let name : PolynomialControlName n := .inl (vertexControlNameOf i j k hij hik hjk)
    areaPolynomial i j k = namedControlPolynomial name ∨
      areaPolynomial i j k = -namedControlPolynomial name
  edge_coverage : ∀ (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g),
    let name : PolynomialControlName n := .inr (edgeControlNameOf e f g hef heg hfg)
    concurrencePolynomial e f g = namedControlPolynomial name ∨
      concurrencePolynomial e f g = -namedControlPolynomial name
  area_evaluation : ∀ (P : LabelledTuple n) (i j k : ZMod n),
    eval (scalarCoordinates P) (areaPolynomial i j k) = det (P j - P i) (P k - P i)
  concurrence_evaluation : ∀ (P : LabelledTuple n) (e f g : ZMod n),
    eval (scalarCoordinates P) (concurrencePolynomial e f g) = concurrenceDet P e f g
  nonzero : ∀ name : PolynomialControlName n, namedControlPolynomial name ≠ 0
  irreducible : ∀ name : PolynomialControlName n, Irreducible (namedControlPolynomial name)
  nonassociate : ∀ u v : PolynomialControlName n, u ≠ v →
    ¬ Associated (namedControlPolynomial u) (namedControlPolynomial v)
  affine : ∀ (name : PolynomialControlName n) (z : ScalarCoordinate n),
    (namedControlPolynomial name).degreeOf z ≤ 1
  coefficient_decomposition : ∀ (name : PolynomialControlName n) (z : ScalarCoordinate n),
    namedControlPolynomial name =
      embedRemaining z (coordinateSlope z (namedControlPolynomial name)) * X z +
        embedRemaining z (coordinateIntercept z (namedControlPolynomial name))
  slope_nonzero : ∀ (name : PolynomialControlName n) (z : ScalarCoordinate n),
    z ∈ (namedControlPolynomial name).vars → coordinateSlope z (namedControlPolynomial name) ≠ 0
  resultant_nonzero : ∀ (u v : PolynomialControlName n) (z : ScalarCoordinate n),
    u ≠ v → z ∈ (namedControlPolynomial u).vars → z ∈ (namedControlPolynomial v).vars →
      coordinateResultant z (namedControlPolynomial u) (namedControlPolynomial v) ≠ 0
  specialization_evaluation : ∀ (name : PolynomialControlName n) (z : ScalarCoordinate n)
      (η : {w : ScalarCoordinate n // w ≠ z} → ℝ) (t : ℝ),
    (specializeCoordinate z (namedControlPolynomial name) η).eval t =
      eval (extendCoordinateAssignment z η t) (namedControlPolynomial name)
  simple_root : ∀ (name : PolynomialControlName n) (z : ScalarCoordinate n)
      (η : {w : ScalarCoordinate n // w ≠ z} → ℝ),
    eval η (coordinateSlope z (namedControlPolynomial name)) ≠ 0 →
    let r := -eval η (coordinateIntercept z (namedControlPolynomial name)) /
      eval η (coordinateSlope z (namedControlPolynomial name))
    (specializeCoordinate z (namedControlPolynomial name) η).IsRoot r ∧
      (∀ t, (specializeCoordinate z (namedControlPolynomial name) η).IsRoot t ↔ t = r) ∧
      (specializeCoordinate z (namedControlPolynomial name) η).rootMultiplicity r = 1
  no_common_root : ∀ (u v : PolynomialControlName n) (z : ScalarCoordinate n)
      (η : {w : ScalarCoordinate n // w ≠ z} → ℝ),
    eval η (coordinateResultant z (namedControlPolynomial u) (namedControlPolynomial v)) ≠ 0 →
    ∀ t, ¬ ((specializeCoordinate z (namedControlPolynomial u) η).IsRoot t ∧
      (specializeCoordinate z (namedControlPolynomial v) η).IsRoot t)

/-- SM lem:transport-polynomials, all clauses for the concrete finite family.
The NeZero instance is redundant with the source restriction n≥3. -/
theorem transport_polynomials [NeZero n] (hn : 3 ≤ n) : PolynomialControlsStatement n where
  family_exact := mem_polynomialControlFamily
  one_per_name := namedControlPolynomial_injective hn
  vertex_coverage := vertexControlNameOf_coverage
  edge_coverage := edgeControlNameOf_coverage
  area_evaluation := eval_areaPolynomial
  concurrence_evaluation := eval_concurrencePolynomial
  nonzero := namedControlPolynomial_ne_zero hn
  irreducible := namedControlPolynomial_irreducible hn
  nonassociate := namedControlPolynomial_not_associated hn
  affine := namedControlPolynomial_affine
  coefficient_decomposition name z := coordinate_affine_decomposition z _
    (namedControlPolynomial_affine name z)
  slope_nonzero name z hdep := coordinateSlope_ne_zero z _
    (namedControlPolynomial_affine name z) hdep
  resultant_nonzero u v z hne hdep _ := coordinateResultant_ne_zero z _ _
    (namedControlPolynomial_affine u z) (namedControlPolynomial_affine v z) hdep
    (namedControlPolynomial_irreducible hn u) (namedControlPolynomial_irreducible hn v)
    (namedControlPolynomial_not_associated hn u v hne)
  specialization_evaluation name z η t := specializeCoordinate_eval z _
    (namedControlPolynomial_affine name z) η t
  simple_root name z η ha := specializeCoordinate_simple_root z _
    (namedControlPolynomial_affine name z) η ha
  no_common_root u v z η hr t := specializeCoordinate_no_common_root z _ _
    (namedControlPolynomial_affine u z) (namedControlPolynomial_affine v z) η hr t

end

end SM
