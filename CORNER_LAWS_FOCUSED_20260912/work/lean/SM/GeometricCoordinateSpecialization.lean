import SM.CoefficientSpecialization
import SM.ConcurrenceAffinity

/-! Identification of the scalar specialization with an actual labelled tuple
whose other scalar coordinates are fixed. Area and concurrence evaluations
therefore retain exactly the geometric source meaning. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

def tupleScalarSpecialization (P : LabelledTuple n) (i : ScalarCoordinate n) (t : ℝ) :
    LabelledTuple n :=
  tupleOfScalarCoordinates (extendCoordinateAssignment i
    (fun j : {j : ScalarCoordinate n // j ≠ i} => scalarCoordinates P j) t)

@[simp] theorem scalarCoordinates_tupleScalarSpecialization
    (P : LabelledTuple n) (i : ScalarCoordinate n) (t : ℝ) :
    scalarCoordinates (tupleScalarSpecialization P i t) = extendCoordinateAssignment i
      (fun j : {j : ScalarCoordinate n // j ≠ i} => scalarCoordinates P j) t := by
  simp [tupleScalarSpecialization]

@[simp] theorem tupleScalarSpecialization_base (P : LabelledTuple n) (i : ScalarCoordinate n) :
    tupleScalarSpecialization P i (scalarCoordinates P i) = P := by
  rw [tupleScalarSpecialization, extendCoordinateAssignment_reconstruct, tupleOf_scalarCoordinates]

theorem tupleScalarSpecialization_self (P : LabelledTuple n) (i : ScalarCoordinate n) (t : ℝ) :
    scalarCoordinates (tupleScalarSpecialization P i t) i = t := by simp

theorem tupleScalarSpecialization_other (P : LabelledTuple n) (i j : ScalarCoordinate n)
    (hji : j ≠ i) (t : ℝ) :
    scalarCoordinates (tupleScalarSpecialization P i t) j = scalarCoordinates P j := by
  simpa only [scalarCoordinates_tupleScalarSpecialization] using
    extendCoordinateAssignment_other i
      (fun k : {k : ScalarCoordinate n // k ≠ i} => scalarCoordinates P k) t ⟨j, hji⟩

theorem specializeCoordinate_tuple_value (P : LabelledTuple n) (i : ScalarCoordinate n)
    (p : CoordinatePolynomial n) (h : p.degreeOf i ≤ 1) (t : ℝ) :
    (specializeCoordinate i p (fun j : {j : ScalarCoordinate n // j ≠ i} =>
      scalarCoordinates P j)).eval t = eval (scalarCoordinates (tupleScalarSpecialization P i t)) p := by
  rw [scalarCoordinates_tupleScalarSpecialization]
  exact specializeCoordinate_eval i p h _ t

theorem specializeCoordinate_area_value (P : LabelledTuple n) (i : ScalarCoordinate n)
    (a b c : ZMod n) (t : ℝ) :
    (specializeCoordinate i (areaPolynomial a b c)
      (fun j : {j : ScalarCoordinate n // j ≠ i} => scalarCoordinates P j)).eval t =
      det (tupleScalarSpecialization P i t b - tupleScalarSpecialization P i t a)
        (tupleScalarSpecialization P i t c - tupleScalarSpecialization P i t a) := by
  rw [specializeCoordinate_tuple_value P i _ (areaPolynomial_affine i a b c) t]
  exact eval_areaPolynomial _ a b c

theorem specializeCoordinate_concurrence_value (P : LabelledTuple n) (i : ScalarCoordinate n)
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) (t : ℝ) :
    (specializeCoordinate i (concurrencePolynomial e f g)
      (fun j : {j : ScalarCoordinate n // j ≠ i} => scalarCoordinates P j)).eval t =
      concurrenceDet (tupleScalarSpecialization P i t) e f g := by
  rw [specializeCoordinate_tuple_value P i _ (concurrencePolynomial_affine i e f g hef heg hfg) t]
  exact eval_concurrencePolynomial _ e f g

end

end SM
