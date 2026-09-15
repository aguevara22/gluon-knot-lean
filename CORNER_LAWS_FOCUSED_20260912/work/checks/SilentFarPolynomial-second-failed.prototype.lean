import SM.Farout
import Mathlib.Algebra.MvPolynomial.Invertible

namespace SM

noncomputable section
universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v}
  [CommRing R] [CommRing S] [Invertible (2 : R)] [Invertible (2 : S)]

/-- The designated inverses of two are respected by every ring map,
including maps into polynomial rings. No cancellation assumption is needed. -/
theorem ringHom_map_half (f : R →+* S) : f (⅟ (2 : R)) = ⅟ (2 : S) := by
  have hprod : f (⅟ (2 : R)) * (2 : S) = 1 := by
    calc
      _ = f (⅟ (2 : R) * 2) := by rw [map_mul, map_ofNat]
      _ = 1 := by rw [invOf_mul_self, map_one]
  calc
    f (⅟ (2 : R)) = f (⅟ (2 : R)) * ((2 : S) * ⅟ (2 : S)) := by
      rw [mul_invOf_self, mul_one]
    _ = (f (⅟ (2 : R)) * (2 : S)) * ⅟ (2 : S) := by rw [mul_assoc]
    _ = ⅟ (2 : S) := by rw [hprod, one_mul]

theorem map_nearFarWeight (f : R →+* S) (D H : TripleArray n R)
    {I : BoundaryInterval n} (π : IntervalComposition I) :
    f (π.nearFarWeight D H) = π.nearFarWeight (fun t => f (D t)) (fun t => f (H t)) := by
  simp only [IntervalComposition.nearFarWeight, map_prod, map_mul, map_sub,
    ringHom_map_half]

theorem map_boundaryUnitArray (f : R →+* S) (I : BoundaryInterval n) :
    f (boundaryUnitArray (R := R) I) = boundaryUnitArray (R := S) I := by
  by_cases h : I.right.val = I.left.val + 1 <;> simp [boundaryUnitArray, h]

/-- Naturality preserves the complete sum, including its unary term and
all actual child intervals. -/
theorem map_nearFarTransform (f : R →+* S) (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarTransform D H X I) = nearFarTransform (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (X J)) I := by
  simp only [nearFarTransform, map_sum, map_mul, map_prod, map_nearFarWeight]

theorem map_farTransform (f : R →+* S) (H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (farTransform H X I) = farTransform (fun t => f (H t)) (fun J => f (X J)) I := by
  have hz : (fun t : IncreasingBoundaryTriple n => f ((0 : TripleArray n R) t)) =
      (0 : TripleArray n S) := by funext t; exact map_zero f
  have h := map_nearFarTransform f 0 H X I
  rw [hz] at h
  exact h

/-- The existing well-founded inverse recursion commutes with every ring
map, after mapping its actual near/far weights. -/
theorem map_nearFarInverse (f : R →+* S) (D H : TripleArray n R)
    (Y : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarInverse D H Y I) = nearFarInverse (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (Y J)) I := by
  simpa only [nearFarInverse, map_nearFarWeight] using
    map_triangularInverse f (fun _ π => π.nearFarWeight D H) Y I

theorem map_farOnlyCoordinates (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyCoordinates H I) = farOnlyCoordinates (fun t => f (H t)) I := by
  have hz : (fun t : IncreasingBoundaryTriple n => f ((0 : TripleArray n R) t)) =
      (0 : TripleArray n S) := by funext t; exact map_zero f
  have he : (fun J : BoundaryInterval n => f (boundaryUnitArray (R := R) J)) =
      boundaryUnitArray (R := S) := funext (map_boundaryUnitArray f)
  have h := map_nearFarInverse f 0 H boundaryUnitArray I
  rw [hz, he] at h
  exact h

theorem map_farOnlyOutput (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyOutput H I) = farOnlyOutput (fun t => f (H t)) I := by
  have hn : (fun t => f ((-H) t)) = -(fun t => f (H t)) := by
    funext t
    exact map_neg f (H t)
  have hc : (fun J => f (farOnlyCoordinates H J)) = farOnlyCoordinates (fun t => f (H t)) :=
    funext (map_farOnlyCoordinates f H)
  have h := map_farTransform f (-H) (farOnlyCoordinates H) I
  rw [hn, hc] at h
  exact h

end
end SM

namespace SM

noncomputable section
universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- Exactly one independent variable for each zero entry of the fixed
far array. No realizability relation is imposed on this variable type. -/
def SilentFarEntry (H0 : TripleArray n R) := {t : IncreasingBoundaryTriple n // H0 t = 0}

def silentFarArray (H0 : TripleArray n R) : TripleArray n (MvPolynomial (SilentFarEntry H0) R) := by
  classical
  exact fun t => if h : H0 t = 0 then MvPolynomial.X ⟨t, h⟩ else MvPolynomial.C (H0 t)

/-- The variable part vanishes identically at every initially nonzero entry. -/
def silentFarVariable (H0 : TripleArray n R) : TripleArray n (MvPolynomial (SilentFarEntry H0) R) := by
  classical
  exact fun t => if h : H0 t = 0 then MvPolynomial.X ⟨t, h⟩ else 0

theorem silentFarArray_eq_constant_add_variable (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) :
    silentFarArray H0 t = MvPolynomial.C (H0 t) + silentFarVariable H0 t := by
  by_cases h : H0 t = 0 <;> simp [silentFarArray, silentFarVariable, h]

theorem silentFarArray_at_zero_entry (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : H0 t = 0) :
    silentFarArray H0 t = MvPolynomial.X (⟨t, h⟩ : SilentFarEntry H0) := by
  simp [silentFarArray, h]

theorem silentFarArray_at_nonzero_entry (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : H0 t ≠ 0) :
    silentFarArray H0 t = MvPolynomial.C (H0 t) := by
  simp [silentFarArray, h]

def silentFarZeroHom (H0 : TripleArray n R) : MvPolynomial (SilentFarEntry H0) R →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)

theorem silentFarZeroHom_array (H0 : TripleArray n R) :
    (fun t => silentFarZeroHom H0 (silentFarArray H0 t)) = H0 := by
  funext t
  by_cases h : H0 t = 0 <;>
    simp [silentFarArray, silentFarZeroHom, h]

variable [Invertible (2 : R)]

/-- The fixed child coordinates from the source, lifted as constants. -/
def constantFarCoordinates (H0 : TripleArray n R) :
    IntervalArray n (MvPolynomial (SilentFarEntry H0) R) :=
  fun I => MvPolynomial.C (farOnlyCoordinates H0 I)

/-- Lifting c0 through the constant ring map preserves its defining
zero-specialized equation on every interval. -/
theorem constantFarCoordinates_equation (H0 : TripleArray n R) :
    farTransform (fun t => MvPolynomial.C (H0 t)) (constantFarCoordinates H0) =
      boundaryUnitArray := by
  funext I
  have h := map_farTransform (MvPolynomial.C : R →+* MvPolynomial (SilentFarEntry H0) R)
    H0 (farOnlyCoordinates H0) I
  rw [congrFun (farOnlyCoordinates_equation H0) I, map_boundaryUnitArray] at h
  exact h.symm

theorem constantFarCoordinates_inverse (H0 : TripleArray n R) :
    constantFarCoordinates H0 = farOnlyCoordinates (fun t => MvPolynomial.C (H0 t)) := by
  funext I
  exact map_farOnlyCoordinates
    (MvPolynomial.C : R →+* MvPolynomial (SilentFarEntry H0) R) H0 I

/-- Evaluating all formal variables at zero recovers c0. This is only
specialization; it does not assert independence from those variables. -/
theorem silentFarCoordinates_zero_specialization (H0 : TripleArray n R)
    (I : BoundaryInterval n) :
    silentFarZeroHom H0 (farOnlyCoordinates (silentFarArray H0) I) = farOnlyCoordinates H0 I := by
  have h := map_farOnlyCoordinates (silentFarZeroHom H0) (silentFarArray H0) I
  rw [silentFarZeroHom_array] at h
  exact h

/-- Zero specialization also commutes with the full reversed-far output.
Formal constancy is a separate, still necessary proof obligation. -/
theorem silentFarOutput_zero_specialization (H0 : TripleArray n R)
    (I : BoundaryInterval n) :
    silentFarZeroHom H0 (farOnlyOutput (silentFarArray H0) I) = farOnlyOutput H0 I := by
  have h := map_farOnlyOutput (silentFarZeroHom H0) (silentFarArray H0) I
  rw [silentFarZeroHom_array] at h
  exact h

end
end SM

#print axioms SM.SilentFarEntry
#print axioms SM.silentFarArray
#print axioms SM.silentFarVariable
#print axioms SM.silentFarArray_eq_constant_add_variable
#print axioms SM.silentFarArray_at_zero_entry
#print axioms SM.silentFarArray_at_nonzero_entry
#print axioms SM.silentFarZeroHom
#print axioms SM.silentFarZeroHom_array
#print axioms SM.constantFarCoordinates
#print axioms SM.constantFarCoordinates_equation
#print axioms SM.constantFarCoordinates_inverse
#print axioms SM.silentFarCoordinates_zero_specialization
#print axioms SM.silentFarOutput_zero_specialization
