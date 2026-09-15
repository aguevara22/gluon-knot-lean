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
  exact dif_pos h

theorem silentFarArray_at_nonzero_entry (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : H0 t ≠ 0) :
    silentFarArray H0 t = MvPolynomial.C (H0 t) := by
  simp [silentFarArray, h]

def silentFarZeroHom (H0 : TripleArray n R) : MvPolynomial (SilentFarEntry H0) R →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)

theorem silentFarZeroHom_array (H0 : TripleArray n R) :
    (fun t => silentFarZeroHom H0 (silentFarArray H0 t)) = H0 := by
  funext t
  by_cases h : H0 t = 0
  · rw [silentFarArray_at_zero_entry H0 t h]
    change MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)
      (MvPolynomial.X (⟨t, h⟩ : SilentFarEntry H0)) = H0 t
    rw [MvPolynomial.eval₂Hom_X', h]
  · rw [silentFarArray_at_nonzero_entry H0 t h]
    exact MvPolynomial.eval₂Hom_C (RingHom.id R) (fun _ => 0) (H0 t)

variable [Invertible (2 : R)]

/-- The numeral two in the polynomial ring inherits its actual inverse
through the constant ring map. This supplies an instance, not a new premise. -/
local instance silentPolynomialTwoInvertible (σ : Type*) :
    Invertible (2 : MvPolynomial σ R) := by
  have h : MvPolynomial.C (2 : R) = (2 : MvPolynomial σ R) := map_ofNat MvPolynomial.C 2
  exact h ▸ MvPolynomial.invertibleC σ (2 : R)

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
