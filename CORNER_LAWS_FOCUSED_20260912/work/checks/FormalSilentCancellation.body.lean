namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Geometric arrays use integer signs, so every ring map transports
their values exactly, including zero entries. -/
theorem map_geometricBoundaryArray {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : LabelledTuple n) (g : ZMod n) :
    (fun t => f (geometricBoundaryArray (R := R) P g t)) =
      geometricBoundaryArray (R := S) P g := by
  funext t
  exact map_intCast f _

attribute [local instance] silentPolynomialTwoInvertible

/-- The exact formal replacement array splits into the geometric constant
array and the independent variables at its zero entries. -/
theorem silentFarArray_geometric_split (P : LabelledTuple n) (g : ZMod n) :
    silentFarArray (geometricBoundaryArray (R := ℚ) P g) =
      geometricBoundaryArray P g + silentFarVariable (geometricBoundaryArray (R := ℚ) P g) := by
  funext t
  rw [silentFarArray_eq_constant_add_variable]
  have h := congrFun (map_geometricBoundaryArray
    (MvPolynomial.C : ℚ →+* MvPolynomial
      (SilentFarEntry (geometricBoundaryArray (R := ℚ) P g)) ℚ) P g) t
  rw [h]
  rfl

theorem silentFarVariable_geometric_support (P : LabelledTuple n) (g : ZMod n) :
    ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 →
      silentFarVariable (geometricBoundaryArray (R := ℚ) P g) t = 0 := by
  intro t ht
  simp [silentFarVariable, ht]

/-- Full source pf:formal-cancellation. Every zero geometric far entry is
replaced by its own unrestricted polynomial variable. The complete inverse
array equals its constant zero-specialization, and the complete reversed-far
output agrees at the physical root. No realizability or independence of
zero-determinant differentials is required. -/
theorem formal_silent_cancellation (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) :
    farOnlyCoordinates (silentFarArray (geometricBoundaryArray (R := ℚ) P g)) =
      constantFarCoordinates (geometricBoundaryArray (R := ℚ) P g) ∧
    farOnlyOutput (silentFarArray (geometricBoundaryArray (R := ℚ) P g))
        (fullBoundaryInterval hn) =
      MvPolynomial.C (farOnlyOutput (geometricBoundaryArray (R := ℚ) P g)
        (fullBoundaryInterval hn)) := by
  let H0 := geometricBoundaryArray (R := ℚ) P g
  let C : ℚ →+* MvPolynomial (SilentFarEntry H0) ℚ := MvPolynomial.C
  have hcast : (fun t => C (H0 t)) = geometricBoundaryArray P g :=
    map_geometricBoundaryArray C P g
  have hU := silentFarVariable_geometric_support P g
  constructor
  · rw [silentFarArray_geometric_split,
      silent_supported_coordinates hn hP g (silentFarVariable H0) hU]
    have hc := constantFarCoordinates_inverse H0
    rw [hcast] at hc
    exact hc.symm
  · rw [silentFarArray_geometric_split,
      silent_supported_output hn hP g (silentFarVariable H0) hU]
    have ho := map_farOnlyOutput C H0 (fullBoundaryInterval hn)
    rw [hcast] at ho
    exact ho.symm

end
end SM
