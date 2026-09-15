import SM.NearFarFactorization
import SM.GeometricNearFar

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Factorization and inverse uniqueness identify the entire near-only array
of any solution, for arbitrary right-hand side and independent arrays. -/
theorem nearTransform_of_nearFar_solution (D H : TripleArray n R)
    (X Y : IntervalArray n R) (h : nearFarTransform D H X = Y) :
    nearTransform D X = nearFarInverse 0 H Y := by
  apply nearFar_solution_unique 0 H
  calc
    nearFarTransform 0 H (nearTransform D X) = nearFarTransform D H X := by
      funext I
      exact nearFar_factorization_coordinate D H X I
    _ = Y := h

/-- The whole output with reversed far signs is determined by H and the
right-hand side. No claim of independence is made for individual tree terms. -/
theorem reversedFar_output_of_solution (D H : TripleArray n R)
    (X Y : IntervalArray n R) (h : nearFarTransform D H X = Y) :
    nearFarTransform D (-H) X = farTransform (-H) (nearFarInverse 0 H Y) := by
  have hc := nearTransform_of_nearFar_solution D H X Y h
  funext I
  rw [← nearFar_factorization_coordinate D (-H) X I, hc]

/-- Changing D while keeping H and the target fixed leaves the complete
reversed-far output unchanged, even though the two input arrays may differ. -/
theorem complete_output_near_independent (D₁ D₂ H : TripleArray n R)
    (X₁ X₂ Y : IntervalArray n R)
    (h₁ : nearFarTransform D₁ H X₁ = Y) (h₂ : nearFarTransform D₂ H X₂ = Y) :
    nearFarTransform D₁ (-H) X₁ = nearFarTransform D₂ (-H) X₂ := by
  rw [reversedFar_output_of_solution D₁ H X₁ Y h₁,
    reversedFar_output_of_solution D₂ H X₂ Y h₂]

def farOnlyCoordinates (H : TripleArray n R) : IntervalArray n R :=
  nearFarInverse 0 H boundaryUnitArray

def farOnlyOutput (H : TripleArray n R) : IntervalArray n R :=
  farTransform (-H) (farOnlyCoordinates H)

theorem farOnlyCoordinates_equation (H : TripleArray n R) :
    farTransform H (farOnlyCoordinates H) = boundaryUnitArray :=
  nearFarTransform_inverse 0 H boundaryUnitArray

/-- The source geometric open sums yield the same complete far-only output. -/
theorem geometric_farOnly_output (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    nearFarTransform (geometricBoundaryArray (R := R) P g) (-geometricBoundaryArray P g)
      (fun I => (openTreeSum P hP g I : R)) = farOnlyOutput (geometricBoundaryArray P g) :=
  reversedFar_output_of_solution _ _ _ _ (geometric_nearFar_open P hP g)

/-- The original rooted tree coefficient, at its specified root, is the
full-interval coordinate of the far-only output. -/
theorem treeCoefficient_farOnly (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    (treeCoefficient P hP g hn : R) =
      farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn) := by
  rw [geometric_nearFar_root P hP g hn, geometric_farOnly_output P hP g]

/-- Every allowed transform is the identity on a one-leaf coordinate, since
there is no nonunary composition of that interval. -/
theorem nearFarTransform_leaf (D H : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : nearFarTransform D H X I = X I := by
  letI : IsEmpty {π : IntervalComposition I // 2 ≤ π.parts} :=
    ⟨fun π => by have := π.val.parts_eq_one_of_leaves_eq_one hI; have := π.property; omega⟩
  rw [nearFarTransform_eq_triangular]
  simp [triangularTransform]

theorem boundaryUnitArray_leaf (I : BoundaryInterval n) (hI : I.leaves = 1) :
    boundaryUnitArray (R := R) I = 1 := by
  have hi := I.increasing
  have he : I.right.val = I.left.val + 1 := by
    unfold BoundaryInterval.leaves at hI
    change I.left.val < I.right.val at hi
    omega
  simp [boundaryUnitArray, he]

theorem farOnlyCoordinates_leaf (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : I.leaves = 1) : farOnlyCoordinates H I = 1 := by
  have hc := congrFun (farOnlyCoordinates_equation H) I
  change nearFarTransform 0 H (farOnlyCoordinates H) I = boundaryUnitArray I at hc
  rw [nearFarTransform_leaf 0 H _ I hI, boundaryUnitArray_leaf I hI] at hc
  exact hc

/-- The two one-leaf values are both one. This is the source's open-word
convention; no two-vertex polygon amplitude is introduced. -/
theorem farOnly_leaf_values (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : I.leaves = 1) :
    farTransform H (farOnlyCoordinates H) I = 1 ∧ farOnlyOutput H I = 1 := by
  constructor
  · rw [farOnlyCoordinates_equation, boundaryUnitArray_leaf I hI]
  · change nearFarTransform 0 (-H) (farOnlyCoordinates H) I = 1
    rw [nearFarTransform_leaf 0 (-H) _ I hI, farOnlyCoordinates_leaf H I hI]

/-- The ordinary far-transform coordinate vanishes on each nonleaf interval. -/
theorem farOnly_nonleaf_E (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : 2 ≤ I.leaves) : farTransform H (farOnlyCoordinates H) I = 0 := by
  rw [farOnlyCoordinates_equation]
  have he : ¬ I.right.val = I.left.val + 1 := by
    unfold BoundaryInterval.leaves at hI
    omega
  simp [boundaryUnitArray, he]

end
end SM
