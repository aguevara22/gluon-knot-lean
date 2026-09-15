namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- The geometric near and far arrays descend under the source's simultaneous
tuple/root relabelling; all abstract transforms then read the same arrays. -/
theorem geometricBoundaryArray_shift (P : LabelledTuple n) (g a : ZMod n) :
    geometricBoundaryArray (R := R) (shift a P) (g - a) = geometricBoundaryArray (R := R) P g := by
  have hi (k : Fin n) : boundaryIndex (g - a) k + a = boundaryIndex g k := by
    unfold boundaryIndex
    abel
  funext t
  simp only [geometricBoundaryArray, chi_shift, hi]

end

end SM
