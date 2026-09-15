namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual open tree recursion solves the complete near/far system
for arbitrary arrays in the full ring, without a geometric specialization. -/
theorem openTreeRec_nearFar_equation (D H : TripleArray n R) :
    nearFarTransform D H (openTreeRec (fun _ π => π.nearFarWeight D H)) = boundaryUnitArray := by
  rw [nearFarTransform_eq_triangular]
  funext I
  have hp := I.leaves_pos
  have hi : I.right.val = I.left.val + 1 ↔ I.leaves = 1 := by
    have := I.increasing
    unfold BoundaryInterval.leaves
    change I.left.val < I.right.val at this
    omega
  by_cases hI : I.leaves = 1
  · letI : IsEmpty {π : IntervalComposition I // 2 ≤ π.parts} :=
      ⟨fun π => by have := π.val.parts_eq_one_of_leaves_eq_one hI; have := π.property; omega⟩
    simp [triangularTransform, boundaryUnitArray, hi.mpr hI, openTreeRec_one _ I hI]
  · have hm : 2 ≤ I.leaves := by omega
    simp only [triangularTransform, boundaryUnitArray,
      show ¬I.right.val = I.left.val + 1 from fun h => hI (hi.mp h), if_false]
    rw [openTreeRec_many _ I hm]
    exact neg_add_cancel _

/-- Uniqueness identifies the actual formal recursion with the existing
polynomial inverse on every interval. -/
theorem openTreeRec_nearFar_inverse (D H : TripleArray n R) :
    openTreeRec (fun _ π => π.nearFarWeight D H) = nearFarInverse D H boundaryUnitArray :=
  nearFar_solution_unique D H _ _ (openTreeRec_nearFar_equation D H)

/-- The actual rooted recursion is the far-only output as a full ring
identity, with each root weight the entire reversed-far cut product. -/
theorem rootedTreeRec_nearFar_farOnly (D H : TripleArray n R) (I : BoundaryInterval n) :
    rootedTreeRec (fun _ π => π.nearFarWeight D H)
      (fun _ π => π.nearFarWeight D (-H)) I = farOnlyOutput H I := by
  exact congrFun (reversedFar_output_of_solution D H
    (openTreeRec (fun _ π => π.nearFarWeight D H)) boundaryUnitArray
    (openTreeRec_nearFar_equation D H)) I

end
end SM
