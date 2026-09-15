namespace SM

noncomputable section
universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- Integer sign gates become the exact half factors in every commutative
ring where2 is invertible, by the four nonzero sign pairs. -/
theorem gate_pair_cast (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    (ordinaryGate d h hd hh : R) = (((d : ℤ) : R) - ((h : ℤ) : R)) * ⅟ (2 : R) ∧
    (rootGate d h hd hh : R) = (((d : ℤ) : R) + ((h : ℤ) : R)) * ⅟ (2 : R) := by
  have hi : (2 : ℤ) * ordinaryGate d h hd hh = (d : ℤ) - (h : ℤ) ∧
      (2 : ℤ) * rootGate d h hd hh = (d : ℤ) + (h : ℤ) := by
    cases d <;> cases h <;>
      first | exact (hd rfl).elim | exact (hh rfl).elim |
        norm_num [ordinaryGate, rootGate, signTheta]
  have ho : (2 : R) * (ordinaryGate d h hd hh : R) = ((d : ℤ) : R) - ((h : ℤ) : R) := by
    exact_mod_cast hi.1
  have hr : (2 : R) * (rootGate d h hd hh : R) = ((d : ℤ) : R) + ((h : ℤ) : R) := by
    exact_mod_cast hi.2
  constructor
  · rw [← ho, mul_right_comm, mul_invOf_self, one_mul]
  · rw [← hr, mul_right_comm, mul_invOf_self, one_mul]

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem ordinaryWeight_cast (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.ordinaryWeight P hP g : R) =
      π.nearFarWeight (geometricBoundaryArray P g) (geometricBoundaryArray P g) := by
  simp only [ordinaryWeight, Int.cast_prod, nearFarWeight,
    geometricBoundaryArray_near, geometricBoundaryArray_far]
  apply Finset.prod_congr rfl
  intro k _
  exact (gate_pair_cast _ _ _ _).1

theorem rootWeight_cast (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.rootWeight P hP g : R) =
      π.nearFarWeight (geometricBoundaryArray P g) (-geometricBoundaryArray P g) := by
  simp only [rootWeight, Int.cast_prod, nearFarWeight, Pi.neg_apply,
    geometricBoundaryArray_near, geometricBoundaryArray_far, sub_neg_eq_add]
  apply Finset.prod_congr rfl
  intro k _
  exact (gate_pair_cast _ _ _ _).2

/-- A leaf interval admits no nonunary composition: such a composition would
have a positive-length child shorter than one. -/
theorem parts_eq_one_of_leaves_eq_one (hI : I.leaves = 1) : π.parts = 1 := by
  by_contra h
  have hp := π.parts_pos
  have hp2 : 2 ≤ π.parts := by omega
  let k : Fin π.parts := ⟨0, hp⟩
  have hs := π.part_leaves_lt hp2 k
  have ht := (π.part k).leaves_pos
  omega

end IntervalComposition

/-- The integer open-tree recursion solves the actual geometric near-far
coordinate equations after casting into any allowed coefficient ring. -/
theorem geometric_nearFar_open (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    nearFarTransform (geometricBoundaryArray (R := R) P g) (geometricBoundaryArray P g)
      (fun I => (openTreeSum P hP g I : R)) = boundaryUnitArray := by
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
    simp [triangularTransform, boundaryUnitArray, hi.mpr hI, openTreeSum_one P hP g I hI]
  · have hm : 2 ≤ I.leaves := by omega
    have hs := congrArg (Int.castRingHom R) (openTreeSum_many P hP g I hm)
    simp only [map_neg, map_sum, map_mul, map_prod, Int.castRingHom_apply] at hs
    simp only [triangularTransform, boundaryUnitArray, show ¬I.right.val = I.left.val + 1 from
      fun h => hI (hi.mp h), if_false]
    simp_rw [← IntervalComposition.ordinaryWeight_cast P hP g]
    rw [hs]
    exact neg_add_cancel _

/-- The complete rooted source sum equals the near-far transform with the
far signs negated, including its one-part root term. -/
theorem geometric_nearFar_root (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    (treeCoefficient P hP g hn : R) =
      nearFarTransform (geometricBoundaryArray P g) (-geometricBoundaryArray P g)
        (fun I => (openTreeSum P hP g I : R)) (fullBoundaryInterval hn) := by
  rw [treeCoefficient_eq]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_prod, nearFarTransform]
  apply Finset.sum_congr rfl
  intro π _
  rw [π.rootWeight_cast P hP g]

end
end SM
