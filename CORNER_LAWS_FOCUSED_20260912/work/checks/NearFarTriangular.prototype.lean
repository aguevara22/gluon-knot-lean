import SM.Gates
import SM.FiniteCompositions
import Mathlib.Tactic

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- All increasing triples of actual boundary positions, with no geometric
restriction on the independent scalars assigned to them. -/
structure IncreasingBoundaryTriple (n : ℕ) where
  lower : Fin n
  middle : Fin n
  upper : Fin n
  lower_middle : lower < middle
  middle_upper : middle < upper

abbrev TripleArray (n : ℕ) (R : Type u) := IncreasingBoundaryTriple n → R
abbrev IntervalArray (n : ℕ) (R : Type u) := BoundaryInterval n → R

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

def nearTriple (k : Fin (π.parts - 1)) : IncreasingBoundaryTriple n where
  lower := π.cut ⟨k.val, by have := k.isLt; omega⟩
  middle := π.cut ⟨k.val + 1, by have := k.isLt; omega⟩
  upper := π.cut ⟨k.val + 2, by have := k.isLt; omega⟩
  lower_middle := π.strict (by change k.val < k.val + 1; omega)
  middle_upper := π.strict (by change k.val + 1 < k.val + 2; omega)

def farTriple (k : Fin (π.parts - 1)) : IncreasingBoundaryTriple n where
  lower := I.left
  middle := π.cut ⟨k.val + 1, by have := k.isLt; omega⟩
  upper := I.right
  lower_middle := by
    rw [← π.first]
    apply π.strict
    change 0 < k.val + 1
    omega
  middle_upper := by
    rw [← π.last]
    apply π.strict
    change k.val + 1 < π.parts
    have := k.isLt
    omega

def nearFarWeight (D H : TripleArray n R) : R :=
  ∏ k : Fin (π.parts - 1), (D (π.nearTriple k) - H (π.farTriple k)) * ⅟ (2 : R)

end IntervalComposition

/-- The complete source polynomial transform, including every unary composition. -/
def nearFarTransform (D H : TripleArray n R) (X : IntervalArray n R) : IntervalArray n R :=
  fun I => ∑ π : IntervalComposition I,
    π.nearFarWeight D H * ∏ k : Fin π.parts, X (π.part k)

def farTransform (H : TripleArray n R) : IntervalArray n R → IntervalArray n R :=
  nearFarTransform 0 H

def nearTransform (D : TripleArray n R) : IntervalArray n R → IntervalArray n R :=
  nearFarTransform D 0

def boundaryUnitArray : IntervalArray n R :=
  fun I => if I.right.val = I.left.val + 1 then 1 else 0

/-- Both geometric arrays read this same reversed-order chirotope entry;
near and far gates sample it at different actual triples. -/
def geometricBoundaryArray (P : LabelledTuple n) (g : ZMod n) : TripleArray n R :=
  fun t => ((chi P (boundaryIndex g t.upper) (boundaryIndex g t.middle)
    (boundaryIndex g t.lower) : ℤ) : R)

theorem geometricBoundaryArray_near (P : LabelledTuple n) (g : ZMod n)
    {I : BoundaryInterval n} (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    geometricBoundaryArray (R := R) P g (π.nearTriple k) = ((π.nearSign P g k : ℤ) : R) := rfl

theorem geometricBoundaryArray_far (P : LabelledTuple n) (g : ZMod n)
    {I : BoundaryInterval n} (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    geometricBoundaryArray (R := R) P g (π.farTriple k) = ((π.farSign P g k : ℤ) : R) := rfl

def nearfarData (n : ℕ) [NeZero n] (R : Type u) [CommRing R] [Invertible (2 : R)] (_hn : 3 ≤ n) :=
  (IncreasingBoundaryTriple n, nearFarTransform (n := n) (R := R),
    farTransform (n := n) (R := R), nearTransform (n := n) (R := R),
    boundaryUnitArray (n := n) (R := R), geometricBoundaryArray (n := n) (R := R))

end

end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IntervalComposition
variable {I : BoundaryInterval n}

/-- A one-part composition has only its two fixed endpoints. -/
theorem eq_single_of_parts_eq_one (π : IntervalComposition I) (hparts : π.parts = 1) :
    π = single I := by
  cases π with
  | mk parts hp cut hstrict hfirst hlast =>
    change parts = 1 at hparts
    subst parts
    have hc : cut = ![I.left, I.right] := by
      funext k
      fin_cases k
      · exact hfirst
      · exact hlast
    subst cut
    rfl

theorem parts_eq_one_iff_eq_single (π : IntervalComposition I) :
    π.parts = 1 ↔ π = single I :=
  ⟨π.eq_single_of_parts_eq_one, fun h => by rw [h]; rfl⟩

/-- The sole part of the unary composition is exactly the original interval. -/
theorem single_part (I : BoundaryInterval n) (k : Fin (single I).parts) :
    (single I).part k = I := by
  change Fin 1 at k
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  rfl

theorem single_product {R : Type*} [CommMonoid R]
    (X : BoundaryInterval n → R) (I : BoundaryInterval n) :
    (∏ k : Fin (single I).parts, X ((single I).part k)) = X I := by
  simp only [single_part]
  exact Fin.prod_univ_one (fun _ => X I)

/-- Every nonunary composition has at least two parts; its underlying cuts
are unchanged by this equivalence. -/
def nonSingleEquiv (I : BoundaryInterval n) :
    {π : IntervalComposition I // π ≠ single I} ≃
      {π : IntervalComposition I // 2 ≤ π.parts} :=
  Equiv.subtypeEquivRight (fun π => by
    constructor
    · intro h
      have hn : π.parts ≠ 1 := fun hp => h (π.eq_single_of_parts_eq_one hp)
      have := π.parts_pos
      omega
    · intro h he
      have hp : π.parts = 1 := π.parts_eq_one_iff_eq_single.mpr he
      omega)

end IntervalComposition

end

end SM

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- A triangular composition transform: the unary coordinate has coefficient
one; every nonunary term reads only strictly shorter child intervals. -/
def triangularTransform
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X : BoundaryInterval n → R) : BoundaryInterval n → R :=
  fun I => X I + ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
    weight I π.val * ∏ k : Fin π.val.parts, X (π.val.part k)

/-- Construct the inverse in increasing interval length using only subtraction,
finite sums and finite products. No coefficient is divided by. -/
def triangularInverse
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) (I : BoundaryInterval n) : R :=
  Y I - ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
    weight I π.val * ∏ k : Fin π.val.parts, triangularInverse weight Y (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

theorem triangularTransform_inverse
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) :
    triangularTransform weight (triangularInverse weight Y) = Y := by
  funext I
  unfold triangularTransform
  rw [triangularInverse]
  ring

theorem triangularInverse_transform_apply
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X : BoundaryInterval n → R) (I : BoundaryInterval n) :
    triangularInverse weight (triangularTransform weight X) I = X I := by
  rw [triangularInverse]
  change (X I + ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      weight I π.val * ∏ k : Fin π.val.parts, X (π.val.part k)) -
    (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      weight I π.val * ∏ k : Fin π.val.parts,
        triangularInverse weight (triangularTransform weight X) (π.val.part k)) = X I
  have hs : (∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      weight I π.val * ∏ k : Fin π.val.parts,
        triangularInverse weight (triangularTransform weight X) (π.val.part k)) =
      ∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        weight I π.val * ∏ k : Fin π.val.parts, X (π.val.part k) := by
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact triangularInverse_transform_apply weight X (π.val.part k)
  rw [hs]
  ring
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

theorem triangularInverse_transform
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X : BoundaryInterval n → R) :
    triangularInverse weight (triangularTransform weight X) = X :=
  funext (triangularInverse_transform_apply weight X)

theorem triangular_solution_unique
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (X Y : BoundaryInterval n → R) (hX : triangularTransform weight X = Y) :
    X = triangularInverse weight Y := by
  rw [← hX]
  exact (triangularInverse_transform weight X).symm

def triangularEquiv
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R) :
    (BoundaryInterval n → R) ≃ (BoundaryInterval n → R) where
  toFun := triangularTransform weight
  invFun := triangularInverse weight
  left_inv := triangularInverse_transform weight
  right_inv := triangularTransform_inverse weight

end

end SM

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearFarWeight_one (D H : TripleArray n R) (hparts : π.parts = 1) :
    π.nearFarWeight D H = 1 := by
  letI : IsEmpty (Fin (π.parts - 1)) := ⟨fun k => by have := k.isLt; omega⟩
  simp [nearFarWeight]

end IntervalComposition

/-- Separate the unique unary composition from the complete source sum, with
the same cuts and the same coefficients on every nonunary term. -/
theorem nearFarTransform_eq_triangular (D H : TripleArray n R) :
    nearFarTransform D H = triangularTransform (fun _ π => π.nearFarWeight D H) := by
  classical
  funext X I
  unfold nearFarTransform triangularTransform
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (IntervalComposition.single I)]
  rw [(IntervalComposition.single I).nearFarWeight_one D H rfl,
    IntervalComposition.single_product X I, one_mul]
  congr 1
  exact Fintype.sum_equiv (IntervalComposition.nonSingleEquiv I) _ _ (fun _ => rfl)

def nearFarInverse (D H : TripleArray n R) : IntervalArray n R → IntervalArray n R :=
  triangularInverse (fun _ π => π.nearFarWeight D H)

theorem nearFarTransform_inverse (D H : TripleArray n R) (Y : IntervalArray n R) :
    nearFarTransform D H (nearFarInverse D H Y) = Y := by
  rw [nearFarTransform_eq_triangular]
  exact triangularTransform_inverse _ Y

theorem nearFarInverse_transform (D H : TripleArray n R) (X : IntervalArray n R) :
    nearFarInverse D H (nearFarTransform D H X) = X := by
  rw [nearFarTransform_eq_triangular]
  exact triangularInverse_transform _ X

theorem nearFar_solution_unique (D H : TripleArray n R) (X Y : IntervalArray n R)
    (hX : nearFarTransform D H X = Y) : X = nearFarInverse D H Y := by
  rw [nearFarTransform_eq_triangular] at hX
  exact triangular_solution_unique _ X Y hX

end

end SM

#print axioms SM.nearFarTransform_eq_triangular
#print axioms SM.nearFarTransform_inverse
#print axioms SM.nearFarInverse_transform
#print axioms SM.nearFar_solution_unique
