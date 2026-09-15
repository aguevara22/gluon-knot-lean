import SM.Gates
import SM.FiniteCompositions
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Eval

set_option pp.fullNames true
set_option pp.universes false

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

#check SM.IncreasingBoundaryTriple
#print axioms SM.IncreasingBoundaryTriple
#check SM.TripleArray
#print axioms SM.TripleArray
#check SM.IntervalArray
#print axioms SM.IntervalArray
#check SM.IntervalComposition.nearTriple
#print axioms SM.IntervalComposition.nearTriple
#check SM.IntervalComposition.farTriple
#print axioms SM.IntervalComposition.farTriple
#check SM.IntervalComposition.nearFarWeight
#print axioms SM.IntervalComposition.nearFarWeight
#check SM.nearFarTransform
#print axioms SM.nearFarTransform
#check SM.farTransform
#print axioms SM.farTransform
#check SM.nearTransform
#print axioms SM.nearTransform
#check SM.boundaryUnitArray
#print axioms SM.boundaryUnitArray
#check SM.geometricBoundaryArray
#print axioms SM.geometricBoundaryArray
#check SM.geometricBoundaryArray_near
#print axioms SM.geometricBoundaryArray_near
#check SM.geometricBoundaryArray_far
#print axioms SM.geometricBoundaryArray_far
#check SM.nearfarData
#print axioms SM.nearfarData
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

#check SM.IntervalComposition.eq_single_of_parts_eq_one
#print axioms SM.IntervalComposition.eq_single_of_parts_eq_one
#check SM.IntervalComposition.parts_eq_one_iff_eq_single
#print axioms SM.IntervalComposition.parts_eq_one_iff_eq_single
#check SM.IntervalComposition.single_part
#print axioms SM.IntervalComposition.single_part
#check SM.IntervalComposition.single_product
#print axioms SM.IntervalComposition.single_product
#check SM.IntervalComposition.nonSingleEquiv
#print axioms SM.IntervalComposition.nonSingleEquiv
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

#check SM.triangularTransform
#print axioms SM.triangularTransform
#check SM.triangularInverse
#print axioms SM.triangularInverse
#check SM.triangularTransform_inverse
#print axioms SM.triangularTransform_inverse
#check SM.triangularInverse_transform_apply
#print axioms SM.triangularInverse_transform_apply
#check SM.triangularInverse_transform
#print axioms SM.triangularInverse_transform
#check SM.triangular_solution_unique
#print axioms SM.triangular_solution_unique
#check SM.triangularEquiv
#print axioms SM.triangularEquiv
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

#check SM.IntervalComposition.nearFarWeight_one
#print axioms SM.IntervalComposition.nearFarWeight_one
#check SM.nearFarTransform_eq_triangular
#print axioms SM.nearFarTransform_eq_triangular
#check SM.nearFarInverse
#print axioms SM.nearFarInverse
#check SM.nearFarTransform_inverse
#print axioms SM.nearFarTransform_inverse
#check SM.nearFarInverse_transform
#print axioms SM.nearFarInverse_transform
#check SM.nearFar_solution_unique
#print axioms SM.nearFar_solution_unique
namespace SM

noncomputable section

universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Every coordinate of the recursive inverse commutes with a ring homomorphism:
the recursion uses only the mapped scalars, subtraction, finite sums and products. -/
theorem map_triangularInverse (f : R →+* S)
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) (I : BoundaryInterval n) :
    f (triangularInverse weight Y I) =
      triangularInverse (fun J π => f (weight J π)) (fun J => f (Y J)) I := by
  conv_lhs => rw [triangularInverse]
  conv_rhs => rw [triangularInverse]
  simp only [map_sub, map_sum, map_mul, map_prod]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact map_triangularInverse f weight Y (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

/-- The actual inverse coordinate as a polynomial in the target array entries. -/
def triangularInversePolynomial
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : MvPolynomial (BoundaryInterval n) R :=
  triangularInverse (fun J π => MvPolynomial.C (weight J π)) MvPolynomial.X I

theorem triangularInversePolynomial_eval
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) (I : BoundaryInterval n) :
    MvPolynomial.eval₂Hom (RingHom.id R) Y (triangularInversePolynomial weight I) =
      triangularInverse weight Y I := by
  simpa only [triangularInversePolynomial, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', RingHom.id_apply] using
    map_triangularInverse (MvPolynomial.eval₂Hom (RingHom.id R) Y)
      (fun J π => MvPolynomial.C (weight J π)) MvPolynomial.X I

/-- Explicit coordinate polynomials giving both inverse identities for the
source near-far transform. Factorization and geometric output are separate claims. -/
theorem nearFar_has_polynomial_inverse [Invertible (2 : R)] (D H : TripleArray n R) :
    ∃ Ψ : BoundaryInterval n → MvPolynomial (BoundaryInterval n) R,
      (∀ Y : IntervalArray n R,
        nearFarTransform D H (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = Y) ∧
      (∀ X : IntervalArray n R,
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) (nearFarTransform D H X) (Ψ I)) = X) := by
  let Ψ := triangularInversePolynomial (fun _ π => π.nearFarWeight D H)
  have he (Y : IntervalArray n R) :
      (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = nearFarInverse D H Y :=
    funext (fun I => triangularInversePolynomial_eval _ Y I)
  refine ⟨Ψ, ?_, ?_⟩
  · intro Y
    rw [he Y]
    exact nearFarTransform_inverse D H Y
  · intro X
    rw [he (nearFarTransform D H X)]
    exact nearFarInverse_transform D H X

end

end SM

#check SM.map_triangularInverse
#print axioms SM.map_triangularInverse
#check SM.triangularInversePolynomial
#print axioms SM.triangularInversePolynomial
#check SM.triangularInversePolynomial_eval
#print axioms SM.triangularInversePolynomial_eval
#check SM.nearFar_has_polynomial_inverse
#print axioms SM.nearFar_has_polynomial_inverse
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

#check SM.geometricBoundaryArray_shift
#print axioms SM.geometricBoundaryArray_shift
#print SM.IncreasingBoundaryTriple
#print SM.TripleArray
#print SM.IntervalArray
#print SM.IntervalComposition.nearTriple
#print SM.IntervalComposition.farTriple
#print SM.IntervalComposition.nearFarWeight
#print SM.nearFarTransform
#print SM.farTransform
#print SM.nearTransform
#print SM.boundaryUnitArray
#print SM.geometricBoundaryArray
#print SM.nearfarData
#print SM.triangularTransform
#print SM.triangularInverse
#print SM.nearFarInverse
#print SM.triangularInversePolynomial
namespace NearFarInverseIndependentReview
open SM
variable {n : ℕ} [NeZero n]

-- Every source increasing natural triple in0..N is admitted without a
-- geometric restriction or a selected subset of triples.
theorem all_raw_increasing_triples (hn : 3 ≤ n) (x y z : ℕ)
    (hxy : x < y) (hyz : y < z) (hz : z ≤ n - 1) :
    ∃ t : IncreasingBoundaryTriple n,
      t.lower.val = x ∧ t.middle.val = y ∧ t.upper.val = z := by
  exact ⟨⟨⟨x, by omega⟩, ⟨y, by omega⟩, ⟨z, by omega⟩, hxy, hyz⟩, rfl, rfl, rfl⟩

theorem full_triple_domain_finite : Finite (IncreasingBoundaryTriple n) := by
  let f : IncreasingBoundaryTriple n → Fin n × Fin n × Fin n :=
    fun t => (t.lower, t.middle, t.upper)
  apply Finite.of_injective f
  rintro ⟨x,y,z,hxy,hyz⟩ ⟨a,b,c,hab,hbc⟩ he
  have hx := congrArg (fun p => p.1) he
  have hy := congrArg (fun p => p.2.1) he
  have hz := congrArg (fun p => p.2.2) he
  change x = a at hx
  change y = b at hy
  change z = c at hz
  cases hx; cases hy; cases hz
  rfl

theorem full_interval_domain_finite : Finite (BoundaryInterval n) := by
  let f : BoundaryInterval n → Fin n × Fin n := fun I => (I.left, I.right)
  apply Finite.of_injective f
  rintro ⟨x,y,hxy⟩ ⟨a,b,hab⟩ he
  have hx := congrArg (fun p => p.1) he
  have hy := congrArg (fun p => p.2) he
  change x = a at hx
  change y = b at hy
  cases hx; cases hy
  rfl

theorem unary_term_is_exact {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) (X : IntervalArray n R) (I : BoundaryInterval n) :
    (IntervalComposition.single I).nearFarWeight D H *
      ∏ k : Fin (IntervalComposition.single I).parts,
        X ((IntervalComposition.single I).part k) = X I := by
  rw [(IntervalComposition.single I).nearFarWeight_one D H rfl,
    IntervalComposition.single_product X I, one_mul]

-- Clearing the two in every factor checks the actual half convention in
-- arbitrary commutative rings with invertible two, including empty products.
theorem every_half_factor_is_exact {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) {I : BoundaryInterval n} (π : IntervalComposition I) :
    π.nearFarWeight D H * (2 : R) ^ (π.parts - 1) =
      ∏ k : Fin (π.parts - 1), (D (π.nearTriple k) - H (π.farTriple k)) := by
  have he : ∀ k : Fin (π.parts - 1),
      ((D (π.nearTriple k) - H (π.farTriple k)) * ⅟ (2 : R)) * 2 =
        D (π.nearTriple k) - H (π.farTriple k) := by
    intro k
    rw [mul_assoc, invOf_mul_self, mul_one]
  have hp := Finset.prod_congr (s₁ := Finset.univ) rfl (fun k _ => he k)
  rw [Finset.prod_mul_distrib] at hp
  simpa only [IntervalComposition.nearFarWeight, Fin.prod_const] using hp

theorem unit_array_is_leaf_indicator {R : Type*} [CommRing R]
    (I : BoundaryInterval n) :
    boundaryUnitArray (R := R) I = if I.leaves = 1 then 1 else 0 := by
  have he : I.right.val = I.left.val + 1 ↔ I.leaves = 1 := by
    have := I.increasing
    change I.right.val = I.left.val + 1 ↔ I.right.val - I.left.val = 1
    omega
  simp only [boundaryUnitArray, he]

theorem inverse_base_coordinate {R : Type*} [CommRing R]
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : IntervalArray n R) (I : BoundaryInterval n) (hI : I.leaves = 1) :
    triangularInverse weight Y I = Y I := by
  letI : IsEmpty {π : IntervalComposition I // 2 ≤ π.parts} := ⟨fun π => by
    have hl := π.val.part_leaves_lt π.property ⟨0, π.val.parts_pos⟩
    have hp := (π.val.part ⟨0, π.val.parts_pos⟩).leaves_pos
    omega⟩
  rw [triangularInverse]
  simp

theorem unique_solution_for_every_target {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) (Y : IntervalArray n R) :
    ∃! X : IntervalArray n R, nearFarTransform D H X = Y := by
  refine ⟨nearFarInverse D H Y, nearFarTransform_inverse D H Y, ?_⟩
  intro X hX
  exact nearFar_solution_unique D H X Y hX

theorem inverse_is_coordinate_polynomial {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) (Y : IntervalArray n R) (I : BoundaryInterval n) :
    MvPolynomial.eval₂Hom (RingHom.id R) Y
      (triangularInversePolynomial (fun _ π => π.nearFarWeight D H) I) =
        nearFarInverse D H Y I :=
  triangularInversePolynomial_eval _ Y I

theorem zero_triangular_weights_give_identity {R : Type*} [CommRing R]
    (Y : IntervalArray n R) : triangularInverse (fun _ _ => (0 : R)) Y = Y := by
  funext I
  rw [triangularInverse]
  simp

theorem geometric_arrays_use_same_physical_root {R : Type*} [CommRing R]
    (P : LabelledTuple n) (g a : ZMod n) :
    geometricBoundaryArray (R := R) (shift a P) (g - a) =
      geometricBoundaryArray (R := R) P g :=
  geometricBoundaryArray_shift P g a

end NearFarInverseIndependentReview

#print axioms NearFarInverseIndependentReview.all_raw_increasing_triples
#print axioms NearFarInverseIndependentReview.full_triple_domain_finite
#print axioms NearFarInverseIndependentReview.full_interval_domain_finite
#print axioms NearFarInverseIndependentReview.unary_term_is_exact
#print axioms NearFarInverseIndependentReview.every_half_factor_is_exact
#print axioms NearFarInverseIndependentReview.unit_array_is_leaf_indicator
#print axioms NearFarInverseIndependentReview.inverse_base_coordinate
#print axioms NearFarInverseIndependentReview.unique_solution_for_every_target
#print axioms NearFarInverseIndependentReview.inverse_is_coordinate_polynomial
#print axioms NearFarInverseIndependentReview.zero_triangular_weights_give_identity
#print axioms NearFarInverseIndependentReview.geometric_arrays_use_same_physical_root
