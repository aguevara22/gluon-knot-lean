import SM.Gates
import SM.FiniteCompositions

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
