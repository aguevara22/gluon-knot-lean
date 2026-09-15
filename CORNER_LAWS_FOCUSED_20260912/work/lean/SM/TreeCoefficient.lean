import SM.Gates
import SM.FiniteCompositions

namespace SM

noncomputable section

universe u

variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- The open source recursion with arbitrary independent ordinary weights.
The complete raw composition type is finite by the proved encoding; every
recursive call has strictly fewer leaves by the proved child-size theorem. -/
def openTreeRec (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R :=
  if I.leaves = 1 then 1 else
    -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      ordinary I π.val * ∏ k : Fin π.val.parts, openTreeRec ordinary (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

/-- The distinguished root may have one child and carries no extra minus sign. -/
def rootedTreeRec (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R :=
  ∑ π : IntervalComposition I,
    rootWeight I π * ∏ k : Fin π.parts, openTreeRec ordinary (π.part k)

theorem openTreeRec_one (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openTreeRec ordinary I = 1 := by
  rw [openTreeRec]
  simp [hI]

theorem openTreeRec_many (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openTreeRec ordinary I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        ordinary I π.val * ∏ k : Fin π.val.parts, openTreeRec ordinary (π.val.part k) := by
  rw [openTreeRec]
  simp [show I.leaves ≠ 1 by omega]

def fullBoundaryInterval (hn : 3 ≤ n) : BoundaryInterval n where
  left := ⟨0, by omega⟩
  right := ⟨n - 1, by omega⟩
  increasing := by change 0 < n - 1; omega

def openTreeSum (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) : ℤ :=
  openTreeRec (fun _ π => π.ordinaryWeight P hP g) I

def treeCoefficient (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) : ℤ :=
  rootedTreeRec (fun _ π => π.ordinaryWeight P hP g)
    (fun _ π => π.rootWeight P hP g) (fullBoundaryInterval hn)

/-- The main text's last-edge root n is residue zero in the source label convention. -/
def mainTreeCoefficient (P : LabelledTuple n) (hP : G1 P) (hn : 3 ≤ n) : ℤ :=
  treeCoefficient P hP 0 hn

theorem openTreeSum_one (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openTreeSum P hP g I = 1 :=
  openTreeRec_one _ I hI

theorem openTreeSum_many (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openTreeSum P hP g I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.ordinaryWeight P hP g * ∏ k : Fin π.val.parts, openTreeSum P hP g (π.val.part k) :=
  openTreeRec_many _ I hI

theorem treeCoefficient_eq (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn =
      ∑ π : IntervalComposition (fullBoundaryInterval hn),
        π.rootWeight P hP g * ∏ k : Fin π.parts, openTreeSum P hP g (π.part k) := rfl

/-- Source def:treesum, including all open interval sums and the rooted output. -/
def treesumData (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :=
  (openTreeSum P hP g, treeCoefficient P hP g hn, mainTreeCoefficient P hP hn)

end

end SM

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.nearSign P g k = π.nearSign Q g k := hchi _ _ _

theorem farSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.farSign P g k = π.farSign Q g k := hchi _ _ _

theorem ordinaryWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g :=
  π.ordinaryWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

theorem rootWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.rootWeight P hP g = π.rootWeight Q hQ g :=
  π.rootWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

end IntervalComposition

theorem openTreeSum_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (I : BoundaryInterval n) :
    openTreeSum P hP g I = openTreeSum Q hQ g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_eq_of_chi hP hQ hchi g

theorem treeCoefficient_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_eq_of_chi hP hQ hchi g
  · funext J π
    exact π.rootWeight_eq_of_chi hP hQ hchi g

theorem openTreeSum_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n)
    (I : BoundaryInterval n) :
    openTreeSum (shift a P) (g1_shift_forward a hP) (g - a) I = openTreeSum P hP g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_shift P hP g a

theorem treeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (shift a P) (g1_shift_forward a hP) (g - a) hn =
      treeCoefficient P hP g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_shift P hP g a
  · funext J π
    exact π.rootWeight_shift P hP g a

/-- Fixed label zero on the shifted representative corresponds to label a on
the original representative. No independence of different physical roots is assumed. -/
theorem mainTreeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (a : ZMod n) (hn : 3 ≤ n) :
    mainTreeCoefficient (shift a P) (g1_shift_forward a hP) hn = treeCoefficient P hP a hn := by
  simpa only [mainTreeCoefficient, sub_self] using treeCoefficient_shift P hP a a hn

theorem treesumData_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treesumData (shift a P) (g1_shift_forward a hP) (g - a) hn =
      (openTreeSum P hP g, treeCoefficient P hP g hn, treeCoefficient P hP a hn) := by
  unfold treesumData
  rw [funext (openTreeSum_shift P hP g a), treeCoefficient_shift P hP g a hn,
    mainTreeCoefficient_shift P hP a hn]

end

end SM
