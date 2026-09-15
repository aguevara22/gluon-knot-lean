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
