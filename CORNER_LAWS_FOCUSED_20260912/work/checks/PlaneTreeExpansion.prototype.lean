import SM.Gates
import SM.FiniteCompositions
import Mathlib.Tactic

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

/-- An ordinary plane tree on an actual leaf interval. Ordered children are
indexed by the parts of its actual composition. Binary nodes are included,
even when a later gate evaluation gives them weight zero. -/
inductive OpenPlaneTree : BoundaryInterval n → Type
  | leaf {I : BoundaryInterval n} (one : I.leaves = 1) : OpenPlaneTree I
  | node {I : BoundaryInterval n} (π : IntervalComposition I) (many : 2 ≤ π.parts)
      (children : ∀ k : Fin π.parts, OpenPlaneTree (π.part k)) : OpenPlaneTree I

/-- Removing the top vertex records exactly its ordered child composition.
Grafting reconstructs the same tree; the leaf summand records the unique leaf. -/
def openPlaneTreeUngraft (I : BoundaryInterval n) :
    OpenPlaneTree I ≃ (PLift (I.leaves = 1) ⊕
      Σ π : {π : IntervalComposition I // 2 ≤ π.parts},
        (∀ k : Fin π.val.parts, OpenPlaneTree (π.val.part k))) where
  toFun t := match t with
    | .leaf hI => Sum.inl ⟨hI⟩
    | .node π hp children => Sum.inr ⟨⟨π, hp⟩, children⟩
  invFun t := match t with
    | Sum.inl hI => .leaf hI.down
    | Sum.inr ⟨π, children⟩ => .node π.val π.property children
  left_inv t := by cases t <;> rfl
  right_inv t := by
    rcases t with ⟨hI⟩ | ⟨⟨π, hp⟩, children⟩ <;> rfl

/-- All actual ordinary plane trees form a finite type. This is induction on
leaf count, using the full raw composition type and strict decrease for every
child. It does not impose a chosen height bound or discard any arity. -/
theorem openPlaneTree_finite (I : BoundaryInterval n) : Finite (OpenPlaneTree I) := by
  induction hm : I.leaves using Nat.strong_induction_on generalizing I with
  | h m ih =>
    letI childrenFinite (π : {π : IntervalComposition I // 2 ≤ π.parts})
        (k : Fin π.val.parts) : Finite (OpenPlaneTree (π.val.part k)) :=
      ih (π.val.part k).leaves (by simpa only [hm] using π.val.part_leaves_lt π.property k)
        (π.val.part k) rfl
    exact Finite.of_injective (openPlaneTreeUngraft I) (openPlaneTreeUngraft I).injective

instance (I : BoundaryInterval n) : Finite (OpenPlaneTree I) := openPlaneTree_finite I

noncomputable instance (I : BoundaryInterval n) : Fintype (OpenPlaneTree I) :=
  Fintype.ofFinite _

/-- The distinguished root has at least one child and no ordinary-node sign.
Its composition is unrestricted beyond the exact source definition. -/
def RootedPlaneTree (I : BoundaryInterval n) :=
  Σ π : IntervalComposition I, (∀ k : Fin π.parts, OpenPlaneTree (π.part k))

instance (I : BoundaryInterval n) : Finite (RootedPlaneTree I) := by
  unfold RootedPlaneTree
  infer_instance

noncomputable instance (I : BoundaryInterval n) : Fintype (RootedPlaneTree I) :=
  Fintype.ofFinite _

end

end SM

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

namespace OpenPlaneTree

/-- One minus sign for each ordinary internal vertex, with independent weights. -/
def weight (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R) :
    {I : BoundaryInterval n} → OpenPlaneTree I → R
  | _, .leaf _ => 1
  | I, .node π _ children => -ordinary I π * ∏ k, weight ordinary (children k)

def ordinaryCount : {I : BoundaryInterval n} → OpenPlaneTree I → ℕ
  | _, .leaf _ => 0
  | _, .node π _ children => 1 + ∑ k : Fin π.parts, ordinaryCount (children k)

/-- The product over actual ordinary vertices, before inserting its sign. -/
def ordinaryProduct (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R) :
    {I : BoundaryInterval n} → OpenPlaneTree I → R
  | _, .leaf _ => 1
  | I, .node π _ children => ordinary I π * ∏ k, ordinaryProduct ordinary (children k)

theorem weight_eq_signed_product
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    weight ordinary T = (-1 : R) ^ ordinaryCount T * ordinaryProduct ordinary T := by
  induction T with
  | leaf hI => simp [weight, ordinaryCount, ordinaryProduct]
  | node π hp children ih =>
    simp only [weight, ordinaryCount, ordinaryProduct]
    rw [Finset.prod_congr rfl (fun k _ => ih k), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, pow_add, pow_one]
    ring

end OpenPlaneTree

/-- The root carries its own weight and no extra minus sign. -/
def RootedPlaneTree.weight
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) : R :=
  rootWeight I T.fst * ∏ k, OpenPlaneTree.weight ordinary (T.snd k)

def RootedPlaneTree.ordinaryCount {I : BoundaryInterval n} (T : RootedPlaneTree I) : ℕ :=
  ∑ k, OpenPlaneTree.ordinaryCount (T.snd k)

def RootedPlaneTree.ordinaryProduct
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) : R :=
  ∏ k, OpenPlaneTree.ordinaryProduct ordinary (T.snd k)

theorem RootedPlaneTree.weight_eq_signed_product
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.weight ordinary rootWeight = (-1 : R) ^ T.ordinaryCount *
      rootWeight I T.fst * T.ordinaryProduct ordinary := by
  unfold weight ordinaryCount ordinaryProduct
  rw [Finset.prod_congr rfl (fun k _ => OpenPlaneTree.weight_eq_signed_product ordinary (T.snd k)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end

end SM

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

def openPlaneTreeSum (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R := ∑ T : OpenPlaneTree I, T.weight ordinary

theorem OpenPlaneTree.eq_leaf {I : BoundaryInterval n} (hI : I.leaves = 1)
    (T : OpenPlaneTree I) : T = .leaf hI := by
  cases T with
  | leaf h => rfl
  | node π hp children =>
    have hk := π.part_leaves_lt hp (⟨0, π.parts_pos⟩ : Fin π.parts)
    have hkpos := (π.part (⟨0, π.parts_pos⟩ : Fin π.parts)).leaves_pos
    omega

theorem openPlaneTreeSum_one (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openPlaneTreeSum ordinary I = 1 := by
  letI : Unique (OpenPlaneTree I) := ⟨⟨.leaf hI⟩, OpenPlaneTree.eq_leaf hI⟩
  rw [openPlaneTreeSum, Fintype.sum_unique, OpenPlaneTree.eq_leaf hI (default : OpenPlaneTree I)]
  rfl

/-- Ungrafting splits the finite sum into the top composition and all independent
ordered child choices. Distributivity changes the sum over those choices into
the product of the child sums. The single top minus is kept outside. -/
theorem openPlaneTreeSum_many (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openPlaneTreeSum ordinary I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        ordinary I π.val * ∏ k : Fin π.val.parts, openPlaneTreeSum ordinary (π.val.part k) := by
  classical
  letI : IsEmpty (PLift (I.leaves = 1)) := ⟨fun h => by have := h.down; omega⟩
  have hs := Fintype.sum_equiv (openPlaneTreeUngraft I)
    (OpenPlaneTree.weight ordinary)
    (Sum.elim (fun _ => (1 : R)) (fun v =>
      -ordinary I v.1.val * ∏ k, OpenPlaneTree.weight ordinary (v.2 k)))
    (by intro T; cases T <;> rfl)
  unfold openPlaneTreeSum
  rw [hs, Fintype.sum_sum_type]
  simp only [Finset.sum_of_isEmpty, zero_add, Fintype.sum_sigma, Sum.elim_inr]
  simp_rw [← Finset.mul_sum, ← Fintype.prod_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- The recursively defined open coefficient equals the sum over all actual
ordinary plane trees, proved by strict decrease of every child interval. -/
theorem openTreeRec_eq_planeTreeSum
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R) (I : BoundaryInterval n) :
    openTreeRec ordinary I = openPlaneTreeSum ordinary I := by
  by_cases hI : I.leaves = 1
  · rw [openTreeRec_one ordinary I hI, openPlaneTreeSum_one ordinary I hI]
  · have hm : 2 ≤ I.leaves := by have := I.leaves_pos; omega
    rw [openTreeRec_many ordinary I hm, openPlaneTreeSum_many ordinary I hm]
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact openTreeRec_eq_planeTreeSum ordinary (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

/-- Grafting at the distinguished root allows every source composition,
including the single-child case, and inserts no ordinary-vertex sign. -/
theorem rootedTreeRec_eq_planeTreeSum
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) :
    rootedTreeRec ordinary rootWeight I = ∑ T : RootedPlaneTree I, T.weight ordinary rootWeight := by
  classical
  unfold rootedTreeRec
  simp_rw [openTreeRec_eq_planeTreeSum, openPlaneTreeSum, Fintype.prod_sum, Finset.mul_sum]
  let e : (Σ π : IntervalComposition I, ∀ k : Fin π.parts, OpenPlaneTree (π.part k)) ≃
      RootedPlaneTree I := Equiv.refl _
  calc
    _ = ∑ T : (Σ π : IntervalComposition I, ∀ k : Fin π.parts, OpenPlaneTree (π.part k)),
        rootWeight I T.1 * ∏ k, OpenPlaneTree.weight ordinary (T.2 k) :=
      (Fintype.sum_sigma (fun T : (Σ π : IntervalComposition I,
        ∀ k : Fin π.parts, OpenPlaneTree (π.part k)) =>
        rootWeight I T.1 * ∏ k, OpenPlaneTree.weight ordinary (T.2 k))).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The full signed vertex-product formula, valid for arbitrary independent
weights in every commutative ring. -/
theorem rootedTreeRec_eq_signed_planeTreeSum
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) :
    rootedTreeRec ordinary rootWeight I = ∑ T : RootedPlaneTree I,
      (-1 : R) ^ T.ordinaryCount * rootWeight I T.fst * T.ordinaryProduct ordinary := by
  rw [rootedTreeRec_eq_planeTreeSum]
  apply Finset.sum_congr rfl
  intro T _
  exact T.weight_eq_signed_product ordinary rootWeight

end

end SM

#print axioms SM.openTreeRec_eq_planeTreeSum
#print axioms SM.rootedTreeRec_eq_planeTreeSum
#print axioms SM.rootedTreeRec_eq_signed_planeTreeSum
