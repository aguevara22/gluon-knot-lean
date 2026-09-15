import SM.Gates
import SM.FiniteCompositions
import SM.CyclicChambers
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Eval

set_option pp.fullNames true
set_option pp.universes false

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

#check SM.openTreeRec
#print axioms SM.openTreeRec
#check SM.rootedTreeRec
#print axioms SM.rootedTreeRec
#check SM.openTreeRec_one
#print axioms SM.openTreeRec_one
#check SM.openTreeRec_many
#print axioms SM.openTreeRec_many
#check SM.fullBoundaryInterval
#print axioms SM.fullBoundaryInterval
#check SM.openTreeSum
#print axioms SM.openTreeSum
#check SM.treeCoefficient
#print axioms SM.treeCoefficient
#check SM.mainTreeCoefficient
#print axioms SM.mainTreeCoefficient
#check SM.openTreeSum_one
#print axioms SM.openTreeSum_one
#check SM.openTreeSum_many
#print axioms SM.openTreeSum_many
#check SM.treeCoefficient_eq
#print axioms SM.treeCoefficient_eq
#check SM.treesumData
#print axioms SM.treesumData

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

#check SM.IntervalComposition.nearSign_eq_of_chi
#print axioms SM.IntervalComposition.nearSign_eq_of_chi
#check SM.IntervalComposition.farSign_eq_of_chi
#print axioms SM.IntervalComposition.farSign_eq_of_chi
#check SM.IntervalComposition.ordinaryWeight_eq_of_chi
#print axioms SM.IntervalComposition.ordinaryWeight_eq_of_chi
#check SM.IntervalComposition.rootWeight_eq_of_chi
#print axioms SM.IntervalComposition.rootWeight_eq_of_chi
#check SM.openTreeSum_eq_of_chi
#print axioms SM.openTreeSum_eq_of_chi
#check SM.treeCoefficient_eq_of_chi
#print axioms SM.treeCoefficient_eq_of_chi
#check SM.openTreeSum_shift
#print axioms SM.openTreeSum_shift
#check SM.treeCoefficient_shift
#print axioms SM.treeCoefficient_shift
#check SM.mainTreeCoefficient_shift
#print axioms SM.mainTreeCoefficient_shift
#check SM.treesumData_shift
#print axioms SM.treesumData_shift

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

/-- All quantities in the source chirotope-constancy clause, on G1 alone. -/
theorem tree_data_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
      π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
    (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn :=
  ⟨fun _ π => ⟨π.ordinaryWeight_eq_of_chi hP hQ hchi g,
    π.rootWeight_eq_of_chi hP hQ hchi g⟩,
    openTreeSum_eq_of_chi hP hQ hchi g, treeCoefficient_eq_of_chi hP hQ hchi g hn⟩

/-- The labelled chamber is the actual connected component of the generic locus.
Its continuous sign maps have discrete target, so they are constant on it. -/
theorem labelled_chamber_chi_constant (P Q : GenericTuple n) (hQ : Q ∈ labelledChamber P)
    (i j k : ZMod n) : chi P.val i j k = chi Q.val i j k := by
  exact isPreconnected_connectedComponent.constant
    (continuous_generic_chi i j k).continuousOn mem_connectedComponent hQ

theorem tree_data_labelled_chamber_constant (P Q : GenericTuple n)
    (hQ : Q ∈ labelledChamber P) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P.val P.property.1 g = π.ordinaryWeight Q.val Q.property.1 g ∧
      π.rootWeight P.val P.property.1 g = π.rootWeight Q.val Q.property.1 g) ∧
    (∀ I, openTreeSum P.val P.property.1 g I = openTreeSum Q.val Q.property.1 g I) ∧
    treeCoefficient P.val P.property.1 g hn = treeCoefficient Q.val Q.property.1 g hn :=
  tree_data_eq_of_chi P.property.1 Q.property.1 (labelled_chamber_chi_constant P Q hQ) g hn

/-- The path clause retains G1 only. Its asserted constant chirotope already
forces all values to agree; no further geometric condition is needed. -/
theorem tree_data_G1_path_constant {P Q : {P : LabelledTuple n // G1 P}}
    (γ : Path P Q)
    (hchi : ∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k)
    (g : ZMod n) (hn : 3 ≤ n) (s t : unitInterval) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight (γ s).val (γ s).property g =
        π.ordinaryWeight (γ t).val (γ t).property g ∧
      π.rootWeight (γ s).val (γ s).property g = π.rootWeight (γ t).val (γ t).property g) ∧
    (∀ I, openTreeSum (γ s).val (γ s).property g I =
      openTreeSum (γ t).val (γ t).property g I) ∧
    treeCoefficient (γ s).val (γ s).property g hn =
      treeCoefficient (γ t).val (γ t).property g hn :=
  tree_data_eq_of_chi (γ s).property (γ t).property (hchi s t) g hn

/-- On the actual unlabelled chamber, a label change must carry the root with it.
The proved chamber preimage theorem supplies the shift; this does not assume
independence of different physical roots. -/
theorem treeCoefficient_quotient_chamber_transport (P Q : GenericTuple n)
    (hn : 3 ≤ n) (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, Q ∈ labelledChamber (genericShift a P) ∧
      ∀ g : ZMod n, treeCoefficient Q.val Q.property.1 (g - a) hn =
        treeCoefficient P.val P.property.1 g hn := by
  have hm : Q ∈ ⋃ a : ZMod n, labelledChamber (genericShift a P) := by
    rw [← chamber_preimage_eq_cyclic_union hn P]
    exact hQ
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hm
  refine ⟨a, ha, ?_⟩
  intro g
  have he := (tree_data_labelled_chamber_constant (genericShift a P) Q ha (g - a) hn).2.2
  exact he.symm.trans (treeCoefficient_shift P.val P.property.1 g a hn)

end

end SM

#check SM.tree_data_eq_of_chi
#print axioms SM.tree_data_eq_of_chi
#check SM.labelled_chamber_chi_constant
#print axioms SM.labelled_chamber_chi_constant
#check SM.tree_data_labelled_chamber_constant
#print axioms SM.tree_data_labelled_chamber_constant
#check SM.tree_data_G1_path_constant
#print axioms SM.tree_data_G1_path_constant
#check SM.treeCoefficient_quotient_chamber_transport
#print axioms SM.treeCoefficient_quotient_chamber_transport

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

#check SM.OpenPlaneTree
#print axioms SM.OpenPlaneTree
#check SM.openPlaneTreeUngraft
#print axioms SM.openPlaneTreeUngraft
#check SM.openPlaneTree_finite
#print axioms SM.openPlaneTree_finite
#check SM.RootedPlaneTree
#print axioms SM.RootedPlaneTree

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

#check SM.OpenPlaneTree.weight
#print axioms SM.OpenPlaneTree.weight
#check SM.OpenPlaneTree.ordinaryCount
#print axioms SM.OpenPlaneTree.ordinaryCount
#check SM.OpenPlaneTree.ordinaryProduct
#print axioms SM.OpenPlaneTree.ordinaryProduct
#check SM.OpenPlaneTree.weight_eq_signed_product
#print axioms SM.OpenPlaneTree.weight_eq_signed_product
#check SM.RootedPlaneTree.weight
#print axioms SM.RootedPlaneTree.weight
#check SM.RootedPlaneTree.ordinaryCount
#print axioms SM.RootedPlaneTree.ordinaryCount
#check SM.RootedPlaneTree.ordinaryProduct
#print axioms SM.RootedPlaneTree.ordinaryProduct
#check SM.RootedPlaneTree.weight_eq_signed_product
#print axioms SM.RootedPlaneTree.weight_eq_signed_product

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

#check SM.openPlaneTreeSum
#print axioms SM.openPlaneTreeSum
#check SM.OpenPlaneTree.eq_leaf
#print axioms SM.OpenPlaneTree.eq_leaf
#check SM.openPlaneTreeSum_one
#print axioms SM.openPlaneTreeSum_one
#check SM.openPlaneTreeSum_many
#print axioms SM.openPlaneTreeSum_many
#check SM.openTreeRec_eq_planeTreeSum
#print axioms SM.openTreeRec_eq_planeTreeSum
#check SM.rootedTreeRec_eq_planeTreeSum
#print axioms SM.rootedTreeRec_eq_planeTreeSum
#check SM.rootedTreeRec_eq_signed_planeTreeSum
#print axioms SM.rootedTreeRec_eq_signed_planeTreeSum

namespace SM

noncomputable section

universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism preserves every actual finite tree evaluation. -/
theorem OpenPlaneTree.map_weight (f : R →+* S)
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    f (T.weight ordinary) = T.weight (fun J π => f (ordinary J π)) := by
  induction T with
  | leaf hI => simp [OpenPlaneTree.weight]
  | node π hp children ih => simp [OpenPlaneTree.weight, map_prod, ih]

theorem RootedPlaneTree.map_weight (f : R →+* S)
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    f (T.weight ordinary rootWeight) =
      T.weight (fun J π => f (ordinary J π)) (fun J π => f (rootWeight J π)) := by
  simp [RootedPlaneTree.weight, map_prod, OpenPlaneTree.map_weight]

theorem map_rootedTreeRec (f : R →+* S)
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) :
    f (rootedTreeRec ordinary rootWeight I) =
      rootedTreeRec (fun J π => f (ordinary J π)) (fun J π => f (rootWeight J π)) I := by
  rw [rootedTreeRec_eq_planeTreeSum, map_sum, rootedTreeRec_eq_planeTreeSum]
  apply Finset.sum_congr rfl
  intro T _
  exact T.map_weight f ordinary rootWeight

/-- Separate variables for the ordinary and distinguished-root weights of every
actual interval composition. No geometric gate relation is imposed. -/
abbrev TreeWeightIndex (n : ℕ) := Bool × (Σ I : BoundaryInterval n, IntervalComposition I)

def formalOrdinaryWeight (I : BoundaryInterval n) (π : IntervalComposition I) :
    MvPolynomial (TreeWeightIndex n) ℤ := MvPolynomial.X (false, ⟨I, π⟩)

def formalRootWeight (I : BoundaryInterval n) (π : IntervalComposition I) :
    MvPolynomial (TreeWeightIndex n) ℤ := MvPolynomial.X (true, ⟨I, π⟩)

theorem planeTree_formal_identity (I : BoundaryInterval n) :
    rootedTreeRec formalOrdinaryWeight formalRootWeight I =
      ∑ T : RootedPlaneTree I, (-1 : MvPolynomial (TreeWeightIndex n) ℤ) ^ T.ordinaryCount *
        formalRootWeight I T.fst * T.ordinaryProduct formalOrdinaryWeight :=
  rootedTreeRec_eq_signed_planeTreeSum _ _ I

/-- The formal polynomial evaluates to the same recursion for every assignment
of its independent variables in any commutative ring. -/
theorem planeTree_formal_evaluation (I : BoundaryInterval n) (values : TreeWeightIndex n → S) :
    MvPolynomial.eval₂Hom (Int.castRingHom S) values
        (rootedTreeRec formalOrdinaryWeight formalRootWeight I) =
      rootedTreeRec (fun J π => values (false, ⟨J, π⟩))
        (fun J π => values (true, ⟨J, π⟩)) I := by
  simpa only [formalOrdinaryWeight, formalRootWeight, MvPolynomial.eval₂Hom_X'] using
    map_rootedTreeRec (MvPolynomial.eval₂Hom (Int.castRingHom S) values)
      formalOrdinaryWeight formalRootWeight I

theorem treeCoefficient_eq_signed_planeTreeSum (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : ℤ) ^ T.ordinaryCount * T.fst.rootWeight P hP g *
        T.ordinaryProduct (fun _ π => π.ordinaryWeight P hP g) :=
  rootedTreeRec_eq_signed_planeTreeSum _ _ _

/-- All clauses of source lem:treesum-trees: actual gate evaluation, the
independent-variable identity over integers, and every ring evaluation. The
separate ungrafting equivalence records the term-by-term tree correspondence. -/
theorem treesum_trees (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    (treeCoefficient P hP g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : ℤ) ^ T.ordinaryCount * T.fst.rootWeight P hP g *
        T.ordinaryProduct (fun _ π => π.ordinaryWeight P hP g)) ∧
    (rootedTreeRec formalOrdinaryWeight formalRootWeight (fullBoundaryInterval hn) =
      ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
        (-1 : MvPolynomial (TreeWeightIndex n) ℤ) ^ T.ordinaryCount *
          formalRootWeight (fullBoundaryInterval hn) T.fst * T.ordinaryProduct formalOrdinaryWeight) ∧
    (∀ (A : Type v) [CommRing A] (values : TreeWeightIndex n → A),
      MvPolynomial.eval₂Hom (Int.castRingHom A) values
          (rootedTreeRec formalOrdinaryWeight formalRootWeight (fullBoundaryInterval hn)) =
        rootedTreeRec (fun J π => values (false, ⟨J, π⟩))
          (fun J π => values (true, ⟨J, π⟩)) (fullBoundaryInterval hn)) :=
  ⟨treeCoefficient_eq_signed_planeTreeSum P hP g hn,
    planeTree_formal_identity _, fun _ _ values => planeTree_formal_evaluation _ values⟩

end

end SM

#check SM.OpenPlaneTree.map_weight
#print axioms SM.OpenPlaneTree.map_weight
#check SM.RootedPlaneTree.map_weight
#print axioms SM.RootedPlaneTree.map_weight
#check SM.map_rootedTreeRec
#print axioms SM.map_rootedTreeRec
#check SM.TreeWeightIndex
#print axioms SM.TreeWeightIndex
#check SM.formalOrdinaryWeight
#print axioms SM.formalOrdinaryWeight
#check SM.formalRootWeight
#print axioms SM.formalRootWeight
#check SM.planeTree_formal_identity
#print axioms SM.planeTree_formal_identity
#check SM.planeTree_formal_evaluation
#print axioms SM.planeTree_formal_evaluation
#check SM.treeCoefficient_eq_signed_planeTreeSum
#print axioms SM.treeCoefficient_eq_signed_planeTreeSum
#check SM.treesum_trees
#print axioms SM.treesum_trees

#print SM.openTreeRec
#print SM.rootedTreeRec
#print SM.fullBoundaryInterval
#print SM.openTreeSum
#print SM.treeCoefficient
#print SM.mainTreeCoefficient
#print SM.treesumData
#print SM.OpenPlaneTree
#print SM.openPlaneTreeUngraft
#print SM.RootedPlaneTree
#print SM.OpenPlaneTree.weight
#print SM.OpenPlaneTree.ordinaryCount
#print SM.OpenPlaneTree.ordinaryProduct
#print SM.RootedPlaneTree.weight
#print SM.RootedPlaneTree.ordinaryCount
#print SM.RootedPlaneTree.ordinaryProduct
#print SM.TreeWeightIndex
#print SM.formalOrdinaryWeight
#print SM.formalRootWeight

namespace TreeDefinitionIndependentReview
open SM

variable {n : ℕ} [NeZero n]

-- The source base case and recursive case exhaust every actual interval.
theorem interval_recursion_cases (I : BoundaryInterval n) :
    I.leaves = 1 ∨ 2 ≤ I.leaves := by
  have := I.leaves_pos
  omega

-- Telescoping the actual successive cuts recovers every leaf exactly in size.
theorem part_leaf_sum {I : BoundaryInterval n} (π : IntervalComposition I) :
    (∑ k : Fin π.parts, (π.part k).leaves) = I.leaves := by
  have hterm : ∀ k : Fin π.parts,
      (π.part k).leaves + (π.cut k.castSucc).val = (π.cut k.succ).val := by
    intro k
    exact Nat.sub_add_cancel (π.strict (show k.castSucc < k.succ by simp)).le
  have hs : (∑ k : Fin π.parts, (π.part k).leaves + (π.cut k.castSucc).val) =
      ∑ k : Fin π.parts, (π.cut k.succ).val :=
    Finset.sum_congr rfl (fun k _ => hterm k)
  rw [Finset.sum_add_distrib] at hs
  have hf := Fin.sum_univ_castSucc (fun k : Fin (π.parts + 1) => (π.cut k).val)
  have hl := Fin.sum_univ_succ (fun k : Fin (π.parts + 1) => (π.cut k).val)
  rw [π.last] at hf
  rw [π.first] at hl
  change (∑ k : Fin π.parts, (π.part k).leaves) = I.right.val - I.left.val
  omega

-- No high-arity composition can hide inside a shorter interval.
theorem source_arity_bound {I : BoundaryInterval n} (π : IntervalComposition I) :
    π.parts ≤ I.leaves := by
  calc
    π.parts = ∑ _k : Fin π.parts, (1 : ℕ) := by simp
    _ ≤ ∑ k : Fin π.parts, (π.part k).leaves := by
      apply Finset.sum_le_sum
      intro k _
      exact (π.part k).leaves_pos
    _ = I.leaves := part_leaf_sum π

-- This also checks that the root's one-part term is literally the open sum.
theorem one_part_root_term (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) :
    let π := IntervalComposition.single I
    π.rootWeight P hP g * ∏ k : Fin π.parts, openTreeSum P hP g (π.part k) =
      openTreeSum P hP g I := by
  dsimp only
  rw [((IntervalComposition.single I).one_part_weights P hP g rfl).2, one_mul]
  change (∏ k : Fin 1, openTreeSum P hP g ((IntervalComposition.single I).part k)) = _
  rw [Fin.prod_univ_one]
  congr 1

-- The printed recurrence determines the open quantity uniquely on the full
-- source interval domain, using strict child-size decrease rather than a bound.
theorem source_recursion_unique {R : Type*} [CommRing R]
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (b : BoundaryInterval n → R)
    (one : ∀ I, I.leaves = 1 → b I = 1)
    (many : ∀ I, 2 ≤ I.leaves → b I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        ordinary I π.val * ∏ k : Fin π.val.parts, b (π.val.part k)) :
    ∀ I, b I = openTreeRec ordinary I := by
  intro I
  induction hm : I.leaves using Nat.strong_induction_on generalizing I with
  | h m ih =>
    rcases interval_recursion_cases I with hI | hI
    · rw [one I hI, openTreeRec_one ordinary I hI]
    · rw [many I hI, openTreeRec_many ordinary I hI]
      congr 1
      apply Finset.sum_congr rfl
      intro π _
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      exact ih (π.val.part k).leaves
        (by simpa only [hm] using π.val.part_leaves_lt π.property k)
        (π.val.part k) rfl

theorem full_interval_and_last_root (hn : 3 ≤ n) (P : LabelledTuple n) (hP : G1 P) :
    (fullBoundaryInterval hn).left.val = 0 ∧
    (fullBoundaryInterval hn).right.val = n - 1 ∧
    (fullBoundaryInterval hn).leaves = n - 1 ∧
    mainTreeCoefficient P hP hn = treeCoefficient P hP (n : ZMod n) hn := by
  simp [fullBoundaryInterval, BoundaryInterval.leaves, mainTreeCoefficient]

-- Physical-root transport and the separately fixed-last-label convention must
-- remain distinct; no independence of different roots is assumed.
theorem exact_root_transport (P : LabelledTuple n) (hP : G1 P)
    (g a : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (shift a P) (g1_shift_forward a hP) (g - a) hn =
      treeCoefficient P hP g hn ∧
    mainTreeCoefficient (shift a P) (g1_shift_forward a hP) hn =
      treeCoefficient P hP a hn :=
  ⟨treeCoefficient_shift P hP g a hn, mainTreeCoefficient_shift P hP a hn⟩

def actualLeafCount : {I : BoundaryInterval n} → OpenPlaneTree I → ℕ
  | _, .leaf _ => 1
  | _, .node _ _ children => ∑ k, actualLeafCount (children k)

theorem actual_tree_leaf_count {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    actualLeafCount T = I.leaves := by
  induction T with
  | leaf hI => exact hI.symm
  | node π hp children ih =>
    simp only [actualLeafCount]
    rw [Finset.sum_congr rfl (fun k _ => ih k)]
    exact part_leaf_sum π

theorem only_leaf_on_one_leaf_interval {I : BoundaryInterval n}
    (hI : I.leaves = 1) (T : OpenPlaneTree I) : T = OpenPlaneTree.leaf hI := by
  cases T with
  | leaf h => rfl
  | node π hp children =>
    have := source_arity_bound π
    omega

-- All source ordered child arrays are accepted, including binary nodes.
theorem arbitrary_graft_and_ungraft {I : BoundaryInterval n}
    (π : IntervalComposition I) (hp : 2 ≤ π.parts)
    (children : ∀ k : Fin π.parts, OpenPlaneTree (π.part k)) :
    (openPlaneTreeUngraft I) (.node π hp children) =
      Sum.inr ⟨⟨π, hp⟩, children⟩ ∧
    (openPlaneTreeUngraft I).symm (Sum.inr ⟨⟨π, hp⟩, children⟩) =
      OpenPlaneTree.node π hp children := ⟨rfl, rfl⟩

theorem all_actual_tree_shapes_enumerated (I : BoundaryInterval n) :
    (∀ T : OpenPlaneTree I, T ∈ (Finset.univ : Finset (OpenPlaneTree I))) ∧
    (∀ T : RootedPlaneTree I, T ∈ (Finset.univ : Finset (RootedPlaneTree I))) :=
  ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩

-- Arbitrary ring-valued vertex weights are kept independent, including the
-- root's weight, and the exponent counts only ordinary vertices.
theorem arbitrary_root_weight_formula {R : Type*} [CommRing R]
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.weight ordinary rootWeight = (-1 : R) ^ T.ordinaryCount *
      rootWeight I T.fst * T.ordinaryProduct ordinary :=
  T.weight_eq_signed_product ordinary rootWeight

def twoLeafInterval : BoundaryInterval 3 := ⟨0, 2, by decide⟩

def binaryComposition : IntervalComposition twoLeafInterval where
  parts := 2
  parts_pos := by decide
  cut := id
  strict := strictMono_id
  first := rfl
  last := rfl

def actualBinaryTree : OpenPlaneTree twoLeafInterval :=
  .node binaryComposition (by decide)
    (fun k => .leaf (by fin_cases k <;> rfl))

-- Binary trees remain present before gate specialization: their formal
-- ordinary weight is an arbitrary variable, with one ordinary minus sign.
theorem binary_tree_formal_weight {R : Type*} [CommRing R]
    (ordinary : ∀ I : BoundaryInterval 3, IntervalComposition I → R) :
    actualBinaryTree.ordinaryCount = 1 ∧
    actualBinaryTree.weight ordinary = -ordinary twoLeafInterval binaryComposition := by
  simp [actualBinaryTree, OpenPlaneTree.ordinaryCount, OpenPlaneTree.weight]

-- An evaluation separating the Boolean tags proves that ordinary and root
-- indeterminates for the same composition have not been identified.
theorem ordinary_root_variables_distinct (I : BoundaryInterval n) (π : IntervalComposition I) :
    formalOrdinaryWeight I π ≠ formalRootWeight I π := by
  intro he
  let ev := MvPolynomial.eval₂Hom (Int.castRingHom ℤ)
    (fun v : TreeWeightIndex n => if v.1 then (1 : ℤ) else 0)
  have hh := congrArg ev he
  norm_num [ev, formalOrdinaryWeight, formalRootWeight] at hh

-- Every pair of independent weight assignments occurs as a polynomial
-- evaluation; neither a geometric sign relation nor root/ordinary equality is required.
theorem arbitrary_separate_assignments {R : Type*} [CommRing R]
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) :
    ∃ values : TreeWeightIndex n → R,
      (∀ J π, values (false, ⟨J, π⟩) = ordinary J π) ∧
      (∀ J π, values (true, ⟨J, π⟩) = rootWeight J π) ∧
      MvPolynomial.eval₂Hom (Int.castRingHom R) values
        (rootedTreeRec formalOrdinaryWeight formalRootWeight I) =
          rootedTreeRec ordinary rootWeight I := by
  let values : TreeWeightIndex n → R := fun v =>
    if v.1 then rootWeight v.2.1 v.2.2 else ordinary v.2.1 v.2.2
  refine ⟨values, by intros; rfl, by intros; rfl, ?_⟩
  simpa [values] using planeTree_formal_evaluation I values

-- The complete actual geometric identity is extracted without supplying any
-- plane-tree identity as an assumption and using G1 alone.
theorem actual_source_identity (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn =
      ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
        (-1 : ℤ) ^ T.ordinaryCount * T.fst.rootWeight P hP g *
          T.ordinaryProduct (fun _ π => π.ordinaryWeight P hP g) :=
  (treesum_trees.{0} P hP g hn).1

end TreeDefinitionIndependentReview

#print axioms TreeDefinitionIndependentReview.interval_recursion_cases
#print axioms TreeDefinitionIndependentReview.part_leaf_sum
#print axioms TreeDefinitionIndependentReview.source_arity_bound
#print axioms TreeDefinitionIndependentReview.one_part_root_term
#print axioms TreeDefinitionIndependentReview.source_recursion_unique
#print axioms TreeDefinitionIndependentReview.full_interval_and_last_root
#print axioms TreeDefinitionIndependentReview.exact_root_transport
#print axioms TreeDefinitionIndependentReview.actual_tree_leaf_count
#print axioms TreeDefinitionIndependentReview.only_leaf_on_one_leaf_interval
#print axioms TreeDefinitionIndependentReview.arbitrary_graft_and_ungraft
#print axioms TreeDefinitionIndependentReview.all_actual_tree_shapes_enumerated
#print axioms TreeDefinitionIndependentReview.arbitrary_root_weight_formula
#print axioms TreeDefinitionIndependentReview.binary_tree_formal_weight
#print axioms TreeDefinitionIndependentReview.ordinary_root_variables_distinct
#print axioms TreeDefinitionIndependentReview.arbitrary_separate_assignments
#print axioms TreeDefinitionIndependentReview.actual_source_identity

#print TreeDefinitionIndependentReview.part_leaf_sum
#print axioms Fin.sum_univ_castSucc
#print axioms Fin.sum_univ_succ
#print axioms Finset.sum_congr
