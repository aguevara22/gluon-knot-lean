import SM.PlaneTreeFormal
import SM.TreeChamber

set_option pp.fullNames true
set_option pp.universes false

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
#check SM.OpenPlaneTree
#print axioms SM.OpenPlaneTree
#check SM.openPlaneTreeUngraft
#print axioms SM.openPlaneTreeUngraft
#check SM.openPlaneTree_finite
#print axioms SM.openPlaneTree_finite
#check SM.RootedPlaneTree
#print axioms SM.RootedPlaneTree
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
#check SM.TreeDataEqual
#print axioms SM.TreeDataEqual
#check SM.A_chamber
#print axioms SM.A_chamber
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
#print SM.TreeDataEqual
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
  have hs : (∑ k : Fin π.parts, ((π.part k).leaves + (π.cut k.castSucc).val)) =
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
namespace TreeChamberClaimIndependentReview
open SM
variable {n : ℕ} [NeZero n]

theorem complete_G1_quantities (hn : 3 ≤ n) (P Q : LabelledTuple n)
    (hP : G1 P) (hQ : G1 Q) (hc : ∀ i j k, chi P i j k = chi Q i j k)
    (g : ZMod n) :
    (∀ I (π : IntervalComposition I),
      π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
      π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
    (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn :=
  (A_chamber hn).1 P Q hP hQ hc g

theorem actual_connected_component (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : Q ∈ connectedComponent P) (g : ZMod n) :
    TreeDataEqual P.val Q.val P.property.1 Q.property.1 g hn :=
  (A_chamber hn).2.1 P Q hQ g

theorem actual_G1_path (hn : 3 ≤ n) (P Q : {P : LabelledTuple n // G1 P})
    (γ : Path P Q)
    (hc : ∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k)
    (g : ZMod n) (s t : unitInterval) :
    TreeDataEqual (γ s).val (γ t).val (γ s).property (γ t).property g hn :=
  (A_chamber hn).2.2.2 P Q γ hc g s t

-- The quotient statement exposes an actual labelled component and a single
-- coherent cyclic relabelling of every physical root. All weights and open
-- sums transport as well; this does not choose a new arbitrary fixed root.
theorem all_quantities_under_quotient_transport (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, Q ∈ connectedComponent (genericShift a P) ∧
      ∀ g : ZMod n,
        (∀ I (π : IntervalComposition I),
          π.ordinaryWeight Q.val Q.property.1 (g - a) = π.ordinaryWeight P.val P.property.1 g ∧
          π.rootWeight Q.val Q.property.1 (g - a) = π.rootWeight P.val P.property.1 g) ∧
        (∀ I, openTreeSum Q.val Q.property.1 (g - a) I = openTreeSum P.val P.property.1 g I) ∧
        treeCoefficient Q.val Q.property.1 (g - a) hn = treeCoefficient P.val P.property.1 g hn := by
  obtain ⟨a, ha, hcoef⟩ := (A_chamber hn).2.2.1 P Q hQ
  refine ⟨a, ha, ?_⟩
  intro g
  have he := (A_chamber hn).2.1 (genericShift a P) Q ha (g - a)
  refine ⟨?_, ?_, hcoef g⟩
  · intro I π
    exact ⟨(he.1 I π).1.symm.trans (π.ordinaryWeight_shift P.val P.property.1 g a),
      (he.1 I π).2.symm.trans (π.rootWeight_shift P.val P.property.1 g a)⟩
  · intro I
    exact (he.2.1 I).symm.trans (openTreeSum_shift P.val P.property.1 g a I)

end TreeChamberClaimIndependentReview

#print axioms TreeChamberClaimIndependentReview.complete_G1_quantities
#print axioms TreeChamberClaimIndependentReview.actual_connected_component
#print axioms TreeChamberClaimIndependentReview.actual_G1_path
#print axioms TreeChamberClaimIndependentReview.all_quantities_under_quotient_transport
