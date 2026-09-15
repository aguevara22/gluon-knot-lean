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
  have hs := Finset.sum_congr (s := Finset.univ) rfl (fun k _ => hterm k)
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
  simpa [IntervalComposition.single, IntervalComposition.part] using
    (Fin.prod_univ_one (fun k : Fin 1 => openTreeSum P hP g
      ((IntervalComposition.single I).part k)))

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
  (treesum_trees P hP g hn).1

end TreeDefinitionIndependentReview
