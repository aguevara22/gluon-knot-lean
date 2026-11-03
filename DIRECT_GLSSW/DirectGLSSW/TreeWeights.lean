import DirectGLSSW.IntervalTrees
import DirectGLSSW.CompositionExpansion
import DirectGLSSW.NearData

/-!
# Independent finite tree weights and their current equation

Source: `ep:Phi`, `ep:tree-recursion`. Ordinary leaves have weight one;
ordinary internal nodes carry the negative ordinary gate product. A marked
root retains every cut, including the empty cut. The sums below are over
the finite tree objects and are defined without reference to the current.
Identification with the published geometric GLSSW conventions is separate.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- The product of actual ordinary vertex weights, defined by tree recursion. -/
noncomputable def ordinaryTreeWeight (D H : TripleArray) :
    {i j : ℕ} → OrdinaryTree i j → ℚ
  | _, _, .leaf _ => 1
  | i, j, .node S children =>
      -gateProduct D H i j (cutVertices i j S.val) *
        ∏ e : CutGap i j S.val, ordinaryTreeWeight D H (children e)

@[simp] theorem ordinaryTreeWeight_leaf (D H : TripleArray) (i : ℕ) :
    ordinaryTreeWeight D H (OrdinaryTree.leaf i) = 1 := rfl

@[simp] theorem ordinaryTreeWeight_node (D H : TripleArray) {i j : ℕ}
    (S : NonUnaryCutSet i j)
    (children : ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2) :
    ordinaryTreeWeight D H (OrdinaryTree.node S children) =
      -gateProduct D H i j (cutVertices i j S.val) *
        ∏ e : CutGap i j S.val, ordinaryTreeWeight D H (children e) := rfl

/-- Sum the independently defined weights over all ordinary interval trees. -/
noncomputable def ordinaryTreeSum (D H : TripleArray) (i j : ℕ) : ℚ :=
  ∑ t : OrdinaryTree i j, ordinaryTreeWeight D H t

/-- Independent choices of one child tree per gap distribute exactly. -/
theorem treeChildren_weight_sum (D H : TripleArray) (i j : ℕ) (S : Finset ℕ) :
    (∑ children : (∀ e : CutGap i j S, OrdinaryTree e.val.1 e.val.2),
      ∏ e : CutGap i j S, ordinaryTreeWeight D H (children e)) =
      ∏ e : CutGap i j S, ordinaryTreeSum D H e.val.1 e.val.2 := by
  classical
  exact (Fintype.prod_sum _).symm

/-- The product of child-tree sums uses precisely the source branch list. -/
theorem treeChildren_weight_sum_eq_branchProduct (D H : TripleArray)
    {i j : ℕ} {S : Finset ℕ} (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    (∑ children : (∀ e : CutGap i j S, OrdinaryTree e.val.1 e.val.2),
      ∏ e : CutGap i j S, ordinaryTreeWeight D H (children e)) =
      branchProduct (ordinaryTreeSum D H) (cutVertices i j S) := by
  rw [treeChildren_weight_sum, branchProduct_eq_prod_cutEdges _ hij hS]
  exact Finset.prod_coe_sort (cutEdges i j S)
    (fun e : ℕ × ℕ => ordinaryTreeSum D H e.1 e.2)

/-- The unique possible leaf contributes exactly the one-edge source. -/
theorem ordinaryTree_leaf_sum (i j : ℕ) :
    (∑ _h : PLift (j = i + 1), (1 : ℚ)) = source i j := by
  classical
  by_cases h : j = i + 1
  · subst j
    simp [source]
  · letI : IsEmpty (PLift (j = i + 1)) := ⟨fun x => h x.down⟩
    simp [source, h]

/-- Decomposing each ordinary tree at its root gives the actual finite recurrence. -/
theorem ordinaryTreeSum_recurrence (D H : TripleArray) {i j : ℕ}
    (hij : i < j) :
    ordinaryTreeSum D H i j =
      source i j - nonUnary D H (ordinaryTreeSum D H) i j := by
  classical
  let f : (PLift (j = i + 1) ⊕
      (Σ S : NonUnaryCutSet i j,
        ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2)) → ℚ :=
    Sum.elim (fun _ => 1) (fun R =>
      -gateProduct D H i j (cutVertices i j R.1.val) *
        ∏ e : CutGap i j R.1.val, ordinaryTreeWeight D H (R.2 e))
  have hdecomp : ordinaryTreeSum D H i j = ∑ R, f R := by
    apply Fintype.sum_equiv (ordinaryTreeEquiv (i := i) (j := j))
    intro t
    cases t <;> rfl
  rw [hdecomp, Fintype.sum_sum_type, Fintype.sum_sigma]
  dsimp only [f, Sum.elim]
  rw [ordinaryTree_leaf_sum]
  simp_rw [← Finset.mul_sum]
  have hbranch (S : NonUnaryCutSet i j) :=
    treeChildren_weight_sum_eq_branchProduct D H hij
      (Finset.mem_powerset.mp (Finset.mem_erase.mp S.property).2)
  simp_rw [hbranch, neg_mul]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  congr 1
  exact Finset.sum_coe_sort ((Finset.Ioo i j).powerset.erase ∅)
    (cutContribution D H (ordinaryTreeSum D H) i j)

/-- The independent finite tree sum satisfies the source Phi equation. -/
theorem ordinaryTreeSum_phi (D H : TripleArray) {i j : ℕ} (hij : i < j) :
    phi D H (ordinaryTreeSum D H) i j = source i j := by
  rw [phi_eq_unary_add]
  exact (eq_sub_iff_add_eq).mp (ordinaryTreeSum_recurrence D H hij)

/-- Triangular uniqueness identifies the tree sum with the constructed current. -/
theorem ordinaryTreeSum_eq_current (D H : TripleArray) {i j : ℕ} (hij : i < j) :
    ordinaryTreeSum D H i j = ordinaryCurrent D H i j := by
  apply ordinaryCurrent_unique D H (ordinaryTreeSum D H) _ hij
  intro a b hab
  exact ordinaryTreeSum_phi D H hab

/-- A marked root permits every cut, including the retained unary root. -/
abbrev MarkedTree (i j : ℕ) :=
  Σ S : IntervalCutSet i j,
    ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2

/-- The marked root has the marked gate product and ordinary weighted children. -/
noncomputable def markedTreeWeight (D H : TripleArray) {i j : ℕ}
    (t : MarkedTree i j) : ℚ :=
  gateProduct D (fun a b c => -H a b c) i j (cutVertices i j t.1.val) *
    ∏ e : CutGap i j t.1.val, ordinaryTreeWeight D H (t.2 e)

/-- The marked expansion is a finite sum over independently defined trees. -/
noncomputable def markedTreeSum (D H : TripleArray) (i j : ℕ) : ℚ :=
  ∑ t : MarkedTree i j, markedTreeWeight D H t

/-- Finite distributivity gives the marked Phi map on the ordinary tree sum. -/
theorem markedTreeSum_eq_phi (D H : TripleArray) {i j : ℕ} (hij : i < j) :
    markedTreeSum D H i j =
      phi D (fun a b c => -H a b c) (ordinaryTreeSum D H) i j := by
  classical
  unfold markedTreeSum
  rw [Fintype.sum_sigma]
  simp only [markedTreeWeight, ← Finset.mul_sum]
  have hbranch (S : IntervalCutSet i j) :=
    treeChildren_weight_sum_eq_branchProduct D H hij
      (Finset.mem_powerset.mp S.property)
  simp_rw [hbranch]
  exact Finset.sum_coe_sort ((Finset.Ioo i j).powerset)
    (cutContribution D (fun a b c => -H a b c) (ordinaryTreeSum D H) i j)

/-- The concrete marked-tree expansion equals the array marked amplitude. -/
theorem markedTreeSum_eq_markedAmplitude (D H : TripleArray) {i j : ℕ}
    (hij : i < j) :
    markedTreeSum D H i j = markedAmplitude D H i j := by
  rw [markedTreeSum_eq_phi D H hij]
  unfold markedAmplitude phi
  apply Finset.sum_congr rfl
  intro S hS
  unfold cutContribution
  congr 1
  rw [branchProduct_eq_prod_cutEdges _ hij (Finset.mem_powerset.mp hS),
    branchProduct_eq_prod_cutEdges _ hij (Finset.mem_powerset.mp hS)]
  apply Finset.prod_congr rfl
  intro e he
  exact ordinaryTreeSum_eq_current D H
    ((cutEdges_mem_iff hij (Finset.mem_powerset.mp hS)).mp he).2.2.1

/-- The finite tree sum in the note's gate conventions is independent of
the rational near array. Geometric and published spinor identifications
remain separate obligations. -/
theorem markedTreeSum_near_independent (D₁ D₂ H : TripleArray)
    {i j : ℕ} (hij : i < j) :
    markedTreeSum D₁ H i j = markedTreeSum D₂ H i j := by
  rw [markedTreeSum_eq_markedAmplitude D₁ H hij,
    markedTreeSum_eq_markedAmplitude D₂ H hij]
  exact markedAmplitude_near_independent D₁ D₂ H hij

end DirectGLSSW
