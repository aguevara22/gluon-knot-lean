import DirectGLSSW.CutRefinement
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

/-!
# Independently defined finite ordinary interval trees

Source: `ep:tree-recursion`. A leaf spans one elementary interval. An
ordinary internal node selects a nonempty set of interior cuts and has
one child on each consecutive gap. Its interval labels retain the planar
order; no ordinary unary insertion is available. This type is independent
of the array current and of any choice of vertex weights.

The decomposition equivalence records the two constructors explicitly.
Finiteness follows from strict decrease of the children's interval lengths.
These declarations are provisional pending independent fidelity review.
-/

namespace DirectGLSSW

/-- The allowed shapes of an ordinary internal node exclude the empty cut set. -/
abbrev NonUnaryCutSet (i j : ℕ) := ↥((Finset.Ioo i j).powerset.erase ∅)

theorem nonUnaryCutSet_subset {i j : ℕ} (S : NonUnaryCutSet i j) :
    S.val ⊆ Finset.Ioo i j :=
  Finset.mem_powerset.mp (Finset.mem_erase.mp S.property).2

theorem nonUnaryCutSet_nonempty {i j : ℕ} (S : NonUnaryCutSet i j) :
    S.val.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp S.property).1

theorem nonUnaryCutSet_lt {i j : ℕ} (S : NonUnaryCutSet i j) : i < j := by
  obtain ⟨k, hk⟩ := nonUnaryCutSet_nonempty S
  have hk' := Finset.mem_Ioo.mp (nonUnaryCutSet_subset S hk)
  omega

/-- A concrete ordered tree, with a leaf on each elementary interval and
nonunary ordinary nodes only. -/
inductive OrdinaryTree : ℕ → ℕ → Type
  | leaf (i : ℕ) : OrdinaryTree i (i + 1)
  | node {i j : ℕ} (S : NonUnaryCutSet i j)
      (children : ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2) :
      OrdinaryTree i j

/-- Read the root constructor, retaining the full dependent child family. -/
def ordinaryTreeDecompose {i j : ℕ} (t : OrdinaryTree i j) :
    PLift (j = i + 1) ⊕
      (Σ S : NonUnaryCutSet i j,
        ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2) :=
  match t with
  | .leaf _ => Sum.inl ⟨rfl⟩
  | .node S children => Sum.inr ⟨S, children⟩

/-- Build the root and its actual children from the constructor data. -/
def ordinaryTreeAssemble {i j : ℕ}
    (r : PLift (j = i + 1) ⊕
      (Σ S : NonUnaryCutSet i j,
        ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2)) :
    OrdinaryTree i j :=
  match r with
  | Sum.inl h => h.down ▸ OrdinaryTree.leaf i
  | Sum.inr ⟨S, children⟩ => OrdinaryTree.node S children

theorem ordinaryTreeAssemble_decompose {i j : ℕ} (t : OrdinaryTree i j) :
    ordinaryTreeAssemble (ordinaryTreeDecompose t) = t := by
  cases t <;> rfl

theorem ordinaryTreeDecompose_assemble {i j : ℕ}
    (r : PLift (j = i + 1) ⊕
      (Σ S : NonUnaryCutSet i j,
        ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2)) :
    ordinaryTreeDecompose (ordinaryTreeAssemble r) = r := by
  rcases r with ⟨h⟩ | ⟨S, children⟩
  · rcases h with ⟨h⟩
    subst j
    rfl
  · rfl

/-- Exactly the leaf alternative and all nonunary node shapes with their
children. Both inverse proofs are separate opaque theorems. -/
def ordinaryTreeEquiv (i j : ℕ) :
    OrdinaryTree i j ≃ PLift (j = i + 1) ⊕
      (Σ S : NonUnaryCutSet i j,
        ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2) where
  toFun := ordinaryTreeDecompose
  invFun := ordinaryTreeAssemble
  left_inv := ordinaryTreeAssemble_decompose
  right_inv := ordinaryTreeDecompose_assemble

/-- Every recursive child has smaller interval length. -/
theorem nonUnaryCutSet_gap_lt {i j : ℕ} (S : NonUnaryCutSet i j)
    (e : CutGap i j S.val) : e.val.2 - e.val.1 < j - i := by
  have hmem : e.val ∈ (cutVertices i j S.val).zip (cutVertices i j S.val).tail := by
    simpa only [cutEdges, List.mem_toFinset] using e.property
  exact (cutVertices_branch_bounds (nonUnaryCutSet_lt S)
    (nonUnaryCutSet_subset S) (nonUnaryCutSet_nonempty S) hmem).2.2.2

/-- Ordinary trees on any fixed interval form a finite type, by induction
on interval length and the proved strict decrease at every internal node. -/
theorem ordinaryTree_finite (i j : ℕ) : Finite (OrdinaryTree i j) := by
  classical
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      haveI childFinite (S : NonUnaryCutSet i j) (e : CutGap i j S.val) :
          Finite (OrdinaryTree e.val.1 e.val.2) :=
        ih (e.val.2 - e.val.1) (by simpa only [hn] using nonUnaryCutSet_gap_lt S e)
          e.val.1 e.val.2 rfl
      haveI childFintype (S : NonUnaryCutSet i j) (e : CutGap i j S.val) :
          Fintype (OrdinaryTree e.val.1 e.val.2) := Fintype.ofFinite _
      exact Finite.of_equiv
        (PLift (j = i + 1) ⊕
          (Σ S : NonUnaryCutSet i j,
            ∀ e : CutGap i j S.val, OrdinaryTree e.val.1 e.val.2))
        (ordinaryTreeEquiv i j).symm

noncomputable instance ordinaryTreeFintype (i j : ℕ) : Fintype (OrdinaryTree i j) :=
  @Fintype.ofFinite _ (ordinaryTree_finite i j)

end DirectGLSSW
