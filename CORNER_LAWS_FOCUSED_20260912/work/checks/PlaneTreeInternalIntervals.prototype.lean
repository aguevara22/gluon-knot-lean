import SM.PlaneTreeShape
import SM.ConsecutiveCuts
import SM.UnaryComposition
import Mathlib.Tactic

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace OpenPlaneTree

/-- All actual ordinary internal nodes, including binary nodes with zero
eventual weight. A node is located by its ordered child choices. -/
def InternalOccurrence : {I : BoundaryInterval n} → OpenPlaneTree I → Type
  | _, .leaf _ => PEmpty
  | _, .node π _ children =>
      Unit ⊕ (Σ j : Fin π.parts, InternalOccurrence (children j))

def internalInterval : {I : BoundaryInterval n} → (T : OpenPlaneTree I) →
    T.InternalOccurrence → BoundaryInterval n
  | _, .leaf _, o => nomatch o
  | I, .node π _ children, o =>
      match o with
      | Sum.inl _ => I
      | Sum.inr ⟨j, o⟩ => internalInterval (children j) o

/-- A structural constructor test for the actual top node; this predicate
is not defined by equality of leaf intervals. -/
def IsTopInternal : {I : BoundaryInterval n} → (T : OpenPlaneTree I) →
    T.InternalOccurrence → Prop
  | _, .leaf _, o => nomatch o
  | _, .node π _ children, o =>
      match o with
      | Sum.inl _ => True
      | Sum.inr _ => False

theorem internalInterval_bounds {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    ∀ o : T.InternalOccurrence,
      I.left ≤ (T.internalInterval o).left ∧ (T.internalInterval o).right ≤ I.right := by
  induction T with
  | leaf hI =>
      intro o
      exact PEmpty.elim o
  | node π hp children ih =>
      intro o
      rcases o with u | ⟨j, o⟩
      · exact ⟨le_rfl, le_rfl⟩
      · have hb := ih j o
        have hp := π.part_bounds j
        exact ⟨le_trans hp.1 hb.1, le_trans hb.2 hp.2⟩

theorem internalInterval_leaves_le {I : BoundaryInterval n} (T : OpenPlaneTree I)
    (o : T.InternalOccurrence) : (T.internalInterval o).leaves ≤ I.leaves := by
  have hb := T.internalInterval_bounds o
  have hl : I.left.val ≤ (T.internalInterval o).left.val := hb.1
  have hr : (T.internalInterval o).right.val ≤ I.right.val := hb.2
  unfold BoundaryInterval.leaves
  omega

end OpenPlaneTree

namespace IntervalComposition

/-- Every actual node anywhere in a child of a nonunary composition has a
strictly smaller leaf interval than the parent composition. -/
theorem child_internalInterval_leaves_lt {I : BoundaryInterval n}
    (π : IntervalComposition I) (hp : 2 ≤ π.parts)
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j))
    (j : Fin π.parts) (o : (children j).InternalOccurrence) :
    ((children j).internalInterval o).leaves < I.leaves :=
  lt_of_le_of_lt ((children j).internalInterval_leaves_le o) (π.part_leaves_lt hp j)

/-- The actual sole child interval of any unary composition is exactly its
parent interval, proved from the complete cut data. -/
theorem part_eq_parent_of_unary {I : BoundaryInterval n} (π : IntervalComposition I)
    (hp : π.parts = 1) (j : Fin π.parts) : π.part j = I := by
  have he := π.eq_single_of_parts_eq_one hp
  subst π
  exact single_part I j

end IntervalComposition

namespace OpenPlaneTree

/-- A proper descendant of an actual ordinary top node has strictly fewer
leaves. Ordinary nodes have at least two children by the tree constructor. -/
theorem internalInterval_leaves_lt_of_not_top {I : BoundaryInterval n}
    (T : OpenPlaneTree I) (o : T.InternalOccurrence) (ho : ¬ T.IsTopInternal o) :
    (T.internalInterval o).leaves < I.leaves := by
  cases T with
  | leaf hI => exact PEmpty.elim o
  | node π hp children =>
      rcases o with u | ⟨j, o⟩
      · exact (ho trivial).elim
      · exact π.child_internalInterval_leaves_lt hp children j o

/-- Equality with the parent interval characterizes the actual top internal
node, rather than serving as its definition. -/
theorem internalInterval_eq_parent_iff_top {I : BoundaryInterval n}
    (T : OpenPlaneTree I) (o : T.InternalOccurrence) :
    T.internalInterval o = I ↔ T.IsTopInternal o := by
  classical
  constructor
  · intro he
    by_contra ho
    have hs := T.internalInterval_leaves_lt_of_not_top o ho
    rw [he] at hs
    exact lt_irrefl _ hs
  · intro ho
    cases T with
    | leaf hI => exact PEmpty.elim o
    | node π hp children =>
        rcases o with u | ⟨j, o⟩
        · rfl
        · exact ho.elim

/-- Distinct actual ordinary internal nodes have different leaf intervals.
Sibling separation uses the whole positive-length interval and actual part
order; no identification of occurrences by intervals is assumed. -/
theorem internalInterval_injective {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    Function.Injective T.internalInterval := by
  induction T with
  | leaf hI =>
      intro a
      exact PEmpty.elim a
  | node π hp children ih =>
      intro a b he
      rcases a with u | ⟨j, a⟩
      · rcases b with v | ⟨j, b⟩
        · cases u
          cases v
          rfl
        · change _ = (children j).internalInterval b at he
          have hs := π.child_internalInterval_leaves_lt hp children j b
          rw [← he] at hs
          exact (lt_irrefl _ hs).elim
      · rcases b with u | ⟨k, b⟩
        · change (children j).internalInterval a = _ at he
          have hs := π.child_internalInterval_leaves_lt hp children j a
          rw [he] at hs
          exact (lt_irrefl _ hs).elim
        · have hb : (π.part k).left ≤ ((children j).internalInterval a).left ∧
              ((children j).internalInterval a).right ≤ (π.part k).right := by
            change (children j).internalInterval a = (children k).internalInterval b at he
            rw [he]
            exact (children k).internalInterval_bounds b
          have hjk := π.containing_part_unique ((children j).internalInterval a)
            ((children j).internalInterval_bounds a) hb
          subst k
          have hab := ih j he
          cases hab
          rfl

end OpenPlaneTree

namespace RootedPlaneTree

/-- Actual internal nodes of the rooted tree, including the distinguished
root even when its cut-factor product is empty. -/
def InternalOccurrence {I : BoundaryInterval n} (T : RootedPlaneTree I) : Type :=
  Unit ⊕ (Σ j : Fin T.fst.parts, (T.snd j).InternalOccurrence)

def internalInterval {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.InternalOccurrence → BoundaryInterval n
  | Sum.inl _ => I
  | Sum.inr ⟨j, o⟩ => (T.snd j).internalInterval o

def rootOccurrence {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.InternalOccurrence := Sum.inl ()

/-- Structural immediate-child test: choose one root child and then that
ordinary tree's actual top internal-node constructor. -/
def IsImmediateChild {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.InternalOccurrence → Prop
  | Sum.inl _ => False
  | Sum.inr ⟨j, o⟩ => (T.snd j).IsTopInternal o

theorem internalInterval_bounds {I : BoundaryInterval n} (T : RootedPlaneTree I)
    (o : T.InternalOccurrence) :
    I.left ≤ (T.internalInterval o).left ∧ (T.internalInterval o).right ≤ I.right := by
  rcases o with u | ⟨j, o⟩
  · exact ⟨le_rfl, le_rfl⟩
  · have hb := (T.snd j).internalInterval_bounds o
    have hp := T.fst.part_bounds j
    exact ⟨le_trans hp.1 hb.1, le_trans hb.2 hp.2⟩

/-- Among all actual ordinary nodes below the root, interval equality
forces both the same root-child index and the same internal occurrence. -/
theorem childInternalInterval_injective {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    Function.Injective (fun o : (Σ j : Fin T.fst.parts, (T.snd j).InternalOccurrence) =>
      (T.snd o.fst).internalInterval o.snd) := by
  rintro ⟨j, a⟩ ⟨k, b⟩ he
  change (T.snd j).internalInterval a = (T.snd k).internalInterval b at he
  have hb : (T.fst.part k).left ≤ ((T.snd j).internalInterval a).left ∧
      ((T.snd j).internalInterval a).right ≤ (T.fst.part k).right := by
    rw [he]
    exact (T.snd k).internalInterval_bounds b
  have hjk := T.fst.containing_part_unique ((T.snd j).internalInterval a)
    ((T.snd j).internalInterval_bounds a) hb
  subst k
  have hab := (T.snd j).internalInterval_injective he
  cases hab
  rfl

/-- A node below the root has the root's interval exactly when the root is
unary and that occurrence is the top of its immediate ordinary child. -/
theorem child_internalInterval_eq_root_iff {I : BoundaryInterval n} (T : RootedPlaneTree I)
    (j : Fin T.fst.parts) (o : (T.snd j).InternalOccurrence) :
    (T.snd j).internalInterval o = I ↔
      T.fst.parts = 1 ∧ (T.snd j).IsTopInternal o := by
  constructor
  · intro he
    have hp : T.fst.parts = 1 := by
      by_contra hn
      have hm : 2 ≤ T.fst.parts := by have := T.fst.parts_pos; omega
      have hs := T.fst.child_internalInterval_leaves_lt hm T.snd j o
      rw [he] at hs
      exact lt_irrefl _ hs
    have hpart := T.fst.part_eq_parent_of_unary hp j
    exact ⟨hp, ((T.snd j).internalInterval_eq_parent_iff_top o).mp (he.trans hpart.symm)⟩
  · rintro ⟨hp, ho⟩
    exact (((T.snd j).internalInterval_eq_parent_iff_top o).mpr ho).trans
      (T.fst.part_eq_parent_of_unary hp j)

/-- The complete source shared-interval exception for distinct actual
internal vertices: they are the unary root and its immediate sole child,
in either order. Ordinary internal vertices are never silently removed. -/
theorem internalInterval_eq_of_distinct {I : BoundaryInterval n} (T : RootedPlaneTree I)
    {a b : T.InternalOccurrence} (hab : a ≠ b)
    (he : T.internalInterval a = T.internalInterval b) :
    T.fst.parts = 1 ∧
      ((a = T.rootOccurrence ∧ T.IsImmediateChild b) ∨
        (b = T.rootOccurrence ∧ T.IsImmediateChild a)) := by
  rcases a with u | ⟨j, a⟩
  · rcases b with v | ⟨j, b⟩
    · cases u
      cases v
      exact (hab rfl).elim
    · cases u
      have h := (T.child_internalInterval_eq_root_iff j b).mp he.symm
      exact ⟨h.1, Or.inl ⟨rfl, h.2⟩⟩
  · rcases b with u | ⟨k, b⟩
    · cases u
      have h := (T.child_internalInterval_eq_root_iff j a).mp he
      exact ⟨h.1, Or.inr ⟨rfl, h.2⟩⟩
    · apply False.elim
      apply hab
      exact congrArg Sum.inr (T.childInternalInterval_injective he)

/-- Every possible factor assignment has empty product at a unary root;
this is independent of any later gate or polynomial evaluation. -/
theorem unary_cut_product {I : BoundaryInterval n} (T : RootedPlaneTree I)
    (hp : T.fst.parts = 1) {R : Type*} [CommMonoid R]
    (f : Fin (T.fst.parts - 1) → R) : (∏ k, f k) = 1 := by
  haveI : IsEmpty (Fin (T.fst.parts - 1)) := ⟨fun k => by have := k.isLt; omega⟩
  simp

end RootedPlaneTree

end
end SM

#check SM.OpenPlaneTree.InternalOccurrence
#print axioms SM.OpenPlaneTree.InternalOccurrence

#check SM.OpenPlaneTree.internalInterval
#print axioms SM.OpenPlaneTree.internalInterval

#check SM.OpenPlaneTree.IsTopInternal
#print axioms SM.OpenPlaneTree.IsTopInternal

#check SM.OpenPlaneTree.internalInterval_bounds
#print axioms SM.OpenPlaneTree.internalInterval_bounds

#check SM.OpenPlaneTree.internalInterval_leaves_le
#print axioms SM.OpenPlaneTree.internalInterval_leaves_le

#check SM.IntervalComposition.child_internalInterval_leaves_lt
#print axioms SM.IntervalComposition.child_internalInterval_leaves_lt

#check SM.IntervalComposition.part_eq_parent_of_unary
#print axioms SM.IntervalComposition.part_eq_parent_of_unary

#check SM.OpenPlaneTree.internalInterval_leaves_lt_of_not_top
#print axioms SM.OpenPlaneTree.internalInterval_leaves_lt_of_not_top

#check SM.OpenPlaneTree.internalInterval_eq_parent_iff_top
#print axioms SM.OpenPlaneTree.internalInterval_eq_parent_iff_top

#check SM.OpenPlaneTree.internalInterval_injective
#print axioms SM.OpenPlaneTree.internalInterval_injective

#check SM.RootedPlaneTree.InternalOccurrence
#print axioms SM.RootedPlaneTree.InternalOccurrence

#check SM.RootedPlaneTree.internalInterval
#print axioms SM.RootedPlaneTree.internalInterval

#check SM.RootedPlaneTree.rootOccurrence
#print axioms SM.RootedPlaneTree.rootOccurrence

#check SM.RootedPlaneTree.IsImmediateChild
#print axioms SM.RootedPlaneTree.IsImmediateChild

#check SM.RootedPlaneTree.internalInterval_bounds
#print axioms SM.RootedPlaneTree.internalInterval_bounds

#check SM.RootedPlaneTree.childInternalInterval_injective
#print axioms SM.RootedPlaneTree.childInternalInterval_injective

#check SM.RootedPlaneTree.child_internalInterval_eq_root_iff
#print axioms SM.RootedPlaneTree.child_internalInterval_eq_root_iff

#check SM.RootedPlaneTree.internalInterval_eq_of_distinct
#print axioms SM.RootedPlaneTree.internalInterval_eq_of_distinct

#check SM.RootedPlaneTree.unary_cut_product
#print axioms SM.RootedPlaneTree.unary_cut_product
