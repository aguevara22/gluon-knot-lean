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
