namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace OpenPlaneTree

/-- A factor occurrence records its actual node by the successive child
choices, and then its cut index. Leaves carry no cut factor. -/
def CutOccurrence : {I : BoundaryInterval n} → OpenPlaneTree I → Type
  | _, .leaf _ => PEmpty
  | _, .node π _ children =>
      Fin (π.parts - 1) ⊕ (Σ j : Fin π.parts, CutOccurrence (children j))

/-- The two actual increasing triples sampled by the factor at this
occurrence. Their possible binary coincidence stays inside this one support. -/
def cutTripleSupport : {I : BoundaryInterval n} → (T : OpenPlaneTree I) →
    T.CutOccurrence → Finset (IncreasingBoundaryTriple n)
  | _, .leaf _, o => nomatch o
  | _, .node π _ children, o =>
      match o with
      | Sum.inl k => π.cutTripleSet k
      | Sum.inr ⟨j, o⟩ => cutTripleSupport (children j) o

instance cutOccurrence_finite {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    Finite T.CutOccurrence := by
  induction T with
  | leaf hI =>
      change Finite PEmpty
      infer_instance
  | node π hp children ih =>
      letI childFinite (j : Fin π.parts) : Finite (children j).CutOccurrence := ih j
      change Finite (Fin (π.parts - 1) ⊕ (Σ j : Fin π.parts, (children j).CutOccurrence))
      infer_instance

noncomputable instance cutOccurrence_fintype {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    Fintype T.CutOccurrence := Fintype.ofFinite _

/-- Every occurrence, including one arbitrarily deep in the actual tree,
uses triples whose extreme positions lie in the tree's own leaf interval. -/
theorem cutTripleSupport_bounds {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    ∀ (o : T.CutOccurrence) {t : IncreasingBoundaryTriple n},
      t ∈ T.cutTripleSupport o → I.left ≤ t.lower ∧ t.upper ≤ I.right := by
  induction T with
  | leaf hI =>
      intro o
      exact PEmpty.elim o
  | node π hp children ih =>
      intro o t ht
      rcases o with k | ⟨j, o⟩
      · exact π.cutTripleSet_bounds k ht
      · have hb := ih j o ht
        have hp := π.part_bounds j
        exact ⟨le_trans hp.1 hb.1, le_trans hb.2 hp.2⟩

/-- The finite support of all factors of this actual ordinary tree. -/
def tripleSupport {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    Finset (IncreasingBoundaryTriple n) := by
  classical
  exact Finset.univ.biUnion T.cutTripleSupport

theorem mem_tripleSupport {I : BoundaryInterval n} (T : OpenPlaneTree I)
    (t : IncreasingBoundaryTriple n) :
    t ∈ T.tripleSupport ↔ ∃ o : T.CutOccurrence, t ∈ T.cutTripleSupport o := by
  classical
  simp [tripleSupport]

theorem tripleSupport_bounds {I : BoundaryInterval n} (T : OpenPlaneTree I)
    {t : IncreasingBoundaryTriple n} (ht : t ∈ T.tripleSupport) :
    I.left ≤ t.lower ∧ t.upper ≤ I.right := by
  obtain ⟨o, ho⟩ := (T.mem_tripleSupport t).mp ht
  exact T.cutTripleSupport_bounds o ho

end OpenPlaneTree

namespace IntervalComposition

/-- A top cut factor is disjoint from the entire support of each actual
child tree. This also applies at an unrestricted distinguished root. -/
theorem cutTripleSet_disjoint_child_support {I : BoundaryInterval n}
    (π : IntervalComposition I) (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j))
    (k : Fin (π.parts - 1)) (j : Fin π.parts) :
    Disjoint (π.cutTripleSet k) (children j).tripleSupport := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hu
  exact π.cutTripleSet_not_contained_in_part k ht j ((children j).tripleSupport_bounds hu)

/-- Entire actual subtrees in distinct children have disjoint triple
supports; shared boundary endpoints do not contain an increasing triple. -/
theorem children_tripleSupport_disjoint {I : BoundaryInterval n}
    (π : IntervalComposition I) (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j))
    {j k : Fin π.parts} (hjk : j ≠ k) :
    Disjoint (children j).tripleSupport (children k).tripleSupport := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hu
  exact hjk (π.triple_containing_part_unique t
    ((children j).tripleSupport_bounds ht) ((children k).tripleSupport_bounds hu))

end IntervalComposition

namespace OpenPlaneTree

/-- Distinct actual node-and-cut occurrences use disjoint triple supports.
The proof separates top/top, top/descendant, and the two sibling cases. -/
theorem cutTripleSupport_pairwise {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    Pairwise (fun a b : T.CutOccurrence =>
      Disjoint (T.cutTripleSupport a) (T.cutTripleSupport b)) := by
  induction T with
  | leaf hI =>
      intro a
      exact PEmpty.elim a
  | node π hp children ih =>
      intro a b hab
      rcases a with k | ⟨j, a⟩
      · rcases b with l | ⟨j, b⟩
        · exact π.cutTripleSet_disjoint (fun h => hab (congrArg Sum.inl h))
        · apply Finset.disjoint_left.mpr
          intro t ht hu
          exact π.cutTripleSet_not_contained_in_part k ht j
            ((children j).cutTripleSupport_bounds b hu)
      · rcases b with k | ⟨l, b⟩
        · apply Finset.disjoint_left.mpr
          intro t ht hu
          exact π.cutTripleSet_not_contained_in_part k hu j
            ((children j).cutTripleSupport_bounds a ht)
        · by_cases hjl : j = l
          · subst l
            have hab' : a ≠ b := by
              intro he
              apply hab
              cases he
              rfl
            exact ih j hab'
          · apply Finset.disjoint_left.mpr
            intro t ht hu
            exact hjl (π.triple_containing_part_unique t
              ((children j).cutTripleSupport_bounds a ht)
              ((children l).cutTripleSupport_bounds b hu))

/-- A triple occurring anywhere in two factors of an ordinary tree forces
the same actual node-and-cut occurrence, not merely the same interval. -/
theorem cutTripleSupport_nonrepetition {I : BoundaryInterval n} (T : OpenPlaneTree I)
    {a b : T.CutOccurrence} {t : IncreasingBoundaryTriple n}
    (ha : t ∈ T.cutTripleSupport a) (hb : t ∈ T.cutTripleSupport b) : a = b := by
  classical
  by_contra h
  exact (Finset.disjoint_left.mp (T.cutTripleSupport_pairwise h)) ha hb

end OpenPlaneTree

namespace RootedPlaneTree

/-- The distinguished root's own cut indices and all actual ordinary-child
occurrences. The root composition is unrestricted, including one child. -/
def CutOccurrence {I : BoundaryInterval n} (T : RootedPlaneTree I) : Type :=
  Fin (T.fst.parts - 1) ⊕ (Σ j : Fin T.fst.parts, (T.snd j).CutOccurrence)

def cutTripleSupport {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.CutOccurrence → Finset (IncreasingBoundaryTriple n)
  | Sum.inl k => T.fst.cutTripleSet k
  | Sum.inr ⟨j, o⟩ => (T.snd j).cutTripleSupport o

instance cutOccurrence_finite {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    Finite T.CutOccurrence := by
  unfold CutOccurrence
  infer_instance

noncomputable instance cutOccurrence_fintype {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    Fintype T.CutOccurrence := Fintype.ofFinite _

/-- The same complete endpoint bound holds for the actual distinguished
root and every factor arbitrarily deep in its ordinary children. -/
theorem cutTripleSupport_bounds {I : BoundaryInterval n} (T : RootedPlaneTree I)
    (o : T.CutOccurrence) {t : IncreasingBoundaryTriple n}
    (ht : t ∈ T.cutTripleSupport o) : I.left ≤ t.lower ∧ t.upper ≤ I.right := by
  rcases o with k | ⟨j, o⟩
  · exact T.fst.cutTripleSet_bounds k ht
  · have hb := (T.snd j).cutTripleSupport_bounds o ht
    have hp := T.fst.part_bounds j
    exact ⟨le_trans hp.1 hb.1, le_trans hb.2 hp.2⟩

/-- All root and ordinary factors of one actual rooted tree have pairwise
disjoint supports, with no assumption that its root has at least two children. -/
theorem cutTripleSupport_pairwise {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    Pairwise (fun a b : T.CutOccurrence =>
      Disjoint (T.cutTripleSupport a) (T.cutTripleSupport b)) := by
  intro a b hab
  rcases a with k | ⟨j, a⟩
  · rcases b with l | ⟨j, b⟩
    · exact T.fst.cutTripleSet_disjoint (fun h => hab (congrArg Sum.inl h))
    · apply Finset.disjoint_left.mpr
      intro t ht hu
      exact T.fst.cutTripleSet_not_contained_in_part k ht j
        ((T.snd j).cutTripleSupport_bounds b hu)
  · rcases b with k | ⟨l, b⟩
    · apply Finset.disjoint_left.mpr
      intro t ht hu
      exact T.fst.cutTripleSet_not_contained_in_part k hu j
        ((T.snd j).cutTripleSupport_bounds a ht)
    · by_cases hjl : j = l
      · subst l
        have hab' : a ≠ b := by
          intro he
          apply hab
          cases he
          rfl
        exact (T.snd j).cutTripleSupport_pairwise hab'
      · apply Finset.disjoint_left.mpr
        intro t ht hu
        exact hjl (T.fst.triple_containing_part_unique t
          ((T.snd j).cutTripleSupport_bounds a ht)
          ((T.snd l).cutTripleSupport_bounds b hu))

/-- The tree-level source nonrepetition statement: every increasing triple
belongs to at most one actual node-and-cut factor of a rooted plane tree. -/
theorem cutTripleSupport_nonrepetition {I : BoundaryInterval n} (T : RootedPlaneTree I)
    {a b : T.CutOccurrence} {t : IncreasingBoundaryTriple n}
    (ha : t ∈ T.cutTripleSupport a) (hb : t ∈ T.cutTripleSupport b) : a = b := by
  classical
  by_contra h
  exact (Finset.disjoint_left.mp (T.cutTripleSupport_pairwise h)) ha hb

def tripleSupport {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    Finset (IncreasingBoundaryTriple n) := by
  classical
  exact Finset.univ.biUnion T.cutTripleSupport

theorem mem_tripleSupport {I : BoundaryInterval n} (T : RootedPlaneTree I)
    (t : IncreasingBoundaryTriple n) :
    t ∈ T.tripleSupport ↔ ∃ o : T.CutOccurrence, t ∈ T.cutTripleSupport o := by
  classical
  simp [tripleSupport]

theorem tripleSupport_bounds {I : BoundaryInterval n} (T : RootedPlaneTree I)
    {t : IncreasingBoundaryTriple n} (ht : t ∈ T.tripleSupport) :
    I.left ≤ t.lower ∧ t.upper ≤ I.right := by
  obtain ⟨o, ho⟩ := (T.mem_tripleSupport t).mp ht
  exact T.cutTripleSupport_bounds o ho

/-- A unary root has no top cut factor at all. Every factor occurrence is
in its actual child, so equality of root and child intervals cannot duplicate
a variable. No ordinary binary vertex is discarded by this assertion. -/
theorem cutOccurrence_of_unary {I : BoundaryInterval n} (T : RootedPlaneTree I)
    (hp : T.fst.parts = 1) (o : T.CutOccurrence) :
    ∃ j : Fin T.fst.parts, ∃ c : (T.snd j).CutOccurrence, o = Sum.inr ⟨j, c⟩ := by
  rcases o with k | ⟨j, o⟩
  · have hk := k.isLt
    omega
  · exact ⟨j, o, rfl⟩

end RootedPlaneTree

end
end SM
