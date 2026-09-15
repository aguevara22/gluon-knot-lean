import SM.ConsecutiveTriples
import SM.CriticalFarOccurrence
import SM.PlaneTreeExpansion
import Mathlib.Tactic

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- The two formal triple variables sampled by one actual cut factor.
For a binary composition this is a singleton, not two independent variables. -/
def cutTripleSet (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    Finset (IncreasingBoundaryTriple n) := by
  classical
  exact {π.nearTriple k, π.farTriple k}

theorem mem_cutTripleSet (π : IntervalComposition I) (k : Fin (π.parts - 1))
    (t : IncreasingBoundaryTriple n) :
    t ∈ π.cutTripleSet k ↔ t = π.nearTriple k ∨ t = π.farTriple k := by
  classical
  simp only [cutTripleSet, Finset.mem_insert, Finset.mem_singleton]

/-- Distinct cut indices have different near triples, because their actual
middle cut positions differ under the strict cut map. -/
theorem nearTriple_injective (π : IntervalComposition I) : Function.Injective π.nearTriple := by
  intro k l h
  exact π.interiorPosition_injective (congrArg IncreasingBoundaryTriple.middle h)

/-- Near/far coincidence is exactly the binary case at the same cut.
The endpoint equalities force the first and last indices, not merely a
coincidence of geometric coordinates. -/
theorem nearTriple_eq_farTriple_iff (π : IntervalComposition I)
    (k l : Fin (π.parts - 1)) :
    π.nearTriple k = π.farTriple l ↔ π.parts = 2 ∧ k = l := by
  constructor
  · intro h
    have hl := congrArg IncreasingBoundaryTriple.lower h
    have hu := congrArg IncreasingBoundaryTriple.upper h
    change π.cut ⟨k.val, by have := k.isLt; omega⟩ = I.left at hl
    change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ = I.right at hu
    rw [← π.first] at hl
    rw [← π.last] at hu
    have hli := congrArg Fin.val (π.strict.injective hl)
    have hui := congrArg Fin.val (π.strict.injective hu)
    change k.val = 0 at hli
    change k.val + 2 = π.parts at hui
    refine ⟨by omega, ?_⟩
    exact π.interiorPosition_injective (congrArg IncreasingBoundaryTriple.middle h)
  · rintro ⟨hp, hkl⟩
    subst l
    have hk : k.val = 0 := by have := k.isLt; omega
    apply IncreasingBoundaryTriple.eq_of_entries
    · change π.cut ⟨k.val, by have := k.isLt; omega⟩ = I.left
      have he : (⟨k.val, by have := k.isLt; omega⟩ : Fin (π.parts + 1)) = 0 := by
        apply Fin.ext
        exact hk
      rw [he, π.first]
    · rfl
    · change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ = I.right
      have he : (⟨k.val + 2, by have := k.isLt; omega⟩ : Fin (π.parts + 1)) =
          Fin.last π.parts := by
        apply Fin.ext
        change k.val + 2 = π.parts
        omega
      rw [he, π.last]

/-- Every two distinct factors have disjoint triple-variable supports.
No three-or-more-parts assumption discards the binary or unary cases. -/
theorem cutTripleSet_disjoint (π : IntervalComposition I)
    {k l : Fin (π.parts - 1)} (hkl : k ≠ l) :
    Disjoint (π.cutTripleSet k) (π.cutTripleSet l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t htk htl
  rcases (π.mem_cutTripleSet k t).mp htk with hk | hk
  · rcases (π.mem_cutTripleSet l t).mp htl with hl | hl
    · exact hkl (π.nearTriple_injective (hk.symm.trans hl))
    · exact hkl ((π.nearTriple_eq_farTriple_iff k l).mp (hk.symm.trans hl)).2
  · rcases (π.mem_cutTripleSet l t).mp htl with hl | hl
    · exact hkl (((π.nearTriple_eq_farTriple_iff l k).mp (hl.symm.trans hk)).2.symm)
    · exact hkl (π.farTriple_injective (hk.symm.trans hl))

/-- Every sampled triple lies within its actual parent interval. -/
theorem cutTripleSet_bounds (π : IntervalComposition I) (k : Fin (π.parts - 1))
    {t : IncreasingBoundaryTriple n} (ht : t ∈ π.cutTripleSet k) :
    I.left ≤ t.lower ∧ t.upper ≤ I.right := by
  rcases (π.mem_cutTripleSet k t).mp ht with rfl | rfl
  · constructor
    · change I.left ≤ π.cut ⟨k.val, by have := k.isLt; omega⟩
      rw [← π.first]
      exact π.strict.monotone (Fin.zero_le _)
    · change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ ≤ I.right
      rw [← π.last]
      exact π.strict.monotone (Fin.le_last _)
  · exact ⟨le_rfl, le_rfl⟩

/-- The middle of either sampled triple is a genuine cut position of the
same composition, including when the near and far triples coincide. -/
theorem cutTripleSet_middle_mem (π : IntervalComposition I) (k : Fin (π.parts - 1))
    {t : IncreasingBoundaryTriple n} (ht : t ∈ π.cutTripleSet k) :
    t.middle ∈ π.cutSet.cuts := by
  classical
  have hm : π.interiorPosition k ∈ π.cutSet.cuts := by
    exact Finset.mem_image.mpr
      ⟨⟨k.val + 1, by have := k.isLt; omega⟩, Finset.mem_univ _, rfl⟩
  rcases (π.mem_cutTripleSet k t).mp ht with rfl | rfl
  · exact hm
  · exact hm

/-- A parent cut triple cannot fit inside any one actual child interval.
Such containment would put its middle cut strictly between two consecutive
cuts of that same composition. All endpoint inequalities are explicit. -/
theorem cutTripleSet_not_contained_in_part (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) {t : IncreasingBoundaryTriple n}
    (ht : t ∈ π.cutTripleSet k) (j : Fin π.parts) :
    ¬ ((π.part j).left ≤ t.lower ∧ t.upper ≤ (π.part j).right) := by
  intro h
  have hm := π.cutTripleSet_middle_mem k ht
  have hc := π.part_consecutive j
  exact hc.2.2 t.middle hm
    ⟨lt_of_le_of_lt h.1 t.lower_middle, lt_of_lt_of_le t.middle_upper h.2⟩

/-- An increasing triple can lie in at most one child interval. The possible
shared boundary endpoint between two children cannot contain its two distinct
extreme positions. No cut-membership assumption is imposed on this triple. -/
theorem triple_containing_part_unique (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) {j k : Fin π.parts}
    (hj : (π.part j).left ≤ t.lower ∧ t.upper ≤ (π.part j).right)
    (hk : (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right) : j = k := by
  have ht : t.lower < t.upper := lt_trans t.lower_middle t.middle_upper
  rcases lt_trichotomy j k with h | h | h
  · have ho := π.part_order h
    have he : t.upper ≤ t.lower := le_trans hj.2 (le_trans ho hk.1)
    exact False.elim ((not_le_of_gt ht) he)
  · exact h
  · have ho := π.part_order h
    have he : t.upper ≤ t.lower := le_trans hk.2 (le_trans ho hj.1)
    exact False.elim ((not_le_of_gt ht) he)

end
end SM.IntervalComposition

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
  | _, .node π _ _, Sum.inl k => π.cutTripleSet k
  | _, .node _ _ children, Sum.inr ⟨j, o⟩ => cutTripleSupport (children j) o

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

#check SM.OpenPlaneTree.CutOccurrence
#print axioms SM.OpenPlaneTree.CutOccurrence

#check SM.OpenPlaneTree.cutTripleSupport
#print axioms SM.OpenPlaneTree.cutTripleSupport

#check SM.OpenPlaneTree.cutOccurrence_finite
#print axioms SM.OpenPlaneTree.cutOccurrence_finite

#check SM.OpenPlaneTree.cutOccurrence_fintype
#print axioms SM.OpenPlaneTree.cutOccurrence_fintype

#check SM.OpenPlaneTree.cutTripleSupport_bounds
#print axioms SM.OpenPlaneTree.cutTripleSupport_bounds

#check SM.OpenPlaneTree.tripleSupport
#print axioms SM.OpenPlaneTree.tripleSupport

#check SM.OpenPlaneTree.mem_tripleSupport
#print axioms SM.OpenPlaneTree.mem_tripleSupport

#check SM.OpenPlaneTree.tripleSupport_bounds
#print axioms SM.OpenPlaneTree.tripleSupport_bounds

#check SM.IntervalComposition.cutTripleSet_disjoint_child_support
#print axioms SM.IntervalComposition.cutTripleSet_disjoint_child_support

#check SM.IntervalComposition.children_tripleSupport_disjoint
#print axioms SM.IntervalComposition.children_tripleSupport_disjoint

#check SM.OpenPlaneTree.cutTripleSupport_pairwise
#print axioms SM.OpenPlaneTree.cutTripleSupport_pairwise

#check SM.OpenPlaneTree.cutTripleSupport_nonrepetition
#print axioms SM.OpenPlaneTree.cutTripleSupport_nonrepetition

#check SM.RootedPlaneTree.CutOccurrence
#print axioms SM.RootedPlaneTree.CutOccurrence

#check SM.RootedPlaneTree.cutTripleSupport
#print axioms SM.RootedPlaneTree.cutTripleSupport

#check SM.RootedPlaneTree.cutOccurrence_finite
#print axioms SM.RootedPlaneTree.cutOccurrence_finite

#check SM.RootedPlaneTree.cutOccurrence_fintype
#print axioms SM.RootedPlaneTree.cutOccurrence_fintype

#check SM.RootedPlaneTree.cutTripleSupport_bounds
#print axioms SM.RootedPlaneTree.cutTripleSupport_bounds

#check SM.RootedPlaneTree.cutTripleSupport_pairwise
#print axioms SM.RootedPlaneTree.cutTripleSupport_pairwise

#check SM.RootedPlaneTree.cutTripleSupport_nonrepetition
#print axioms SM.RootedPlaneTree.cutTripleSupport_nonrepetition

#check SM.RootedPlaneTree.tripleSupport
#print axioms SM.RootedPlaneTree.tripleSupport

#check SM.RootedPlaneTree.mem_tripleSupport
#print axioms SM.RootedPlaneTree.mem_tripleSupport

#check SM.RootedPlaneTree.tripleSupport_bounds
#print axioms SM.RootedPlaneTree.tripleSupport_bounds

#check SM.RootedPlaneTree.cutOccurrence_of_unary
#print axioms SM.RootedPlaneTree.cutOccurrence_of_unary
