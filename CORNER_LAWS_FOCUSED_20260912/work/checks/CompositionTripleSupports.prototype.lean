import SM.ConsecutiveTriples
import SM.CriticalFarOccurrence
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

#check SM.IntervalComposition.cutTripleSet
#print axioms SM.IntervalComposition.cutTripleSet

#check SM.IntervalComposition.mem_cutTripleSet
#print axioms SM.IntervalComposition.mem_cutTripleSet

#check SM.IntervalComposition.nearTriple_injective
#print axioms SM.IntervalComposition.nearTriple_injective

#check SM.IntervalComposition.nearTriple_eq_farTriple_iff
#print axioms SM.IntervalComposition.nearTriple_eq_farTriple_iff

#check SM.IntervalComposition.cutTripleSet_disjoint
#print axioms SM.IntervalComposition.cutTripleSet_disjoint

#check SM.IntervalComposition.cutTripleSet_bounds
#print axioms SM.IntervalComposition.cutTripleSet_bounds

#check SM.IntervalComposition.cutTripleSet_middle_mem
#print axioms SM.IntervalComposition.cutTripleSet_middle_mem

#check SM.IntervalComposition.cutTripleSet_not_contained_in_part
#print axioms SM.IntervalComposition.cutTripleSet_not_contained_in_part

#check SM.IntervalComposition.triple_containing_part_unique
#print axioms SM.IntervalComposition.triple_containing_part_unique
