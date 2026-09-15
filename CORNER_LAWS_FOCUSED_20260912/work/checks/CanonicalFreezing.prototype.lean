import SM.Farout
import Mathlib.Algebra.MvPolynomial.Invertible
import SM.PlaneTreeFormal
import SM.ConsecutiveTriples
import SM.CriticalFarOccurrence
import Mathlib.Algebra.MvPolynomial.Eval
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import Mathlib.Tactic

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IncreasingBoundaryTriple

def positionSet (t : IncreasingBoundaryTriple n) : Finset (Fin n) :=
  {t.lower, t.middle, t.upper}

theorem positionSet_bounds (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ∈ t.positionSet) : t.lower ≤ x ∧ x ≤ t.upper := by
  simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨le_rfl, le_of_lt (lt_trans t.lower_middle t.middle_upper)⟩
  · exact ⟨le_of_lt t.lower_middle, le_of_lt t.middle_upper⟩
  · exact ⟨le_of_lt (lt_trans t.lower_middle t.middle_upper), le_rfl⟩

/-- The unordered position set determines the increasing triple. Min/max
fix both endpoints, and the distinct remaining position fixes the middle. -/
theorem positionSet_injective : Function.Injective (positionSet (n := n)) := by
  intro t u he
  have hl : t.lower = u.lower := by
    apply le_antisymm
    · exact (t.positionSet_bounds u.lower (by rw [he]; simp [positionSet])).1
    · exact (u.positionSet_bounds t.lower (by rw [← he]; simp [positionSet])).1
  have hr : t.upper = u.upper := by
    apply le_antisymm
    · exact (u.positionSet_bounds t.upper (by rw [← he]; simp [positionSet])).2
    · exact (t.positionSet_bounds u.upper (by rw [he]; simp [positionSet])).2
  have hm : t.middle = u.middle := by
    have hx : t.middle ∈ u.positionSet := by rw [← he]; simp [positionSet]
    simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ((ne_of_gt t.lower_middle) (h.trans hl.symm)).elim
    · exact h
    · exact ((ne_of_lt t.middle_upper) (h.trans hr.symm)).elim
  exact eq_of_entries hl hm hr

/-- The actual unordered source vertex support in the chosen root reading. -/
def vertexSet (g : ZMod n) (t : IncreasingBoundaryTriple n) : Finset (ZMod n) :=
  t.positionSet.image (boundaryIndex g)

theorem vertexSet_injective (g : ZMod n) : Function.Injective (vertexSet g) := by
  intro t u he
  apply positionSet_injective
  exact Finset.image_injective (boundaryIndex_injective g) he

theorem vertexSet_reversed (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    t.vertexSet g = {boundaryIndex g t.upper, boundaryIndex g t.middle, boundaryIndex g t.lower} := by
  ext x
  simp [vertexSet, positionSet, or_comm, or_left_comm, or_assoc]

end IncreasingBoundaryTriple

/-- Unique zero support implies every other increasing boundary triple has
a nonzero determinant sign. This uses label injectivity of the root reading,
without inferring geometric vertex distinctness from singleton Zpt at n=3. -/
theorem boundary_chi_nonzero_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g})
    (u : IncreasingBoundaryTriple n) (hu : u ≠ t) :
    chi P (boundaryIndex g u.upper) (boundaryIndex g u.middle) (boundaryIndex g u.lower) ≠ 0 := by
  apply chi_nonzero_outside_singleton hP
  · exact fun h => (ne_of_gt u.middle_upper) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt u.lower_middle) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt (lt_trans u.lower_middle u.middle_upper)) (boundaryIndex_injective g h)
  · intro he
    have hs : u.vertexSet g = t.vertexSet g := (u.vertexSet_reversed g).trans he
    exact hu (IncreasingBoundaryTriple.vertexSet_injective g hs)

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Position in the source's increasing physical label order 1,...,n.
The source label n is represented by residue zero, and has position n-1. -/
def canonicalPosition (i : ZMod n) : Fin n := ⟨(i - 1).val, ZMod.val_lt _⟩

theorem canonical_label (k : Fin n) :
    boundaryIndex 0 k = ((k.val + 1 : ℕ) : ZMod n) := by
  simp [boundaryIndex]

theorem canonical_label_range (k : Fin n) : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ n := by
  have := k.isLt
  omega

@[simp] theorem boundaryIndex_canonicalPosition (i : ZMod n) :
    boundaryIndex 0 (canonicalPosition i) = i := by
  change 0 + ((i - 1).val : ZMod n) + 1 = i
  rw [ZMod.natCast_zmod_val]
  ring

@[simp] theorem canonicalPosition_boundaryIndex (k : Fin n) :
    canonicalPosition (boundaryIndex 0 k) = k := by
  apply boundaryIndex_injective 0
  exact boundaryIndex_canonicalPosition _

theorem canonicalPosition_injective : Function.Injective (canonicalPosition (n := n)) := by
  intro i j h
  have he := congrArg (boundaryIndex 0) h
  simpa only [boundaryIndex_canonicalPosition] using he

/-- Exact six-order sorting with parity, before any polynomial relations.
The three positions must be distinct; repeated ordered labels will be zero. -/
def sortTriplePositions (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IncreasingBoundaryTriple n × ℚ :=
  if hab' : a < b then
    if hbc' : b < c then (⟨a, b, c, hab', hbc'⟩, 1)
    else
      have hcb : c < b := lt_of_le_of_ne (le_of_not_gt hbc') hbc.symm
      if hac' : a < c then (⟨a, c, b, hac', hcb⟩, -1)
      else
        have hca : c < a := lt_of_le_of_ne (le_of_not_gt hac') hac.symm
        (⟨c, a, b, hca, hab'⟩, 1)
  else
    have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab') hab.symm
    if hac' : a < c then (⟨b, a, c, hba, hac'⟩, -1)
    else
      have hca : c < a := lt_of_le_of_ne (le_of_not_gt hac') hac.symm
      if hbc' : b < c then (⟨b, c, a, hbc', hca⟩, 1)
      else
        have hcb : c < b := lt_of_le_of_ne (le_of_not_gt hbc') hbc.symm
        (⟨c, b, a, hcb, hba⟩, -1)

theorem sortTriplePositions_sign (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (sortTriplePositions a b c hab hac hbc).2 = 1 ∨
      (sortTriplePositions a b c hab hac hbc).2 = -1 := by
  unfold sortTriplePositions
  split_ifs <;> simp

theorem sortTriplePositions_positionSet (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (sortTriplePositions a b c hab hac hbc).1.positionSet = {a, b, c} := by
  unfold sortTriplePositions
  split_ifs <;> ext x <;>
    simp [IncreasingBoundaryTriple.positionSet, or_comm, or_left_comm, or_assoc]

/-- Evaluation of the source variable X_(a+1,b+1,c+1), with a<b<c. -/
def canonicalTripleValue (P : LabelledTuple n) (t : IncreasingBoundaryTriple n) : ℚ :=
  ((chi P (boundaryIndex 0 t.lower) (boundaryIndex 0 t.middle)
    (boundaryIndex 0 t.upper) : ℤ) : ℚ)

/-- Alternation gives the exact rational sign for all six orders, for every
tuple, including collinear triples. No G1 hypothesis is used. -/
theorem sortTriplePositions_evaluation (P : LabelledTuple n) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((chi P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c) : ℤ) : ℚ) =
      (sortTriplePositions a b c hab hac hbc).2 *
        canonicalTripleValue P (sortTriplePositions a b c hab hac hbc).1 := by
  unfold sortTriplePositions
  split_ifs <;> simp only [canonicalTripleValue, one_mul, neg_one_mul]
  · rw [chi_swap_last P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c),
      SignType.coe_neg, Int.cast_neg, neg_neg]
  · rw [chi_cyclic P (boundaryIndex 0 b) (boundaryIndex 0 c) (boundaryIndex 0 a),
      chi_cyclic P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c)]
  · rw [chi_swap_first P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c),
      SignType.coe_neg, Int.cast_neg, neg_neg]
  · rw [chi_cyclic P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c)]
  · rw [chi_swap_outer P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c),
      SignType.coe_neg, Int.cast_neg, neg_neg]

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A canonical physical triple and its exact orientation parity. -/
def orderedTripleData (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    IncreasingBoundaryTriple n × ℚ :=
  sortTriplePositions (canonicalPosition i) (canonicalPosition j) (canonicalPosition k)
    (fun h => hij (canonicalPosition_injective h))
    (fun h => hik (canonicalPosition_injective h))
    (fun h => hjk (canonicalPosition_injective h))

theorem orderedTripleData_sign (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (orderedTripleData i j k hij hik hjk).2 = 1 ∨
      (orderedTripleData i j k hij hik hjk).2 = -1 :=
  sortTriplePositions_sign _ _ _ _ _ _

theorem orderedTripleData_vertexSet (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (orderedTripleData i j k hij hik hjk).1.vertexSet 0 = {i, j, k} := by
  unfold orderedTripleData IncreasingBoundaryTriple.vertexSet
  rw [sortTriplePositions_positionSet]
  simp only [Finset.image_insert, Finset.image_singleton, boundaryIndex_canonicalPosition]

theorem orderedTripleData_evaluation (P : LabelledTuple n) (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((chi P i j k : ℤ) : ℚ) = (orderedTripleData i j k hij hik hjk).2 *
      canonicalTripleValue P (orderedTripleData i j k hij hik hjk).1 := by
  have h := sortTriplePositions_evaluation P (canonicalPosition i) (canonicalPosition j)
    (canonicalPosition k) (fun h => hij (canonicalPosition_injective h))
    (fun h => hik (canonicalPosition_injective h))
    (fun h => hjk (canonicalPosition_injective h))
  simpa only [boundaryIndex_canonicalPosition, orderedTripleData] using h

/-- Ordered chirotopes interpreted in the unrestricted polynomial ring.
Repeated labels are zero. Distinct labels give exactly one signed variable. -/
def formalOrderedChi (i j k : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  if h : i ≠ j ∧ i ≠ k ∧ j ≠ k then
    MvPolynomial.C (orderedTripleData i j k h.1 h.2.1 h.2.2).2 *
      MvPolynomial.X (orderedTripleData i j k h.1 h.2.1 h.2.2).1
  else 0

theorem formalOrderedChi_distinct (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    formalOrderedChi i j k = MvPolynomial.C (orderedTripleData i j k hij hik hjk).2 *
      MvPolynomial.X (orderedTripleData i j k hij hik hjk).1 := by
  simp only [formalOrderedChi, dif_pos (show i ≠ j ∧ i ≠ k ∧ j ≠ k from ⟨hij, hik, hjk⟩)]

theorem formalOrderedChi_repeated (i j k : ZMod n) (h : i = j ∨ i = k ∨ j = k) :
    formalOrderedChi i j k = 0 := by
  rcases h with rfl | rfl | rfl <;> simp [formalOrderedChi]

/-- Polynomial evaluation recovers every actual chirotope, including zero
values and repeated labels. This does not use realizability to identify
different polynomials. -/
theorem eval_formalOrderedChi (P : LabelledTuple n) (i j k : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (formalOrderedChi i j k) =
      ((chi P i j k : ℤ) : ℚ) := by
  classical
  by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
  · rw [formalOrderedChi_distinct i j k h.1 h.2.1 h.2.2,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact (orderedTripleData_evaluation P i j k h.1 h.2.1 h.2.2).symm
  · have he : i = j ∨ i = k ∨ j = k := by tauto
    rw [formalOrderedChi_repeated i j k he, map_zero]
    rcases he with rfl | rfl | rfl <;> simp

/-- The source's actual reversed boundary order for near/far entries. -/
def boundaryTripleData (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    IncreasingBoundaryTriple n × ℚ :=
  orderedTripleData (boundaryIndex g t.upper) (boundaryIndex g t.middle)
    (boundaryIndex g t.lower)
    (fun h => (ne_of_gt t.middle_upper) (boundaryIndex_injective g h))
    (fun h => (ne_of_gt (lt_trans t.lower_middle t.middle_upper)) (boundaryIndex_injective g h))
    (fun h => (ne_of_gt t.lower_middle) (boundaryIndex_injective g h))

theorem boundaryTripleData_vertexSet (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    (boundaryTripleData g t).1.vertexSet 0 = t.vertexSet g := by
  exact (orderedTripleData_vertexSet _ _ _ _ _ _).trans (t.vertexSet_reversed g).symm

theorem boundaryTripleData_injective (g : ZMod n) :
    Function.Injective (fun t : IncreasingBoundaryTriple n => (boundaryTripleData g t).1) := by
  intro t u h
  apply IncreasingBoundaryTriple.vertexSet_injective g
  have he := congrArg (IncreasingBoundaryTriple.vertexSet 0) h
  simpa only [boundaryTripleData_vertexSet] using he

def formalBoundaryChi (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  formalOrderedChi (boundaryIndex g t.upper) (boundaryIndex g t.middle)
    (boundaryIndex g t.lower)

theorem formalBoundaryChi_eq (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    formalBoundaryChi g t = MvPolynomial.C (boundaryTripleData g t).2 *
      MvPolynomial.X (boundaryTripleData g t).1 :=
  formalOrderedChi_distinct _ _ _ _ _ _

theorem eval_formalBoundaryChi (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    MvPolynomial.eval (canonicalTripleValue P) (formalBoundaryChi g t) =
      ((chi P (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) : ℤ) : ℚ) :=
  eval_formalOrderedChi P _ _ _

end
end SM


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

/-- Rational gate identities are proved directly on all four nonzero sign
pairs; integer division is not transported through a cast. -/
theorem gate_pair_rational (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    (ordinaryGate d h hd hh : ℚ) = (1 / 2 : ℚ) * ((d : ℤ) - (h : ℤ)) ∧
    (rootGate d h hd hh : ℚ) = (1 / 2 : ℚ) * ((d : ℤ) + (h : ℤ)) := by
  cases d <;> cases h <;>
    first | exact (hd rfl).elim | exact (hh rfl).elim |
      norm_num [ordinaryGate, rootGate, signTheta]

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- Source ordinary half-difference, in independent canonical triple variables. -/
def tripleOrdinaryFactor (g : ZMod n) (k : Fin (π.parts - 1)) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) *
    (formalBoundaryChi g (π.nearTriple k) - formalBoundaryChi g (π.farTriple k))

/-- Source root half-sum, with the same physical root reading. -/
def tripleRootFactor (g : ZMod n) (k : Fin (π.parts - 1)) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) *
    (formalBoundaryChi g (π.nearTriple k) + formalBoundaryChi g (π.farTriple k))

def tripleOrdinaryWeight (g : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  ∏ k : Fin (π.parts - 1), π.tripleOrdinaryFactor g k

def tripleRootWeight (g : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  ∏ k : Fin (π.parts - 1), π.tripleRootFactor g k

theorem tripleFactors_binary (g : ZMod n) (hp : π.parts = 2) (k : Fin (π.parts - 1)) :
    π.tripleOrdinaryFactor g k = 0 ∧
      π.tripleRootFactor g k = formalBoundaryChi g (π.nearTriple k) := by
  have he := (π.nearTriple_eq_farTriple_iff k k).mpr ⟨hp, rfl⟩
  have hc : (MvPolynomial.C (1 / 2 : ℚ) : MvPolynomial (IncreasingBoundaryTriple n) ℚ) +
      MvPolynomial.C (1 / 2 : ℚ) = 1 := by
    rw [← map_add]
    norm_num
  constructor
  · simp only [tripleOrdinaryFactor, he, sub_self, mul_zero]
  · unfold tripleRootFactor
    rw [← he]
    calc
      _ = (MvPolynomial.C (1 / 2 : ℚ) + MvPolynomial.C (1 / 2 : ℚ)) *
          formalBoundaryChi g (π.nearTriple k) := by ring
      _ = formalBoundaryChi g (π.nearTriple k) := by rw [hc, one_mul]

theorem tripleWeights_unary (g : ZMod n) (hp : π.parts = 1) :
    π.tripleOrdinaryWeight g = 1 ∧ π.tripleRootWeight g = 1 := by
  letI : IsEmpty (Fin (π.parts - 1)) := ⟨fun k => by have := k.isLt; omega⟩
  simp [tripleOrdinaryWeight, tripleRootWeight]

theorem tripleOrdinaryWeight_binary (g : ZMod n) (hp : π.parts = 2) :
    π.tripleOrdinaryWeight g = 0 := by
  let k : Fin (π.parts - 1) := ⟨0, by omega⟩
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  exact (π.tripleFactors_binary g hp k).1

theorem tripleRootWeight_binary (g : ZMod n) (hp : π.parts = 2)
    (k : Fin (π.parts - 1)) :
    π.tripleRootWeight g = formalBoundaryChi g (π.nearTriple k) := by
  calc
    _ = π.tripleRootFactor g k := by
      apply Finset.prod_eq_single k
      · intro l _ hl
        exfalso
        apply hl
        apply Fin.ext
        have := l.isLt
        have := k.isLt
        omega
      · simp
    _ = _ := (π.tripleFactors_binary g hp k).2

theorem eval_tripleOrdinaryFactor (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleOrdinaryFactor g k) =
      (ordinaryGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k) : ℚ) := by
  rw [tripleOrdinaryFactor, map_mul, MvPolynomial.eval_C, map_sub,
    eval_formalBoundaryChi, eval_formalBoundaryChi]
  exact (gate_pair_rational _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).1.symm

theorem eval_tripleRootFactor (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleRootFactor g k) =
      (rootGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k) : ℚ) := by
  rw [tripleRootFactor, map_mul, MvPolynomial.eval_C, map_add,
    eval_formalBoundaryChi, eval_formalBoundaryChi]
  exact (gate_pair_rational _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).2.symm

theorem eval_tripleOrdinaryWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleOrdinaryWeight g) =
      (π.ordinaryWeight P hP g : ℚ) := by
  simp only [tripleOrdinaryWeight, ordinaryWeight, map_prod, Int.cast_prod,
    eval_tripleOrdinaryFactor π P hP g]

theorem eval_tripleRootWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleRootWeight g) =
      (π.rootWeight P hP g : ℚ) := by
  simp only [tripleRootWeight, rootWeight, map_prod, Int.cast_prod,
    eval_tripleRootFactor π P hP g]

end IntervalComposition

/-- Exactly the polynomial prescribed by the finite rooted tree recursion,
using signed canonical physical triple variables for each original cut. -/
def canonicalTreePolynomial (g : ZMod n) (hn : 3 ≤ n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  rootedTreeRec (fun _ π => π.tripleOrdinaryWeight g)
    (fun _ π => π.tripleRootWeight g) (fullBoundaryInterval hn)

/-- The actual signed finite-tree sum, without independent composition variables. -/
theorem canonicalTreePolynomial_eq_signed_tree_sum (g : ZMod n) (hn : 3 ≤ n) :
    canonicalTreePolynomial g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : MvPolynomial (IncreasingBoundaryTriple n) ℚ) ^ T.ordinaryCount *
        T.fst.tripleRootWeight g * T.ordinaryProduct (fun _ π => π.tripleOrdinaryWeight g) :=
  rootedTreeRec_eq_signed_planeTreeSum _ _ _

/-- Exact G1 evaluation of the prescribed polynomial at the same physical root.
This theorem does not yet assert its individual-variable degree bound. -/
theorem eval_canonicalTreePolynomial (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) =
      (treeCoefficient P hP g hn : ℚ) := by
  unfold canonicalTreePolynomial
  rw [map_rootedTreeRec]
  change rootedTreeRec _ _ _ = (Int.castRingHom ℚ) (rootedTreeRec _ _ _)
  rw [map_rootedTreeRec]
  congr 1
  · funext I π
    exact π.eval_tripleOrdinaryWeight P hP g
  · funext I π
    exact π.eval_tripleRootWeight P hP g

end
end SM

#check SM.gate_pair_rational
#check SM.IntervalComposition.tripleOrdinaryFactor
#check SM.IntervalComposition.tripleRootFactor
#check SM.IntervalComposition.tripleOrdinaryWeight
#check SM.IntervalComposition.tripleRootWeight
#check SM.IntervalComposition.tripleFactors_binary
#check SM.IntervalComposition.tripleWeights_unary
#check SM.IntervalComposition.tripleOrdinaryWeight_binary
#check SM.IntervalComposition.tripleRootWeight_binary
#check SM.IntervalComposition.eval_tripleOrdinaryFactor
#check SM.IntervalComposition.eval_tripleRootFactor
#check SM.IntervalComposition.eval_tripleOrdinaryWeight
#check SM.IntervalComposition.eval_tripleRootWeight
#check SM.canonicalTreePolynomial
#check SM.canonicalTreePolynomial_eq_signed_tree_sum
#check SM.eval_canonicalTreePolynomial

namespace SM

noncomputable section
universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v}
  [CommRing R] [CommRing S] [Invertible (2 : R)] [Invertible (2 : S)]

/-- The designated inverses of two are respected by every ring map,
including maps into polynomial rings. No cancellation assumption is needed. -/
theorem ringHom_map_half (f : R →+* S) : f (⅟ (2 : R)) = ⅟ (2 : S) := by
  have hprod : f (⅟ (2 : R)) * (2 : S) = 1 := by
    calc
      _ = f (⅟ (2 : R) * 2) := by rw [map_mul, map_ofNat]
      _ = 1 := by rw [invOf_mul_self, map_one]
  calc
    f (⅟ (2 : R)) = f (⅟ (2 : R)) * ((2 : S) * ⅟ (2 : S)) := by
      rw [mul_invOf_self, mul_one]
    _ = (f (⅟ (2 : R)) * (2 : S)) * ⅟ (2 : S) := by rw [mul_assoc]
    _ = ⅟ (2 : S) := by rw [hprod, one_mul]

theorem map_nearFarWeight (f : R →+* S) (D H : TripleArray n R)
    {I : BoundaryInterval n} (π : IntervalComposition I) :
    f (π.nearFarWeight D H) = π.nearFarWeight (fun t => f (D t)) (fun t => f (H t)) := by
  simp only [IntervalComposition.nearFarWeight, map_prod, map_mul, map_sub,
    ringHom_map_half]

theorem map_boundaryUnitArray (f : R →+* S) (I : BoundaryInterval n) :
    f (boundaryUnitArray (R := R) I) = boundaryUnitArray (R := S) I := by
  by_cases h : I.right.val = I.left.val + 1 <;> simp [boundaryUnitArray, h]

/-- Naturality preserves the complete sum, including its unary term and
all actual child intervals. -/
theorem map_nearFarTransform (f : R →+* S) (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarTransform D H X I) = nearFarTransform (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (X J)) I := by
  simp only [nearFarTransform, map_sum, map_mul, map_prod, map_nearFarWeight]

theorem map_farTransform (f : R →+* S) (H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (farTransform H X I) = farTransform (fun t => f (H t)) (fun J => f (X J)) I := by
  have hz : (fun t : IncreasingBoundaryTriple n => f ((0 : TripleArray n R) t)) =
      (0 : TripleArray n S) := by funext t; exact map_zero f
  have h := map_nearFarTransform f 0 H X I
  rw [hz] at h
  exact h

/-- The existing well-founded inverse recursion commutes with every ring
map, after mapping its actual near/far weights. -/
theorem map_nearFarInverse (f : R →+* S) (D H : TripleArray n R)
    (Y : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarInverse D H Y I) = nearFarInverse (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (Y J)) I := by
  simpa only [nearFarInverse, map_nearFarWeight] using
    map_triangularInverse f (fun _ π => π.nearFarWeight D H) Y I

theorem map_farOnlyCoordinates (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyCoordinates H I) = farOnlyCoordinates (fun t => f (H t)) I := by
  have hz : (fun t : IncreasingBoundaryTriple n => f ((0 : TripleArray n R) t)) =
      (0 : TripleArray n S) := by funext t; exact map_zero f
  have he : (fun J : BoundaryInterval n => f (boundaryUnitArray (R := R) J)) =
      boundaryUnitArray (R := S) := funext (map_boundaryUnitArray f)
  have h := map_nearFarInverse f 0 H boundaryUnitArray I
  rw [hz, he] at h
  exact h

theorem map_farOnlyOutput (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyOutput H I) = farOnlyOutput (fun t => f (H t)) I := by
  have hn : (fun t => f ((-H) t)) = -(fun t => f (H t)) := by
    funext t
    exact map_neg f (H t)
  have hc : (fun J => f (farOnlyCoordinates H J)) = farOnlyCoordinates (fun t => f (H t)) :=
    funext (map_farOnlyCoordinates f H)
  have h := map_farTransform f (-H) (farOnlyCoordinates H) I
  rw [hn, hc] at h
  exact h

end
end SM

namespace SM

noncomputable section
universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- Exactly one independent variable for each zero entry of the fixed
far array. No realizability relation is imposed on this variable type. -/
def SilentFarEntry (H0 : TripleArray n R) := {t : IncreasingBoundaryTriple n // H0 t = 0}

def silentFarArray (H0 : TripleArray n R) : TripleArray n (MvPolynomial (SilentFarEntry H0) R) := by
  classical
  exact fun t => if h : H0 t = 0 then MvPolynomial.X ⟨t, h⟩ else MvPolynomial.C (H0 t)

/-- The variable part vanishes identically at every initially nonzero entry. -/
def silentFarVariable (H0 : TripleArray n R) : TripleArray n (MvPolynomial (SilentFarEntry H0) R) := by
  classical
  exact fun t => if h : H0 t = 0 then MvPolynomial.X ⟨t, h⟩ else 0

theorem silentFarArray_eq_constant_add_variable (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) :
    silentFarArray H0 t = MvPolynomial.C (H0 t) + silentFarVariable H0 t := by
  by_cases h : H0 t = 0 <;> simp [silentFarArray, silentFarVariable, h]

theorem silentFarArray_at_zero_entry (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : H0 t = 0) :
    silentFarArray H0 t = MvPolynomial.X (⟨t, h⟩ : SilentFarEntry H0) := by
  exact dif_pos h

theorem silentFarArray_at_nonzero_entry (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : H0 t ≠ 0) :
    silentFarArray H0 t = MvPolynomial.C (H0 t) := by
  simp [silentFarArray, h]

def silentFarZeroHom (H0 : TripleArray n R) : MvPolynomial (SilentFarEntry H0) R →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)

theorem silentFarZeroHom_array (H0 : TripleArray n R) :
    (fun t => silentFarZeroHom H0 (silentFarArray H0 t)) = H0 := by
  funext t
  by_cases h : H0 t = 0
  · rw [silentFarArray_at_zero_entry H0 t h]
    change MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)
      (MvPolynomial.X (⟨t, h⟩ : SilentFarEntry H0)) = H0 t
    rw [MvPolynomial.eval₂Hom_X', h]
  · rw [silentFarArray_at_nonzero_entry H0 t h]
    exact MvPolynomial.eval₂Hom_C (RingHom.id R) (fun _ => 0) (H0 t)

variable [Invertible (2 : R)]

/-- The numeral two in the polynomial ring inherits its actual inverse
through the constant ring map. This supplies an instance, not a new premise. -/
local instance silentPolynomialTwoInvertible (σ : Type*) :
    Invertible (2 : MvPolynomial σ R) := by
  have h : MvPolynomial.C (2 : R) = (2 : MvPolynomial σ R) := map_ofNat MvPolynomial.C 2
  exact h ▸ MvPolynomial.invertibleC σ (2 : R)

/-- The fixed child coordinates from the source, lifted as constants. -/
def constantFarCoordinates (H0 : TripleArray n R) :
    IntervalArray n (MvPolynomial (SilentFarEntry H0) R) :=
  fun I => MvPolynomial.C (farOnlyCoordinates H0 I)

/-- Lifting c0 through the constant ring map preserves its defining
zero-specialized equation on every interval. -/
theorem constantFarCoordinates_equation (H0 : TripleArray n R) :
    farTransform (fun t => MvPolynomial.C (H0 t)) (constantFarCoordinates H0) =
      boundaryUnitArray := by
  funext I
  have h := map_farTransform (MvPolynomial.C : R →+* MvPolynomial (SilentFarEntry H0) R)
    H0 (farOnlyCoordinates H0) I
  rw [congrFun (farOnlyCoordinates_equation H0) I, map_boundaryUnitArray] at h
  exact h.symm

theorem constantFarCoordinates_inverse (H0 : TripleArray n R) :
    constantFarCoordinates H0 = farOnlyCoordinates (fun t => MvPolynomial.C (H0 t)) := by
  funext I
  exact map_farOnlyCoordinates
    (MvPolynomial.C : R →+* MvPolynomial (SilentFarEntry H0) R) H0 I

/-- Evaluating all formal variables at zero recovers c0. This is only
specialization; it does not assert independence from those variables. -/
theorem silentFarCoordinates_zero_specialization (H0 : TripleArray n R)
    (I : BoundaryInterval n) :
    silentFarZeroHom H0 (farOnlyCoordinates (silentFarArray H0) I) = farOnlyCoordinates H0 I := by
  have h := map_farOnlyCoordinates (silentFarZeroHom H0) (silentFarArray H0) I
  rw [silentFarZeroHom_array] at h
  exact h

/-- Zero specialization also commutes with the full reversed-far output.
Formal constancy is a separate, still necessary proof obligation. -/
theorem silentFarOutput_zero_specialization (H0 : TripleArray n R)
    (I : BoundaryInterval n) :
    silentFarZeroHom H0 (farOnlyOutput (silentFarArray H0) I) = farOnlyOutput H0 I := by
  have h := map_farOnlyOutput (silentFarZeroHom H0) (silentFarArray H0) I
  rw [silentFarZeroHom_array] at h
  exact h

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual open tree recursion solves the complete near/far system
for arbitrary arrays in the full ring, without a geometric specialization. -/
theorem openTreeRec_nearFar_equation (D H : TripleArray n R) :
    nearFarTransform D H (openTreeRec (fun _ π => π.nearFarWeight D H)) = boundaryUnitArray := by
  rw [nearFarTransform_eq_triangular]
  funext I
  have hp := I.leaves_pos
  have hi : I.right.val = I.left.val + 1 ↔ I.leaves = 1 := by
    have := I.increasing
    unfold BoundaryInterval.leaves
    change I.left.val < I.right.val at this
    omega
  by_cases hI : I.leaves = 1
  · letI : IsEmpty {π : IntervalComposition I // 2 ≤ π.parts} :=
      ⟨fun π => by have := π.val.parts_eq_one_of_leaves_eq_one hI; have := π.property; omega⟩
    simp [triangularTransform, boundaryUnitArray, hi.mpr hI, openTreeRec_one _ I hI]
  · have hm : 2 ≤ I.leaves := by omega
    simp only [triangularTransform, boundaryUnitArray,
      show ¬I.right.val = I.left.val + 1 from fun h => hI (hi.mp h), if_false]
    rw [openTreeRec_many _ I hm]
    exact neg_add_cancel _

/-- Uniqueness identifies the actual formal recursion with the existing
polynomial inverse on every interval. -/
theorem openTreeRec_nearFar_inverse (D H : TripleArray n R) :
    openTreeRec (fun _ π => π.nearFarWeight D H) = nearFarInverse D H boundaryUnitArray :=
  nearFar_solution_unique D H _ _ (openTreeRec_nearFar_equation D H)

/-- The actual rooted recursion is the far-only output as a full ring
identity, with each root weight the entire reversed-far cut product. -/
theorem rootedTreeRec_nearFar_farOnly (D H : TripleArray n R) (I : BoundaryInterval n) :
    rootedTreeRec (fun _ π => π.nearFarWeight D H)
      (fun _ π => π.nearFarWeight D (-H)) I = farOnlyOutput H I := by
  exact congrFun (reversedFar_output_of_solution D H
    (openTreeRec (fun _ π => π.nearFarWeight D H)) boundaryUnitArray
    (openTreeRec_nearFar_equation D H)) I

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] silentPolynomialTwoInvertible

theorem canonicalPolynomial_half :
    (MvPolynomial.C (1 / 2 : ℚ) : MvPolynomial (IncreasingBoundaryTriple n) ℚ) =
      ⅟ (2 : MvPolynomial (IncreasingBoundaryTriple n) ℚ) := by
  simpa only [invOf_eq_inv, one_div] using
    (ringHom_map_half (MvPolynomial.C : ℚ →+* MvPolynomial (IncreasingBoundaryTriple n) ℚ))

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- Every ordinary gate variable is specialized to its entire cut product,
not to one linear factor representing the whole composition. -/
theorem tripleOrdinaryWeight_nearFar (g : ZMod n) :
    π.tripleOrdinaryWeight g = π.nearFarWeight (formalBoundaryChi g) (formalBoundaryChi g) := by
  unfold tripleOrdinaryWeight nearFarWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [tripleOrdinaryFactor, canonicalPolynomial_half]
  exact mul_comm _ _

/-- The root weight specializes to the entire reversed-far product,
including the empty product for a unary root. -/
theorem tripleRootWeight_nearFar (g : ZMod n) :
    π.tripleRootWeight g = π.nearFarWeight (formalBoundaryChi g) (-formalBoundaryChi g) := by
  unfold tripleRootWeight nearFarWeight
  apply Finset.prod_congr rfl
  intro k _
  simp only [tripleRootFactor, canonicalPolynomial_half, Pi.neg_apply, sub_neg_eq_add]
  exact mul_comm _ _

end IntervalComposition

/-- The actual prescribed canonical physical-triple polynomial equals the
far-only output as an identity in its unrestricted rational polynomial ring. -/
theorem canonicalTreePolynomial_farOnly (g : ZMod n) (hn : 3 ≤ n) :
    canonicalTreePolynomial g hn = farOnlyOutput (formalBoundaryChi g) (fullBoundaryInterval hn) := by
  unfold canonicalTreePolynomial
  simp_rw [IntervalComposition.tripleOrdinaryWeight_nearFar,
    IntervalComposition.tripleRootWeight_nearFar]
  exact rootedTreeRec_nearFar_farOnly (formalBoundaryChi g) (formalBoundaryChi g) _

/-- Polynomial evaluation at every tuple, including simultaneous silent
zeros, equals the geometric far-only output. No step-function gate at zero
or genericity assumption enters this full polynomial identity. -/
theorem eval_canonicalTreePolynomial_farOnly (P : LabelledTuple n) (g : ZMod n)
    (hn : 3 ≤ n) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) =
      farOnlyOutput (geometricBoundaryArray (R := ℚ) P g) (fullBoundaryInterval hn) := by
  rw [canonicalTreePolynomial_farOnly]
  have h := map_farOnlyOutput (MvPolynomial.eval (canonicalTripleValue P))
    (formalBoundaryChi g) (fullBoundaryInterval hn)
  have he : (fun t => MvPolynomial.eval (canonicalTripleValue P) (formalBoundaryChi g t)) =
      geometricBoundaryArray (R := ℚ) P g := by
    funext t
    exact eval_formalBoundaryChi P g t
  rw [he] at h
  exact h

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Fix precisely the initially nonzero canonical physical-triple entries.
Every zero entry remains its own independent variable in the full free ring. -/
def canonicalFreezeValue (P : LabelledTuple n) (t : IncreasingBoundaryTriple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  if canonicalTripleValue P t = 0 then MvPolynomial.X t
  else MvPolynomial.C (canonicalTripleValue P t)

def canonicalFreezeHom (P : LabelledTuple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ →+*
      MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (canonicalFreezeValue P)

theorem canonicalFreezeHom_C (P : LabelledTuple n) (a : ℚ) :
    canonicalFreezeHom P (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem canonicalFreezeHom_X_zero (P : LabelledTuple n) (t : IncreasingBoundaryTriple n)
    (ht : canonicalTripleValue P t = 0) :
    canonicalFreezeHom P (MvPolynomial.X t) = MvPolynomial.X t := by
  simp [canonicalFreezeHom, canonicalFreezeValue, ht]

theorem canonicalFreezeHom_X_nonzero (P : LabelledTuple n) (t : IncreasingBoundaryTriple n)
    (ht : canonicalTripleValue P t ≠ 0) :
    canonicalFreezeHom P (MvPolynomial.X t) = MvPolynomial.C (canonicalTripleValue P t) := by
  simp [canonicalFreezeHom, canonicalFreezeValue, ht]

/-- Any assignment agreeing on the fixed entries evaluates a polynomial and
its freezing identically. No realizability condition is imposed on v. -/
theorem eval_canonicalFreezeHom_of_agree (P : LabelledTuple n)
    (v : IncreasingBoundaryTriple n → ℚ)
    (hv : ∀ t, canonicalTripleValue P t ≠ 0 → v t = canonicalTripleValue P t)
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ) :
    MvPolynomial.eval v (canonicalFreezeHom P p) = MvPolynomial.eval v p := by
  have he : (MvPolynomial.eval v).comp (canonicalFreezeHom P) = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, canonicalFreezeHom_C]
    · intro t
      simp only [RingHom.comp_apply]
      by_cases ht : canonicalTripleValue P t = 0
      · rw [canonicalFreezeHom_X_zero P t ht]
      · rw [canonicalFreezeHom_X_nonzero P t ht,
          MvPolynomial.eval_C, MvPolynomial.eval_X, hv t ht]
  exact DFunLike.congr_fun he p

theorem eval_canonicalFreezeHom_base (P : LabelledTuple n)
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalFreezeHom P p) =
      MvPolynomial.eval (canonicalTripleValue P) p :=
  eval_canonicalFreezeHom_of_agree P _ (fun _ _ => rfl) p

/-- The exact parity and canonical label attached to a reversed boundary
triple recover its geometric sign, including zero. -/
theorem boundaryTripleData_geometric (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    (boundaryTripleData g t).2 * canonicalTripleValue P (boundaryTripleData g t).1 =
      geometricBoundaryArray (R := ℚ) P g t := by
  have h := eval_formalBoundaryChi P g t
  rw [formalBoundaryChi_eq, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
  exact h

/-- Every nonzero geometric boundary entry becomes exactly its constant
under the canonical freezing, with the reversed-order parity retained. -/
theorem canonicalFreezeHom_formalBoundaryChi_nonzero (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n)
    (ht : geometricBoundaryArray (R := ℚ) P g t ≠ 0) :
    canonicalFreezeHom P (formalBoundaryChi g t) =
      geometricBoundaryArray (R := MvPolynomial (IncreasingBoundaryTriple n) ℚ) P g t := by
  have he := boundaryTripleData_geometric P g t
  have hc : canonicalTripleValue P (boundaryTripleData g t).1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact ht he.symm
  rw [formalBoundaryChi_eq, map_mul, canonicalFreezeHom_C,
    canonicalFreezeHom_X_nonzero P _ hc, ← map_mul, he]
  exact map_intCast MvPolynomial.C _

end
end SM

#print axioms SM.canonicalFreezeValue
#print axioms SM.canonicalFreezeHom
#print axioms SM.canonicalFreezeHom_C
#print axioms SM.canonicalFreezeHom_X_zero
#print axioms SM.canonicalFreezeHom_X_nonzero
#print axioms SM.eval_canonicalFreezeHom_of_agree
#print axioms SM.eval_canonicalFreezeHom_base
#print axioms SM.boundaryTripleData_geometric
#print axioms SM.canonicalFreezeHom_formalBoundaryChi_nonzero
