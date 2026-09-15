import Mathlib.Algebra.MvPolynomial.CommRing
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

namespace SM

noncomputable section
variable {σ : Type*} [DecidableEq σ]

/-- A direct degree bound in the unrestricted polynomial ring: degree at most
one on S, and zero outside S. This is not a quotient or an evaluation relation. -/
def SupportedMultiaffine (p : MvPolynomial σ ℚ) (S : Finset σ) : Prop :=
  ∀ x, p.degreeOf x ≤ if x ∈ S then 1 else 0

namespace SupportedMultiaffine

theorem degree_le_one {p : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (x : σ) : p.degreeOf x ≤ 1 := by
  have h := hp x
  split_ifs at h <;> omega

theorem constant (c : ℚ) (S : Finset σ) : SupportedMultiaffine (MvPolynomial.C c) S := by
  intro x
  rw [MvPolynomial.degreeOf_C]
  exact Nat.zero_le _

theorem zero (S : Finset σ) : SupportedMultiaffine (0 : MvPolynomial σ ℚ) S := by
  simpa using constant (σ := σ) 0 S

theorem one (S : Finset σ) : SupportedMultiaffine (1 : MvPolynomial σ ℚ) S := by
  simpa using constant (σ := σ) 1 S

theorem X_singleton (x : σ) : SupportedMultiaffine (MvPolynomial.X x) {x} := by
  intro y
  simp only [MvPolynomial.degreeOf_X, Finset.mem_singleton]
  exact le_rfl

theorem mono {p : MvPolynomial σ ℚ} {S T : Finset σ}
    (hp : SupportedMultiaffine p S) (hST : S ⊆ T) : SupportedMultiaffine p T := by
  intro x
  have h := hp x
  by_cases hs : x ∈ S
  · simpa only [if_pos hs, if_pos (hST hs)] using h
  · simp only [if_neg hs] at h
    exact le_trans h (Nat.zero_le _)

theorem neg {p : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) : SupportedMultiaffine (-p) S := by
  intro x
  simpa only [MvPolynomial.degreeOf_neg] using hp x

theorem add {p q : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (hq : SupportedMultiaffine q S) :
    SupportedMultiaffine (p + q) S := by
  intro x
  exact le_trans (MvPolynomial.degreeOf_add_le x p q) (max_le (hp x) (hq x))

theorem sub {p q : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (hq : SupportedMultiaffine q S) :
    SupportedMultiaffine (p - q) S := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem constant_mul {p : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (c : ℚ) :
    SupportedMultiaffine (MvPolynomial.C c * p) S := by
  intro x
  exact le_trans (MvPolynomial.degreeOf_C_mul_le p x c) (hp x)

/-- Distinct supports prevent adding two positive exponents of one variable. -/
theorem mul_disjoint {p q : MvPolynomial σ ℚ} {S T : Finset σ}
    (hp : SupportedMultiaffine p S) (hq : SupportedMultiaffine q T)
    (hST : Disjoint S T) : SupportedMultiaffine (p * q) (S ∪ T) := by
  intro x
  have h := MvPolynomial.degreeOf_mul_le x p q
  have hpx := hp x
  have hqx := hq x
  have hn : ¬ (x ∈ S ∧ x ∈ T) := fun hh => (Finset.disjoint_left.mp hST) hh.1 hh.2
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
    simp_all [Finset.mem_union] <;> omega

/-- The finite product bound includes empty products and zero factors. -/
theorem prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → MvPolynomial σ ℚ) (S : ι → Finset σ)
    (hp : ∀ i, SupportedMultiaffine (p i) (S i))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) :
    SupportedMultiaffine (∏ i ∈ s, p i) (s.biUnion S) := by
  induction s using Finset.induction_on with
  | empty => simpa using one (σ := σ) ∅
  | @insert i s hi ih =>
      have hd : Disjoint (S i) (s.biUnion S) := by
        apply Finset.disjoint_left.mpr
        intro x hx hu
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hu
        have hij : i ≠ j := by intro h; subst j; exact hi hj
        exact (Finset.disjoint_left.mp (hS hij)) hx hxj
      simpa only [Finset.prod_insert hi, Finset.biUnion_insert] using
        (hp i).mul_disjoint ih hd

theorem sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℚ) (S : Finset σ)
    (hp : ∀ i ∈ s, SupportedMultiaffine (p i) S) :
    SupportedMultiaffine (∑ i ∈ s, p i) S := by
  intro x
  apply le_trans (MvPolynomial.degreeOf_sum_le x s p)
  exact Finset.sup_le (fun i hi => hp i hi x)

end SupportedMultiaffine
end
end SM

namespace SM

noncomputable section
open scoped Classical
variable {n : ℕ} [NeZero n]

/-- Transport actual unordered boundary supports to canonical physical variables. -/
def canonicalSupport (g : ZMod n) (S : Finset (IncreasingBoundaryTriple n)) :
    Finset (IncreasingBoundaryTriple n) := by
  classical
  exact S.image (fun t => (boundaryTripleData g t).1)

theorem canonicalSupport_mono (g : ZMod n) {S T : Finset (IncreasingBoundaryTriple n)}
    (hST : S ⊆ T) : canonicalSupport g S ⊆ canonicalSupport g T := by
  classical
  exact Finset.image_subset_image hST

theorem canonicalSupport_disjoint (g : ZMod n) {S T : Finset (IncreasingBoundaryTriple n)}
    (hST : Disjoint S T) : Disjoint (canonicalSupport g S) (canonicalSupport g T) := by
  classical
  exact (Finset.disjoint_image (boundaryTripleData_injective g)).mpr hST

theorem canonicalSupport_union (g : ZMod n) (S T : Finset (IncreasingBoundaryTriple n)) :
    canonicalSupport g (S ∪ T) = canonicalSupport g S ∪ canonicalSupport g T := by
  classical
  exact Finset.image_union _ _

theorem canonicalSupport_biUnion {ι : Type*} (g : ZMod n) (s : Finset ι)
    (S : ι → Finset (IncreasingBoundaryTriple n)) :
    canonicalSupport g (s.biUnion S) = s.biUnion (fun i => canonicalSupport g (S i)) := by
  classical
  exact Finset.biUnion_image

theorem formalBoundaryChi_supported (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    SupportedMultiaffine (formalBoundaryChi g t) (canonicalSupport g {t}) := by
  classical
  rw [formalBoundaryChi_eq]
  simpa only [canonicalSupport, Finset.image_singleton] using
    (SupportedMultiaffine.X_singleton (boundaryTripleData g t).1).constant_mul
      (boundaryTripleData g t).2

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- All sampled boundary triples at this actual node. -/
def tripleSupport : Finset (IncreasingBoundaryTriple n) := by
  classical
  exact Finset.univ.biUnion π.cutTripleSet

theorem mem_tripleSupport (t : IncreasingBoundaryTriple n) :
    t ∈ π.tripleSupport ↔ ∃ k, t ∈ π.cutTripleSet k := by
  classical
  simp [tripleSupport]

theorem tripleFactors_supported (g : ZMod n) (k : Fin (π.parts - 1)) :
    SupportedMultiaffine (π.tripleOrdinaryFactor g k) (canonicalSupport g (π.cutTripleSet k)) ∧
      SupportedMultiaffine (π.tripleRootFactor g k) (canonicalSupport g (π.cutTripleSet k)) := by
  classical
  have hn := (formalBoundaryChi_supported g (π.nearTriple k)).mono
    (canonicalSupport_mono g (show {π.nearTriple k} ⊆ π.cutTripleSet k by
      intro t ht
      have he := Finset.mem_singleton.mp ht
      subst t
      exact (π.mem_cutTripleSet k _).mpr (Or.inl rfl)))
  have hf := (formalBoundaryChi_supported g (π.farTriple k)).mono
    (canonicalSupport_mono g (show {π.farTriple k} ⊆ π.cutTripleSet k by
      intro t ht
      have he := Finset.mem_singleton.mp ht
      subst t
      exact (π.mem_cutTripleSet k _).mpr (Or.inr rfl)))
  exact ⟨(hn.sub hf).constant_mul (1 / 2), (hn.add hf).constant_mul (1 / 2)⟩

theorem tripleWeights_supported (g : ZMod n) :
    SupportedMultiaffine (π.tripleOrdinaryWeight g) (canonicalSupport g π.tripleSupport) ∧
      SupportedMultiaffine (π.tripleRootWeight g) (canonicalSupport g π.tripleSupport) := by
  classical
  have hd : Pairwise (fun k l : Fin (π.parts - 1) =>
      Disjoint (canonicalSupport g (π.cutTripleSet k)) (canonicalSupport g (π.cutTripleSet l))) :=
    fun _ _ h => canonicalSupport_disjoint g (π.cutTripleSet_disjoint h)
  constructor
  · simpa only [tripleOrdinaryWeight, tripleSupport, canonicalSupport_biUnion] using
      SupportedMultiaffine.prod Finset.univ (π.tripleOrdinaryFactor g)
        (fun k => canonicalSupport g (π.cutTripleSet k))
        (fun k => (π.tripleFactors_supported g k).1) hd
  · simpa only [tripleRootWeight, tripleSupport, canonicalSupport_biUnion] using
      SupportedMultiaffine.prod Finset.univ (π.tripleRootFactor g)
        (fun k => canonicalSupport g (π.cutTripleSet k))
        (fun k => (π.tripleFactors_supported g k).2) hd

theorem tripleSupport_disjoint_child_support
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j)) (j : Fin π.parts) :
    Disjoint π.tripleSupport (children j).tripleSupport := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hu
  obtain ⟨k, hk⟩ := (π.mem_tripleSupport t).mp ht
  exact (Finset.disjoint_left.mp (π.cutTripleSet_disjoint_child_support children k j)) hk hu

theorem tripleSupport_disjoint_children_support
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j)) :
    Disjoint π.tripleSupport (Finset.univ.biUnion (fun j => (children j).tripleSupport)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hu
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hu
  exact (Finset.disjoint_left.mp (π.tripleSupport_disjoint_child_support children j)) ht hj

end IntervalComposition

/-- Actual-tree nonrepetition transported to the source's physical variable
set, independently of geometric evaluation or realizability. -/
theorem RootedPlaneTree.canonical_cut_nonrepetition {I : BoundaryInterval n}
    (T : RootedPlaneTree I) (g : ZMod n) {a b : T.CutOccurrence}
    {t : IncreasingBoundaryTriple n}
    (ha : t ∈ canonicalSupport g (T.cutTripleSupport a))
    (hb : t ∈ canonicalSupport g (T.cutTripleSupport b)) : a = b := by
  classical
  by_contra h
  exact (Finset.disjoint_left.mp
    (canonicalSupport_disjoint g (T.cutTripleSupport_pairwise h))) ha hb

end
end SM


namespace SM

noncomputable section
open scoped Classical
variable {n : ℕ} [NeZero n]

theorem OpenPlaneTree.tripleSupport_node {I : BoundaryInterval n}
    (π : IntervalComposition I) (hp : 2 ≤ π.parts)
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j)) :
    (OpenPlaneTree.node π hp children).tripleSupport =
      π.tripleSupport ∪ Finset.univ.biUnion (fun j => (children j).tripleSupport) := by
  ext t
  constructor
  · intro ht
    obtain ⟨o, ho⟩ := ((OpenPlaneTree.node π hp children).mem_tripleSupport t).mp ht
    rcases o with k | ⟨j, o⟩
    · exact Finset.mem_union_left _ ((π.mem_tripleSupport t).mpr ⟨k, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ _, ((children j).mem_tripleSupport t).mpr ⟨o, ho⟩⟩)
  · intro ht
    apply ((OpenPlaneTree.node π hp children).mem_tripleSupport t).mpr
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨k, hk⟩ := (π.mem_tripleSupport t).mp ht
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨o, ho⟩ := ((children j).mem_tripleSupport t).mp hj
      exact ⟨Sum.inr ⟨j, o⟩, ho⟩

theorem RootedPlaneTree.tripleSupport_eq {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.tripleSupport = T.fst.tripleSupport ∪
      Finset.univ.biUnion (fun j => (T.snd j).tripleSupport) := by
  ext t
  constructor
  · intro ht
    obtain ⟨o, ho⟩ := (T.mem_tripleSupport t).mp ht
    rcases o with k | ⟨j, o⟩
    · exact Finset.mem_union_left _ ((T.fst.mem_tripleSupport t).mpr ⟨k, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ _, ((T.snd j).mem_tripleSupport t).mpr ⟨o, ho⟩⟩)
  · intro ht
    apply (T.mem_tripleSupport t).mpr
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨k, hk⟩ := (T.fst.mem_tripleSupport t).mp ht
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨o, ho⟩ := ((T.snd j).mem_tripleSupport t).mp hj
      exact ⟨Sum.inr ⟨j, o⟩, ho⟩

/-- Composition of supported polynomials on the actual parent and children.
All disjointness is derived from actual tree intervals and cut supports. -/
theorem IntervalComposition.combine_supported {I : BoundaryInterval n}
    (π : IntervalComposition I) (g : ZMod n)
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j))
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ)
    (q : Fin π.parts → MvPolynomial (IncreasingBoundaryTriple n) ℚ)
    (hp : SupportedMultiaffine p (canonicalSupport g π.tripleSupport))
    (hq : ∀ j, SupportedMultiaffine (q j) (canonicalSupport g (children j).tripleSupport)) :
    SupportedMultiaffine (p * ∏ j, q j)
      (canonicalSupport g (π.tripleSupport ∪
        Finset.univ.biUnion (fun j => (children j).tripleSupport))) := by
  have hdis : Pairwise (fun j k => Disjoint
      (canonicalSupport g (children j).tripleSupport)
      (canonicalSupport g (children k).tripleSupport)) :=
    fun _ _ h => canonicalSupport_disjoint g (π.children_tripleSupport_disjoint children h)
  have hprod := SupportedMultiaffine.prod Finset.univ q
    (fun j => canonicalSupport g (children j).tripleSupport) hq hdis
  have htop : Disjoint (canonicalSupport g π.tripleSupport)
      (Finset.univ.biUnion (fun j => canonicalSupport g (children j).tripleSupport)) := by
    rw [← canonicalSupport_biUnion]
    exact canonicalSupport_disjoint g (π.tripleSupport_disjoint_children_support children)
  simpa only [canonicalSupport_union, canonicalSupport_biUnion] using hp.mul_disjoint hprod htop

/-- Every actual ordinary tree weight is multi-affine, with zero degree
outside its derived canonical triple support, including zero binary weights. -/
theorem OpenPlaneTree.tripleWeight_supported {I : BoundaryInterval n}
    (T : OpenPlaneTree I) (g : ZMod n) :
    SupportedMultiaffine (T.weight (fun _ π => π.tripleOrdinaryWeight g))
      (canonicalSupport g T.tripleSupport) := by
  induction T with
  | leaf hI => exact SupportedMultiaffine.one _
  | node π hp children ih =>
      rw [OpenPlaneTree.weight, OpenPlaneTree.tripleSupport_node]
      exact π.combine_supported g children (-π.tripleOrdinaryWeight g)
        (fun j => (children j).weight (fun _ ρ => ρ.tripleOrdinaryWeight g))
        (π.tripleWeights_supported g).1.neg ih

/-- Every actual rooted tree weight has the same bound; the root may be unary. -/
theorem RootedPlaneTree.tripleWeight_supported {I : BoundaryInterval n}
    (T : RootedPlaneTree I) (g : ZMod n) :
    SupportedMultiaffine
      (T.weight (fun _ π => π.tripleOrdinaryWeight g) (fun _ π => π.tripleRootWeight g))
      (canonicalSupport g T.tripleSupport) := by
  rw [RootedPlaneTree.weight, T.tripleSupport_eq]
  exact T.fst.combine_supported g T.snd (T.fst.tripleRootWeight g)
    (fun j => (T.snd j).weight (fun _ π => π.tripleOrdinaryWeight g))
    (T.fst.tripleWeights_supported g).2 (fun j => (T.snd j).tripleWeight_supported g)

/-- The prescribed polynomial has individual degree at most one in every
independent canonical physical variable, in the unrestricted rational ring. -/
theorem canonicalTreePolynomial_multiaffine (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) : (canonicalTreePolynomial g hn).degreeOf t ≤ 1 := by
  unfold canonicalTreePolynomial
  rw [rootedTreeRec_eq_planeTreeSum]
  apply le_trans (MvPolynomial.degreeOf_sum_le t Finset.univ _)
  exact Finset.sup_le (fun T _ => (T.tripleWeight_supported g).degree_le_one t)

end
end SM

#check SM.OpenPlaneTree.tripleSupport_node
#print axioms SM.OpenPlaneTree.tripleSupport_node
#check SM.RootedPlaneTree.tripleSupport_eq
#print axioms SM.RootedPlaneTree.tripleSupport_eq
#check SM.IntervalComposition.combine_supported
#print axioms SM.IntervalComposition.combine_supported
#check SM.OpenPlaneTree.tripleWeight_supported
#print axioms SM.OpenPlaneTree.tripleWeight_supported
#check SM.RootedPlaneTree.tripleWeight_supported
#print axioms SM.RootedPlaneTree.tripleWeight_supported
#check SM.canonicalTreePolynomial_multiaffine
#print axioms SM.canonicalTreePolynomial_multiaffine
