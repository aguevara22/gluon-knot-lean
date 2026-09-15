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
  simp only [formalOrderedChi, dif_pos ⟨hij, hik, hjk⟩]

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

#check SM.orderedTripleData
#print axioms SM.orderedTripleData
#check SM.orderedTripleData_sign
#print axioms SM.orderedTripleData_sign
#check SM.orderedTripleData_vertexSet
#print axioms SM.orderedTripleData_vertexSet
#check SM.orderedTripleData_evaluation
#print axioms SM.orderedTripleData_evaluation
#check SM.formalOrderedChi
#print axioms SM.formalOrderedChi
#check SM.formalOrderedChi_distinct
#print axioms SM.formalOrderedChi_distinct
#check SM.formalOrderedChi_repeated
#print axioms SM.formalOrderedChi_repeated
#check SM.eval_formalOrderedChi
#print axioms SM.eval_formalOrderedChi
#check SM.boundaryTripleData
#print axioms SM.boundaryTripleData
#check SM.boundaryTripleData_vertexSet
#print axioms SM.boundaryTripleData_vertexSet
#check SM.boundaryTripleData_injective
#print axioms SM.boundaryTripleData_injective
#check SM.formalBoundaryChi
#print axioms SM.formalBoundaryChi
#check SM.formalBoundaryChi_eq
#print axioms SM.formalBoundaryChi_eq
#check SM.eval_formalBoundaryChi
#print axioms SM.eval_formalBoundaryChi
