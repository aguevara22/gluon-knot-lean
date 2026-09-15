import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import Mathlib.Tactic
import SM.RootBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import SM.InsertionIndices
import SM.NearFar
import SM.FarOnlyOutput

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

/-- Insert immediately after j in the source's physical order 1,...,n.
Inserting after source label n appends at position n of the enlarged list. -/
def softNewPosition (j : ZMod n) : Fin (n + 1) :=
  ⟨(canonicalPosition j).val + 1, Nat.succ_lt_succ (canonicalPosition j).isLt⟩

def softNewIndex (j : ZMod n) : ZMod (n + 1) :=
  boundaryIndex 0 (softNewPosition j)

def softOldIndex (j k : ZMod n) : ZMod (n + 1) :=
  boundaryIndex 0 ((softNewPosition j).succAbove (canonicalPosition k))

theorem softOldIndex_injective (j : ZMod n) : Function.Injective (softOldIndex j) := by
  intro k l h
  apply canonicalPosition_injective
  exact Fin.succAbove_right_injective (boundaryIndex_injective 0 h)

theorem softOldIndex_ne_new (j k : ZMod n) : softOldIndex j k ≠ softNewIndex j := by
  intro h
  exact Fin.succAbove_ne _ _ (boundaryIndex_injective 0 h)

theorem soft_indices_exhaust (j : ZMod n) (a : ZMod (n + 1)) :
    a = softNewIndex j ∨ ∃ k : ZMod n, a = softOldIndex j k := by
  obtain h | ⟨k, hk⟩ := Fin.eq_self_or_eq_succAbove (softNewPosition j) (canonicalPosition a)
  · left
    simpa only [boundaryIndex_canonicalPosition, softNewIndex] using congrArg (boundaryIndex 0) h
  · right
    refine ⟨boundaryIndex 0 k, ?_⟩
    simpa only [boundaryIndex_canonicalPosition, softOldIndex, canonicalPosition_boundaryIndex] using
      congrArg (boundaryIndex 0) hk

/-- Old physical labels at or before j are retained; every later label moves
one place forward. This explicitly identifies the literal source insertion. -/
theorem softOldIndex_physical (j : ZMod n) (k : Fin n) :
    softOldIndex j (boundaryIndex 0 k) =
      if k.val ≤ (canonicalPosition j).val then ((k.val + 1 : ℕ) : ZMod (n + 1))
      else ((k.val + 2 : ℕ) : ZMod (n + 1)) := by
  unfold softOldIndex
  rw [canonicalPosition_boundaryIndex]
  by_cases h : k.val ≤ (canonicalPosition j).val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt]
    · exact canonical_label k.castSucc
    · change k.val < (canonicalPosition j).val + 1
      omega
  · rw [if_neg h, Fin.succAbove_of_le_castSucc]
    · simpa only [Fin.val_succ, Nat.add_assoc] using canonical_label k.succ
    · change (canonicalPosition j).val + 1 ≤ k.val
      omega

theorem softNewIndex_physical (j : ZMod n) :
    softNewIndex j = (((canonicalPosition j).val + 2 : ℕ) : ZMod (n + 1)) := by
  exact canonical_label (softNewPosition j)

theorem softOldIndex_at_attachment (j : ZMod n) :
    softOldIndex j j = (((canonicalPosition j).val + 1 : ℕ) : ZMod (n + 1)) := by
  have h := softOldIndex_physical j (canonicalPosition j)
  simpa only [boundaryIndex_canonicalPosition, le_refl, ite_true] using h

theorem softOldIndex_attachment_next (j : ZMod n) :
    softOldIndex j j + 1 = softNewIndex j := by
  rw [softOldIndex_at_attachment, softNewIndex_physical]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem soft_physical_label_next (a : Fin n) (h : a.val + 1 < n) :
    boundaryIndex 0 (⟨a.val + 1, h⟩ : Fin n) = boundaryIndex 0 a + 1 := by
  simp only [canonical_label, Nat.cast_add, Nat.cast_one]

theorem soft_physical_last_label (a : Fin n) (h : a.val + 1 = n) :
    boundaryIndex 0 a = 0 := by
  rw [canonical_label, h, ZMod.natCast_self]

/-- Every old cyclic successor pair remains consecutive except the one
pair split by the actual soft vertex. This includes the physical wrap. -/
theorem softOldIndex_next (j k : ZMod n) (hk : k ≠ j) :
    softOldIndex j (k + 1) = softOldIndex j k + 1 := by
  let a := canonicalPosition k
  have ha : boundaryIndex 0 a = k := boundaryIndex_canonicalPosition k
  have hne : a.val ≠ (canonicalPosition j).val := by
    intro h
    apply hk
    exact canonicalPosition_injective (Fin.ext h)
  by_cases hw : a.val + 1 < n
  · let b : Fin n := ⟨a.val + 1, hw⟩
    have hb : boundaryIndex 0 b = k + 1 := (soft_physical_label_next a hw).trans (congrArg (· + 1) ha)
    calc
      softOldIndex j (k + 1) = softOldIndex j (boundaryIndex 0 b) := congrArg (softOldIndex j) hb.symm
      _ = softOldIndex j (boundaryIndex 0 a) + 1 := by
        rw [softOldIndex_physical, softOldIndex_physical]
        by_cases hlt : a.val < (canonicalPosition j).val
        · have hb_le : b.val ≤ (canonicalPosition j).val := by dsimp [b]; omega
          rw [if_pos hb_le, if_pos (le_of_lt hlt)]
          simp only [b, Nat.cast_add, Nat.cast_one]
        · have hgt : (canonicalPosition j).val < a.val := by omega
          have hb_gt : ¬ b.val ≤ (canonicalPosition j).val := by dsimp [b]; omega
          rw [if_neg hb_gt, if_neg (not_le_of_gt hgt)]
          simp only [b, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
      _ = softOldIndex j k + 1 := by rw [ha]
  · have hn : a.val + 1 = n := by have := a.isLt; omega
    have hk0 : k = 0 := ha.symm.trans (soft_physical_last_label a hn)
    let first : Fin n := ⟨0, NeZero.pos n⟩
    have hf : boundaryIndex 0 first = 1 := by simp [canonical_label, first]
    have hgt : (canonicalPosition j).val < a.val := by
      have := (canonicalPosition j).isLt
      omega
    calc
      softOldIndex j (k + 1) = softOldIndex j (boundaryIndex 0 first) := by rw [hk0, zero_add, hf]
      _ = 1 := by
        rw [softOldIndex_physical, if_pos (show first.val ≤ (canonicalPosition j).val from Nat.zero_le _)]
        simp [first]
      _ = softOldIndex j (boundaryIndex 0 a) + 1 := by
        rw [softOldIndex_physical, if_neg (not_le_of_gt hgt)]
        have he : a.val + 2 = n + 1 := by omega
        rw [he, ZMod.natCast_self, zero_add]
      _ = softOldIndex j k + 1 := by rw [ha]

/-- The newborn's outgoing edge returns to the original successor of j,
including insertion at the last physical label. -/
theorem softNewIndex_next (j : ZMod n) :
    softNewIndex j + 1 = softOldIndex j (j + 1) := by
  let a := canonicalPosition j
  have ha : boundaryIndex 0 a = j := boundaryIndex_canonicalPosition j
  by_cases hw : a.val + 1 < n
  · let b : Fin n := ⟨a.val + 1, hw⟩
    have hb : boundaryIndex 0 b = j + 1 := (soft_physical_label_next a hw).trans (congrArg (· + 1) ha)
    rw [← hb, softOldIndex_physical, softNewIndex_physical]
    have hgt : ¬ b.val ≤ (canonicalPosition j).val := by dsimp [b, a]; omega
    rw [if_neg hgt]
    simp only [b, a, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  · have hn : a.val + 1 = n := by have := a.isLt; omega
    have hj0 : j = 0 := ha.symm.trans (soft_physical_last_label a hn)
    let first : Fin n := ⟨0, NeZero.pos n⟩
    have hf : boundaryIndex 0 first = 1 := by simp [canonical_label, first]
    calc
      softNewIndex j + 1 = 1 := by
        rw [softNewIndex_physical]
        have he : (canonicalPosition j).val + 2 = n + 1 := by change a.val + 2 = n + 1; omega
        rw [he, ZMod.natCast_self, zero_add]
      _ = softOldIndex j (boundaryIndex 0 first) := by
        rw [softOldIndex_physical, if_pos (show first.val ≤ (canonicalPosition j).val from Nat.zero_le _)]
        simp [first]
      _ = softOldIndex j (j + 1) := by rw [hj0, zero_add, hf]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The literal physical-order soft family: insert P(j)+epsilon*q just after
j, with every old vertex retained. The formula is defined at all real parameters;
the source soft family uses its restriction to positive epsilon. -/
def softInsertion (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) :
    LabelledTuple (n + 1) :=
  fun a => Fin.insertNth (α := fun _ : Fin (n + 1) => Plane) (softNewPosition j) (P j + ε • q)
    (fun k : Fin n => P (boundaryIndex 0 k)) (canonicalPosition a)

theorem softInsertion_old (P : LabelledTuple n) (j k : ZMod n) (q : Plane) (ε : ℝ) :
    softInsertion P j q ε (softOldIndex j k) = P k := by
  simp only [softInsertion, softOldIndex, canonicalPosition_boundaryIndex,
    Fin.insertNth_apply_succAbove, boundaryIndex_canonicalPosition]

theorem softInsertion_new (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) :
    softInsertion P j q ε (softNewIndex j) = P j + ε • q := by
  simp only [softInsertion, softNewIndex, canonicalPosition_boundaryIndex,
    Fin.insertNth_apply_same]

theorem continuous_softInsertion (P : LabelledTuple n) (j : ZMod n) (q : Plane) :
    Continuous (softInsertion P j q) := by
  apply continuous_pi
  intro a
  obtain rfl | ⟨k, rfl⟩ := soft_indices_exhaust j a
  · simp_rw [softInsertion_new]
    fun_prop
  · simp_rw [softInsertion_old]
    exact continuous_const

theorem edge_softInsertion_old (P : LabelledTuple n) (j k : ZMod n) (q : Plane) (ε : ℝ)
    (hk : k ≠ j) :
    edge (softInsertion P j q ε) (softOldIndex j k) = edge P k := by
  rw [edge, ← softOldIndex_next j k hk, softInsertion_old, softInsertion_old]
  rfl

theorem edge_softInsertion_soft (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) :
    edge (softInsertion P j q ε) (softOldIndex j j) = ε • q := by
  rw [edge, softOldIndex_attachment_next, softInsertion_new, softInsertion_old]
  abel

theorem edge_softInsertion_return (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) :
    edge (softInsertion P j q ε) (softNewIndex j) = edge P j - ε • q := by
  rw [edge, softNewIndex_next, softInsertion_old, softInsertion_new]
  unfold edge
  abel

/-- Exactly the three determinant nonvanishing conditions of def:soft. -/
def SoftAdmissible (P : LabelledTuple n) (j : ZMod n) (q : Plane) : Prop :=
  det (edge P (j - 1)) q ≠ 0 ∧ det q (edge P j) ≠ 0 ∧
    ∀ k : ZMod n, k ≠ j → det q (P k - P j) ≠ 0

theorem SoftAdmissible.vector_ne_zero {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (h : SoftAdmissible P j q) : q ≠ 0 := by
  intro hq
  exact h.2.1 (by simp [hq, det])

def softAttachmentMinus (P : LabelledTuple n) (j : ZMod n) (q : Plane) : SignType :=
  -SignType.sign (det (edge P (j - 1)) q)

def softAttachmentPlus (P : LabelledTuple n) (j : ZMod n) (q : Plane) : SignType :=
  -SignType.sign (det q (edge P j))

end
end SM

namespace SM

noncomputable section
open Filter Topology

/-- The actual inserted point, independent of any cyclic label convention. -/
def softLocalPoint (M q : Plane) (ε : ℝ) : Plane := M + ε • q

/-- The actual direction from the inserted point to the old next vertex. -/
def softLocalReturn (M B q : Plane) (ε : ℝ) : Plane := B - M - ε • q

theorem softLocalPoint_add_return (M B q : Plane) (ε : ℝ) :
    softLocalPoint M q ε + softLocalReturn M B q ε = B := by
  unfold softLocalPoint softLocalReturn
  abel

/-- All new triples containing M have this exact area determinant. -/
theorem softLocal_new_old_area (M X q : Plane) (ε : ℝ) :
    det (M - softLocalPoint M q ε) (X - softLocalPoint M q ε) =
      -ε * det q (X - M) := by
  dsimp [softLocalPoint, det]
  ring

/-- The attachment order is (inserted point, M, A) and (inserted point, M, B). -/
theorem softLocal_attachment_determinants (M A B q : Plane) (ε : ℝ) :
    det (M - softLocalPoint M q ε) (A - softLocalPoint M q ε) =
      -ε * det (M - A) q ∧
    det (M - softLocalPoint M q ε) (B - softLocalPoint M q ε) =
      -ε * det q (B - M) := by
  constructor <;> dsimp [softLocalPoint, det] <;> ring

/-- The two new turn determinants are the negatives of the attachment areas. -/
theorem softLocal_turn_determinants (M A B q : Plane) (ε : ℝ) :
    det (M - A) (softLocalPoint M q ε - M) = ε * det (M - A) q ∧
    det (softLocalPoint M q ε - M) (softLocalReturn M B q ε) =
      ε * det q (B - M) := by
  constructor <;> dsimp [softLocalPoint, softLocalReturn, det] <;> ring

/-- Both exact heights for the incoming-line strict-straddle test. -/
theorem softLocal_incoming_heights (M A B q : Plane) (ε : ℝ) :
    det (M - A) (softLocalPoint M q ε - A) = ε * det (M - A) q ∧
    det (M - A) (B - A) = det (M - A) (B - M) := by
  constructor <;> dsimp [softLocalPoint, det] <;> ring

/-- The return-line height of A has nonzero constant term T. -/
theorem softLocal_return_heights (M A B q : Plane) (ε : ℝ) :
    det (softLocalReturn M B q ε) (M - softLocalPoint M q ε) =
      ε * det q (B - M) ∧
    det (softLocalReturn M B q ε) (A - softLocalPoint M q ε) =
      det (M - A) (B - M) + ε * (det q (B - M) - det (M - A) q) := by
  constructor <;> dsimp [softLocalPoint, softLocalReturn, det] <;> ring

/-- Ordered direction determinants, including exact independence of the
soft/return pair from the parameter after its scalar factor is removed. -/
theorem softLocal_return_determinants (M A B q : Plane) (ε : ℝ) :
    det (M - A) (softLocalReturn M B q ε) =
      det (M - A) (B - M) - ε * det (M - A) q ∧
    det (softLocalReturn M B q ε) (M - A) =
      -(det (M - A) (B - M) - ε * det (M - A) q) ∧
    det q (softLocalReturn M B q ε) = det q (B - M) := by
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [softLocalReturn, det] <;> ring

/-- Attachment signs hold for every positive parameter, not just near zero. -/
theorem softLocal_attachment_signs (M A B q : Plane) (ε : ℝ) (hε : 0 < ε) :
    SignType.sign (det (M - softLocalPoint M q ε) (A - softLocalPoint M q ε)) =
      -SignType.sign (det (M - A) q) ∧
    SignType.sign (det (M - softLocalPoint M q ε) (B - softLocalPoint M q ε)) =
      -SignType.sign (det q (B - M)) := by
  have h := softLocal_attachment_determinants M A B q ε
  constructor
  · rw [h.1, sign_mul, Left.sign_neg, sign_eq_one_iff.mpr hε, neg_one_mul]
  · rw [h.2, sign_mul, Left.sign_neg, sign_eq_one_iff.mpr hε, neg_one_mul]

theorem softLocal_turn_signs (M A B q : Plane) (ε : ℝ) (hε : 0 < ε) :
    SignType.sign (det (M - A) (softLocalPoint M q ε - M)) =
      SignType.sign (det (M - A) q) ∧
    SignType.sign (det (softLocalPoint M q ε - M) (softLocalReturn M B q ε)) =
      SignType.sign (det q (B - M)) := by
  have h := softLocal_turn_determinants M A B q ε
  constructor
  · rw [h.1, sign_mul, sign_eq_one_iff.mpr hε, one_mul]
  · rw [h.2, sign_mul, sign_eq_one_iff.mpr hε, one_mul]

/-- The second sign is nonzero; the first is allowed to be zero. -/
theorem softLocal_sign_product_iff (s t : SignType) (ht : t ≠ 0) :
    s * t = -1 ↔ -s = t := by
  cases s <;> cases t <;> simp_all

/-- A linear real expression with nonzero constant term has one fixed sign
on a genuine two-sided neighborhood of zero. -/
theorem softLocal_linear_sign_persistence (T c : ℝ) (hT : T ≠ 0) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ →
      SignType.sign (T + ε * c) = SignType.sign T := by
  have hf : ContinuousAt (fun ε : ℝ => T + ε * c) (0 : ℝ) :=
    continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hz : T + (0 : ℝ) * c ≠ 0 := by simpa using hT
  have hs := ((continuousAt_sign_of_ne_zero hz).comp
    (f := fun ε : ℝ => T + ε * c) hf).eventually
    (isOpen_discrete _ |>.mem_nhds
      (Set.mem_singleton (SignType.sign (T + (0 : ℝ) * c))))
  have he : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      SignType.sign (T + ε * c) = SignType.sign T := by
    filter_upwards [hs] with ε hε
    change SignType.sign (T + ε * c) = SignType.sign (T + (0 : ℝ) * c) at hε
    simpa only [zero_mul, add_zero] using hε
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  exact hmem (by simpa [Real.dist_eq] using hε)

/-- The two nonzero constant terms needed by the source crossing argument
keep their signs on the same neighborhood. -/
theorem softLocal_small_signs (M A B q : Plane)
    (hT : det (M - A) (B - M) ≠ 0) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ →
      SignType.sign (det (M - A) (softLocalReturn M B q ε)) =
        SignType.sign (det (M - A) (B - M)) ∧
      SignType.sign (det (softLocalReturn M B q ε) (A - softLocalPoint M q ε)) =
        SignType.sign (det (M - A) (B - M)) := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := softLocal_linear_sign_persistence
    (det (M - A) (B - M)) (-det (M - A) q) hT
  obtain ⟨δ₂, hδ₂, h₂⟩ := softLocal_linear_sign_persistence
    (det (M - A) (B - M)) (det q (B - M) - det (M - A) q) hT
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ε hε
  constructor
  · rw [(softLocal_return_determinants M A B q ε).1]
    have h := h₁ ε (lt_of_lt_of_le hε (min_le_left _ _))
    simpa only [mul_neg, sub_eq_add_neg] using h
  · rw [(softLocal_return_heights M A B q ε).2]
    exact h₂ ε (lt_of_lt_of_le hε (min_le_right _ _))

/-- The first strict-straddle test is exactly the incoming attachment
condition chi_minus = tau. -/
theorem softLocal_first_straddle_iff (M A B q : Plane) (ε : ℝ) (hε : 0 < ε)
    (hT : det (M - A) (B - M) ≠ 0) :
    (det (M - A) (softLocalPoint M q ε - A) * det (M - A) (B - A) < 0) ↔
      -SignType.sign (det (M - A) q) = SignType.sign (det (M - A) (B - M)) := by
  rw [(softLocal_incoming_heights M A B q ε).1,
    (softLocal_incoming_heights M A B q ε).2,
    ← sign_product_neg_iff, sign_mul, sign_eq_one_iff.mpr hε, one_mul]
  exact softLocal_sign_product_iff _ _ (sign_ne_zero.mpr hT)

/-- The second strict-straddle test is exactly chi_plus = tau, once the
actual return-line height of A has its proved small-parameter sign. -/
theorem softLocal_second_straddle_iff (M A B q : Plane) (ε : ℝ) (hε : 0 < ε)
    (hT : det (M - A) (B - M) ≠ 0)
    (hA : SignType.sign (det (softLocalReturn M B q ε) (A - softLocalPoint M q ε)) =
      SignType.sign (det (M - A) (B - M))) :
    (det (softLocalReturn M B q ε) (A - softLocalPoint M q ε) *
      det (softLocalReturn M B q ε) (M - softLocalPoint M q ε) < 0) ↔
      -SignType.sign (det q (B - M)) = SignType.sign (det (M - A) (B - M)) := by
  rw [mul_comm, ← sign_product_neg_iff,
    (softLocal_return_heights M A B q ε).1,
    sign_mul, sign_eq_one_iff.mpr hε, one_mul, hA]
  exact softLocal_sign_product_iff _ _ (sign_ne_zero.mpr hT)

/-- Both line tests are required for an intersection in both open segments. -/
theorem softLocal_interior_crossing_iff (M A B q : Plane) (ε : ℝ) (hε : 0 < ε)
    (hT : det (M - A) (B - M) ≠ 0)
    (hA : SignType.sign (det (softLocalReturn M B q ε) (A - softLocalPoint M q ε)) =
      SignType.sign (det (M - A) (B - M))) :
    (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      A + s • (M - A) = softLocalPoint M q ε + t • softLocalReturn M B q ε ∧
      det (M - A) (softLocalReturn M B q ε) ≠ 0) ↔
      -SignType.sign (det (M - A) q) = SignType.sign (det (M - A) (B - M)) ∧
      -SignType.sign (det q (B - M)) = SignType.sign (det (M - A) (B - M)) := by
  have h := segment_crossing_criterion A (softLocalPoint M q ε)
    (M - A) (softLocalReturn M B q ε)
  have hAM : A + (M - A) = M := by abel
  rw [softLocalPoint_add_return, hAM] at h
  exact h.trans (and_congr (softLocal_first_straddle_iff M A B q ε hε hT)
    (softLocal_second_straddle_iff M A B q ε hε hT hA))

/-- Nonzero endpoint heights exclude endpoint-only contacts without a G1
hypothesis on an ambient polygon. This is ordinary segment geometry. -/
theorem softLocal_closed_iff_strict (a b u v : Plane) (hd : det u v ≠ 0)
    (hv0 : det v (a - b) ≠ 0) (hv1 : det v (a + u - b) ≠ 0)
    (hu0 : det u (b - a) ≠ 0) (hu1 : det u (b + v - a) ≠ 0) :
    (∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ a + s • u = b + t • v) ↔
    (∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      a + s • u = b + t • v ∧ det u v ≠ 0) := by
  have hon : ∀ (x y w : Plane) (r : ℝ), x = y + r • w → det w (x - y) = 0 := by
    intro x y w r h
    have hs := congrArg (fun z : Plane => z - y) h
    have he : x - y = r • w := by simpa using hs
    rw [he]
    exact det_smul_self w r
  constructor
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, heq⟩
    have hs_ne0 : s ≠ 0 := by
      intro hs
      exact hv0 (hon a b v t (by simpa [hs] using heq))
    have hs_ne1 : s ≠ 1 := by
      intro hs
      exact hv1 (hon (a + u) b v t (by simpa [hs] using heq))
    have ht_ne0 : t ≠ 0 := by
      intro ht
      exact hu0 (hon b a u s (by simpa [ht] using heq.symm))
    have ht_ne1 : t ≠ 1 := by
      intro ht
      exact hu1 (hon (b + v) a u s (by simpa [ht] using heq.symm))
    exact ⟨s, t, lt_of_le_of_ne hs0 hs_ne0.symm, lt_of_le_of_ne hs1 hs_ne1,
      lt_of_le_of_ne ht0 ht_ne0.symm, lt_of_le_of_ne ht1 ht_ne1, heq, hd⟩
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, heq, _⟩
    exact ⟨s, t, hs0.le, hs1.le, ht0.le, ht1.le, heq⟩

/-- The complete local crossing criterion on one common positive interval.
Every height and transversality premise of the segment tests is derived
from the three printed nonzero determinants. No soft-family oracle is used. -/
theorem softLocal_small_crossing_sector (M A B q : Plane)
    (hT : det (M - A) (B - M) ≠ 0)
    (hminus : det (M - A) q ≠ 0) (hplus : det q (B - M) ≠ 0) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      SignType.sign (det (M - A) (softLocalReturn M B q ε)) =
        SignType.sign (det (M - A) (B - M)) ∧
      SignType.sign (det (softLocalReturn M B q ε) (M - A)) =
        -SignType.sign (det (M - A) (B - M)) ∧
      ((∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
        A + s • (M - A) = softLocalPoint M q ε + t • softLocalReturn M B q ε) ↔
        -SignType.sign (det (M - A) q) = SignType.sign (det (M - A) (B - M)) ∧
        -SignType.sign (det q (B - M)) = SignType.sign (det (M - A) (B - M))) ∧
      ((det (M - A) (softLocalPoint M q ε - A) * det (M - A) (B - A) < 0) ↔
        -SignType.sign (det (M - A) q) = SignType.sign (det (M - A) (B - M))) ∧
      ((det (softLocalReturn M B q ε) (A - softLocalPoint M q ε) *
        det (softLocalReturn M B q ε) (M - softLocalPoint M q ε) < 0) ↔
        -SignType.sign (det q (B - M)) = SignType.sign (det (M - A) (B - M))) := by
  obtain ⟨δ, hδ, hpersist⟩ := softLocal_small_signs M A B q hT
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hεabs : |ε| < δ := by simpa only [abs_of_pos hε] using hεδ
  have hs := hpersist ε hεabs
  have hτ : SignType.sign (det (M - A) (B - M)) ≠ 0 := sign_ne_zero.mpr hT
  have hd : det (M - A) (softLocalReturn M B q ε) ≠ 0 :=
    sign_ne_zero.mp (by rw [hs.1]; exact hτ)
  have hA : det (softLocalReturn M B q ε) (A - softLocalPoint M q ε) ≠ 0 :=
    sign_ne_zero.mp (by rw [hs.2]; exact hτ)
  have hM : det (softLocalReturn M B q ε) (M - softLocalPoint M q ε) ≠ 0 := by
    rw [(softLocal_return_heights M A B q ε).1]
    exact mul_ne_zero hε.ne' hplus
  have hnew : det (M - A) (softLocalPoint M q ε - A) ≠ 0 := by
    rw [(softLocal_incoming_heights M A B q ε).1]
    exact mul_ne_zero hε.ne' hminus
  have hB : det (M - A) (B - A) ≠ 0 := by
    rw [(softLocal_incoming_heights M A B q ε).2]
    exact hT
  have hAM : A + (M - A) = M := by abel
  have hclosed := softLocal_closed_iff_strict A (softLocalPoint M q ε)
    (M - A) (softLocalReturn M B q ε) hd hA
    (by rw [hAM]; exact hM) hnew
    (by rw [softLocalPoint_add_return]; exact hB)
  have hreverse : SignType.sign (det (softLocalReturn M B q ε) (M - A)) =
      -SignType.sign (det (M - A) (B - M)) := by
    rw [det_swap, Left.sign_neg, hs.1]
  exact ⟨hs.1, hreverse,
    hclosed.trans (softLocal_interior_crossing_iff M A B q ε hε hT hs.2),
    softLocal_first_straddle_iff M A B q ε hε hT,
    softLocal_second_straddle_iff M A B q ε hε hT hs.2⟩

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

theorem chi_softInsertion_old (P : LabelledTuple n) (j i k l : ZMod n) (q : Plane) (ε : ℝ) :
    chi (softInsertion P j q ε) (softOldIndex j i) (softOldIndex j k) (softOldIndex j l) =
      chi P i k l := by
  simp only [chi, softInsertion_old]

theorem chi_softInsertion_new_zero (P : LabelledTuple n) (j k l : ZMod n) (q : Plane) :
    chi (softInsertion P j q 0) (softNewIndex j) (softOldIndex j k) (softOldIndex j l) =
      chi P j k l := by
  simp only [chi, softInsertion_new, softInsertion_old, zero_smul, add_zero]

theorem area_softInsertion_new_attachment (P : LabelledTuple n) (j k : ZMod n)
    (q : Plane) (ε : ℝ) :
    det (softInsertion P j q ε (softOldIndex j j) - softInsertion P j q ε (softNewIndex j))
      (softInsertion P j q ε (softOldIndex j k) - softInsertion P j q ε (softNewIndex j)) =
      -ε * det q (P k - P j) := by
  rw [softInsertion_old, softInsertion_old, softInsertion_new]
  exact softLocal_new_old_area (P j) (P k) q ε

theorem chi_softInsertion_new_attachment (P : LabelledTuple n) (j k : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) :
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j k) =
      -SignType.sign (det q (P k - P j)) := by
  unfold chi
  rw [area_softInsertion_new_attachment, sign_mul, Left.sign_neg,
    sign_eq_one_iff.mpr hε, neg_one_mul]

/-- A new triple not containing the attachment vertex has the nonzero parent
triple as its limit. Continuity is used only for this specified triple. -/
theorem soft_new_nonattachment_chi_persists {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hkj : k ≠ j) (hlj : l ≠ j) (hkl : k ≠ l) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j k) (softOldIndex j l) =
        chi P j k l := by
  have hz : chi (softInsertion P j q 0) (softNewIndex j) (softOldIndex j k)
      (softOldIndex j l) ≠ 0 := by
    rw [chi_softInsertion_new_zero]
    exact hP j k l (Ne.symm hkj) hkl (Ne.symm hlj)
  have he := ((continuous_softInsertion P j q).continuousAt :
    ContinuousAt (softInsertion P j q) (0 : ℝ)).eventually (chi_locally_constant_of_ne_zero hz)
  simpa only [chi_softInsertion_new_zero] using he

/-- Every new distinct triple is eventually nonzero on the positive side:
attachment triples use the explicit epsilon factor, and the others use G1
at their actual parent limit. -/
theorem soft_new_chi_eventually_nonzero {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) (k l : ZMod n) (hkl : k ≠ l) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j k) (softOldIndex j l) ≠ 0 := by
  by_cases hkj : k = j
  · subst k
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [chi_softInsertion_new_attachment P j l q ε hε]
    exact fun hz => (sign_ne_zero.mpr (hq.2.2 l hkl.symm)) (SignType.neg_eq_zero_iff.mp hz)
  · by_cases hlj : l = j
    · subst l
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [chi_swap_last, chi_softInsertion_new_attachment P j k q ε hε, neg_neg]
      exact sign_ne_zero.mpr (hq.2.2 k hkj)
    · have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j k) (softOldIndex j l) =
          chi P j k l :=
        (soft_new_nonattachment_chi_persists hP j k l q hkj hlj hkl).filter_mono nhdsWithin_le_nhds
      filter_upwards [he] with ε hε
      rw [hε]
      exact hP j k l (Ne.symm hkj) hkl (Ne.symm hlj)

/-- Exhaustive old/new label classification supplies G1 on the actual
enlarged tuple. The hypotheses contain no crossing or genericity oracle. -/
theorem softInsertion_G1_of_new_triples {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (ε : ℝ)
    (hnew : ∀ k l : ZMod n, k ≠ l →
      chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j k) (softOldIndex j l) ≠ 0) :
    G1 (softInsertion P j q ε) := by
  intro a b c hab hbc hac
  rcases soft_indices_exhaust j a with rfl | ⟨i, rfl⟩
  · rcases soft_indices_exhaust j b with rfl | ⟨k, rfl⟩
    · exact (hab rfl).elim
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · exact (hac rfl).elim
      · exact hnew k l (fun h => hbc (congrArg (softOldIndex j) h))
  · rcases soft_indices_exhaust j b with rfl | ⟨k, rfl⟩
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · exact (hbc rfl).elim
      · rw [chi_swap_first]
        exact fun hz => hnew i l (fun h => hac (congrArg (softOldIndex j) h))
          (SignType.neg_eq_zero_iff.mp hz)
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · rw [chi_cyclic]
        exact hnew i k (fun h => hab (congrArg (softOldIndex j) h))
      · rw [chi_softInsertion_old]
        exact hP i k l (fun h => hab (congrArg (softOldIndex j) h))
          (fun h => hbc (congrArg (softOldIndex j) h)) (fun h => hac (congrArg (softOldIndex j) h))

theorem softInsertion_eventually_G1 {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), G1 (softInsertion P j q ε) := by
  have hnew : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ k l : ZMod n, k ≠ l →
      chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j k) (softOldIndex j l) ≠ 0 := by
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro l
    by_cases hkl : k = l
    · exact Eventually.of_forall (fun _ h => (h hkl).elim)
    · exact (soft_new_chi_eventually_nonzero hP j q hq k l hkl).mono (fun _ h _ => h)
  filter_upwards [hnew] with ε hε
  exact softInsertion_G1_of_new_triples hP j q ε hε

/-- A single positive interval works for every triple simultaneously.
This is the G1 part of lem:soft-generic; G2 and the crossing/word clauses
remain separate obligations and are not asserted by this theorem. -/
theorem softInsertion_small_G1 {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → G1 (softInsertion P j q ε) := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (softInsertion_eventually_G1 hP j q hq)
  exact ⟨δ, hδ, fun ε hε hεδ => hsub ⟨hε, hεδ⟩⟩

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Both source attachment chirotopes agree with their parameter-independent
determinant signs for every positive epsilon, with the actual inserted labels. -/
theorem softInsertion_attachment_signs (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) :
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j - 1)) =
      softAttachmentMinus P j q ∧
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j + 1)) =
      softAttachmentPlus P j q := by
  simpa only [chi, softInsertion_new, softInsertion_old, softLocalPoint,
    softAttachmentMinus, softAttachmentPlus, edge, sub_add_cancel] using
    softLocal_attachment_signs (P j) (P (j - 1)) (P (j + 1)) q ε hε

theorem softAttachment_signs_nonzero {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) :
    softAttachmentMinus P j q ≠ 0 ∧ softAttachmentPlus P j q ≠ 0 := by
  exact ⟨fun hz => (sign_ne_zero.mpr hq.1) (SignType.neg_eq_zero_iff.mp hz),
    fun hz => (sign_ne_zero.mpr hq.2.1) (SignType.neg_eq_zero_iff.mp hz)⟩

/-- The turns at the two ends of the actual soft edge have the source signs.
The size hypothesis is used only to keep the incoming parent edge distinct. -/
theorem softInsertion_attachment_turns (hn : 3 ≤ n) (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) :
    turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
    turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hj : j - 1 ≠ j := by
    intro h
    have h1 : (1 : ZMod n) = 0 := by linear_combination -h
    exact one_ne_zero h1
  have hnext := softOldIndex_next j (j - 1) hj
  rw [sub_add_cancel] at hnext
  have hprev : softOldIndex j j - 1 = softOldIndex j (j - 1) := by
    rw [hnext, add_sub_cancel_right]
  have hnewprev : softNewIndex j - 1 = softOldIndex j j := by
    rw [← softOldIndex_attachment_next, add_sub_cancel_right]
  have hs := softLocal_turn_signs (P j) (P (j - 1)) (P (j + 1)) q ε hε
  constructor
  · rw [turn_det, hprev, edge_softInsertion_old P j (j - 1) q ε hj, edge_softInsertion_soft]
    simpa only [softLocalPoint, add_sub_cancel_left, softAttachmentMinus,
      neg_neg, edge, sub_add_cancel] using hs.1
  · rw [turn_det, hnewprev, edge_softInsertion_soft, edge_softInsertion_return]
    simpa only [softLocalPoint, softLocalReturn, add_sub_cancel_left,
      softAttachmentPlus, neg_neg, edge] using hs.2

/-- All defining clauses of the source soft insertion, expressed directly
on its actual cyclic labels. This is a definition interface, not the later
genericity or crossing theorem. -/
theorem soft_insertion_definition (hn : 3 ≤ n) (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) :
    (∀ k : ZMod n, softInsertion P j q ε (softOldIndex j k) = P k) ∧
    softInsertion P j q ε (softNewIndex j) = P j + ε • q ∧
    (∀ k : ZMod n, k ≠ j → edge (softInsertion P j q ε) (softOldIndex j k) = edge P k) ∧
    edge (softInsertion P j q ε) (softOldIndex j j) = ε • q ∧
    edge (softInsertion P j q ε) (softNewIndex j) = edge P j - ε • q ∧
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j - 1)) =
      softAttachmentMinus P j q ∧
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j (j + 1)) =
      softAttachmentPlus P j q ∧
    turn (softInsertion P j q ε) (softOldIndex j j) = -softAttachmentMinus P j q ∧
    turn (softInsertion P j q ε) (softNewIndex j) = -softAttachmentPlus P j q := by
  have hs := softInsertion_attachment_signs P j q ε hε
  have ht := softInsertion_attachment_turns hn P j q ε hε
  exact ⟨fun k => softInsertion_old P j k q ε, softInsertion_new P j q ε,
    fun k hk => edge_softInsertion_old P j k q ε hk, edge_softInsertion_soft P j q ε,
    edge_softInsertion_return P j q ε, hs.1, hs.2, ht.1, ht.2⟩

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Collapse the new occurrence to its attachment label; every old label
is recovered from the proved exhaustive old/new decomposition. -/
def softCollapseIndex (j : ZMod n) (a : ZMod (n + 1)) : ZMod n :=
  if h : a = softNewIndex j then j else
    Classical.choose ((soft_indices_exhaust j a).resolve_left h)

theorem softCollapseIndex_new (j : ZMod n) :
    softCollapseIndex j (softNewIndex j) = j := by
  simp [softCollapseIndex]

theorem softCollapseIndex_old (j k : ZMod n) :
    softCollapseIndex j (softOldIndex j k) = k := by
  unfold softCollapseIndex
  rw [dif_neg (softOldIndex_ne_new j k)]
  apply softOldIndex_injective j
  exact (Classical.choose_spec ((soft_indices_exhaust j (softOldIndex j k)).resolve_left
    (softOldIndex_ne_new j k))).symm

/-- The source's exceptional far sign, defined on all core labels.
Its value at j is unused; admissibility makes every other value nonzero. -/
def softFarSign (P : LabelledTuple n) (j : ZMod n) (q : Plane) (k : ZMod n) : SignType :=
  -SignType.sign (det q (P k - P j))

theorem softFarSign_ne_zero {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) {k : ZMod n} (hk : k ≠ j) :
    softFarSign P j q k ≠ 0 := by
  intro h
  exact (sign_ne_zero.mpr (hq.2.2 k hk)) (SignType.neg_eq_zero_iff.mp h)

/-- These are exactly the reversed triple orders read by the far gates
of (X,A,B) and (A,B,X). They hold for every positive parameter. -/
theorem softFarSign_exceptional (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) (hε : 0 < ε) (k : ZMod n) :
    chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j k) =
      softFarSign P j q k ∧
    chi (softInsertion P j q ε) (softOldIndex j k) (softNewIndex j) (softOldIndex j j) =
      softFarSign P j q k := by
  have h := chi_softInsertion_new_attachment P j k q ε hε
  refine ⟨h, ?_⟩
  exact (chi_cyclic (softInsertion P j q ε) (softOldIndex j k)
    (softNewIndex j) (softOldIndex j j)).symm.trans h

/-- The neighbors are cyclic core neighbors, including the physical wrap.
Their exceptional far values are precisely the two source attachments. -/
theorem softFarSign_neighbors (P : LabelledTuple n) (j : ZMod n) (q : Plane) :
    softFarSign P j q (j - 1) = softAttachmentMinus P j q ∧
    softFarSign P j q (j + 1) = softAttachmentPlus P j q := by
  have hs := softInsertion_attachment_signs P j q 1 (by norm_num)
  exact ⟨(softFarSign_exceptional P j q 1 (by norm_num) (j - 1)).1.symm.trans hs.1,
    (softFarSign_exceptional P j q 1 (by norm_num) (j + 1)).1.symm.trans hs.2⟩

/-- Each ordered distinct child triple avoiding the pair of attachment
occurrences has the same sign as its collapsed core triple near zero.
Old/new exhaustion and alternation cover every order of the new label. -/
theorem soft_chi_pullback_eventually {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (a b c : ZMod (n + 1))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (havoid : ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
      softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1))))) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), chi (softInsertion P j q ε) a b c =
      chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c) := by
  rcases soft_indices_exhaust j a with rfl | ⟨i, rfl⟩
  · rcases soft_indices_exhaust j b with rfl | ⟨k, rfl⟩
    · exact (hab rfl).elim
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · exact (hac rfl).elim
      · have hkj : k ≠ j := by
          intro h; subst k
          exact havoid ⟨by simp, by simp⟩
        have hlj : l ≠ j := by
          intro h; subst l
          exact havoid ⟨by simp, by simp⟩
        have hkl : k ≠ l := fun h => hbc (congrArg (softOldIndex j) h)
        simpa only [softCollapseIndex_new, softCollapseIndex_old] using
          soft_new_nonattachment_chi_persists hP j k l q hkj hlj hkl
  · rcases soft_indices_exhaust j b with rfl | ⟨k, rfl⟩
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · exact (hbc rfl).elim
      · have hij : i ≠ j := by
          intro h; subst i
          exact havoid ⟨by simp, by simp⟩
        have hlj : l ≠ j := by
          intro h; subst l
          exact havoid ⟨by simp, by simp⟩
        have hil : i ≠ l := fun h => hac (congrArg (softOldIndex j) h)
        filter_upwards [soft_new_nonattachment_chi_persists hP j i l q hij hlj hil] with ε hε
        simp only [softCollapseIndex_old, softCollapseIndex_new]
        calc
          chi (softInsertion P j q ε) (softOldIndex j i) (softNewIndex j) (softOldIndex j l) =
              -chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j i)
                (softOldIndex j l) := chi_swap_first _ _ _ _
          _ = -chi P j i l := congrArg (fun s : SignType => -s) hε
          _ = chi P i j l := (chi_swap_first P j i l).symm
    · rcases soft_indices_exhaust j c with rfl | ⟨l, rfl⟩
      · have hij : i ≠ j := by
          intro h; subst i
          exact havoid ⟨by simp, by simp⟩
        have hkj : k ≠ j := by
          intro h; subst k
          exact havoid ⟨by simp, by simp⟩
        have hik : i ≠ k := fun h => hab (congrArg (softOldIndex j) h)
        filter_upwards [soft_new_nonattachment_chi_persists hP j i k q hij hkj hik] with ε hε
        simp only [softCollapseIndex_old, softCollapseIndex_new]
        calc
          chi (softInsertion P j q ε) (softOldIndex j i) (softOldIndex j k) (softNewIndex j) =
              chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j i)
                (softOldIndex j k) := chi_cyclic _ _ _ _
          _ = chi P j i k := hε
          _ = chi P i k j := (chi_cyclic P j i k).symm
      · exact Eventually.of_forall (fun ε => by
          simp only [chi_softInsertion_old, softCollapseIndex_old])

/-- Finiteness of the actual child label set supplies a common neighborhood
for every allowed ordered triple, not one radius chosen per triple. -/
theorem soft_all_chi_pullback_eventually {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ a b c : ZMod (n + 1),
      a ≠ b → b ≠ c → a ≠ c →
      ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
        softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1)))) →
      chi (softInsertion P j q ε) a b c =
        chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c) := by
  apply eventually_all.mpr
  intro a
  apply eventually_all.mpr
  intro b
  apply eventually_all.mpr
  intro c
  by_cases h : a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
        softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1))))
  · exact (soft_chi_pullback_eventually hP j q a b c h.1 h.2.1 h.2.2.1 h.2.2.2).mono
      (fun _ he _ _ _ _ => he)
  · exact Eventually.of_forall (fun _ hab hbc hac ha => (h ⟨hab, hbc, hac, ha⟩).elim)

/-- Root-independent geometric far data for the duplication proof. G1 and
admissibility suffice. The single positive radius supplies child G1 and
all nonexceptional pullbacks; exceptional signs and cyclic neighbor values
are exact. No boundary-word correspondence or child Generic at zero is assumed. -/
theorem soft_far_sign_family (_hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      G1 (softInsertion P j q ε) ∧
      (∀ a b c : ZMod (n + 1), a ≠ b → b ≠ c → a ≠ c →
        ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
          softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1)))) →
        chi (softInsertion P j q ε) a b c =
          chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c)) ∧
      (∀ k : ZMod n, k ≠ j → softFarSign P j q k ≠ 0 ∧
        chi (softInsertion P j q ε) (softNewIndex j) (softOldIndex j j) (softOldIndex j k) =
          softFarSign P j q k ∧
        chi (softInsertion P j q ε) (softOldIndex j k) (softNewIndex j) (softOldIndex j j) =
          softFarSign P j q k) ∧
      softFarSign P j q (j - 1) = softAttachmentMinus P j q ∧
      softFarSign P j q (j + 1) = softAttachmentPlus P j q := by
  obtain ⟨δp, hδp, hp⟩ := Metric.eventually_nhds_iff.mp (soft_all_chi_pullback_eventually hP j q)
  obtain ⟨δg, hδg, hg⟩ := softInsertion_small_G1 hP j q hq
  refine ⟨min δp δg, lt_min hδp hδg, ?_⟩
  intro ε hε hεδ
  have hεp : dist ε (0 : ℝ) < δp := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      (lt_of_lt_of_le hεδ (min_le_left δp δg))
  refine ⟨hg ε hε (lt_of_lt_of_le hεδ (min_le_right δp δg)), hp hεp, ?_,
    (softFarSign_neighbors P j q).1, (softFarSign_neighbors P j q).2⟩
  intro k hk
  exact ⟨softFarSign_ne_zero hq hk, softFarSign_exceptional P j q ε hε k⟩

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Parent j corresponds to the return edge; every other parent edge is
unchanged. The only enlarged edge omitted is the newly inserted soft edge. -/
def softParentEdge (j k : ZMod n) : ZMod (n + 1) :=
  if k = j then softNewIndex j else softOldIndex j k

theorem softParentEdge_at_attachment (j : ZMod n) :
    softParentEdge j j = softNewIndex j := by simp [softParentEdge]

theorem softParentEdge_of_ne (j k : ZMod n) (hk : k ≠ j) :
    softParentEdge j k = softOldIndex j k := by simp [softParentEdge, hk]

theorem softParentEdge_injective (j : ZMod n) : Function.Injective (softParentEdge j) := by
  intro k l h
  by_cases hk : k = j
  · subst k
    by_cases hl : l = j
    · exact hl.symm
    · rw [softParentEdge_at_attachment, softParentEdge_of_ne j l hl] at h
      exact (softOldIndex_ne_new j l h.symm).elim
  · by_cases hl : l = j
    · subst l
      rw [softParentEdge_at_attachment, softParentEdge_of_ne j k hk] at h
      exact (softOldIndex_ne_new j k h).elim
    · rw [softParentEdge_of_ne j k hk, softParentEdge_of_ne j l hl] at h
      exact softOldIndex_injective j h

theorem softParentEdge_ne_soft (j k : ZMod n) :
    softParentEdge j k ≠ softOldIndex j j := by
  by_cases hk : k = j
  · subst k
    rw [softParentEdge_at_attachment]
    exact Ne.symm (softOldIndex_ne_new j j)
  · rw [softParentEdge_of_ne j k hk]
    exact fun h => hk (softOldIndex_injective j h)

theorem soft_parent_edges_exhaust (j : ZMod n) (a : ZMod (n + 1)) :
    a = softOldIndex j j ∨ ∃ k : ZMod n, a = softParentEdge j k := by
  rcases soft_indices_exhaust j a with h | ⟨k, h⟩
  · exact Or.inr ⟨j, h.trans (softParentEdge_at_attachment j).symm⟩
  · by_cases hk : k = j
    · exact Or.inl (hk ▸ h)
    · exact Or.inr ⟨k, h.trans (softParentEdge_of_ne j k hk).symm⟩

/-- Every corresponding parent edge ends at the retained old successor. -/
theorem softParentEdge_next (j k : ZMod n) :
    softParentEdge j k + 1 = softOldIndex j (k + 1) := by
  by_cases hk : k = j
  · subst k
    rw [softParentEdge_at_attachment, softNewIndex_next]
  · rw [softParentEdge_of_ne j k hk, ← softOldIndex_next j k hk]

theorem softParentEdge_next_eq_iff (j k l : ZMod n) :
    softParentEdge j k + 1 = softParentEdge j l ↔ k + 1 = l ∧ l ≠ j := by
  rw [softParentEdge_next]
  by_cases hl : l = j
  · subst l
    rw [softParentEdge_at_attachment]
    simp only [softOldIndex_ne_new, false_and, ne_eq, not_true_eq_false, and_false]
  · rw [softParentEdge_of_ne j l hl]
    exact (softOldIndex_injective j).eq_iff.trans (and_iff_left hl).symm

/-- Splitting one parent edge cannot make a remote parent pair adjacent. -/
theorem softParentEdge_remote (j k l : ZMod n) (hr : remote k l) :
    remote (softParentEdge j k) (softParentEdge j l) := by
  unfold remote adjacent at *
  rintro (hneg | hzero | hpos)
  · have he : softParentEdge j l + 1 = softParentEdge j k := by linear_combination hneg
    have hp := ((softParentEdge_next_eq_iff j l k).mp he).1
    apply hr
    left
    linear_combination hp
  · have he := softParentEdge_injective j (sub_eq_zero.mp hzero)
    apply hr
    exact Or.inr (Or.inl (sub_eq_zero.mpr he))
  · have he : softParentEdge j k + 1 = softParentEdge j l := by linear_combination -hpos
    have hp := ((softParentEdge_next_eq_iff j k l).mp he).1
    apply hr
    right; right
    linear_combination -hp

theorem softInsertion_parent (P : LabelledTuple n) (j k : ZMod n) (q : Plane) (ε : ℝ) :
    softInsertion P j q ε (softParentEdge j k) = P k + if k = j then ε • q else 0 := by
  by_cases hk : k = j
  · subst k
    simp only [softParentEdge_at_attachment, softInsertion_new, ite_true]
  · simp only [softParentEdge_of_ne j k hk, softInsertion_old, hk, ite_false, add_zero]

theorem edge_softInsertion_parent (P : LabelledTuple n) (j k : ZMod n) (q : Plane) (ε : ℝ) :
    edge (softInsertion P j q ε) (softParentEdge j k) =
      edge P k - if k = j then ε • q else 0 := by
  by_cases hk : k = j
  · subst k
    simp only [softParentEdge_at_attachment, edge_softInsertion_return, ite_true]
  · simp only [softParentEdge_of_ne j k hk, edge_softInsertion_old P j k q ε hk,
      hk, ite_false, sub_zero]

/-- Exact affine-parameter correspondence, uniform in the segment parameter. -/
theorem edgePoint_softInsertion_parent (P : LabelledTuple n) (j k : ZMod n) (q : Plane)
    (ε t : ℝ) :
    edgePoint (softInsertion P j q ε) (softParentEdge j k) t =
      edgePoint P k t + if k = j then (1 - t) • (ε • q) else 0 := by
  rw [edgePoint, softInsertion_parent, edge_softInsertion_parent]
  by_cases hk : k = j
  · simp only [hk, ite_true, smul_sub, sub_smul, one_smul, edgePoint]
    abel
  · simp only [hk, ite_false, add_zero, sub_zero, edgePoint]

theorem softInsertion_parent_zero (P : LabelledTuple n) (j k : ZMod n) (q : Plane) :
    softInsertion P j q 0 (softParentEdge j k) = P k := by
  simp only [softInsertion_parent, zero_smul, ite_self, add_zero]

theorem edge_softInsertion_parent_zero (P : LabelledTuple n) (j k : ZMod n) (q : Plane) :
    edge (softInsertion P j q 0) (softParentEdge j k) = edge P k := by
  simp only [edge_softInsertion_parent, zero_smul, ite_self, sub_zero]

theorem edgePoint_softInsertion_parent_zero (P : LabelledTuple n) (j k : ZMod n) (q : Plane)
    (t : ℝ) : edgePoint (softInsertion P j q 0) (softParentEdge j k) t = edgePoint P k t := by
  simp only [edgePoint_softInsertion_parent, zero_smul, smul_zero, ite_self, add_zero]

end
end SM

namespace SM.SoftDuplication

variable {n : ℕ}

/-- Retained occurrence of the distinguished core position. -/
def A (s : Fin n) : Fin (n + 1) := s.castSucc

/-- New occurrence immediately after A in the linear boundary word. -/
def B (s : Fin n) : Fin (n + 1) := s.succ

/-- Increasing old-position embedding that skips precisely B. -/
def old (s : Fin n) : Fin n → Fin (n + 1) := (B s).succAbove

/-- Collapse both occurrences to s, leaving earlier positions fixed and
subtracting one from every later child position. -/
def collapse (s : Fin n) : Fin (n + 1) → Fin n := s.predAbove

@[simp] theorem A_val (s : Fin n) : (A s).val = s.val := rfl

@[simp] theorem B_val (s : Fin n) : (B s).val = s.val + 1 := rfl

theorem A_lt_B (s : Fin n) : A s < B s := by
  change s.val < s.val + 1
  omega

/-- The old embedding includes the retained occurrence A and shifts exactly
the core positions strictly after it. -/
theorem old_val (s k : Fin n) :
    (old s k).val = if k.val ≤ s.val then k.val else k.val + 1 := by
  by_cases h : k ≤ s
  · have hval : k.val ≤ s.val := h
    rw [if_pos hval]
    change (s.succ.succAbove k).val = k.val
    rw [Fin.succAbove_succ_of_le s k h]
    rfl
  · have hval : ¬ k.val ≤ s.val := h
    rw [if_neg hval]
    change (s.succ.succAbove k).val = k.val + 1
    rw [Fin.succAbove_succ_of_lt s k (lt_of_not_ge h)]
    rfl

@[simp] theorem old_self (s : Fin n) : old s s = A s := Fin.succAbove_succ_self s

theorem old_strictMono (s : Fin n) : StrictMono (old s) := Fin.strictMono_succAbove (B s)

theorem old_injective (s : Fin n) : Function.Injective (old s) := (old_strictMono s).injective

theorem old_ne_B (s k : Fin n) : old s k ≠ B s := Fin.succAbove_ne (B s) k

/-- Exact numeric collapse formula, with equality to s on both A and B. -/
theorem collapse_val (s : Fin n) (p : Fin (n + 1)) :
    (collapse s p).val = if p.val ≤ s.val then p.val else p.val - 1 := by
  by_cases h : p.val ≤ s.val
  · rw [if_pos h]
    change (s.predAbove p).val = p.val
    rw [Fin.predAbove_of_le_castSucc s p (show p ≤ s.castSucc from h)]
    rfl
  · rw [if_neg h]
    change (s.predAbove p).val = p.val - 1
    rw [Fin.predAbove_of_castSucc_lt s p
      (show s.castSucc < p from Nat.lt_of_not_ge h)]
    rfl

@[simp] theorem collapse_A (s : Fin n) : collapse s (A s) = s := Fin.predAbove_castSucc_self s

@[simp] theorem collapse_B (s : Fin n) : collapse s (B s) = s := Fin.predAbove_succ_self s

@[simp] theorem collapse_old (s k : Fin n) : collapse s (old s k) = k := by
  change s.predAbove (s.succ.succAbove k) = k
  by_cases h : k ≤ s
  · rw [Fin.succAbove_succ_of_le s k h, Fin.predAbove_castSucc_of_le s k h]
  · rw [Fin.succAbove_succ_of_lt s k (lt_of_not_ge h),
      Fin.predAbove_succ_of_le s k (le_of_lt (lt_of_not_ge h))]

theorem collapse_leftInverse (s : Fin n) : Function.LeftInverse (collapse s) (old s) :=
  collapse_old s

theorem collapse_monotone (s : Fin n) : Monotone (collapse s) := Fin.predAbove_right_monotone s

/-- Every child position except B is recovered by its unique retained old
preimage; the exceptional position is not silently discarded. -/
theorem old_collapse_of_ne_B (s : Fin n) (p : Fin (n + 1)) (hp : p ≠ B s) :
    old s (collapse s p) = p := Fin.succ_succAbove_predAbove hp

theorem child_exhaust (s : Fin n) (p : Fin (n + 1)) :
    p = B s ∨ ∃ k : Fin n, old s k = p := by
  by_cases hp : p = B s
  · exact Or.inl hp
  · exact Or.inr ⟨collapse s p, old_collapse_of_ne_B s p hp⟩

/-- The distinguished core position has exactly the two occurrence preimages. -/
theorem collapse_eq_s_iff (s : Fin n) (p : Fin (n + 1)) :
    collapse s p = s ↔ p = A s ∨ p = B s := by
  constructor
  · intro hc
    by_cases hp : p = B s
    · exact Or.inr hp
    · left
      calc
        p = old s (collapse s p) := (old_collapse_of_ne_B s p hp).symm
        _ = old s s := congrArg (old s) hc
        _ = A s := old_self s
  · rintro (rfl | rfl)
    · exact collapse_A s
    · exact collapse_B s

/-- Every other core position has exactly its one retained old preimage. -/
theorem collapse_eq_iff_of_ne (s k : Fin n) (hk : k ≠ s) (p : Fin (n + 1)) :
    collapse s p = k ↔ p = old s k := by
  constructor
  · intro hc
    have hp : p ≠ B s := by
      intro he
      have hsk : s = k := by simpa only [he, collapse_B] using hc
      exact hk hsk.symm
    exact (old_collapse_of_ne_B s p hp).symm.trans (congrArg (old s) hc)
  · rintro rfl
    exact collapse_old s k

theorem collapse_fiber_s (s : Fin n) :
    (collapse s) ⁻¹' ({s} : Set (Fin n)) = ({A s, B s} : Set (Fin (n + 1))) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff, collapse_eq_s_iff]

theorem collapse_fiber_of_ne (s k : Fin n) (hk : k ≠ s) :
    (collapse s) ⁻¹' ({k} : Set (Fin n)) = ({old s k} : Set (Fin (n + 1))) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, collapse_eq_iff_of_ne s k hk]

/-- For two increasing child positions, equality after collapse occurs
precisely at the ordered consecutive pair A,B. -/
theorem collapse_eq_iff_of_lt (s : Fin n) (p q : Fin (n + 1)) (hpq : p < q) :
    collapse s p = collapse s q ↔ p = A s ∧ q = B s := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    have hpqv : p.val < q.val := hpq
    rw [collapse_val, collapse_val] at hv
    have hvals : p.val = s.val ∧ q.val = s.val + 1 := by
      split_ifs at hv <;> omega
    exact ⟨Fin.ext hvals.1, Fin.ext hvals.2⟩
  · rintro ⟨rfl, rfl⟩
    rw [collapse_A, collapse_B]

theorem collapse_lt_iff_of_lt (s : Fin n) (p q : Fin (n + 1)) (hpq : p < q) :
    collapse s p < collapse s q ↔ ¬ (p = A s ∧ q = B s) := by
  constructor
  · intro hlt he
    exact (ne_of_lt hlt) ((collapse_eq_iff_of_lt s p q hpq).mpr he)
  · intro hne
    apply lt_of_le_of_ne (collapse_monotone s hpq.le)
    intro he
    exact hne ((collapse_eq_iff_of_lt s p q hpq).mp he)

/-- The sole interval whose two endpoints collapse to the same occurrence. -/
def duplicateInterval (s : Fin n) : BoundaryInterval (n + 1) where
  left := A s
  right := B s
  increasing := A_lt_B s

theorem duplicateInterval_leaves (s : Fin n) : (duplicateInterval s).leaves = 1 := by
  simp only [BoundaryInterval.leaves, duplicateInterval, A_val, B_val, Nat.add_sub_cancel_left]

theorem collapse_endpoints_eq_iff (s : Fin n) (I : BoundaryInterval (n + 1)) :
    collapse s I.left = collapse s I.right ↔ I = duplicateInterval s := by
  constructor
  · intro he
    obtain ⟨hl, hr⟩ := (collapse_eq_iff_of_lt s I.left I.right I.increasing).mp he
    cases I with
    | mk l r h =>
      change l = A s at hl
      change r = B s at hr
      cases hl
      cases hr
      rfl
  · rintro rfl
    exact (collapse_A s).trans (collapse_B s).symm

theorem collapse_endpoints_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) : collapse s I.left < collapse s I.right := by
  apply lt_of_le_of_ne (collapse_monotone s I.increasing.le)
  intro he
  exact hI ((collapse_endpoints_eq_iff s I).mp he)

/-- Every other interval has a genuine core boundary interval. Its increasing
endpoint proof is derived; callers do not supply distinct collapsed endpoints. -/
def collapseInterval (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) : BoundaryInterval n where
  left := collapse s I.left
  right := collapse s I.right
  increasing := collapse_endpoints_lt s I hI

theorem collapseInterval_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) :
    (collapseInterval s I hI).left = collapse s I.left ∧
    (collapseInterval s I hI).right = collapse s I.right := ⟨rfl, rfl⟩

end SM.SoftDuplication

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Position of the attachment vertex in the boundary word cut immediately
after the specified parent root. The subtraction is in ZMod n. -/
def softRootPosition (j g : ZMod n) : Fin n :=
  ⟨(j - g - 1).val, ZMod.val_lt _⟩

theorem softRootPosition_index (j g : ZMod n) :
    boundaryIndex g (softRootPosition j g) = j := by
  change g + ((j - g - 1).val : ZMod n) + 1 = j
  rw [ZMod.natCast_zmod_val]
  abel

/-- Moving a specified number of positions in a boundary word moves the
actual cyclic label by that number, including wraparound. -/
theorem softRoot_boundaryIndex_add (g : ZMod n) {a b : Fin n} (d : ℕ)
    (h : b.val = a.val + d) :
    boundaryIndex g b = boundaryIndex g a + (d : ZMod n) := by
  simp only [boundaryIndex, h, Nat.cast_add]
  abel

/-- Successive retained old positions differ by one, except that the step
after the attachment skips the new occurrence and therefore differs by two. -/
theorem softRoot_old_step_val (s : Fin n) (m : ℕ) (hm : m + 1 < n) :
    (SoftDuplication.old s (⟨m + 1, hm⟩ : Fin n)).val =
      (SoftDuplication.old s (⟨m, by omega⟩ : Fin n)).val +
        (if m = s.val then 2 else 1) := by
  simp only [SoftDuplication.old_val]
  split_ifs <;> omega

/-- The actual old-position embedding in every nonsoft-root boundary word.
The proof follows cyclic successors, so no physical-label-zero exception
or freely supplied correspondence is needed. -/
theorem softRootBoundary_old_index (j g : ZMod n) (k : Fin n) :
    boundaryIndex (softParentEdge j g) (SoftDuplication.old (softRootPosition j g) k) =
      softOldIndex j (boundaryIndex g k) := by
  let s := softRootPosition j g
  have hs : boundaryIndex g s = j := softRootPosition_index j g
  have h : ∀ (m : ℕ) (hm : m < n),
      boundaryIndex (softParentEdge j g) (SoftDuplication.old s (⟨m, hm⟩ : Fin n)) =
        softOldIndex j (boundaryIndex g (⟨m, hm⟩ : Fin n)) := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hv : (SoftDuplication.old s (⟨0, hm⟩ : Fin n)).val = 0 := by
        rw [SoftDuplication.old_val]
        simp only [Nat.zero_le, ite_true]
      simp only [boundaryIndex, hv, Nat.cast_zero, add_zero]
      exact softParentEdge_next j g
    | succ m ih =>
      intro hm
      have hm0 : m < n := by omega
      let k0 : Fin n := ⟨m, hm0⟩
      let k1 : Fin n := ⟨m + 1, hm⟩
      have hp : boundaryIndex g k1 = boundaryIndex g k0 + 1 := by
        simpa only [Nat.cast_one] using
          (softRoot_boundaryIndex_add g (a := k0) (b := k1) 1 rfl)
      have hh : boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) =
          softOldIndex j (boundaryIndex g k0) := ih hm0
      have hstep := softRoot_old_step_val s m hm
      change boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
        softOldIndex j (boundaryIndex g k1)
      by_cases he : m = s.val
      · have hk0 : k0 = s := Fin.ext he
        have hj0 : boundaryIndex g k0 = j := by simpa only [hk0] using hs
        have hc : boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
            boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 2 := by
          apply softRoot_boundaryIndex_add (softParentEdge j g) 2
          simpa only [if_pos he] using hstep
        calc
          boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
              boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 2 := hc
          _ = softOldIndex j (boundaryIndex g k0) + 2 := congrArg (fun x => x + 2) hh
          _ = softOldIndex j (j + 1) := by
            rw [hj0]
            calc
              softOldIndex j j + 2 = (softOldIndex j j + 1) + 1 := by ring
              _ = softNewIndex j + 1 := by rw [softOldIndex_attachment_next]
              _ = softOldIndex j (j + 1) := softNewIndex_next j
          _ = softOldIndex j (boundaryIndex g k1) := by rw [hp, hj0]
      · have hj0 : boundaryIndex g k0 ≠ j := by
          intro hj
          have hk0 : k0 = s := boundaryIndex_injective g (hj.trans hs.symm)
          exact he (congrArg Fin.val hk0)
        have hc : boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
            boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 1 := by
          apply softRoot_boundaryIndex_add (softParentEdge j g) 1
          simpa only [if_neg he] using hstep
        calc
          boundaryIndex (softParentEdge j g) (SoftDuplication.old s k1) =
              boundaryIndex (softParentEdge j g) (SoftDuplication.old s k0) + 1 := hc
          _ = softOldIndex j (boundaryIndex g k0) + 1 := congrArg (fun x => x + 1) hh
          _ = softOldIndex j (boundaryIndex g k0 + 1) :=
            (softOldIndex_next j (boundaryIndex g k0) hj0).symm
          _ = softOldIndex j (boundaryIndex g k1) := congrArg (softOldIndex j) hp.symm
  exact h k.val k.isLt

theorem softRootBoundary_A_index (j g : ZMod n) :
    boundaryIndex (softParentEdge j g) (SoftDuplication.A (softRootPosition j g)) =
      softOldIndex j j := by
  have h := softRootBoundary_old_index j g (softRootPosition j g)
  simpa only [SoftDuplication.old_self, softRootPosition_index] using h

/-- The extra position really is the inserted physical vertex, including
when it is the last position for the return-edge root. -/
theorem softRootBoundary_B_index (j g : ZMod n) :
    boundaryIndex (softParentEdge j g) (SoftDuplication.B (softRootPosition j g)) =
      softNewIndex j := by
  have h : boundaryIndex (softParentEdge j g) (SoftDuplication.B (softRootPosition j g)) =
      boundaryIndex (softParentEdge j g) (SoftDuplication.A (softRootPosition j g)) + 1 := by
    apply softRoot_boundaryIndex_add (softParentEdge j g) 1
    rfl
  rw [h, softRootBoundary_A_index, softOldIndex_attachment_next]

/-- Every retained boundary vertex agrees exactly with the parent word;
this is an equality for the actual soft tuple at every real parameter. -/
theorem softRootBoundary_old_word (P : LabelledTuple n) (j g : ZMod n) (q : Plane)
    (ε : ℝ) (k : Fin n) :
    boundaryWord (softInsertion P j q ε) (softParentEdge j g)
      (SoftDuplication.old (softRootPosition j g) k) = boundaryWord P g k := by
  unfold boundaryWord
  rw [softRootBoundary_old_index, softInsertion_old]

theorem softRootBoundary_new_word (P : LabelledTuple n) (j g : ZMod n) (q : Plane)
    (ε : ℝ) :
    boundaryWord (softInsertion P j q ε) (softParentEdge j g)
      (SoftDuplication.B (softRootPosition j g)) = P j + ε • q := by
  rw [boundaryWord, softRootBoundary_B_index, softInsertion_new]

/-- Cutting after the incoming parent edge puts the attachment first. -/
theorem softRootPosition_incoming (j : ZMod n) :
    (softRootPosition j (j - 1)).val = 0 := by
  have h : j - (j - 1) - 1 = (0 : ZMod n) := by abel
  simp only [softRootPosition, h, ZMod.val_zero]

/-- Cutting after the return edge puts the retained attachment last in the
core word, followed by the new occurrence at the last child position. -/
theorem softRootPosition_return (j : ZMod n) :
    (softRootPosition j j).val = n - 1 := by
  have h : j - j - 1 = (-1 : ZMod n) := by abel
  change (j - j - 1).val = n - 1
  rw [h]
  have hn := last_index_val_succ (n := n)
  omega

/-- Every actual child root except the soft edge has a unique parent root
with these proved label and vertex identities. No correspondence is a
caller premise, and the return root is included by softParentEdge. -/
theorem softRootBoundary_nonsoft (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) (a : ZMod (n + 1)) (ha : a ≠ softOldIndex j j) :
    ∃! g : ZMod n, a = softParentEdge j g ∧
      (∀ k : Fin n, boundaryIndex a (SoftDuplication.old (softRootPosition j g) k) =
        softOldIndex j (boundaryIndex g k)) ∧
      boundaryIndex a (SoftDuplication.B (softRootPosition j g)) = softNewIndex j ∧
      (∀ k : Fin n, boundaryWord (softInsertion P j q ε) a
        (SoftDuplication.old (softRootPosition j g) k) = boundaryWord P g k) ∧
      boundaryWord (softInsertion P j q ε) a
        (SoftDuplication.B (softRootPosition j g)) = P j + ε • q := by
  obtain ⟨g, hg⟩ := (soft_parent_edges_exhaust j a).resolve_left ha
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact ⟨rfl, softRootBoundary_old_index j g, softRootBoundary_B_index j g,
      softRootBoundary_old_word P j g q ε, softRootBoundary_new_word P j g q ε⟩
  · intro g' hg'
    exact softParentEdge_injective j (hg'.1.symm.trans hg)

end
end SM

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Collapse remains strictly below s before A. -/
theorem collapse_lt_distinguished (s : Fin n) (p : Fin (n + 1)) (hp : p < A s) :
    collapse s p < s := by
  have h := (collapse_lt_iff_of_lt s p (A s) hp).mpr
    (fun he => (ne_of_lt hp) he.1)
  simpa only [collapse_A] using h

/-- Collapse remains strictly above s after B. -/
theorem distinguished_lt_collapse (s : Fin n) (p : Fin (n + 1)) (hp : B s < p) :
    s < collapse s p := by
  have h := (collapse_lt_iff_of_lt s (B s) p hp).mpr
    (fun he => (ne_of_lt (A_lt_B s)) he.1.symm)
  simpa only [collapse_B] using h

/-- Literal occurrence membership of both duplicated positions in a triple. -/
def tripleContainsBoth (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) : Prop :=
  (T.lower = A s ∨ T.middle = A s ∨ T.upper = A s) ∧
  (T.lower = B s ∨ T.middle = B s ∨ T.upper = B s)

theorem triple_exception_disjoint (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) :
    ¬ ((T.middle = A s ∧ T.upper = B s) ∧ (T.lower = A s ∧ T.middle = B s)) := by
  rintro ⟨hu, hl⟩
  exact (ne_of_lt (A_lt_B s)) (hu.1.symm.trans hl.2)

/-- Consecutiveness rules out A and B as lower/upper with a middle between
them. The two adjacent exceptional placements are therefore exhaustive. -/
theorem triple_contains_both_iff (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) :
    tripleContainsBoth s T ↔
      (T.middle = A s ∧ T.upper = B s) ∨ (T.lower = A s ∧ T.middle = B s) := by
  constructor
  · rintro ⟨hA, hB⟩
    have hlow : T.lower.val < T.middle.val := T.lower_middle
    have hupp : T.middle.val < T.upper.val := T.middle_upper
    rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
      first
      | exact Or.inl ⟨hA, hB⟩
      | exact Or.inr ⟨hA, hB⟩
      | have ha := congrArg Fin.val hA
        have hb := congrArg Fin.val hB
        simp only [A_val, B_val] at ha hb
        omega
  · rintro (⟨hm, hu⟩ | ⟨hl, hm⟩)
    · exact ⟨Or.inr (Or.inl hm), Or.inr (Or.inr hu)⟩
    · exact ⟨Or.inl hl, Or.inr (Or.inl hm)⟩

/-- The plain case has strictly increasing collapsed positions, proved from
the exact sole equality exception of the collapse map. -/
def collapseTriple (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ tripleContainsBoth s T) : IncreasingBoundaryTriple n where
  lower := collapse s T.lower
  middle := collapse s T.middle
  upper := collapse s T.upper
  lower_middle := (collapse_lt_iff_of_lt s T.lower T.middle T.lower_middle).mpr
    (fun hl => hplain ((triple_contains_both_iff s T).mpr (Or.inr hl)))
  middle_upper := (collapse_lt_iff_of_lt s T.middle T.upper T.middle_upper).mpr
    (fun hu => hplain ((triple_contains_both_iff s T).mpr (Or.inl hu)))

theorem collapseTriple_positions (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ tripleContainsBoth s T) :
    (collapseTriple s T hplain).lower = collapse s T.lower ∧
    (collapseTriple s T hplain).middle = collapse s T.middle ∧
    (collapseTriple s T hplain).upper = collapse s T.upper := ⟨rfl, rfl, rfl⟩

def oldTriple (s : Fin n) (T : IncreasingBoundaryTriple n) : IncreasingBoundaryTriple (n + 1) where
  lower := old s T.lower
  middle := old s T.middle
  upper := old s T.upper
  lower_middle := old_strictMono s T.lower_middle
  middle_upper := old_strictMono s T.middle_upper

theorem oldTriple_plain (s : Fin n) (T : IncreasingBoundaryTriple n) :
    ¬ tripleContainsBoth s (oldTriple s T) := by
  intro h
  rcases (triple_contains_both_iff s (oldTriple s T)).mp h with hu | hl
  · exact old_ne_B s T.upper hu.2
  · exact old_ne_B s T.middle hl.2

theorem triple_ext {T U : IncreasingBoundaryTriple n}
    (hl : T.lower = U.lower) (hm : T.middle = U.middle) (hu : T.upper = U.upper) : T = U := by
  cases T with
  | mk l m u h1 h2 =>
    cases U with
    | mk l' m' u' h1' h2' =>
      change l = l' at hl
      change m = m' at hm
      change u = u' at hu
      cases hl
      cases hm
      cases hu
      rfl

theorem collapseTriple_oldTriple (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hplain : ¬ tripleContainsBoth s (oldTriple s T)) :
    collapseTriple s (oldTriple s T) hplain = T := by
  apply triple_ext
  · exact collapse_old s T.lower
  · exact collapse_old s T.middle
  · exact collapse_old s T.upper

/-- The complete source pullback/exceptional array prescription. The two
exceptional pairs are disjoint; every other triple has a proved core triple. -/
def tripleLift {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R) :
    TripleArray (n + 1) R := fun T =>
  if hu : T.middle = A s ∧ T.upper = B s then t (collapse s T.lower)
  else if hl : T.lower = A s ∧ T.middle = B s then t (collapse s T.upper)
  else H0 (collapseTriple s T (fun h =>
    ((triple_contains_both_iff s T).mp h).elim hu hl))

theorem tripleLift_upper {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hu : T.middle = A s ∧ T.upper = B s) :
    tripleLift s H0 t T = t (collapse s T.lower) := by
  simp only [tripleLift, dif_pos hu]

theorem tripleLift_lower {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hl : T.lower = A s ∧ T.middle = B s) :
    tripleLift s H0 t T = t (collapse s T.upper) := by
  have hu : ¬ (T.middle = A s ∧ T.upper = B s) :=
    fun h => triple_exception_disjoint s T ⟨h, hl⟩
  simp only [tripleLift, dif_neg hu, dif_pos hl]

theorem tripleLift_plain {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hplain : ¬ tripleContainsBoth s T) :
    tripleLift s H0 t T = H0 (collapseTriple s T hplain) := by
  have hu : ¬ (T.middle = A s ∧ T.upper = B s) :=
    fun h => hplain ((triple_contains_both_iff s T).mpr (Or.inl h))
  have hl : ¬ (T.lower = A s ∧ T.middle = B s) :=
    fun h => hplain ((triple_contains_both_iff s T).mpr (Or.inr h))
  simp only [tripleLift, dif_neg hu, dif_neg hl]

theorem tripleLift_oldTriple {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple n) : tripleLift s H0 t (oldTriple s T) = H0 T := by
  rw [tripleLift_plain s H0 t (oldTriple s T) (oldTriple_plain s T), collapseTriple_oldTriple]

theorem upper_exception_argument_lt (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hu : T.middle = A s ∧ T.upper = B s) : collapse s T.lower < s :=
  collapse_lt_distinguished s T.lower (lt_of_lt_of_eq T.lower_middle hu.1)

theorem lower_exception_argument_gt (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hl : T.lower = A s ∧ T.middle = B s) : s < collapse s T.upper := by
  apply distinguished_lt_collapse s T.upper
  simpa only [hl.2] using T.middle_upper

/-- The source auxiliary core near array; it is not asserted geometric. -/
def coreNear (s : Fin n) (t : Fin n → ℚ) : TripleArray n ℚ := fun T =>
  if T.middle = s then t T.lower else 0

theorem coreNear_at_middle (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n)
    (hm : T.middle = s) : coreNear s t T = t T.lower := by
  simp only [coreNear, if_pos hm]

theorem coreNear_off_middle (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n)
    (hm : T.middle ≠ s) : coreNear s t T = 0 := by
  simp only [coreNear, if_neg hm]

theorem coreNear_argument_lt (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hm : T.middle = s) : T.lower < s := lt_of_lt_of_eq T.lower_middle hm

/-- The auxiliary parent near array uses the same exact exceptional t-data
and otherwise pulls back coreNear. -/
def parentNear (s : Fin n) (t : Fin n → ℚ) : TripleArray (n + 1) ℚ :=
  tripleLift s (coreNear s t) t

theorem parentNear_oldTriple (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n) :
    parentNear s t (oldTriple s T) = coreNear s t T := tripleLift_oldTriple s _ t T

/-- Both occurrences lie in the closed interval. Since A<B, the other two
endpoint inequalities follow automatically. -/
def intervalContainsBoth (s : Fin n) (I : BoundaryInterval (n + 1)) : Prop :=
  I.left ≤ A s ∧ B s ≤ I.right

theorem intervalContainsBoth_iff (s : Fin n) (I : BoundaryInterval (n + 1)) :
    intervalContainsBoth s I ↔
      (I.left ≤ A s ∧ A s ≤ I.right) ∧ (I.left ≤ B s ∧ B s ≤ I.right) := by
  constructor
  · intro h
    exact ⟨⟨h.1, le_trans (A_lt_B s).le h.2⟩,
      ⟨le_trans h.1 (A_lt_B s).le, h.2⟩⟩
  · intro h
    exact ⟨h.1.1, h.2.2⟩

theorem interval_eq_duplicate (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : I.right = B s) : I = duplicateInterval s := by
  apply (collapse_endpoints_eq_iff s I).mp
  rw [hl, hr, collapse_A, collapse_B]

/-- Exactly the five source rows, with strict exterior endpoints in the
three nonsingleton cases containing both occurrences. -/
theorem interval_five_cases (s : Fin n) (I : BoundaryInterval (n + 1)) :
    (¬ intervalContainsBoth s I) ∨ I = duplicateInterval s ∨
    (I.left = A s ∧ B s < I.right) ∨ (I.left < A s ∧ I.right = B s) ∨
    (I.left < A s ∧ B s < I.right) := by
  by_cases h : intervalContainsBoth s I
  · rcases lt_or_eq_of_le h.1 with hl | hl
    · rcases lt_or_eq_of_le h.2 with hr | hr
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hl, hr⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, hr.symm⟩)))
    · rcases lt_or_eq_of_le h.2 with hr | hr
      · exact Or.inr (Or.inr (Or.inl ⟨hl, hr⟩))
      · exact Or.inr (Or.inl (interval_eq_duplicate s I hl hr.symm))
  · exact Or.inl h

theorem not_duplicate_of_not_contains (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : ¬ intervalContainsBoth s I) : I ≠ duplicateInterval s := by
  rintro rfl
  exact h ⟨le_rfl, le_rfl⟩

theorem not_duplicate_of_right_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : B s < I.right) : I ≠ duplicateInterval s := by
  intro he
  have hb : B s < B s := by simpa only [he, duplicateInterval] using h
  exact (lt_irrefl _) hb

theorem not_duplicate_of_left_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : I.left < A s) : I ≠ duplicateInterval s := by
  intro he
  have ha : A s < A s := by simpa only [he, duplicateInterval] using h
  exact (lt_irrefl _) ha

theorem start_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right) :
    collapse s I.left = s ∧ s < collapse s I.right :=
  ⟨by rw [hl, collapse_A], distinguished_lt_collapse s I.right hr⟩

theorem end_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s) :
    collapse s I.left < s ∧ collapse s I.right = s :=
  ⟨collapse_lt_distinguished s I.left hl, by rw [hr, collapse_B]⟩

theorem span_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : B s < I.right) :
    collapse s I.left < s ∧ s < collapse s I.right :=
  ⟨collapse_lt_distinguished s I.left hl, distinguished_lt_collapse s I.right hr⟩

/-- The proposed five-row ordinary array, defined on every child interval.
The duplicate interval is handled before forming any collapsed interval.
No recurrence or inverse-solution assertion is built into this definition. -/
def ordinaryLift (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) : IntervalArray (n + 1) ℚ := fun I =>
  if hdup : I = duplicateInterval s then 1
  else
    let J := collapseInterval s I hdup
    if intervalContainsBoth s I then
      if I.left = A s then ((etaPlus - t (collapse s I.right)) / 2) * b0 J
      else if I.right = B s then ((etaMinus - t (collapse s I.left)) / 2) * b0 J
      else ((etaMinus + etaPlus) / 2) * b0 J
    else b0 J

theorem ordinaryLift_duplicate (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) : ordinaryLift s etaMinus etaPlus t b0 (duplicateInterval s) = 1 := by
  simp [ordinaryLift]

theorem ordinaryLift_plain (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (h : ¬ intervalContainsBoth s I) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      b0 (collapseInterval s I (not_duplicate_of_not_contains s I h)) := by
  simp only [ordinaryLift, dif_neg (not_duplicate_of_not_contains s I h), if_neg h]

theorem ordinaryLift_start (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaPlus - t (collapse s I.right)) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_right_gt s I hr)) := by
  have hboth : intervalContainsBoth s I := ⟨le_of_eq hl, hr.le⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_right_gt s I hr), if_pos hboth, if_pos hl]

theorem ordinaryLift_end (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaMinus - t (collapse s I.left)) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_left_lt s I hl)) := by
  have hboth : intervalContainsBoth s I := ⟨hl.le, le_of_eq hr.symm⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_left_lt s I hl), if_pos hboth,
    if_neg (ne_of_lt hl), if_pos hr]

theorem ordinaryLift_span (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : B s < I.right) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaMinus + etaPlus) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_left_lt s I hl)) := by
  have hboth : intervalContainsBoth s I := ⟨hl.le, hr.le⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_left_lt s I hl), if_pos hboth,
    if_neg (ne_of_lt hl), if_neg (ne_of_gt hr)]

end
end SM.SoftDuplication

namespace SM.SoftDuplication

/-- Two presentations at an interval starting at the duplicated occurrence.
The intermediate t-value cancels in both ordinary and root transforms. -/
theorem first_ordinary (eta tX tY : ℚ) :
    (eta - tX) / 2 + (tX - tY) / 2 = (eta - tY) / 2 := by
  ring

theorem first_root (eta tX tY : ℚ) :
    (eta - tX) / 2 + (tX + tY) / 2 = (eta + tY) / 2 := by
  ring

/-- The same cancellation applies to the last child, with the last boundary
and exterior endpoint playing the ordered roles from the source. -/
theorem last_ordinary (eta tY tX : ℚ) :
    (eta - tY) / 2 + (tY - tX) / 2 = (eta - tX) / 2 := by
  ring

theorem last_root (eta tY tX : ℚ) :
    (eta - tY) / 2 + (tY + tX) / 2 = (eta + tX) / 2 := by
  ring

/-- The exact residual for a spanning ordinary top before any sign identity.
This is not asserted zero for arbitrary independent far scalars. -/
theorem ordinary_residual (a b h : ℚ) :
    -(a + b) / 2 * ((a - h) / 2) + ((a - h) * (b - h)) / 4 =
      (h ^ 2 - a ^ 2) / 4 := by
  ring

/-- The root residual has the same value with the far signs reversed. -/
theorem root_residual (a b h : ℚ) :
    -(a + b) / 2 * ((a + h) / 2) + ((a + h) * (b + h)) / 4 =
      (h ^ 2 - a ^ 2) / 4 := by
  ring

/-- A nonzero SignType supplies precisely the square identity consumed below. -/
theorem sign_square (a : SignType) (ha : a ≠ 0) :
    (((a : ℤ) : ℚ)) ^ 2 = 1 := by
  cases a <;> norm_num at *

/-- Sum of the B-only, A-only and both-cut presentations at an ordinary top.
Only equality of a^2 and h^2 is needed; b and the neighbor data are arbitrary. -/
theorem three_ordinary (etaMinus etaPlus a b h : ℚ) (hsq : h ^ 2 = a ^ 2) :
    ((etaMinus - a) / 2) * ((a - h) / 2) +
      ((etaPlus - b) / 2) * ((a - h) / 2) +
      ((a - h) / 2) * ((b - h) / 2) =
        ((etaMinus + etaPlus) / 2) * ((a - h) / 2) := by
  calc
    _ = ((etaMinus + etaPlus) / 2) * ((a - h) / 2) +
        (h ^ 2 - a ^ 2) / 4 := by ring
    _ = _ := by rw [hsq]; ring

theorem three_root (etaMinus etaPlus a b h : ℚ) (hsq : h ^ 2 = a ^ 2) :
    ((etaMinus - a) / 2) * ((a + h) / 2) +
      ((etaPlus - b) / 2) * ((a + h) / 2) +
      ((a + h) / 2) * ((b + h) / 2) =
        ((etaMinus + etaPlus) / 2) * ((a + h) / 2) := by
  calc
    _ = ((etaMinus + etaPlus) / 2) * ((a + h) / 2) +
        (h ^ 2 - a ^ 2) / 4 := by ring
    _ = _ := by rw [hsq]; ring

/-- The three-row identities can be multiplied by any common exterior
product, including zero. No cancellation or division by that product occurs. -/
theorem three_ordinary_with_exterior (etaMinus etaPlus a b h F : ℚ)
    (hsq : h ^ 2 = a ^ 2) :
    (((etaMinus - a) / 2) * ((a - h) / 2)) * F +
      (((etaPlus - b) / 2) * ((a - h) / 2)) * F +
      (((a - h) / 2) * ((b - h) / 2)) * F =
        (((etaMinus + etaPlus) / 2) * ((a - h) / 2)) * F := by
  rw [← add_mul, ← add_mul, three_ordinary etaMinus etaPlus a b h hsq]

theorem three_root_with_exterior (etaMinus etaPlus a b h F : ℚ)
    (hsq : h ^ 2 = a ^ 2) :
    (((etaMinus - a) / 2) * ((a + h) / 2)) * F +
      (((etaPlus - b) / 2) * ((a + h) / 2)) * F +
      (((a + h) / 2) * ((b + h) / 2)) * F =
        (((etaMinus + etaPlus) / 2) * ((a + h) / 2)) * F := by
  rw [← add_mul, ← add_mul, three_root etaMinus etaPlus a b h hsq]

end SM.SoftDuplication

namespace SM

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Collapse of every actual root-relative child label, including the new label. -/
theorem softRootBoundary_collapse_index (j g : ZMod n) (p : Fin (n + 1)) :
    softCollapseIndex j (boundaryIndex (softParentEdge j g) p) =
      boundaryIndex g (SoftDuplication.collapse (softRootPosition j g) p) := by
  rcases SoftDuplication.child_exhaust (softRootPosition j g) p with rfl | ⟨k, rfl⟩
  · rw [softRootBoundary_B_index, softCollapseIndex_new, SoftDuplication.collapse_B,
      softRootPosition_index]
  · rw [softRootBoundary_old_index, softCollapseIndex_old, SoftDuplication.collapse_old]

/-- Every position other than B is the retained old occurrence of its collapse. -/
theorem softRootBoundary_old_collapse_index (j g : ZMod n) (p : Fin (n + 1))
    (hp : p ≠ SoftDuplication.B (softRootPosition j g)) :
    boundaryIndex (softParentEdge j g) p =
      softOldIndex j (boundaryIndex g (SoftDuplication.collapse (softRootPosition j g) p)) := by
  have h := softRootBoundary_old_index j g (SoftDuplication.collapse (softRootPosition j g) p)
  rw [SoftDuplication.old_collapse_of_ne_B (softRootPosition j g) p hp] at h
  exact h

/-- The exceptional sign data indexed by the actual parent boundary word. -/
def softRootFarData (P : LabelledTuple n) (j g : ZMod n) (q : Plane) (k : Fin n) : ℚ :=
  ((softFarSign P j q (boundaryIndex g k) : ℤ) : ℚ)

theorem softRootFarData_square {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) (g : ZMod n) (k : Fin n)
    (hk : k ≠ softRootPosition j g) : (softRootFarData P j g q k)^2 = 1 := by
  apply SoftDuplication.sign_square
  apply softFarSign_ne_zero hq
  intro he
  exact hk (boundaryIndex_injective g (he.trans (softRootPosition_index j g).symm))

/-- Core geometric far values are signs on every increasing boundary triple. -/
theorem geometricBoundaryArray_square {P : LabelledTuple n} (hP : G1 P)
    (g : ZMod n) (T : IncreasingBoundaryTriple n) :
    (geometricBoundaryArray (R := ℚ) P g T)^2 = 1 := by
  apply SoftDuplication.sign_square
  apply hP
  · intro h
    exact (ne_of_gt T.middle_upper) (boundaryIndex_injective g h)
  · intro h
    exact (ne_of_gt T.lower_middle) (boundaryIndex_injective g h)
  · intro h
    exact (ne_of_gt (lt_trans T.lower_middle T.middle_upper)) (boundaryIndex_injective g h)

/-- The values at the actual cyclic neighboring labels give both attachments. -/
theorem softRootFarData_neighbors (P : LabelledTuple n) (j g : ZMod n) (q : Plane) :
    softRootFarData P j g q (softRootPosition (j - 1) g) =
      ((softAttachmentMinus P j q : ℤ) : ℚ) ∧
    softRootFarData P j g q (softRootPosition (j + 1) g) =
      ((softAttachmentPlus P j q : ℤ) : ℚ) := by
  simp only [softRootFarData, softRootPosition_index,
    (softFarSign_neighbors P j q).1, (softFarSign_neighbors P j q).2]
  exact ⟨True.intro, True.intro⟩

/-- Plain linear triples avoid precisely the two physical attachment occurrences. -/
theorem softRootBoundary_plain_avoids (j g : ZMod n)
    (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ SoftDuplication.tripleContainsBoth (softRootPosition j g) T) :
    ¬ (softOldIndex j j ∈ ({boundaryIndex (softParentEdge j g) T.upper,
        boundaryIndex (softParentEdge j g) T.middle,
        boundaryIndex (softParentEdge j g) T.lower} : Finset (ZMod (n + 1))) ∧
      softNewIndex j ∈ ({boundaryIndex (softParentEdge j g) T.upper,
        boundaryIndex (softParentEdge j g) T.middle,
        boundaryIndex (softParentEdge j g) T.lower} : Finset (ZMod (n + 1)))) := by
  rintro ⟨ha, hb⟩
  rw [← softRootBoundary_A_index j g] at ha
  rw [← softRootBoundary_B_index j g] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton,
    (boundaryIndex_injective (softParentEdge j g)).eq_iff] at ha hb
  apply hplain
  constructor
  · rcases ha with ha | ha | ha
    · exact Or.inr (Or.inr ha.symm)
    · exact Or.inr (Or.inl ha.symm)
    · exact Or.inl ha.symm
  · rcases hb with hb | hb | hb
    · exact Or.inr (Or.inr hb.symm)
    · exact Or.inr (Or.inl hb.symm)
    · exact Or.inl hb.symm

/-- Upper exceptional triples read the first proved physical exceptional sign. -/
theorem softGeometricBoundaryArray_upper (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) (T : IncreasingBoundaryTriple (n + 1))
    (hu : T.middle = SoftDuplication.A (softRootPosition j g) ∧
      T.upper = SoftDuplication.B (softRootPosition j g)) :
    geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) T =
      softRootFarData P j g q (SoftDuplication.collapse (softRootPosition j g) T.lower) := by
  have hp : T.lower ≠ SoftDuplication.B (softRootPosition j g) :=
    ne_of_lt (lt_of_lt_of_eq (lt_trans T.lower_middle T.middle_upper) hu.2)
  unfold geometricBoundaryArray softRootFarData
  rw [hu.1, hu.2, softRootBoundary_A_index, softRootBoundary_B_index,
    softRootBoundary_old_collapse_index j g T.lower hp,
    (softFarSign_exceptional P j q ε hε _).1]

/-- Lower exceptional triples read the second proved physical exceptional sign. -/
theorem softGeometricBoundaryArray_lower (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) (T : IncreasingBoundaryTriple (n + 1))
    (hl : T.lower = SoftDuplication.A (softRootPosition j g) ∧
      T.middle = SoftDuplication.B (softRootPosition j g)) :
    geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) T =
      softRootFarData P j g q (SoftDuplication.collapse (softRootPosition j g) T.upper) := by
  have hp : T.upper ≠ SoftDuplication.B (softRootPosition j g) :=
    ne_of_gt (lt_of_eq_of_lt hl.2.symm T.middle_upper)
  unfold geometricBoundaryArray softRootFarData
  rw [hl.1, hl.2, softRootBoundary_A_index, softRootBoundary_B_index,
    softRootBoundary_old_collapse_index j g T.upper hp,
    (softFarSign_exceptional P j q ε hε _).2]

/-- A proved common physical pullback specializes to every plain boundary triple. -/
theorem softGeometricBoundaryArray_plain (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) (ε : ℝ)
    (hpull : ∀ a b c : ZMod (n + 1), a ≠ b → b ≠ c → a ≠ c →
      ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
        softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1)))) →
      chi (softInsertion P j q ε) a b c =
        chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c))
    (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ SoftDuplication.tripleContainsBoth (softRootPosition j g) T) :
    geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) T =
      geometricBoundaryArray (R := ℚ) P g
        (SoftDuplication.collapseTriple (softRootPosition j g) T hplain) := by
  have hab : boundaryIndex (softParentEdge j g) T.upper ≠
      boundaryIndex (softParentEdge j g) T.middle := fun h =>
    (ne_of_gt T.middle_upper) (boundaryIndex_injective _ h)
  have hbc : boundaryIndex (softParentEdge j g) T.middle ≠
      boundaryIndex (softParentEdge j g) T.lower := fun h =>
    (ne_of_gt T.lower_middle) (boundaryIndex_injective _ h)
  have hac : boundaryIndex (softParentEdge j g) T.upper ≠
      boundaryIndex (softParentEdge j g) T.lower := fun h =>
    (ne_of_gt (lt_trans T.lower_middle T.middle_upper)) (boundaryIndex_injective _ h)
  have he := hpull _ _ _ hab hbc hac (softRootBoundary_plain_avoids j g T hplain)
  simp only [softRootBoundary_collapse_index] at he
  exact congrArg (fun x : SignType => ((x : ℤ) : ℚ)) he

/-- One positive radius gives the exact formal far array for every parent root.
The array equality and sign hypotheses are derived from the actual polygon.
This is the geometric input to duplication, not its recurrence or output law. -/
theorem soft_geometric_duplication_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      G1 (softInsertion P j q ε) ∧ ∀ g : ZMod n,
      geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) =
        SoftDuplication.tripleLift (softRootPosition j g) (geometricBoundaryArray P g)
          (softRootFarData P j g q) ∧
      (∀ T : IncreasingBoundaryTriple n, (geometricBoundaryArray (R := ℚ) P g T)^2 = 1) ∧
      (∀ k : Fin n, k ≠ softRootPosition j g → (softRootFarData P j g q k)^2 = 1) := by
  obtain ⟨δ, hδ, hf⟩ := soft_far_sign_family hn hP j q hq
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hG, hpull, hrest⟩ := hf ε hε hεδ
  refine ⟨hG, ?_⟩
  intro g
  refine ⟨?_, geometricBoundaryArray_square hP g, softRootFarData_square hq g⟩
  funext T
  by_cases hu : T.middle = SoftDuplication.A (softRootPosition j g) ∧
      T.upper = SoftDuplication.B (softRootPosition j g)
  · rw [SoftDuplication.tripleLift_upper _ _ _ _ hu]
    exact softGeometricBoundaryArray_upper P j g q ε hε T hu
  · by_cases hl : T.lower = SoftDuplication.A (softRootPosition j g) ∧
        T.middle = SoftDuplication.B (softRootPosition j g)
    · rw [SoftDuplication.tripleLift_lower _ _ _ _ hl]
      exact softGeometricBoundaryArray_lower P j g q ε hε T hl
    · have hplain : ¬ SoftDuplication.tripleContainsBoth (softRootPosition j g) T :=
        fun h => ((SoftDuplication.triple_contains_both_iff _ _).mp h).elim hu hl
      rw [SoftDuplication.tripleLift_plain _ _ _ _ hplain]
      exact softGeometricBoundaryArray_plain P j g q ε hpull T hplain

end
end SM

namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The source predecessor is cyclic in the core list, including position zero. -/
def cyclicPred (s : Fin n) : Fin n :=
  ⟨((s.val : ZMod n) - 1).val, ZMod.val_lt _⟩

/-- The source successor is cyclic in the core list, including its last position. -/
def cyclicSucc (s : Fin n) : Fin n :=
  ⟨((s.val : ZMod n) + 1).val, ZMod.val_lt _⟩

theorem cyclicPred_cast (s : Fin n) :
    ((cyclicPred s).val : ZMod n) = (s.val : ZMod n) - 1 :=
  ZMod.natCast_zmod_val _

theorem cyclicSucc_cast (s : Fin n) :
    ((cyclicSucc s).val : ZMod n) = (s.val : ZMod n) + 1 :=
  ZMod.natCast_zmod_val _

theorem cyclicPred_val_of_pos (s : Fin n) (hs : 0 < s.val) :
    (cyclicPred s).val = s.val - 1 := by
  have he : (s.val : ZMod n) - 1 = ((s.val - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s.val), Nat.cast_one]
  change ((s.val : ZMod n) - 1).val = s.val - 1
  rw [he, ZMod.val_natCast_of_lt (by omega : s.val - 1 < n)]

theorem cyclicSucc_val_of_lt (s : Fin n) (hs : s.val + 1 < n) :
    (cyclicSucc s).val = s.val + 1 := by
  have he : (s.val : ZMod n) + 1 = ((s.val + 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_add, Nat.cast_one]
  change ((s.val : ZMod n) + 1).val = s.val + 1
  rw [he, ZMod.val_natCast_of_lt hs]

theorem cyclicPred_val_zero (s : Fin n) (hs : s.val = 0) :
    (cyclicPred s).val = n - 1 := by
  change ((s.val : ZMod n) - 1).val = n - 1
  rw [hs, Nat.cast_zero, zero_sub]
  have hn := SM.last_index_val_succ (n := n)
  omega

theorem cyclicSucc_val_last (s : Fin n) (hs : s.val = n - 1) :
    (cyclicSucc s).val = 0 := by
  have hn : 0 < n := NeZero.pos n
  have he : (s.val : ZMod n) + 1 = (n : ZMod n) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    congr 1
    omega
  change ((s.val : ZMod n) + 1).val = 0
  rw [he, ZMod.natCast_self, ZMod.val_zero]

/-- Neither cyclic neighbor is the distinguished occurrence on the source domain. -/
theorem cyclic_neighbors_ne (hn : 3 ≤ n) (s : Fin n) :
    cyclicPred s ≠ s ∧ cyclicSucc s ≠ s := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    by_cases hs : s.val = 0
    · rw [cyclicPred_val_zero s hs] at hv
      omega
    · rw [cyclicPred_val_of_pos s (by omega)] at hv
      omega
  · intro he
    have hv := congrArg Fin.val he
    by_cases hs : s.val + 1 < n
    · rw [cyclicSucc_val_of_lt s hs] at hv
      omega
    · have hlast : s.val = n - 1 := by omega
      rw [cyclicSucc_val_last s hlast] at hv
      omega

/-- A unit collapsed interval starting at A ends at the actual cyclic successor.
The strict endpoint hypotheses themselves exclude successor wrap here. -/
theorem start_unit_endpoint (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right)
    (hu : (collapseInterval s I (not_duplicate_of_right_gt s I hr)).leaves = 1) :
    collapse s I.right = cyclicSucc s := by
  have hlt : s.val < (collapse s I.right).val := (start_collapsed_bounds s I hl hr).2
  change (collapse s I.right).val - (collapse s I.left).val = 1 at hu
  rw [hl, collapse_A] at hu
  have hv : (collapse s I.right).val = s.val + 1 := by omega
  have hb : s.val + 1 < n := by have := (collapse s I.right).isLt; omega
  apply Fin.ext
  rw [hv, cyclicSucc_val_of_lt s hb]

/-- The analogous unit collapsed interval ending at B begins at the actual
cyclic predecessor, whose no-wrap condition follows from strictness. -/
theorem end_unit_endpoint (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s)
    (hu : (collapseInterval s I (not_duplicate_of_left_lt s I hl)).leaves = 1) :
    collapse s I.left = cyclicPred s := by
  have hlt : (collapse s I.left).val < s.val := (end_collapsed_bounds s I hl hr).1
  change (collapse s I.right).val - (collapse s I.left).val = 1 at hu
  rw [hr, collapse_B] at hu
  have hs : 0 < s.val := by omega
  have hv : (collapse s I.left).val = s.val - 1 := by omega
  apply Fin.ext
  rw [hv, cyclicPred_val_of_pos s hs]

/-- The starting table factor vanishes when the collapsed core interval is
one leaf. No value or nonvanishing assumption on b0 is required. -/
theorem ordinaryLift_start_unit_zero (s : Fin n) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right)
    (hu : (collapseInterval s I (not_duplicate_of_right_gt s I hr)).leaves = 1) :
    ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0 I = 0 := by
  rw [ordinaryLift_start s _ _ t b0 I hl hr, start_unit_endpoint s I hl hr hu]
  simp

theorem ordinaryLift_end_unit_zero (s : Fin n) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s)
    (hu : (collapseInterval s I (not_duplicate_of_left_lt s I hl)).leaves = 1) :
    ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t b0 I = 0 := by
  rw [ordinaryLift_end s _ _ t b0 I hl hr, end_unit_endpoint s I hl hr hu]
  simp

theorem fullInterval_not_duplicate (hn : 3 ≤ n) (s : Fin n) :
    fullBoundaryInterval (by omega : 3 ≤ n + 1) ≠ duplicateInterval s := by
  intro he
  have hl := congrArg (fun J : BoundaryInterval (n + 1) => J.left.val) he
  have hr := congrArg (fun J : BoundaryInterval (n + 1) => J.right.val) he
  simp only [fullBoundaryInterval, duplicateInterval, A_val, B_val] at hl hr
  omega

/-- The entire child word collapses to the entire core word for every placement. -/
theorem collapse_fullInterval (hn : 3 ≤ n) (s : Fin n) :
    collapseInterval s (fullBoundaryInterval (by omega : 3 ≤ n + 1))
      (fullInterval_not_duplicate hn s) = fullBoundaryInterval hn := by
  apply BoundaryInterval.eq_of_endpoints
  · apply Fin.ext
    change (collapse s (⟨0, by omega⟩ : Fin (n + 1))).val = 0
    rw [collapse_val, if_pos (Nat.zero_le _)]
  · apply Fin.ext
    change (collapse s (⟨n + 1 - 1, by omega⟩ : Fin (n + 1))).val = n - 1
    rw [collapse_val, if_neg (by have := s.isLt; omega)]
    omega

end
end SM.SoftDuplication

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryIndex_cyclicPred (g : ZMod n) (s : Fin n) :
    boundaryIndex g (SoftDuplication.cyclicPred s) = boundaryIndex g s - 1 := by
  unfold boundaryIndex
  rw [SoftDuplication.cyclicPred_cast]
  abel

theorem boundaryIndex_cyclicSucc (g : ZMod n) (s : Fin n) :
    boundaryIndex g (SoftDuplication.cyclicSucc s) = boundaryIndex g s + 1 := by
  unfold boundaryIndex
  rw [SoftDuplication.cyclicSucc_cast]
  abel

/-- Literal cyclic core positions coincide with the actual predecessor and
successor labels under every nonsoft-root boundary reading. -/
theorem softRootPosition_cyclic_neighbors (j g : ZMod n) :
    SoftDuplication.cyclicPred (softRootPosition j g) = softRootPosition (j - 1) g ∧
    SoftDuplication.cyclicSucc (softRootPosition j g) = softRootPosition (j + 1) g := by
  constructor
  · apply boundaryIndex_injective g
    rw [boundaryIndex_cyclicPred, softRootPosition_index, softRootPosition_index]
  · apply boundaryIndex_injective g
    rw [boundaryIndex_cyclicSucc, softRootPosition_index, softRootPosition_index]

/-- The formal cyclic eta values are exactly the physical attachment signs. -/
theorem softRootFarData_cyclic_attachments (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) :
    softRootFarData P j g q (SoftDuplication.cyclicPred (softRootPosition j g)) =
      ((softAttachmentMinus P j q : ℤ) : ℚ) ∧
    softRootFarData P j g q (SoftDuplication.cyclicSucc (softRootPosition j g)) =
      ((softAttachmentPlus P j q : ℤ) : ℚ) := by
  rw [(softRootPosition_cyclic_neighbors j g).1, (softRootPosition_cyclic_neighbors j g).2]
  exact softRootFarData_neighbors P j g q

theorem softRootPosition_root_injective (j : ZMod n) :
    Function.Injective (fun g : ZMod n => softRootPosition j g) := by
  intro g h he
  have hg := softRootPosition_index j g
  rw [he] at hg
  have hh := softRootPosition_index j h
  have hx := hg.trans hh.symm
  unfold boundaryIndex at hx
  exact add_right_cancel (add_right_cancel hx)

theorem softRootPosition_first_iff (j g : ZMod n) :
    (softRootPosition j g).val = 0 ↔ g = j - 1 := by
  constructor
  · intro hv
    apply softRootPosition_root_injective j
    apply Fin.ext
    exact hv.trans (softRootPosition_incoming j).symm
  · rintro rfl
    exact softRootPosition_incoming j

theorem softRootPosition_last_iff (j g : ZMod n) :
    (softRootPosition j g).val = n - 1 ↔ g = j := by
  constructor
  · intro hv
    apply softRootPosition_root_injective j
    apply Fin.ext
    exact hv.trans (softRootPosition_return j).symm
  · rintro rfl
    exact softRootPosition_return j

theorem softRootPosition_strict_iff (hn : 3 ≤ n) (j g : ZMod n) :
    (0 < (softRootPosition j g).val ∧ (softRootPosition j g).val < n - 1) ↔
      (g ≠ j - 1 ∧ g ≠ j) := by
  have hfirst := softRootPosition_first_iff j g
  have hlast := softRootPosition_last_iff j g
  have hb := (softRootPosition j g).isLt
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro he; have := hfirst.mpr he; omega
    · intro he; have := hlast.mpr he; omega
  · rintro ⟨hl, hr⟩
    have hz : (softRootPosition j g).val ≠ 0 := fun he => hl (hfirst.mp he)
    have hm : (softRootPosition j g).val ≠ n - 1 := fun he => hr (hlast.mp he)
    omega

/-- The actual full child interval has precisely the incoming-first,
return-last, or strictly spanning placement for its corresponding core root. -/
theorem softRoot_fullInterval_cases (hn : 3 ≤ n) (j g : ZMod n) :
    let I := fullBoundaryInterval (by omega : 3 ≤ n + 1)
    let s := softRootPosition j g
    (g = j - 1 ∧ I.left = SoftDuplication.A s ∧ SoftDuplication.B s < I.right) ∨
    (g = j ∧ I.left < SoftDuplication.A s ∧ I.right = SoftDuplication.B s) ∨
    (g ≠ j - 1 ∧ g ≠ j ∧ I.left < SoftDuplication.A s ∧
      SoftDuplication.B s < I.right) := by
  dsimp only
  by_cases hi : g = j - 1
  · left
    have hs := (softRootPosition_first_iff j g).mpr hi
    refine ⟨hi, ?_, ?_⟩
    · apply Fin.ext
      change 0 = (softRootPosition j g).val
      exact hs.symm
    · change (softRootPosition j g).val + 1 < n + 1 - 1
      omega
  · by_cases hr : g = j
    · right; left
      have hs := (softRootPosition_last_iff j g).mpr hr
      refine ⟨hr, ?_, ?_⟩
      · change 0 < (softRootPosition j g).val
        omega
      · apply Fin.ext
        change n + 1 - 1 = (softRootPosition j g).val + 1
        omega
    · right; right
      obtain ⟨hs0, hsm⟩ := (softRootPosition_strict_iff hn j g).mpr ⟨hi, hr⟩
      refine ⟨hi, hr, ?_, ?_⟩
      · change 0 < (softRootPosition j g).val
        exact hs0
      · change (softRootPosition j g).val + 1 < n + 1 - 1
        omega

end
end SM

#check SM.SoftDuplication.cyclicPred
#print axioms SM.SoftDuplication.cyclicPred
#check SM.SoftDuplication.cyclicSucc
#print axioms SM.SoftDuplication.cyclicSucc
#check SM.SoftDuplication.cyclicPred_cast
#print axioms SM.SoftDuplication.cyclicPred_cast
#check SM.SoftDuplication.cyclicSucc_cast
#print axioms SM.SoftDuplication.cyclicSucc_cast
#check SM.SoftDuplication.cyclicPred_val_of_pos
#print axioms SM.SoftDuplication.cyclicPred_val_of_pos
#check SM.SoftDuplication.cyclicSucc_val_of_lt
#print axioms SM.SoftDuplication.cyclicSucc_val_of_lt
#check SM.SoftDuplication.cyclicPred_val_zero
#print axioms SM.SoftDuplication.cyclicPred_val_zero
#check SM.SoftDuplication.cyclicSucc_val_last
#print axioms SM.SoftDuplication.cyclicSucc_val_last
#check SM.SoftDuplication.cyclic_neighbors_ne
#print axioms SM.SoftDuplication.cyclic_neighbors_ne
#check SM.SoftDuplication.start_unit_endpoint
#print axioms SM.SoftDuplication.start_unit_endpoint
#check SM.SoftDuplication.end_unit_endpoint
#print axioms SM.SoftDuplication.end_unit_endpoint
#check SM.SoftDuplication.ordinaryLift_start_unit_zero
#print axioms SM.SoftDuplication.ordinaryLift_start_unit_zero
#check SM.SoftDuplication.ordinaryLift_end_unit_zero
#print axioms SM.SoftDuplication.ordinaryLift_end_unit_zero
#check SM.SoftDuplication.fullInterval_not_duplicate
#print axioms SM.SoftDuplication.fullInterval_not_duplicate
#check SM.SoftDuplication.collapse_fullInterval
#print axioms SM.SoftDuplication.collapse_fullInterval
#check SM.boundaryIndex_cyclicPred
#print axioms SM.boundaryIndex_cyclicPred
#check SM.boundaryIndex_cyclicSucc
#print axioms SM.boundaryIndex_cyclicSucc
#check SM.softRootPosition_cyclic_neighbors
#print axioms SM.softRootPosition_cyclic_neighbors
#check SM.softRootFarData_cyclic_attachments
#print axioms SM.softRootFarData_cyclic_attachments
#check SM.softRootPosition_root_injective
#print axioms SM.softRootPosition_root_injective
#check SM.softRootPosition_first_iff
#print axioms SM.softRootPosition_first_iff
#check SM.softRootPosition_last_iff
#print axioms SM.softRootPosition_last_iff
#check SM.softRootPosition_strict_iff
#print axioms SM.softRootPosition_strict_iff
#check SM.softRoot_fullInterval_cases
#print axioms SM.softRoot_fullInterval_cases
