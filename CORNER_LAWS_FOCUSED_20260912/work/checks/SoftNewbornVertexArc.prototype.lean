import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.WeakTopology
import SM.WallSegmentStability
import SM.CuspParameters
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import Mathlib.Tactic
import SM.SegmentStability
import SM.G1Consequences
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import SM.GenericTopology
import SM.CyclicChambers
import SM.PairVisits
import SM.Traversal

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

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

theorem continuous_softParent_vertex (P : LabelledTuple n) (j k : ZMod n) (q : Plane) :
    Continuous (fun ε : ℝ => softInsertion P j q ε (softParentEdge j k)) :=
  (continuous_vertex (softParentEdge j k)).comp (continuous_softInsertion P j q)

theorem continuous_softParent_edge (P : LabelledTuple n) (j k : ZMod n) (q : Plane) :
    Continuous (fun ε : ℝ => edge (softInsertion P j q ε) (softParentEdge j k)) :=
  (continuous_edge (softParentEdge j k)).comp (continuous_softInsertion P j q)

theorem softParentParameter_zero (P : LabelledTuple n) (j k l : ZMod n) (q : Plane) :
    edgeParameter (softInsertion P j q 0) (softParentEdge j k) (softParentEdge j l) =
      edgeParameter P k l := by
  simp only [edgeParameter, softInsertion_parent_zero, edge_softInsertion_parent_zero]

/-- Continuity uses the two parent directions, without Generic at the
duplicate-vertex tuple at epsilon zero. -/
theorem continuousAt_softParentParameter (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    ContinuousAt (fun ε : ℝ =>
      edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l)) 0 := by
  have hd0 : det (edge (softInsertion P j q 0) (softParentEdge j k))
      (edge (softInsertion P j q 0) (softParentEdge j l)) ≠ 0 := by
    simpa only [edge_softInsertion_parent_zero] using hd
  exact (continuousAt_edgeParameter_of_det hd0).comp (continuous_softInsertion P j q).continuousAt

theorem softParentParameter_tendsto (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    Tendsto (fun ε : ℝ =>
      edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l))
      (𝓝 (0 : ℝ)) (𝓝 (edgeParameter P k l)) := by
  have h := (continuousAt_softParentParameter P j k l q hd).tendsto
  simpa only [softParentParameter_zero] using h

/-- The supporting-line intersection on the edge corresponding to k. -/
def softInheritedPoint (P : LabelledTuple n) (j k l : ZMod n) (q : Plane) (ε : ℝ) : Plane :=
  edgePoint (softInsertion P j q ε) (softParentEdge j k)
    (edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l))

theorem softInheritedPoint_zero (P : LabelledTuple n) (j k l : ZMod n) (q : Plane) :
    softInheritedPoint P j k l q 0 = edgePoint P k (edgeParameter P k l) := by
  rw [softInheritedPoint, softParentParameter_zero, edgePoint_softInsertion_parent_zero]

theorem continuousAt_softInheritedPoint (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    ContinuousAt (softInheritedPoint P j k l q) (0 : ℝ) :=
  (continuous_softParent_vertex P j k q).continuousAt.add
    ((continuousAt_softParentParameter P j k l q hd).smul
      (continuous_softParent_edge P j k q).continuousAt)

theorem softInheritedPoint_zero_crossing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hc : IsCrossing P {k, l}) :
    softInheritedPoint P j k l q 0 = crossingPoint (⟨{k, l}, hc⟩ : Crossing P) := by
  rw [softInheritedPoint_zero, ← crossingParameter_eq_edgeParameter hn hP hc]
  exact (crossingParameter_spec (⟨{k, l}, hc⟩ : Crossing P) k (by simp)).2.2.symm

theorem softInheritedPoint_tendsto (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hc : IsCrossing P {k, l}) :
    Tendsto (softInheritedPoint P j k l q) (𝓝 (0 : ℝ))
      (𝓝 (crossingPoint (⟨{k, l}, hc⟩ : Crossing P))) := by
  have h := (continuousAt_softInheritedPoint P j k l q
    (crossing_edgeParameter_det_ne_zero hn hP hc)).tendsto
  simpa only [softInheritedPoint_zero_crossing hn hP j k l q hc] using h

theorem softParent_direction_sign_persists (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l)) := by
  have hd0 : det (edge (softInsertion P j q 0) (softParentEdge j k))
      (edge (softInsertion P j q 0) (softParentEdge j l)) ≠ 0 := by
    simpa only [edge_softInsertion_parent_zero] using hd
  have hu := (continuous_softParent_edge P j k q).continuousAt (x := (0 : ℝ))
  have hv := (continuous_softParent_edge P j l q).continuousAt (x := (0 : ℝ))
  have hc := continuousAt_det hu hv
  have hnz := continuousAt_preserves_transversality hu hv hd0
  have hs := ((continuousAt_sign_of_ne_zero hd0).comp
    (f := fun ε : ℝ => det (edge (softInsertion P j q ε) (softParentEdge j k))
      (edge (softInsertion P j q ε) (softParentEdge j l))) hc).eventually
    (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton
      (SignType.sign (det (edge (softInsertion P j q 0) (softParentEdge j k))
        (edge (softInsertion P j q 0) (softParentEdge j l))))))
  filter_upwards [hnz, hs] with ε hε hsε
  refine ⟨hε, ?_⟩
  change SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
    (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge (softInsertion P j q 0) (softParentEdge j k))
        (edge (softInsertion P j q 0) (softParentEdge j l))) at hsε
  simpa only [edge_softInsertion_parent_zero] using hsε

/-- Each actual parent crossing persists with both actual edge parameters
strictly interior and its ordered direction sign unchanged. -/
theorem softParent_crossing_parameters_persist (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hc : IsCrossing P {k, l}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
        edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) < 1) ∧
      (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) ∧
        edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) < 1) ∧
      det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l)) ∧
      IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} := by
  have hd := crossing_edgeParameter_det_ne_zero hn hP hc
  have hrev : IsCrossing P {l, k} := by simpa only [Finset.pair_comm] using hc
  have hdr := crossing_edgeParameter_det_ne_zero hn hP hrev
  have hs := crossingParameter_interior hn hP (⟨{k, l}, hc⟩ : Crossing P) k (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hc] at hs
  have ht := crossingParameter_interior hn hP (⟨{l, k}, hrev⟩ : Crossing P) l (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hrev] at ht
  have hse := continuousAt_preserves_unit_interval (continuousAt_softParentParameter P j k l q hd)
    (by simpa only [softParentParameter_zero] using hs.1)
    (by simpa only [softParentParameter_zero] using hs.2)
  have hte := continuousAt_preserves_unit_interval (continuousAt_softParentParameter P j l k q hdr)
    (by simpa only [softParentParameter_zero] using ht.1)
    (by simpa only [softParentParameter_zero] using ht.2)
  filter_upwards [hse, hte, softParent_direction_sign_persists P j k l q hd] with ε hsε htε hdε
  refine ⟨hsε, htε, hdε.1, hdε.2, ?_⟩
  refine ⟨softParentEdge j k, softParentEdge j l, rfl,
    softParentEdge_remote j k l (crossing_pair_remote hc), ?_⟩
  refine ⟨softInheritedPoint P j k l q ε, ⟨_, hsε.1.le, hsε.2.le, rfl⟩,
    ⟨_, htε.1.le, htε.2.le, ?_⟩⟩
  exact edgeParameters_intersection (softInsertion P j q ε) _ _ hdε.1

/-- Identification with the canonical crossing point, independently of
which proof witnesses this inherited crossing. Child G1 is explicit here. -/
theorem softInheritedPoint_eq_crossingPoint (hn : 3 ≤ n) (P : LabelledTuple n)
    (j k l : ZMod n) (q : Plane) (ε : ℝ) (hQ : G1 (softInsertion P j q ε))
    (hc : IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l}) :
    softInheritedPoint P j k l q ε =
      crossingPoint (⟨{softParentEdge j k, softParentEdge j l}, hc⟩ :
        Crossing (softInsertion P j q ε)) := by
  rw [softInheritedPoint, ← crossingParameter_eq_edgeParameter (by omega : 3 ≤ n + 1) hQ hc]
  exact (crossingParameter_spec (⟨{softParentEdge j k, softParentEdge j l}, hc⟩ :
    Crossing (softInsertion P j q ε)) (softParentEdge j k) (by simp)).2.2.symm

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Every remote parent pair keeps its closed-segment intersection status.
The disjoint branch permits parallel directions and needs only compactness. -/
theorem soft_parent_pair_intersection_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hr : remote k l) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      (edgeSegment (softInsertion P j q ε) (softParentEdge j k) ∩
        edgeSegment (softInsertion P j q ε) (softParentEdge j l)).Nonempty ↔
      (edgeSegment P k ∩ edgeSegment P l).Nonempty := by
  by_cases hc : IsCrossing P {k, l}
  · have he := softParent_crossing_parameters_persist hn hP j k l q hc
    filter_upwards [he] with ε hε
    exact iff_of_true ((isCrossing_pair _ _ _ (softParentEdge_remote j k l hr)).mp hε.2.2.2.2)
      ((isCrossing_pair P k l hr).mp hc)
  · have hd : ¬ segmentsMeet (P k) (P l) (edge P k) (edge P l) := by
      intro hm
      exact hc ((isCrossing_pair P k l hr).mpr ((segmentsMeet_edges_iff P k l).mp hm))
    have hd0 : ¬ segmentsMeet (softInsertion P j q 0 (softParentEdge j k))
        (softInsertion P j q 0 (softParentEdge j l))
        (edge (softInsertion P j q 0) (softParentEdge j k))
        (edge (softInsertion P j q 0) (softParentEdge j l)) := by
      simpa only [softInsertion_parent_zero, edge_softInsertion_parent_zero] using hd
    have he := disjoint_segments_persist
      (continuous_softParent_vertex P j k q).continuousAt
      (continuous_softParent_vertex P j l q).continuousAt
      (continuous_softParent_edge P j k q).continuousAt
      (continuous_softParent_edge P j l q).continuousAt hd0
    filter_upwards [he] with ε hε
    exact iff_of_false
      (fun hm => hε ((segmentsMeet_edges_iff _ _ _).mpr hm))
      (fun hm => hd ((segmentsMeet_edges_iff P k l).mpr hm))

theorem soft_parent_crossing_pair_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hr : remote k l) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} ↔
        IsCrossing P {k, l} := by
  filter_upwards [soft_parent_pair_intersection_persists hn hP j k l q hr] with ε hε
  rw [isCrossing_pair _ _ _ (softParentEdge_remote j k l hr), isCrossing_pair P k l hr]
  exact hε

theorem soft_all_remote_pairs_persist (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k l : ZMod n, remote k l →
      (IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} ↔
        IsCrossing P {k, l}) := by
  apply eventually_all.mpr
  intro k
  apply eventually_all.mpr
  intro l
  by_cases hr : remote k l
  · exact (soft_parent_crossing_pair_persists hn hP j k l q hr).mono (fun _ h _ => h)
  · exact Eventually.of_forall (fun _ h => (hr h).elim)

theorem soft_small_remote_pairs (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → ∀ k l : ZMod n, remote k l →
      (IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} ↔
        IsCrossing P {k, l}) := by
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp
    (soft_all_remote_pairs_persist hn hP j q)
  exact ⟨δ, hδ, fun ε hε => hmem (by simpa only [Real.dist_eq, sub_zero] using hε)⟩

/-- Parent G2 supplies strict separation of distinct crossing visits on
one edge. Their actual transported parameters therefore retain their order. -/
theorem soft_inherited_parameter_order (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j k l m : ZMod n) (q : Plane) (hlm : l ≠ m)
    (hkl : IsCrossing P {k, l}) (hkm : IsCrossing P {k, m}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      (edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) <
        edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j m) ↔
      edgeParameter P k l < edgeParameter P k m) := by
  have hl := continuousAt_softParentParameter P j k l q
    (crossing_edgeParameter_det_ne_zero hn hP.1 hkl)
  have hm := continuousAt_softParentParameter P j k m q
    (crossing_edgeParameter_det_ne_zero hn hP.1 hkm)
  have hne := generic_edgeParameters_ne hn hP hlm hkl hkm
  have he := continuousAt_preserves_parameter_order hl hm
    (by simpa only [softParentParameter_zero] using hne)
  simpa only [softParentParameter_zero] using he

/-- A single neighborhood preserves every inherited comparison, including
the identical-visit case. Child Generic is not assumed. -/
theorem soft_all_inherited_orders_persist (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k l m : ZMod n,
      IsCrossing P {k, l} → IsCrossing P {k, m} →
      (edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) <
        edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j m) ↔
      edgeParameter P k l < edgeParameter P k m) := by
  apply eventually_all.mpr
  intro k
  apply eventually_all.mpr
  intro l
  apply eventually_all.mpr
  intro m
  by_cases hkl : IsCrossing P {k, l}
  · by_cases hkm : IsCrossing P {k, m}
    · by_cases hlm : l = m
      · subst m
        exact Eventually.of_forall (fun _ _ _ => by simp only [lt_self_iff_false])
      · exact (soft_inherited_parameter_order hn hP j k l m q hlm hkl hkm).mono
          (fun _ h _ _ => h)
    · exact Eventually.of_forall (fun _ _ h => (hkm h).elim)
  · exact Eventually.of_forall (fun _ h _ => (hkl h).elim)

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

/-- In the actual enlarged word, the return edge starts two cyclic labels
after the incoming edge, with the soft edge between them. -/
theorem softIncoming_return_difference (hn : 3 ≤ n) (j : ZMod n) :
    softNewIndex j - softOldIndex j (j - 1) = (2 : ZMod (n + 1)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hnext := softOldIndex_next j (j - 1) (prev_ne_self j)
  simp only [sub_add_cancel] at hnext
  rw [← softOldIndex_attachment_next j, hnext]
  ring

/-- The incoming/return pair is actually remote, including at parent
arity three and at every physical wrap position. -/
theorem softIncoming_return_remote (hn : 3 ≤ n) (j : ZMod n) :
    remote (softOldIndex j (j - 1)) (softNewIndex j) := by
  unfold remote adjacent
  rw [softIncoming_return_difference hn j]
  rintro (hneg | hzero | hpos)
  · have h3 : (3 : ZMod (n + 1)) = 0 := by linear_combination hneg
    have hd : n + 1 ∣ 3 := (ZMod.natCast_eq_zero_iff 3 (n + 1)).mp (by simpa using h3)
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  · have hd : n + 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (n + 1)).mp (by simpa using hzero)
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  · have h1 : (1 : ZMod (n + 1)) = 0 := by linear_combination hpos
    have hd : n + 1 ∣ 1 := (ZMod.natCast_eq_zero_iff 1 (n + 1)).mp (by simpa using h1)
    have hle := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega

/-- Exact translation of the two actual closed edge segments to their
local point-and-direction parameter equations; every real parameter is allowed. -/
theorem softIncoming_return_segment_parameters (hn : 3 ≤ n)
    (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) :
    (edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) ∩
      edgeSegment (softInsertion P j q ε) (softNewIndex j)).Nonempty ↔
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
      P (j - 1) + s • (P j - P (j - 1)) =
        softLocalPoint (P j) q ε + t • softLocalReturn (P j) (P (j + 1)) q ε := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hin (s : ℝ) :
      edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1)) s =
        P (j - 1) + s • (P j - P (j - 1)) := by
    rw [edgePoint, softInsertion_old,
      edge_softInsertion_old P j (j - 1) q ε (prev_ne_self j)]
    simp only [edge, sub_add_cancel]
  have hout (t : ℝ) :
      edgePoint (softInsertion P j q ε) (softNewIndex j) t =
        softLocalPoint (P j) q ε + t • softLocalReturn (P j) (P (j + 1)) q ε := by
    rw [edgePoint, softInsertion_new, edge_softInsertion_return]
    rfl
  constructor
  · rintro ⟨x, ⟨s, hs0, hs1, hs⟩, ⟨t, ht0, ht1, ht⟩⟩
    refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
    have he := hs.symm.trans ht
    rwa [hin s, hout t] at he
  · rintro ⟨s, t, hs0, hs1, ht0, ht1, he⟩
    refine ⟨edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1)) s,
      ⟨s, hs0, hs1, rfl⟩, ⟨t, ht0, ht1, ?_⟩⟩
    rw [hin s, hout t]
    exact he

/-- Local incoming/return crossing part of lem:soft-generic. The geometric
inputs are only parent G1 and the actual source admissibility predicate.
No genericity of the enlarged tuple or other soft-family claim is assumed.
This theorem concerns this one pair, not an enumeration of all crossings. -/
theorem softFamily_local_crossing (hn : 3 ≤ n) (P : LabelledTuple n) (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ((edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) ∩
          edgeSegment (softInsertion P j q ε) (softNewIndex j)).Nonempty ↔
        softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ∧
      (IsCrossing (softInsertion P j q ε) {softOldIndex j (j - 1), softNewIndex j} ↔
        softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hT : det (P j - P (j - 1)) (P (j + 1) - P j) ≠ 0 := by
    simpa only [edge, sub_add_cancel] using g1_turn_nonzero hn hP j
  have hm : det (P j - P (j - 1)) q ≠ 0 := by
    simpa only [edge, sub_add_cancel] using hq.1
  have hp : det q (P (j + 1) - P j) ≠ 0 := hq.2.1
  obtain ⟨δ, hδ, hlocal⟩ := softLocal_small_crossing_sector
    (P j) (P (j - 1)) (P (j + 1)) q hT hm hp
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hsector := (hlocal ε hε hεδ).2.2.1
  have hc :
      (edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) ∩
        edgeSegment (softInsertion P j q ε) (softNewIndex j)).Nonempty ↔
      softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j := by
    rw [softIncoming_return_segment_parameters hn P j q ε]
    simpa only [softAttachmentMinus, softAttachmentPlus, turn_det, edge, sub_add_cancel] using hsector
  exact ⟨hc, (isCrossing_pair (softInsertion P j q ε)
    (softOldIndex j (j - 1)) (softNewIndex j) (softIncoming_return_remote hn j)).trans hc⟩

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- The shrinking soft segment is disjoint from every parent edge not
incident to the attachment vertex. Compact closed-segment stability applies
even though the soft direction is zero at the limiting parameter. -/
theorem softEdge_disjoint_old_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k : ZMod n) (q : Plane) (hkj : k ≠ j) (hkp : k ≠ j - 1) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) (softOldIndex j k)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hjnext : j ≠ k + 1 := by
    intro h
    apply hkp
    linear_combination -h
  have hoff := g1_vertex_not_mem_edge hP k j (next_ne_self k).symm (Ne.symm hkj) hjnext
  have hd : ¬ segmentsMeet (P j) (P k) ((0 : ℝ) • q) (edge P k) := by
    rintro ⟨s, t, _, _, ht0, ht1, he⟩
    apply hoff
    refine ⟨t, ht0, ht1, ?_⟩
    simpa only [zero_smul, smul_zero, add_zero, edgePoint] using he
  have he := disjoint_segments_persist
    (a := fun _ : ℝ => P j) (b := fun _ : ℝ => P k)
    (u := fun ε : ℝ => ε • q) (v := fun _ : ℝ => edge P k)
    continuousAt_const continuousAt_const (by fun_prop) continuousAt_const hd
  filter_upwards [he] with ε hε
  apply Set.disjoint_left.mpr
  rintro x ⟨s, hs0, hs1, hs⟩ ⟨t, ht0, ht1, ht⟩
  apply hε
  refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
  simpa only [edgePoint, softInsertion_old, edge_softInsertion_soft,
    edge_softInsertion_old P j k q ε hkj] using hs.symm.trans ht

theorem softEdge_disjoint_all_old_persists (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k : ZMod n, k ≠ j → k ≠ j - 1 →
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) (softOldIndex j k)) := by
  apply eventually_all.mpr
  intro k
  by_cases hk : k = j
  · exact Eventually.of_forall (fun _ h _ => (h hk).elim)
  · by_cases hp : k = j - 1
    · exact Eventually.of_forall (fun _ _ h => (h hp).elim)
    · exact (softEdge_disjoint_old_persists hn hP j k q hk hp).mono (fun _ h _ _ => h)

/-- The complete soft-edge contact clause: its only contacts with other
edges are precisely the two incident endpoints, on one positive interval.
The exclusion quantifies over every enlarged edge, using exhaustive labels. -/
theorem softEdge_only_incident_contacts (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
        edgeSegment (softInsertion P j q ε) (softOldIndex j (j - 1)) = {P j} ∧
      edgeSegment (softInsertion P j q ε) (softOldIndex j j) ∩
        edgeSegment (softInsertion P j q ε) (softNewIndex j) = {P j + ε • q} ∧
      ∀ a : ZMod (n + 1), a ≠ softOldIndex j j → a ≠ softOldIndex j (j - 1) →
        a ≠ softNewIndex j →
        Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
          (edgeSegment (softInsertion P j q ε) a) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  haveI : Fact (1 < n + 1) := ⟨by omega⟩
  obtain ⟨δ₁, hδ₁, hdisjoint⟩ := Metric.eventually_nhds_iff.mp
    (softEdge_disjoint_all_old_persists hn hP j q)
  obtain ⟨δ₂, hδ₂, hG1⟩ := softInsertion_small_G1 hP j q hq
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ε hε hεδ
  have hε₁ : dist ε 0 < δ₁ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using
      lt_of_lt_of_le hεδ (min_le_left δ₁ δ₂)
  have hg := hG1 ε hε (lt_of_lt_of_le hεδ (min_le_right δ₁ δ₂))
  have hi := g1_successive_intersection (by omega : 3 ≤ n + 1) hg (softOldIndex j (j - 1))
  have hs := softOldIndex_next j (j - 1) (prev_ne_self j)
  rw [sub_add_cancel] at hs
  rw [← hs, softInsertion_old] at hi
  have hr := g1_successive_intersection (by omega : 3 ≤ n + 1) hg (softOldIndex j j)
  rw [softOldIndex_attachment_next, softInsertion_new] at hr
  refine ⟨?_, hr, ?_⟩
  · simpa only [Set.inter_comm] using hi
  · intro a ha hp hnew
    rcases soft_indices_exhaust j a with he | ⟨k, rfl⟩
    · exact (hnew he).elim
    · exact hdisjoint hε₁ k (fun h => ha (congrArg (softOldIndex j) h))
        (fun h => hp (congrArg (softOldIndex j) h))

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- The only formerly adjacent parent pair made remote is incoming/return,
in either order. Every other remote pair was already remote in the parent. -/
theorem softParentEdge_remote_cases (hn : 3 ≤ n) (j k l : ZMod n)
    (hr : remote (softParentEdge j k) (softParentEdge j l)) :
    remote k l ∨ (k = j - 1 ∧ l = j) ∨ (k = j ∧ l = j - 1) := by
  by_cases hp : remote k l
  · exact Or.inl hp
  · have hadj : adjacent k l := by simpa only [remote, not_not] using hp
    have hne : k ≠ l := by
      intro he
      exact (remote_endpoints _ _ hr).1 (congrArg (softParentEdge j) he.symm)
    rcases adjacent_distinct_cases hne hadj with he | he
    · have hlj : l = j := by
        by_contra hlj
        have hnext := (softParentEdge_next_eq_iff j k l).mpr ⟨he.symm, hlj⟩
        exact (remote_endpoints _ _ hr).2.1 hnext.symm
      right; left
      refine ⟨?_, hlj⟩
      rw [hlj] at he
      linear_combination -he
    · have hkj : k = j := by
        by_contra hkj
        have hnext := (softParentEdge_next_eq_iff j l k).mpr ⟨he.symm, hkj⟩
        exact (remote_endpoints _ _ hr).2.2.1 hnext
      right; right
      refine ⟨hkj, ?_⟩
      rw [hkj] at he
      linear_combination -he

/-- Complete enumeration of actual enlarged crossing supports. Every
inherited support is present; the sole possible extra support is the actual
incoming/return pair, and it occurs exactly in the loop sector. -/
theorem soft_crossing_support_classification (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → ∀ s : Finset (ZMod (n + 1)),
      IsCrossing (softInsertion P j q ε) s ↔
        (∃ k l : ZMod n, IsCrossing P {k, l} ∧ s = {softParentEdge j k, softParentEdge j l}) ∨
        (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ∧
          s = {softOldIndex j (j - 1), softNewIndex j} := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨δr, hδr, hremote⟩ := soft_small_remote_pairs hn hP j q
  obtain ⟨δl, hδl, hlocal⟩ := softFamily_local_crossing hn P hP j q hq
  obtain ⟨δs, hδs, hsoft⟩ := softEdge_only_incident_contacts hn hP j q hq
  refine ⟨min δr (min δl δs), lt_min hδr (lt_min hδl hδs), ?_⟩
  intro ε hε hεδ
  have hεr : |ε| < δr := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δr (min δl δs))
  have hεl : ε < δl := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δr (min δl δs)) (min_le_left δl δs))
  have hεs : ε < δs := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δr (min δl δs)) (min_le_right δl δs))
  have hmiss (a : ZMod (n + 1)) (ha : remote (softOldIndex j j) a) :
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) a) := by
    apply (hsoft ε hε hεs).2.2 a (remote_endpoints _ _ ha).1
    · intro he
      apply (remote_endpoints _ _ ha).2.2.1
      rw [he, ← softOldIndex_next j (j - 1) (prev_ne_self j), sub_add_cancel]
    · intro he
      apply (remote_endpoints _ _ ha).2.1
      rw [he, softOldIndex_attachment_next]
  intro s
  constructor
  · rintro ⟨a, b, hs, hr, hm⟩
    rcases soft_parent_edges_exhaust j a with rfl | ⟨k, rfl⟩
    · obtain ⟨x, hx, hy⟩ := hm
      exact (Set.disjoint_left.mp (hmiss b hr) hx hy).elim
    · rcases soft_parent_edges_exhaust j b with rfl | ⟨l, rfl⟩
      · obtain ⟨x, hx, hy⟩ := hm
        exact (Set.disjoint_left.mp (hmiss _ (remote_symm hr)) hy hx).elim
      · have hc : IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} :=
          ⟨_, _, rfl, hr, hm⟩
        rcases softParentEdge_remote_cases hn j k l hr with hp | ⟨hk, hl⟩ | ⟨hk, hl⟩
        · exact Or.inl ⟨k, l, (hremote ε hεr k l hp).mp hc, hs⟩
        · subst k; subst l
          have hc' : IsCrossing (softInsertion P j q ε)
              {softOldIndex j (j - 1), softNewIndex j} := by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment] using hc
          exact Or.inr ⟨(hlocal ε hε hεl).2.mp hc', by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment] using hs⟩
        · subst k; subst l
          have hc' : IsCrossing (softInsertion P j q ε)
              {softOldIndex j (j - 1), softNewIndex j} := by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment, Finset.pair_comm] using hc
          exact Or.inr ⟨(hlocal ε hε hεl).2.mp hc', by
            simpa only [softParentEdge_of_ne j (j - 1) (prev_ne_self j),
              softParentEdge_at_attachment, Finset.pair_comm] using hs⟩
  · rintro (⟨k, l, hc, rfl⟩ | ⟨hloop, rfl⟩)
    · exact (hremote ε hεr k l (crossing_pair_remote hc)).mpr hc
    · exact (hlocal ε hε hεl).2.mpr hloop

/-- The newborn support cannot be the image of any actual parent crossing.
Thus the support classification adds exactly one support in the loop sector. -/
theorem soft_newborn_support_not_inherited (hn : 3 ≤ n) (P : LabelledTuple n)
    (j k l : ZMod n) (hc : IsCrossing P {k, l}) :
    ({softParentEdge j k, softParentEdge j l} : Finset (ZMod (n + 1))) ≠
      {softOldIndex j (j - 1), softNewIndex j} := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro he
  have himage : ({k, l} : Finset (ZMod n)).image (softParentEdge j) =
      ({j - 1, j} : Finset (ZMod n)).image (softParentEdge j) := by
    simpa only [Finset.image_insert, Finset.image_singleton,
      softParentEdge_of_ne j (j - 1) (prev_ne_self j), softParentEdge_at_attachment] using he
  have hpair := Finset.image_injective (softParentEdge_injective j) himage
  rw [hpair] at hc
  have hr := crossing_pair_remote hc
  exact (remote_endpoints (j - 1) j hr).2.1 (sub_add_cancel j 1).symm

end
end SM

namespace SM

noncomputable section
open Set Filter Topology
variable {n : ℕ} [NeZero n]

/-- Three distinct closed edges cannot have a common point if one pair is
adjacent: its shared vertex lies on no third edge under G1. -/
theorem g1_no_adjacent_closedTripleMeet (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (ha : adjacent i j) : ¬ ClosedTripleMeet P i j k := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rintro ⟨x, hi, hj, hk⟩
  have hmem : x ∈ edgeSegment P i ∩ edgeSegment P j := ⟨hi, hj⟩
  rcases g1_adjacent_intersection hn hP hij ha with ⟨he, hset⟩ | ⟨he, hset⟩
  · rw [hset] at hmem
    have hx : x = P j := hmem
    have hjnext : j ≠ k + 1 := by
      intro h
      exact hik (add_right_cancel (he.symm.trans h))
    exact (g1_vertex_not_mem_edge hP k j (next_ne_self k).symm hjk hjnext) (hx ▸ hk)
  · rw [hset] at hmem
    have hx : x = P i := hmem
    have hinext : i ≠ k + 1 := by
      intro h
      exact hjk (add_right_cancel (he.symm.trans h))
    exact (g1_vertex_not_mem_edge hP k i (next_ne_self k).symm hik hinext) (hx ▸ hk)

/-- Parent Generic excludes all distinct closed triples, not just the
pairwise remote triples mentioned in the canonical G2 characterization. -/
theorem generic_no_distinct_closedTripleMeet (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ ClosedTripleMeet P i j k := by
  classical
  haveI : Fact (1 < n) := ⟨by omega⟩
  by_cases hr1 : remote i j
  · by_cases hr2 : remote j k
    · by_cases hr3 : remote i k
      · exact (g2_iff_no_remote_closed_triples hn hP.1).mp hP.2 i j k hr1 hr2 hr3
      · have ha : adjacent i k := by simpa only [remote, not_not] using hr3
        rintro ⟨x, hi, hj, hk⟩
        exact g1_no_adjacent_closedTripleMeet hn hP.1 i k j hik hjk.symm hij ha
          ⟨x, hi, hk, hj⟩
    · have ha : adjacent j k := by simpa only [remote, not_not] using hr2
      rintro ⟨x, hi, hj, hk⟩
      exact g1_no_adjacent_closedTripleMeet hn hP.1 j k i hjk hik.symm hij.symm ha
        ⟨x, hj, hk, hi⟩
  · have ha : adjacent i j := by simpa only [remote, not_not] using hr1
    exact g1_no_adjacent_closedTripleMeet hn hP.1 i j k hij hjk hik ha

/-- The complete closed segment at every corresponding parent label is
exactly its parent segment at zero, including the return edge. -/
theorem edgeSegment_softInsertion_parent_zero (P : LabelledTuple n) (j k : ZMod n)
    (q : Plane) :
    edgeSegment (softInsertion P j q 0) (softParentEdge j k) = edgeSegment P k := by
  ext x
  simp only [edgeSegment, mem_setOf_eq, edgePoint_softInsertion_parent_zero]

/-- Compact closed-triple persistence on all actual corresponding edges,
simultaneously. No genericity of the inserted zero tuple is assumed. -/
theorem soft_parent_closedTriples_persist (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → ∀ k l m : ZMod n,
      k ≠ l → l ≠ m → k ≠ m →
        ¬ ClosedTripleMeet (softInsertion P j q ε)
          (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) := by
  classical
  have htrip : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ k l m : ZMod n,
      k ≠ l → l ≠ m → k ≠ m →
        ¬ ClosedTripleMeet (softInsertion P j q ε)
          (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) := by
    refine eventually_all.mpr fun k => eventually_all.mpr fun l =>
      eventually_all.mpr fun m => ?_
    by_cases hd : k ≠ l ∧ l ≠ m ∧ k ≠ m
    · have hzero : ¬ ClosedTripleMeet (softInsertion P j q 0)
          (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) := by
        simpa only [ClosedTripleMeet, edgeSegment_softInsertion_parent_zero] using
          generic_no_distinct_closedTripleMeet hn hP k l m hd.1 hd.2.1 hd.2.2
      have he : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
          ¬ ClosedTripleMeet (softInsertion P j q ε)
            (softParentEdge j k) (softParentEdge j l) (softParentEdge j m) :=
        ((continuous_softInsertion P j q).continuousAt :
          ContinuousAt (softInsertion P j q) (0 : ℝ)).eventually
          ((isClosed_closedTripleMeet (softParentEdge j k) (softParentEdge j l)
            (softParentEdge j m)).isOpen_compl.mem_nhds hzero)
      exact he.mono (fun _ h _ _ _ => h)
    · exact Eventually.of_forall (fun _ hkl hlm hkm => (hd ⟨hkl, hlm, hkm⟩).elim)
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp htrip
  exact ⟨δ, hδ, fun ε hε => hmem (by simpa only [Real.dist_eq, sub_zero] using hε)⟩

/-- Genericity on one positive interval, proved through compact closed
triples and soft-edge avoidance. No inherited/newborn separation theorem,
child Generic hypothesis or crossing classification is used. -/
theorem softInsertion_small_Generic (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → Generic (softInsertion P j q ε) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  haveI : Fact (1 < n + 1) := ⟨by omega⟩
  obtain ⟨δt, hδt, htrip⟩ := soft_parent_closedTriples_persist hn hP j q
  obtain ⟨δg, hδg, hG1⟩ := softInsertion_small_G1 hP.1 j q hq
  obtain ⟨δs, hδs, hcontacts⟩ := softEdge_only_incident_contacts hn hP.1 j q hq
  refine ⟨min δt (min δg δs), lt_min hδt (lt_min hδg hδs), ?_⟩
  intro ε hε hεδ
  have hεt : |ε| < δt := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δt (min δg δs))
  have hεg : ε < δg := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δt (min δg δs)) (min_le_left δg δs))
  have hεs : ε < δs := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δt (min δg δs)) (min_le_right δg δs))
  have hg := hG1 ε hε hεg
  have havoid := (hcontacts ε hε hεs).2.2
  have hsoft (a : ZMod (n + 1)) (hr : remote (softOldIndex j j) a) :
      Disjoint (edgeSegment (softInsertion P j q ε) (softOldIndex j j))
        (edgeSegment (softInsertion P j q ε) a) := by
    have he := remote_endpoints (softOldIndex j j) a hr
    apply havoid a he.1
    · intro ha
      apply he.2.2.1
      have hp := softOldIndex_next j (j - 1) (prev_ne_self j)
      simp only [sub_add_cancel] at hp
      exact (congrArg (fun b : ZMod (n + 1) => b + 1) ha).trans hp.symm
    · intro ha
      exact he.2.1 (ha.trans (softOldIndex_attachment_next j).symm)
  refine ⟨hg, (g2_iff_no_remote_closed_triples (by omega : 3 ≤ n + 1) hg).mpr ?_⟩
  intro a b c hab hbc hac
  rintro ⟨x, hxa, hxb, hxc⟩
  have has : a ≠ softOldIndex j j := by
    intro he
    subst a
    exact Set.disjoint_left.mp (hsoft b hab) hxa hxb
  have hbs : b ≠ softOldIndex j j := by
    intro he
    subst b
    exact Set.disjoint_left.mp (hsoft a (remote_symm hab)) hxb hxa
  have hcs : c ≠ softOldIndex j j := by
    intro he
    subst c
    exact Set.disjoint_left.mp (hsoft a (remote_symm hac)) hxc hxa
  obtain ⟨k, rfl⟩ := (soft_parent_edges_exhaust j a).resolve_left has
  obtain ⟨l, rfl⟩ := (soft_parent_edges_exhaust j b).resolve_left hbs
  obtain ⟨m, rfl⟩ := (soft_parent_edges_exhaust j c).resolve_left hcs
  have hkl : k ≠ l := by
    intro he
    exact (remote_endpoints _ _ hab).1 ((congrArg (softParentEdge j) he).symm)
  have hlm : l ≠ m := by
    intro he
    exact (remote_endpoints _ _ hbc).1 ((congrArg (softParentEdge j) he).symm)
  have hkm : k ≠ m := by
    intro he
    exact (remote_endpoints _ _ hac).1 ((congrArg (softParentEdge j) he).symm)
  exact htrip ε hεt k l m hkl hlm hkm ⟨x, hxa, hxb, hxc⟩

/-- The G2 conclusion alone is available without any extra caller premise. -/
theorem softInsertion_small_G2 (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → G2 (softInsertion P j q ε) := by
  obtain ⟨δ, hδ, hg⟩ := softInsertion_small_Generic hn hP j q hq
  exact ⟨δ, hδ, fun ε hε hεδ => (hg ε hε hεδ).2⟩

/-- The actual generic-valued map from the positive interval lies in one
labelled chamber and one quotient polygon chamber. The base parameter is
the positive midpoint; the duplicate-vertex zero tuple is never used as a
Generic point. -/
theorem softInsertion_one_chamber (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∃ hmid : Generic (softInsertion P j q (δ / 2)),
      ∀ ε : ℝ, 0 < ε → ε < δ → ∃ hg : Generic (softInsertion P j q ε),
        (⟨softInsertion P j q ε, hg⟩ : GenericTuple (n + 1)) ∈
          labelledChamber ⟨softInsertion P j q (δ / 2), hmid⟩ ∧
        polygonProjection (⟨softInsertion P j q ε, hg⟩ : GenericTuple (n + 1)) ∈
          chamber (polygonProjection ⟨softInsertion P j q (δ / 2), hmid⟩) := by
  obtain ⟨δ, hδ, hgen⟩ := softInsertion_small_Generic hn hP j q hq
  have hm0 : 0 < δ / 2 := by linarith
  have hmδ : δ / 2 < δ := by linarith
  have hmid := hgen (δ / 2) hm0 hmδ
  let H : Ioo (0 : ℝ) δ → GenericTuple (n + 1) := fun t =>
    ⟨softInsertion P j q t.val, hgen t.val t.property.1 t.property.2⟩
  have hH : Continuous H :=
    ((continuous_softInsertion P j q).comp continuous_subtype_val).subtype_mk _
  let mid : Ioo (0 : ℝ) δ := ⟨δ / 2, hm0, hmδ⟩
  have hbase : H mid = (⟨softInsertion P j q (δ / 2), hmid⟩ : GenericTuple (n + 1)) :=
    Subtype.ext rfl
  letI : ConnectedSpace (Ioo (0 : ℝ) δ) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo hδ)
  have hrange := isConnected_range hH
  have hproj := isConnected_range (continuous_polygonProjection.comp hH)
  refine ⟨δ, hδ, hmid, ?_⟩
  intro ε hε hεδ
  let t : Ioo (0 : ℝ) δ := ⟨ε, hε, hεδ⟩
  have hm : H t ∈ labelledChamber (H mid) :=
    hrange.subset_connectedComponent (mem_range_self mid) (mem_range_self t)
  have hp : polygonProjection (H t) ∈ chamber (polygonProjection (H mid)) :=
    hproj.subset_connectedComponent (mem_range_self mid) (mem_range_self t)
  refine ⟨hgen ε hε hεδ, ?_, ?_⟩
  · simpa only [hbase, H] using hm
  · simpa only [hbase, H] using hp

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Pointwise persistence of every actual parent crossing pair. This helper
premise is derived on a common interval below. -/
def SoftCrossingPersistence (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) : Prop :=
  ∀ k l : ZMod n, IsCrossing P {k, l} →
    IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l}

/-- The exact frozen support classification at a fixed parameter, with no
chosen crossing correspondence hidden in the definition. -/
def SoftCrossingClassificationAt (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) : Prop :=
  ∀ s : Finset (ZMod (n + 1)), IsCrossing (softInsertion P j q ε) s ↔
    (∃ k l : ZMod n, IsCrossing P {k, l} ∧ s = {softParentEdge j k, softParentEdge j l}) ∨
    (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) ∧
      s = {softOldIndex j (j - 1), softNewIndex j}

/-- All helper premises, including child Generic, are derived on one positive
interval from the actual source hypotheses. Zero is not a Generic basepoint. -/
theorem soft_small_crossing_transport_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      Generic (softInsertion P j q ε) ∧ SoftCrossingPersistence P j q ε ∧
        SoftCrossingClassificationAt P j q ε := by
  obtain ⟨δp, hδp, hpair⟩ := soft_small_remote_pairs hn hP.1 j q
  obtain ⟨δc, hδc, hclass⟩ := soft_crossing_support_classification hn hP.1 j q hq
  obtain ⟨δg, hδg, hgen⟩ := softInsertion_small_Generic hn hP j q hq
  refine ⟨min δp (min δc δg), lt_min hδp (lt_min hδc hδg), ?_⟩
  intro ε hε hεδ
  have hεp : |ε| < δp := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δp (min δc δg))
  have hεc : ε < δc := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δp (min δc δg)) (min_le_left δc δg))
  have hεg : ε < δg := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δp (min δc δg)) (min_le_right δc δg))
  refine ⟨hgen ε hε hεg, ?_, hclass ε hε hεc⟩
  intro k l hc
  exact (hpair ε hεp k l (crossing_pair_remote hc)).mpr hc

variable {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- The inherited crossing is the actual image of its unordered support. -/
def softInheritedCrossing (hp : SoftCrossingPersistence P j q ε) (c : Crossing P) :
    Crossing (softInsertion P j q ε) :=
  ⟨c.val.image (softParentEdge j), by
    obtain ⟨k, l, hs, _, _⟩ := c.property
    have hc : IsCrossing P {k, l} := hs ▸ c.property
    simpa only [hs, Finset.image_insert, Finset.image_singleton] using hp k l hc⟩

theorem softInheritedCrossing_support (hp : SoftCrossingPersistence P j q ε)
    (c : Crossing P) :
    (softInheritedCrossing hp c).val = c.val.image (softParentEdge j) := rfl

theorem softInheritedCrossing_injective (hp : SoftCrossingPersistence P j q ε) :
    Function.Injective (softInheritedCrossing hp) := by
  intro c d he
  apply Subtype.ext
  exact Finset.image_injective (softParentEdge_injective j) (congrArg Subtype.val he)

/-- The incoming/return support is never an inherited actual parent crossing. -/
theorem softInheritedCrossing_ne_newborn (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (c : Crossing P) :
    (softInheritedCrossing hp c).val ≠ {softOldIndex j (j - 1), softNewIndex j} := by
  obtain ⟨k, l, hs, _, _⟩ := c.property
  have hc : IsCrossing P {k, l} := hs ▸ c.property
  simpa only [softInheritedCrossing_support, hs, Finset.image_insert, Finset.image_singleton]
    using soft_newborn_support_not_inherited hn P j k l hc

/-- Exact range, in every sector: all child crossings except the possible
newborn support, rather than a freely supplied image predicate. -/
theorem softInheritedCrossing_range_iff (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (d : Crossing (softInsertion P j q ε)) :
    (∃ c : Crossing P, softInheritedCrossing hp c = d) ↔
      d.val ≠ {softOldIndex j (j - 1), softNewIndex j} := by
  constructor
  · rintro ⟨c, rfl⟩
    exact softInheritedCrossing_ne_newborn hn hp c
  · intro hne
    rcases (hclass d.val).mp d.property with ⟨k, l, hc, hs⟩ | ⟨_, hs⟩
    · refine ⟨⟨{k, l}, hc⟩, Subtype.ext ?_⟩
      change ({k, l} : Finset (ZMod n)).image (softParentEdge j) = d.val
      simpa only [Finset.image_insert, Finset.image_singleton] using hs.symm
    · exact (hne hs).elim

/-- An equivalence onto precisely the inherited child-crossing subtype. -/
def softInheritedCrossingEquiv (hn : 3 ≤ n) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε) :
    Crossing P ≃ {d : Crossing (softInsertion P j q ε) //
      d.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := by
  let f : Crossing P → {d : Crossing (softInsertion P j q ε) //
      d.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := fun c =>
    ⟨softInheritedCrossing hp c, softInheritedCrossing_ne_newborn hn hp c⟩
  apply Equiv.ofBijective f
  constructor
  · intro c d he
    exact softInheritedCrossing_injective hp (congrArg Subtype.val he)
  · intro d
    obtain ⟨c, hc⟩ := (softInheritedCrossing_range_iff hn hp hclass d.val).mpr d.property
    exact ⟨c, Subtype.ext hc⟩

theorem softInheritedCrossing_surjective_nonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Function.Surjective (softInheritedCrossing hp) := by
  intro d
  rcases (hclass d.val).mp d.property with ⟨k, l, hc, hs⟩ | ⟨hloop, _⟩
  · refine ⟨⟨{k, l}, hc⟩, Subtype.ext ?_⟩
    change ({k, l} : Finset (ZMod n)).image (softParentEdge j) = d.val
    simpa only [Finset.image_insert, Finset.image_singleton] using hs.symm
  · exact (hnot hloop).elim

/-- In every non-loop sector the actual inherited crossing map is a bijection. -/
def softCrossingEquivNonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Crossing P ≃ Crossing (softInsertion P j q ε) :=
  Equiv.ofBijective (softInheritedCrossing hp)
    ⟨softInheritedCrossing_injective hp, softInheritedCrossing_surjective_nonloop hp hclass hnot⟩

/-- The actual newborn crossing selected by the proved loop-sector support. -/
def softNewbornCrossing (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    Crossing (softInsertion P j q ε) :=
  ⟨{softOldIndex j (j - 1), softNewIndex j},
    (hclass _).mpr (Or.inr ⟨hloop, rfl⟩)⟩

theorem softNewbornCrossing_support (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornCrossing hclass hloop).val =
      {softOldIndex j (j - 1), softNewIndex j} := rfl

theorem softInheritedCrossing_range_loop (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (d : Crossing (softInsertion P j q ε)) :
    (∃ c : Crossing P, softInheritedCrossing hp c = d) ↔ d ≠ softNewbornCrossing hclass hloop := by
  rw [softInheritedCrossing_range_iff hn hp hclass]
  constructor
  · intro hne he
    exact hne (congrArg Subtype.val he)
  · intro hne he
    exact hne (Subtype.ext he)

/-- A visit is transported by its crossing image and the image of its actual
member edge; no independently chosen edge or visit correspondence is supplied. -/
def softInheritedVisit (hp : SoftCrossingPersistence P j q ε) (v : Visit P) :
    Visit (softInsertion P j q ε) :=
  ⟨softInheritedCrossing hp v.1, softParentEdge j v.2.val,
    Finset.mem_image.mpr ⟨v.2.val, v.2.property, rfl⟩⟩

theorem softInheritedVisit_crossing (hp : SoftCrossingPersistence P j q ε) (v : Visit P) :
    (softInheritedVisit hp v).1 = softInheritedCrossing hp v.1 := rfl

theorem softInheritedVisit_edge (hp : SoftCrossingPersistence P j q ε) (v : Visit P) :
    (softInheritedVisit hp v).2.val = softParentEdge j v.2.val := rfl

theorem softInheritedVisit_injective (hp : SoftCrossingPersistence P j q ε) :
    Function.Injective (softInheritedVisit hp) := by
  intro v w he
  apply visit_ext
  · exact congrArg Subtype.val (softInheritedCrossing_injective hp (congrArg Sigma.fst he))
  · exact softParentEdge_injective j
      (congrArg (fun u : Visit (softInsertion P j q ε) => u.2.val) he)

/-- The two visits of each inherited crossing keep exactly their pairing. -/
theorem softInheritedVisit_pairing (hp : SoftCrossingPersistence P j q ε) (v w : Visit P) :
    (softInheritedVisit hp v).1 = (softInheritedVisit hp w).1 ↔ v.1 = w.1 :=
  (softInheritedCrossing_injective hp).eq_iff

/-- Every member-edge visit of an inherited crossing is inherited. -/
theorem softInheritedVisit_range_crossing_iff (hp : SoftCrossingPersistence P j q ε)
    (w : Visit (softInsertion P j q ε)) :
    (∃ v : Visit P, softInheritedVisit hp v = w) ↔
      ∃ c : Crossing P, softInheritedCrossing hp c = w.1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.1, rfl⟩
  · rintro ⟨c, hc⟩
    have hm : w.2.val ∈ (softInheritedCrossing hp c).val := by
      rw [hc]
      exact w.2.property
    change w.2.val ∈ c.val.image (softParentEdge j) at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact ⟨⟨c, i, hi⟩, visit_ext (congrArg Subtype.val hc) he⟩

theorem softInheritedVisit_range_iff (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (w : Visit (softInsertion P j q ε)) :
    (∃ v : Visit P, softInheritedVisit hp v = w) ↔
      w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j} :=
  (softInheritedVisit_range_crossing_iff hp w).trans
    (softInheritedCrossing_range_iff hn hp hclass w.1)

/-- The visit equivalence onto the exact inherited subtype is suitable for
filtering child Gauss lists before proving their order. -/
def softInheritedVisitEquiv (hn : 3 ≤ n) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε) :
    Visit P ≃ {w : Visit (softInsertion P j q ε) //
      w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := by
  let f : Visit P → {w : Visit (softInsertion P j q ε) //
      w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j}} := fun v =>
    ⟨softInheritedVisit hp v, softInheritedCrossing_ne_newborn hn hp v.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w he
    exact softInheritedVisit_injective hp (congrArg Subtype.val he)
  · intro w
    obtain ⟨v, hv⟩ := (softInheritedVisit_range_iff hn hp hclass w.val).mpr w.property
    exact ⟨v, Subtype.ext hv⟩

theorem softInheritedVisit_surjective_nonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Function.Surjective (softInheritedVisit hp) := by
  intro w
  exact (softInheritedVisit_range_crossing_iff hp w).mpr
    (softInheritedCrossing_surjective_nonloop hp hclass hnot w.1)

def softVisitEquivNonloop (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hnot : ¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)) :
    Visit P ≃ Visit (softInsertion P j q ε) :=
  Equiv.ofBijective (softInheritedVisit hp)
    ⟨softInheritedVisit_injective hp, softInheritedVisit_surjective_nonloop hp hclass hnot⟩

theorem softInheritedVisit_range_loop (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (w : Visit (softInsertion P j q ε)) :
    (∃ v : Visit P, softInheritedVisit hp v = w) ↔ w.1 ≠ softNewbornCrossing hclass hloop :=
  (softInheritedVisit_range_crossing_iff hp w).trans
    (softInheritedCrossing_range_loop hn hp hclass hloop w.1)

/-- Canonical actual visitParameter equals the transported edgeParameter,
for any representation of that visit's two-element parent support. -/
theorem softInheritedVisit_parameter (hn : 3 ≤ n) (hp : SoftCrossingPersistence P j q ε)
    (hQ : G1 (softInsertion P j q ε)) (v : Visit P) (l : ZMod n)
    (hs : v.1.val = {v.2.val, l}) :
    visitParameter (softInheritedVisit hp v) =
      edgeParameter (softInsertion P j q ε) (softParentEdge j v.2.val) (softParentEdge j l) := by
  have hpair : (softInheritedVisit hp v).1.val =
      {softParentEdge j v.2.val, softParentEdge j l} := by
    change v.1.val.image (softParentEdge j) = _
    have himage := congrArg (fun s : Finset (ZMod n) => s.image (softParentEdge j)) hs
    simpa only [Finset.image_insert, Finset.image_singleton] using himage
  have hc : IsCrossing (softInsertion P j q ε)
      {softParentEdge j v.2.val, softParentEdge j l} := hpair ▸ (softInheritedVisit hp v).1.property
  have he : softInheritedVisit hp v = pairVisit hc := visit_ext hpair rfl
  rw [he]
  exact pairVisit_parameter (by omega : 3 ≤ n + 1) hQ hc

/-- Every source visit has such a partner label; no partner-selection oracle
is required to use the preceding parameter formula. -/
theorem softInheritedVisit_parameter_exists (hn : 3 ≤ n)
    (hp : SoftCrossingPersistence P j q ε) (hQ : G1 (softInsertion P j q ε)) (v : Visit P) :
    ∃ l : ZMod n, l ≠ v.2.val ∧ v.1.val = {v.2.val, l} ∧
      visitParameter (softInheritedVisit hp v) =
        edgeParameter (softInsertion P j q ε) (softParentEdge j v.2.val) (softParentEdge j l) := by
  obtain ⟨l, hl, hs⟩ := crossing_pair_of_mem v.1 v.2.val v.2.property
  exact ⟨l, hl, hs, softInheritedVisit_parameter hn hp hQ v l hs⟩

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Cramer's first parameter on the actual incoming edge of the enlarged
polygon. The quotient is defined for all parameters; its geometric use below
is restricted by a proved nonzero determinant. -/
def softNewbornIncomingParameter (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) : ℝ :=
  cramerFirst (softInsertion P j q ε (softOldIndex j (j - 1)))
    (softInsertion P j q ε (softNewIndex j))
    (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
    (edge (softInsertion P j q ε) (softNewIndex j))

/-- Cramer's second parameter is measured in the actual return direction,
from the inserted vertex toward the old next vertex. -/
def softNewbornReturnParameter (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) : ℝ :=
  cramerSecond (softInsertion P j q ε (softOldIndex j (j - 1)))
    (softInsertion P j q ε (softNewIndex j))
    (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
    (edge (softInsertion P j q ε) (softNewIndex j))

/-- The supporting-line intersection evaluated on the actual incoming edge. -/
def softNewbornPoint (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) : Plane :=
  edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1))
    (softNewbornIncomingParameter P j q ε)

/-- At zero, the two directions are exactly the two parent directions at j. -/
theorem softNewborn_det_zero_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    det (edge (softInsertion P j q 0) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q 0) (softNewIndex j)) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [edge_softInsertion_old P j (j - 1) q 0 (prev_ne_self j),
    edge_softInsertion_return, zero_smul, sub_zero]
  exact g1_turn_nonzero hn hP j

/-- The zero-parameter line intersection is the incoming endpoint and the
return starting point, with their actual enlarged labels. -/
theorem softNewborn_zero_meeting (hn : 3 ≤ n) (P : LabelledTuple n)
    (j : ZMod n) (q : Plane) :
    edgePoint (softInsertion P j q 0) (softOldIndex j (j - 1)) 1 =
      edgePoint (softInsertion P j q 0) (softNewIndex j) 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [edgePoint_one, edgePoint_zero,
    ← softOldIndex_next j (j - 1) (prev_ne_self j), sub_add_cancel,
    softInsertion_old, softInsertion_new, zero_smul, add_zero]

/-- The actual Cramer values and supporting-line point at zero. No child
G1 or admissibility assumption is needed at the duplicate-vertex limit. -/
theorem softNewborn_values_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    softNewbornIncomingParameter P j q 0 = 1 ∧
    softNewbornReturnParameter P j q 0 = 0 ∧ softNewbornPoint P j q 0 = P j := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hd := softNewborn_det_zero_ne hn hP j q
  have hm := softNewborn_zero_meeting hn P j q
  have hs : softNewbornIncomingParameter P j q 0 = 1 :=
    (div_eq_iff hd).mpr (intersection_parameter_identity hm)
  have ht : softNewbornReturnParameter P j q 0 = 0 :=
    (div_eq_iff hd).mpr (intersection_second_parameter_identity hm)
  refine ⟨hs, ht, ?_⟩
  rw [softNewbornPoint, hs, edgePoint_one,
    ← softOldIndex_next j (j - 1) (prev_ne_self j), sub_add_cancel, softInsertion_old]

/-- Both Cramer parameters and their point are continuous at zero because
the actual direction determinant there is nonzero. -/
theorem softNewborn_continuousAt_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ContinuousAt (softNewbornIncomingParameter P j q) (0 : ℝ) ∧
    ContinuousAt (softNewbornReturnParameter P j q) (0 : ℝ) ∧
    ContinuousAt (softNewbornPoint P j q) (0 : ℝ) := by
  have hc := continuous_softInsertion P j q
  have ha := ((continuous_vertex (softOldIndex j (j - 1))).comp hc).continuousAt (x := (0 : ℝ))
  have hb := ((continuous_vertex (softNewIndex j)).comp hc).continuousAt (x := (0 : ℝ))
  have hu := ((continuous_edge (softOldIndex j (j - 1))).comp hc).continuousAt (x := (0 : ℝ))
  have hv := ((continuous_edge (softNewIndex j)).comp hc).continuousAt (x := (0 : ℝ))
  have hd := softNewborn_det_zero_ne hn hP j q
  have hs : ContinuousAt (softNewbornIncomingParameter P j q) (0 : ℝ) :=
    continuousAt_cramerFirst ha hb hu hv hd
  have ht : ContinuousAt (softNewbornReturnParameter P j q) (0 : ℝ) :=
    continuousAt_cramerSecond ha hb hu hv hd
  refine ⟨hs, ht, ?_⟩
  exact ha.add (hs.smul hu)

/-- These are two-sided supporting-line limits. In the loop sector they
are the limits of the actual newborn crossing data by the theorem below. -/
theorem softNewborn_limits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    Tendsto (softNewbornIncomingParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) ∧
    Tendsto (softNewbornReturnParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
    Tendsto (softNewbornPoint P j q) (𝓝 (0 : ℝ)) (𝓝 (P j)) := by
  have hc := softNewborn_continuousAt_zero hn hP j q
  have hz := softNewborn_values_zero hn hP j q
  have hs : Tendsto (softNewbornIncomingParameter P j q) (𝓝 (0 : ℝ))
      (𝓝 (softNewbornIncomingParameter P j q 0)) := hc.1
  have ht : Tendsto (softNewbornReturnParameter P j q) (𝓝 (0 : ℝ))
      (𝓝 (softNewbornReturnParameter P j q 0)) := hc.2.1
  have hp : Tendsto (softNewbornPoint P j q) (𝓝 (0 : ℝ))
      (𝓝 (softNewbornPoint P j q 0)) := hc.2.2
  exact ⟨by simpa only [hz.1] using hs, by simpa only [hz.2.1] using ht,
    by simpa only [hz.2.2] using hp⟩

/-- A genuine two-sided interval of transverse supporting lines. -/
theorem softNewborn_small_det_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ →
      det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
        (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0 := by
  have hc := continuous_softInsertion P j q
  have he := continuousAt_preserves_transversality
    (((continuous_edge (softOldIndex j (j - 1))).comp hc).continuousAt)
    (((continuous_edge (softNewIndex j)).comp hc).continuousAt)
    (softNewborn_det_zero_ne hn hP j q)
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ, hδ, fun ε hε => hmem (by simpa only [Real.dist_eq, sub_zero] using hε)⟩

/-- Cramer's rule solves the actual incoming/return supporting-line equations. -/
theorem softNewborn_parameters_intersection (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0) :
    edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1))
        (softNewbornIncomingParameter P j q ε) =
      edgePoint (softInsertion P j q ε) (softNewIndex j)
        (softNewbornReturnParameter P j q ε) :=
  cramer_intersection _ _ _ _ hd

/-- Any actual crossing of this transverse pair has exactly the constructed
parameters and point. This identification itself needs no G1 or G2 hypothesis. -/
theorem softNewborn_crossing_data (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0)
    (hc : IsCrossing (softInsertion P j q ε) {softOldIndex j (j - 1), softNewIndex j}) :
    crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
      Crossing (softInsertion P j q ε)) (softOldIndex j (j - 1)) (by simp) =
        softNewbornIncomingParameter P j q ε ∧
    crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
      Crossing (softInsertion P j q ε)) (softNewIndex j) (by simp) =
        softNewbornReturnParameter P j q ε ∧
    crossingPoint (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
      Crossing (softInsertion P j q ε)) = softNewbornPoint P j q ε := by
  let c : Crossing (softInsertion P j q ε) :=
    ⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩
  have hs := crossingParameter_spec c (softOldIndex j (j - 1)) (by simp [c])
  have ht := crossingParameter_spec c (softNewIndex j) (by simp [c])
  have hu := intersection_parameters_unique hd
    (softNewborn_parameters_intersection P j q ε hd) (hs.2.2.symm.trans ht.2.2)
  refine ⟨hu.1.symm, hu.2.symm, ?_⟩
  change crossingPoint c = edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1))
    (softNewbornIncomingParameter P j q ε)
  exact hs.2.2.trans (congrArg (edgePoint (softInsertion P j q ε)
    (softOldIndex j (j - 1))) hu.1.symm)

/-- On one common positive loop-sector interval, the constructed parameters
are strictly interior and give the actual unordered pair crossing point.
Child G1 and the existence of this crossing are derived here. This theorem
does not assert that the pair is the only newborn among all polygon edges. -/
theorem softNewborn_small_loop_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
        (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0 ∧
      (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j →
        ∃ hc : IsCrossing (softInsertion P j q ε) {softOldIndex j (j - 1), softNewIndex j},
          (0 < softNewbornIncomingParameter P j q ε ∧ softNewbornIncomingParameter P j q ε < 1) ∧
          (0 < softNewbornReturnParameter P j q ε ∧ softNewbornReturnParameter P j q ε < 1) ∧
          crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
            Crossing (softInsertion P j q ε)) (softOldIndex j (j - 1)) (by simp) =
              softNewbornIncomingParameter P j q ε ∧
          crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
            Crossing (softInsertion P j q ε)) (softNewIndex j) (by simp) =
              softNewbornReturnParameter P j q ε ∧
          crossingPoint (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
            Crossing (softInsertion P j q ε)) = softNewbornPoint P j q ε) := by
  obtain ⟨δd, hδd, hdet⟩ := softNewborn_small_det_ne hn hP j q
  obtain ⟨δc, hδc, hcross⟩ := softFamily_local_crossing hn P hP j q hq
  obtain ⟨δg, hδg, hgeneric⟩ := softInsertion_small_G1 hP j q hq
  refine ⟨min δd (min δc δg), lt_min hδd (lt_min hδc hδg), ?_⟩
  intro ε hε hεδ
  have hεd : |ε| < δd := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δd (min δc δg))
  have hεc : ε < δc := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δd (min δc δg)) (min_le_left δc δg))
  have hεg : ε < δg := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δd (min δc δg)) (min_le_right δc δg))
  have hd := hdet ε hεd
  refine ⟨hd, ?_⟩
  intro hloop
  have hc := (hcross ε hε hεc).2.mpr hloop
  have hg := hgeneric ε hε hεg
  have hdata := softNewborn_crossing_data P j q ε hd hc
  have hs := crossingParameter_interior (by omega : 3 ≤ n + 1) hg
    (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ : Crossing (softInsertion P j q ε))
    (softOldIndex j (j - 1)) (by simp)
  have ht := crossingParameter_interior (by omega : 3 ≤ n + 1) hg
    (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ : Crossing (softInsertion P j q ε))
    (softNewIndex j) (by simp)
  refine ⟨hc, ?_, ?_, hdata.1, hdata.2.1, hdata.2.2⟩
  · simpa only [hdata.1] using hs
  · simpa only [hdata.2.1] using ht

end
end SM

namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- The newborn's incoming parameter tends to one, beyond every parent
crossing parameter on the incoming edge. -/
theorem soft_newborn_after_incoming_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j l : ZMod n) (q : Plane) (hc : IsCrossing P {j - 1, l}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
        softNewbornIncomingParameter P j q ε := by
  have hp := continuousAt_softParentParameter P j (j - 1) l q
    (crossing_edgeParameter_det_ne_zero hn hP hc)
  have hs := (softNewborn_continuousAt_zero hn hP j q).1
  have hz := (softNewborn_values_zero hn hP j q).1
  have hi := crossingParameter_interior hn hP
    (⟨{j - 1, l}, hc⟩ : Crossing P) (j - 1) (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hc] at hi
  exact continuousAt_preserves_strict_order hp hs
    (by simpa only [softParentParameter_zero, hz] using hi.2)

/-- The newborn's return parameter tends to zero, before every parent
crossing parameter on the outgoing edge represented by the return edge. -/
theorem soft_newborn_before_return_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j l : ZMod n) (q : Plane) (hc : IsCrossing P {j, l}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), softNewbornReturnParameter P j q ε <
      edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l) := by
  have hp := continuousAt_softParentParameter P j j l q
    (crossing_edgeParameter_det_ne_zero hn hP hc)
  have hs := (softNewborn_continuousAt_zero hn hP j q).2.1
  have hz := (softNewborn_values_zero hn hP j q).2.1
  have hi := crossingParameter_interior hn hP (⟨{j, l}, hc⟩ : Crossing P) j (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hc] at hi
  exact continuousAt_preserves_strict_order hs hp
    (by simpa only [softParentParameter_zero, hz] using hi.1)

/-- One positive interval simultaneously puts all inherited incoming visits
before the newborn and all inherited return visits after it. In the loop
sector the frozen crossing-data theorem identifies these parameters with
the actual newborn visits; the intervening soft edge has no crossings. -/
theorem soft_newborn_small_visit_windows (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → ∀ l : ZMod n,
      (IsCrossing P {j - 1, l} →
        edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
          softNewbornIncomingParameter P j q ε) ∧
      (IsCrossing P {j, l} → softNewbornReturnParameter P j q ε <
        edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ l : ZMod n,
      (IsCrossing P {j - 1, l} →
        edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
          softNewbornIncomingParameter P j q ε) ∧
      (IsCrossing P {j, l} → softNewbornReturnParameter P j q ε <
        edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l)) := by
    apply eventually_all.mpr
    intro l
    apply Filter.Eventually.and
    · by_cases hc : IsCrossing P {j - 1, l}
      · exact (soft_newborn_after_incoming_visits hn hP j l q hc).mono (fun _ h _ => h)
      · exact Eventually.of_forall (fun _ h => (hc h).elim)
    · by_cases hc : IsCrossing P {j, l}
      · exact (soft_newborn_before_return_visits hn hP j l q hc).mono (fun _ h _ => h)
      · exact Eventually.of_forall (fun _ h => (hc h).elim)
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  exact hmem (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using hεδ)

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem canonicalPosition_val_zero : (canonicalPosition (0 : ZMod n)).val = n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  simp [canonicalPosition]

theorem canonicalPosition_val_nonzero (k : ZMod n) (hk : k ≠ 0) :
    (canonicalPosition k).val = k.val - 1 := by
  have hp := ZMod.val_pos.mpr hk
  have hn := ZMod.val_lt k
  haveI : Fact (1 < n) := ⟨by omega⟩
  change (k - 1).val = k.val - 1
  rw [ZMod.val_sub (by rw [ZMod.val_one]; omega), ZMod.val_one]

/-- Exact numerical label formula for the corresponding parent edge. The
return edge, rather than the soft edge, inherits the parent label's place
in the traversal order, including parent label zero. -/
theorem softParentEdge_natCast (j k : ZMod n) :
    softParentEdge j k = if j = 0 ∨ k.val < j.val then (k.val : ZMod (n + 1))
      else ((k.val + 1 : ℕ) : ZMod (n + 1)) := by
  have hn := NeZero.pos n
  have hkn := ZMod.val_lt k
  have hjn := ZMod.val_lt j
  by_cases hj : j = 0
  · subst j
    simp only [true_or, ite_true]
    by_cases hk : k = 0
    · subst k
      rw [softParentEdge_at_attachment, softNewIndex_physical, canonicalPosition_val_zero]
      have he : n - 1 + 2 = n + 1 := by omega
      rw [he, ZMod.natCast_self, ZMod.val_zero, Nat.cast_zero]
    · rw [softParentEdge_of_ne 0 k hk]
      have hp := ZMod.val_pos.mpr hk
      have he := softOldIndex_physical (0 : ZMod n) (canonicalPosition k)
      rw [boundaryIndex_canonicalPosition, canonicalPosition_val_nonzero k hk,
        canonicalPosition_val_zero] at he
      have hle : k.val - 1 ≤ n - 1 := by omega
      rw [if_pos hle] at he
      have hv : k.val - 1 + 1 = k.val := by omega
      simpa only [hv] using he
  · have hjp := ZMod.val_pos.mpr hj
    by_cases hkj : k = j
    · subst k
      simp only [hj, false_or, lt_self_iff_false, ite_false]
      rw [softParentEdge_at_attachment, softNewIndex_physical, canonicalPosition_val_nonzero j hj]
      have hv : j.val - 1 + 2 = j.val + 1 := by omega
      rw [hv]
    · rw [softParentEdge_of_ne j k hkj]
      have he := softOldIndex_physical j (canonicalPosition k)
      rw [boundaryIndex_canonicalPosition, canonicalPosition_val_nonzero j hj] at he
      by_cases hk : k = 0
      · subst k
        rw [canonicalPosition_val_zero] at he
        have hgt : ¬ n - 1 ≤ j.val - 1 := by omega
        rw [if_neg hgt] at he
        have hv : n - 1 + 2 = n + 1 := by omega
        simp only [hv, ZMod.natCast_self] at he
        simp only [hj, false_or, ZMod.val_zero, hjp, ite_true, Nat.cast_zero]
        exact he
      · have hkp := ZMod.val_pos.mpr hk
        have hne : k.val ≠ j.val := fun h => hkj (ZMod.val_injective n h)
        rw [canonicalPosition_val_nonzero k hk] at he
        by_cases hlt : k.val < j.val
        · have hle : k.val - 1 ≤ j.val - 1 := by omega
          have hv : k.val - 1 + 1 = k.val := by omega
          simpa only [hj, false_or, hlt, ite_true, hle, hv] using he
        · have hgt : ¬ k.val - 1 ≤ j.val - 1 := by omega
          have hv : k.val - 1 + 2 = k.val + 1 := by omega
          simpa only [hj, false_or, hlt, ite_false, hgt, hv] using he

theorem softParentEdge_val (j k : ZMod n) :
    (softParentEdge j k).val = if j = 0 ∨ k.val < j.val then k.val else k.val + 1 := by
  rw [softParentEdge_natCast]
  split_ifs
  · exact ZMod.val_natCast_of_lt (by have := ZMod.val_lt k; omega)
  · exact ZMod.val_natCast_of_lt (by have := ZMod.val_lt k; omega)

/-- Unlike a general cyclic relabelling, this parent-edge correspondence
preserves the actual numerical traversal cut, even when inserting after
source label n. This supports equality of inherited sorted visit lists. -/
theorem softParentEdge_val_lt_iff (j k l : ZMod n) :
    (softParentEdge j k).val < (softParentEdge j l).val ↔ k.val < l.val := by
  rw [softParentEdge_val, softParentEdge_val]
  by_cases hj : j = 0
  · simp only [hj, true_or, ite_true]
  · simp only [hj, false_or]
    split_ifs <;> omega

theorem softParentEdge_val_le_iff (j k l : ZMod n) :
    (softParentEdge j k).val ≤ (softParentEdge j l).val ↔ k.val ≤ l.val := by
  simpa only [not_lt] using not_congr (softParentEdge_val_lt_iff j l k)

theorem softParentEdge_zero (j : ZMod n) : softParentEdge j 0 = 0 := by
  apply ZMod.val_injective
  rw [softParentEdge_val, ZMod.val_zero]
  by_cases hj : j = 0
  · simp only [hj, true_or, ite_true, ZMod.val_zero]
  · have hp := ZMod.val_pos.mpr hj
    simp only [hj, false_or, ZMod.val_zero, hp, ite_true]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- There is no parent edge strictly between a predecessor and its successor
in the cyclic numerical edge order. This includes the residue-zero cut. -/
theorem soft_parent_no_cyclic_edge_between (j k : ZMod n) :
    ¬ (((j - 1).val < k.val ∧ k.val < j.val) ∨
      (k.val < j.val ∧ j.val < (j - 1).val) ∨
      (j.val < (j - 1).val ∧ (j - 1).val < k.val)) := by
  have hk := ZMod.val_lt k
  have hj := ZMod.val_lt j
  by_cases hz : j = 0
  · subst j
    have hv : ((0 : ZMod n) - 1).val = n - 1 := canonicalPosition_val_zero
    rw [hv, ZMod.val_zero]
    omega
  · have hv : (j - 1).val = j.val - 1 := canonicalPosition_val_nonzero j hz
    rw [hv]
    omega

/-- Every point on a corresponding parent edge is outside the short inserted
arc if it precedes the incoming endpoint on that edge and follows the return
endpoint on that edge. No visit or chamber premise is hidden here. -/
theorem soft_parent_traversal_arc_empty (hn : 3 ≤ n) (j k : ZMod n)
    (a x b : TraversalPoint (n + 1))
    (ha : a.1 = softParentEdge j (j - 1)) (hx : x.1 = softParentEdge j k)
    (hb : b.1 = softParentEdge j j)
    (hin : k = j - 1 → x.2.val ≤ a.2.val)
    (hout : k = j → b.2.val ≤ x.2.val) : ¬ traversalBetween a x b := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hpj : j - 1 ≠ j := prev_ne_self j
  intro h
  unfold traversalBetween at h
  simp only [traversalKey_lt_iff, ha, hx, hb, softParentEdge_val_lt_iff,
    (softParentEdge_injective j).eq_iff] at h
  by_cases hkprev : k = j - 1
  · have hpar := hin hkprev
    subst k
    simp only [lt_self_iff_false, true_and, false_or, hpj, Ne.symm hpj,
      false_and, or_false] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · omega
    · linarith
  · by_cases hkj : k = j
    · have hpar := hout hkj
      subst k
      simp only [lt_self_iff_false, true_and, false_or, hpj, Ne.symm hpj,
        false_and, or_false] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
      · omega
    · simp only [hkprev, Ne.symm hkprev, hkj, Ne.symm hkj, hpj, Ne.symm hpj,
        false_and, or_false] at h
      exact soft_parent_no_cyclic_edge_between j k h

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
variable {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- The actual visit of the newborn crossing on the incoming enlarged edge. -/
def softNewbornIncomingVisit (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    Visit (softInsertion P j q ε) :=
  ⟨softNewbornCrossing hclass hloop, softOldIndex j (j - 1),
    by simp [softNewbornCrossing]⟩

/-- The actual visit of the same crossing on the return enlarged edge. -/
def softNewbornReturnVisit (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    Visit (softInsertion P j q ε) :=
  ⟨softNewbornCrossing hclass hloop, softNewIndex j,
    by simp [softNewbornCrossing]⟩

theorem softNewbornIncomingVisit_edge (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornIncomingVisit hclass hloop).2.val = softOldIndex j (j - 1) := rfl

theorem softNewbornReturnVisit_edge (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornReturnVisit hclass hloop).2.val = softNewIndex j := rfl

theorem softNewbornVisits_crossing (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornIncomingVisit hclass hloop).1 = softNewbornCrossing hclass hloop ∧
    (softNewbornReturnVisit hclass hloop).1 = softNewbornCrossing hclass hloop := ⟨rfl, rfl⟩

theorem softNewbornVisits_distinct (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    softNewbornIncomingVisit hclass hloop ≠ softNewbornReturnVisit hclass hloop := by
  intro he
  exact softOldIndex_ne_new j (j - 1)
    (congrArg (fun v : Visit (softInsertion P j q ε) => v.2.val) he)

/-- There are exactly these two visits of the newborn crossing; no other
member edge is allowed by its actual two-element support. -/
theorem softNewbornVisits_exhaust (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (w : Visit (softInsertion P j q ε)) (hw : w.1 = softNewbornCrossing hclass hloop) :
    w = softNewbornIncomingVisit hclass hloop ∨ w = softNewbornReturnVisit hclass hloop := by
  have hs : w.1.val = {softOldIndex j (j - 1), softNewIndex j} := congrArg Subtype.val hw
  have hm : w.2.val ∈ ({softOldIndex j (j - 1), softNewIndex j} : Finset (ZMod (n + 1))) :=
    hs ▸ w.2.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hin | hout
  · exact Or.inl (visit_ext hs hin)
  · exact Or.inr (visit_ext hs hout)

/-- The canonical actual visit parameters are exactly the proved Cramer
parameters; this uses actual transversality, not a new parameter choice. -/
theorem softNewbornVisits_parameters (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0) :
    visitParameter (softNewbornIncomingVisit hclass hloop) = softNewbornIncomingParameter P j q ε ∧
    visitParameter (softNewbornReturnVisit hclass hloop) = softNewbornReturnParameter P j q ε := by
  have hdata := softNewborn_crossing_data P j q ε hd (softNewbornCrossing hclass hloop).property
  exact ⟨hdata.1, hdata.2.1⟩

theorem softNewbornVisits_interior (hn : 3 ≤ n)
    (hQ : G1 (softInsertion P j q ε)) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (0 < visitParameter (softNewbornIncomingVisit hclass hloop) ∧
      visitParameter (softNewbornIncomingVisit hclass hloop) < 1) ∧
    (0 < visitParameter (softNewbornReturnVisit hclass hloop) ∧
      visitParameter (softNewbornReturnVisit hclass hloop) < 1) :=
  ⟨visitPosition_interior (by omega : 3 ≤ n + 1) hQ _,
    visitPosition_interior (by omega : 3 ≤ n + 1) hQ _⟩

/-- The two actual visit edges have precisely the soft edge between them.
Its endpoints evaluate to M and M_epsilon, including at the residue-zero cut. -/
theorem softNewbornVisits_physical_path (hn : 3 ≤ n)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornIncomingVisit hclass hloop).2.val + 1 = softOldIndex j j ∧
    softOldIndex j j + 1 = (softNewbornReturnVisit hclass hloop).2.val ∧
    softInsertion P j q ε (softOldIndex j j) = P j ∧
    softInsertion P j q ε (softNewbornReturnVisit hclass hloop).2.val = P j + ε • q := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨?_, softOldIndex_attachment_next j, softInsertion_old P j j q ε,
    softInsertion_new P j q ε⟩
  change softOldIndex j (j - 1) + 1 = softOldIndex j j
  simpa only [sub_add_cancel] using (softOldIndex_next j (j - 1) (prev_ne_self j)).symm

/-- Pointwise use of the proved finite parameter windows. The explicit window
hypothesis is discharged from the actual family in the final interval theorem. -/
theorem softNewbornVisits_inherited_bounds (hn : 3 ≤ n)
    (hQ : G1 (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0)
    (hwin : ∀ l : ZMod n,
      (IsCrossing P {j - 1, l} →
        edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
          softNewbornIncomingParameter P j q ε) ∧
      (IsCrossing P {j, l} → softNewbornReturnParameter P j q ε <
        edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l)))
    (v : Visit P) :
    (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
      visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
    (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
      visitParameter (softInheritedVisit hp v)) := by
  obtain ⟨l, _, hs⟩ := crossing_pair_of_mem v.1 v.2.val v.2.property
  have hc : IsCrossing P {v.2.val, l} := hs ▸ v.1.property
  have hpar := softNewbornVisits_parameters hclass hloop hd
  have hvpar := softInheritedVisit_parameter hn hp hQ v l hs
  constructor
  · intro hv
    have hc' : IsCrossing P {j - 1, l} := by simpa only [hv] using hc
    rw [hvpar, hpar.1, hv]
    exact (hwin l).1 hc'
  · intro hv
    have hc' : IsCrossing P {j, l} := by simpa only [hv] using hc
    rw [hvpar, hpar.2, hv]
    exact (hwin l).2 hc'

/-- Every child visit is either inherited, when the actual parent-edge arc
lemma excludes it, or one of the two endpoints. Thus the short oriented arc
contains no crossing visit, with no exception at j = 0. -/
theorem softNewbornVisits_no_between (hn : 3 ≤ n)
    (hQ : G1 (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hbound : ∀ v : Visit P,
      (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
      (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v)))
    (w : Visit (softInsertion P j q ε)) :
    ¬ traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (visitPosition (by omega : 3 ≤ n + 1) hQ w)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  by_cases hw : w.1 = softNewbornCrossing hclass hloop
  · rcases softNewbornVisits_exhaust hclass hloop w hw with he | he
    · rw [he]
      unfold traversalBetween
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
    · rw [he]
      unfold traversalBetween
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  · obtain ⟨v, rfl⟩ := (softInheritedVisit_range_loop hn hp hclass hloop w).mpr hw
    apply soft_parent_traversal_arc_empty hn j v.2.val
    · change softOldIndex j (j - 1) = softParentEdge j (j - 1)
      exact (softParentEdge_of_ne j (j - 1) (prev_ne_self j)).symm
    · rfl
    · change softNewIndex j = softParentEdge j j
      exact (softParentEdge_at_attachment j).symm
    · intro hv
      exact ((hbound v).1 hv).le
    · intro hv
      exact ((hbound v).2 hv).le

/-- A single positive interval supplies all actual data and the empty short
arc in the loop sector. The geometric assumptions are exactly parent Generic
and actual admissibility; every window and classification premise is derived. -/
theorem soft_newborn_small_empty_arc (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
      ∃ hp : SoftCrossingPersistence P j q ε,
      ∃ hclass : SoftCrossingClassificationAt P j q ε,
      ∀ hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j,
        (∀ v : Visit P,
          (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
            visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
          (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
            visitParameter (softInheritedVisit hp v))) ∧
        (∀ w : Visit (softInsertion P j q ε),
          ¬ traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop))) := by
  obtain ⟨δt, hδt, htransport⟩ := soft_small_crossing_transport_data hn hP j q hq
  obtain ⟨δw, hδw, hwindow⟩ := soft_newborn_small_visit_windows hn hP.1 j q
  obtain ⟨δd, hδd, hdet⟩ := softNewborn_small_det_ne hn hP.1 j q
  refine ⟨min δt (min δw δd), lt_min hδt (lt_min hδw hδd), ?_⟩
  intro ε hε hεδ
  have hεt : ε < δt := lt_of_lt_of_le hεδ (min_le_left δt (min δw δd))
  have hεw : ε < δw := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δt (min δw δd)) (min_le_left δw δd))
  have hεd : |ε| < δd := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ
      (le_trans (min_le_right δt (min δw δd)) (min_le_right δw δd))
  obtain ⟨hQ, hp, hclass⟩ := htransport ε hε hεt
  refine ⟨hQ, hp, hclass, ?_⟩
  intro hloop
  have hbound := softNewbornVisits_inherited_bounds hn hQ.1 hp hclass hloop
    (hdet ε hεd) (hwindow ε hε hεw)
  exact ⟨hbound, softNewbornVisits_no_between hn hQ.1 hp hclass hloop hbound⟩

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The old attachment vertex as an actual half-open traversal position:
the start of the enlarged soft edge, at parameter zero. -/
def softAttachmentVertexPosition (j : ZMod n) : TraversalPoint (n + 1) :=
  (softOldIndex j j, ⟨0, le_rfl, zero_lt_one⟩)

/-- The inserted vertex as the actual start of the return edge. -/
def softInsertedVertexPosition (j : ZMod n) : TraversalPoint (n + 1) :=
  (softNewIndex j, ⟨0, le_rfl, zero_lt_one⟩)

theorem softAttachmentVertexPosition_evaluation (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) :
    traversalEvaluation (softInsertion P j q ε) (softAttachmentVertexPosition j) = P j := by
  change edgePoint (softInsertion P j q ε) (softOldIndex j j) 0 = P j
  rw [edgePoint_zero, softInsertion_old]

theorem softInsertedVertexPosition_evaluation (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) :
    traversalEvaluation (softInsertion P j q ε) (softInsertedVertexPosition j) = P j + ε • q := by
  change edgePoint (softInsertion P j q ε) (softNewIndex j) 0 = P j + ε • q
  rw [edgePoint_zero, softInsertion_new]

/-- Exact numerical representatives of the three consecutive enlarged edges.
The return edge crosses the numerical cut precisely when the parent label is zero. -/
theorem soft_vertex_arc_label_values (hn : 3 ≤ n) (j : ZMod n) :
    (softOldIndex j (j - 1)).val = (canonicalPosition j).val ∧
    (softOldIndex j j).val = (canonicalPosition j).val + 1 ∧
    (softNewIndex j).val = if j = 0 then 0 else j.val + 1 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← softParentEdge_of_ne j (j - 1) (prev_ne_self j), softParentEdge_val]
    by_cases hj : j = 0
    · rw [if_pos (Or.inl hj)]
      rfl
    · have hpos := ZMod.val_pos.mpr hj
      have hprev : (j - 1).val = j.val - 1 := canonicalPosition_val_nonzero j hj
      have hlt : (j - 1).val < j.val := by rw [hprev]; omega
      rw [if_pos (Or.inr hlt)]
      rfl
  · rw [softOldIndex_at_attachment]
    exact ZMod.val_natCast_of_lt (by have := (canonicalPosition j).isLt; omega)
  · rw [← softParentEdge_at_attachment j, softParentEdge_val]
    simp only [lt_self_iff_false, or_false]
    by_cases hj : j = 0
    · simp only [if_pos hj, hj, ZMod.val_zero]
    · simp only [if_neg hj]

/-- The actual three enlarged edge labels force the two vertex positions to
occur in this order on the short incoming-to-return arc. The incoming point
may be anywhere in its half-open edge; positivity of the return parameter is
necessary to put the inserted vertex strictly before it. No order is assumed. -/
theorem soft_vertex_arc_of_edges (hn : 3 ≤ n) (j : ZMod n)
    (a b : TraversalPoint (n + 1))
    (ha : a.1 = softOldIndex j (j - 1)) (hb : b.1 = softNewIndex j)
    (hbpos : 0 < b.2.val) :
    traversalBetween a (softAttachmentVertexPosition j) b ∧
    traversalBetween a (softInsertedVertexPosition j) b ∧
    traversalBetween a (softAttachmentVertexPosition j) (softInsertedVertexPosition j) ∧
    traversalBetween (softAttachmentVertexPosition j) (softInsertedVertexPosition j) b := by
  have hlabels := soft_vertex_arc_label_values hn j
  have ham : traversalKey a < traversalKey (softAttachmentVertexPosition j) := by
    apply traversalKey_lt_of_edge_lt
    change a.1.val < (softOldIndex j j).val
    rw [ha, hlabels.1, hlabels.2.1]
    omega
  have hnb : traversalKey (softInsertedVertexPosition j) < traversalKey b := by
    apply (traversalKey_lt_iff _ _).mpr
    exact Or.inr ⟨hb.symm, hbpos⟩
  by_cases hj : j = 0
  · have hba : traversalKey b < traversalKey a := by
      apply traversalKey_lt_of_edge_lt
      rw [hb, ha, hlabels.1, hlabels.2.2, if_pos hj, hj, canonicalPosition_val_zero]
      omega
    exact ⟨Or.inr (Or.inr ⟨hba, ham⟩),
      Or.inr (Or.inl ⟨hnb, hba⟩),
      Or.inr (Or.inr ⟨lt_trans hnb hba, ham⟩),
      Or.inr (Or.inl ⟨hnb, lt_trans hba ham⟩)⟩
  · have hmn : traversalKey (softAttachmentVertexPosition j) <
        traversalKey (softInsertedVertexPosition j) := by
      apply traversalKey_lt_of_edge_lt
      change (softOldIndex j j).val < (softNewIndex j).val
      rw [hlabels.2.1, hlabels.2.2, if_neg hj, canonicalPosition_val_nonzero j hj]
      have hpos := ZMod.val_pos.mpr hj
      omega
    exact ⟨Or.inl ⟨ham, lt_trans hmn hnb⟩,
      Or.inl ⟨lt_trans ham hmn, hnb⟩,
      Or.inl ⟨ham, hmn⟩,
      Or.inl ⟨hmn, hnb⟩⟩

/-- Source newborn arc through M and M_epsilon, using the actual newborn
visits constructed from classification and the loop sector. Child G1 gives
strict interiority. Every cyclic cut, including j = 0, is covered. -/
theorem softNewbornVisits_vertex_arc (hn : 3 ≤ n) {P : LabelledTuple n}
    {j : ZMod n} {q : Plane} {ε : ℝ}
    (hQ : G1 (softInsertion P j q ε)) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (softAttachmentVertexPosition j)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) ∧
    traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (softInsertedVertexPosition j)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) ∧
    traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (softAttachmentVertexPosition j) (softInsertedVertexPosition j) ∧
    traversalBetween (softAttachmentVertexPosition j) (softInsertedVertexPosition j)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) := by
  apply soft_vertex_arc_of_edges hn j
  · rfl
  · rfl
  · exact (softNewbornVisits_interior hn hQ hclass hloop).2.1

end
end SM

#print axioms SM.softAttachmentVertexPosition
#print axioms SM.softInsertedVertexPosition
#print axioms SM.softAttachmentVertexPosition_evaluation
#print axioms SM.softInsertedVertexPosition_evaluation
#print axioms SM.soft_vertex_arc_label_values
#print axioms SM.soft_vertex_arc_of_edges
#print axioms SM.softNewbornVisits_vertex_arc
