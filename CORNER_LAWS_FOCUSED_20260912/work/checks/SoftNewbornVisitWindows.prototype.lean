import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.CuspParameters
import Mathlib.Data.Fin.Tuple.Basic
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

#check SM.canonicalPosition
#check SM.canonical_label
#check SM.canonical_label_range
#check SM.boundaryIndex_canonicalPosition
#check SM.canonicalPosition_boundaryIndex
#check SM.canonicalPosition_injective
#check SM.sortTriplePositions
#check SM.sortTriplePositions_sign
#check SM.sortTriplePositions_positionSet
#check SM.canonicalTripleValue
#check SM.sortTriplePositions_evaluation

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

#print axioms SM.soft_newborn_after_incoming_visits
#print axioms SM.soft_newborn_before_return_visits
#print axioms SM.soft_newborn_small_visit_windows
