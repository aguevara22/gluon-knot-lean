import SM.Traversal
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

#print axioms SM.soft_parent_no_cyclic_edge_between
#print axioms SM.soft_parent_traversal_arc_empty
