import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.TraversalRelabel

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The source marked traversal retains every original vertex and every actual
crossing visit. In particular it is not empty when the polygon has no crossings. -/
abbrev Mark (P : LabelledTuple n) := ZMod n ⊕ Visit P

/-- Original vertices have parameter zero; crossing visits have their actual
strictly interior crossing parameters on the traversed edge. -/
def markPosition (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) :
    Mark P → TraversalPoint n
  | Sum.inl i => (i, ⟨0, by norm_num⟩)
  | Sum.inr v => visitPosition hn hP v

theorem markPosition_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (i : ZMod n) : markPosition hn hP (Sum.inl i) = (i, ⟨0, by norm_num⟩) := rfl

theorem markPosition_visit (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : markPosition hn hP (Sum.inr v) = visitPosition hn hP v := rfl

/-- The vertex branch evaluates to the actual original vertex. -/
theorem markPosition_evaluation_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (i : ZMod n) : traversalEvaluation P (markPosition hn hP (Sum.inl i)) = P i := by
  simp [markPosition, traversalEvaluation, edgePoint]

/-- Each visit branch evaluates to its own actual crossing point. -/
theorem markPosition_evaluation_visit (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : traversalEvaluation P (markPosition hn hP (Sum.inr v)) = crossingPoint v.1 :=
  visitPosition_evaluation hn hP v

/-- Strict visit interiority separates vertices from visits. Genericity supplies
injectivity within the visit branch, including different crossings on one edge. -/
theorem markPosition_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Function.Injective (markPosition hn hP.1) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (congrArg Prod.fst hab)
    | inr v =>
      have he : (0 : ℝ) = visitParameter v := congrArg (fun x => x.2.val) hab
      have hv := (visitPosition_interior hn hP.1 v).1
      exact (ne_of_gt hv he.symm).elim
  | inr v =>
    cases b with
    | inl i =>
      have he : visitParameter v = (0 : ℝ) := congrArg (fun x => x.2.val) hab
      have hv := (visitPosition_interior hn hP.1 v).1
      exact (ne_of_gt hv he).elim
    | inr w => exact congrArg Sum.inr (visitPosition_injective hn hP hab)

def markKey (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P) (a : Mark P) : ℝ :=
  traversalKey (markPosition hn hP a)

theorem markKey_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (i : ZMod n) : markKey hn hP (Sum.inl i) = i.val := by
  simp [markKey, markPosition, traversalKey]

theorem markKey_visit (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : markKey hn hP (Sum.inr v) = visitKey hn hP v := rfl

theorem markKey_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Function.Injective (markKey hn hP.1) :=
  traversalKey_injective.comp (markPosition_injective hn hP)

@[instance_reducible]
def markLinearOrder (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    LinearOrder (Mark P) := LinearOrder.lift' (markKey hn hP.1) (markKey_injective hn hP)

/-- Sort every actual mark by its edge and parameter position. This list is a
linear representative of the full marked traversal circle, cut at label zero. -/
def markList (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) : List (Mark P) := by
  classical
  letI := markLinearOrder hn hP
  exact Finset.univ.sort

theorem markList_nodup (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (markList hn hP).Nodup := by
  classical
  letI := markLinearOrder hn hP
  exact Finset.sort_nodup _ _

theorem mem_markList (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : a ∈ markList hn hP := by
  classical
  letI := markLinearOrder hn hP
  exact (Finset.mem_sort _).mpr (Finset.mem_univ a)

theorem markList_sorted (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (markList hn hP).Pairwise (fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b) := by
  classical
  letI := markLinearOrder hn hP
  exact Finset.pairwise_sort _ _

theorem markList_length (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (markList hn hP).length = n + 2 * (crossingSet P).card := by
  classical
  letI := markLinearOrder hn hP
  change (Finset.univ.sort (α := Mark P)).length = _
  rw [Finset.length_sort, Finset.card_univ, Fintype.card_sum, ZMod.card, card_visit]

/-- Ordinary vertices ensure a nonempty marked circle, even with no visits. -/
theorem markList_nonempty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (∃ a : Mark P, a ∈ markList hn hP) :=
  ⟨Sum.inl (0 : ZMod n), mem_markList hn hP _⟩

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual full marked traversal circle is the rotation class of its
complete sorted representative, retaining vertices as well as crossing visits. -/
def markCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) : Cycle (Mark P) :=
  (markList hn hP : Cycle (Mark P))

theorem markCycle_nodup (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (markCycle hn hP).Nodup := markList_nodup hn hP

theorem mem_markCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : a ∈ markCycle hn hP := mem_markList hn hP a

/-- Changing the chosen first entry by rotation does not change the marked circle. -/
theorem markCycle_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (k : ℕ) :
    ((markList hn hP).rotate k : Cycle (Mark P)) = markCycle hn hP :=
  Cycle.coe_eq_coe.mpr (List.IsRotated.forall _ _)

/-- The forward mark is constructed from the actual complete cyclic list. -/
def nextMark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (a : Mark P) : Mark P :=
  (markCycle hn hP).next (markCycle_nodup hn hP) a (mem_markCycle hn hP a)

/-- The backward mark is constructed from the same complete cyclic list. -/
def prevMark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (a : Mark P) : Mark P :=
  (markCycle hn hP).prev (markCycle_nodup hn hP) a (mem_markCycle hn hP a)

@[simp]
theorem nextMark_eq_list_next (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : nextMark hn hP a = (markList hn hP).next a (mem_markList hn hP a) := rfl

@[simp]
theorem prevMark_eq_list_prev (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : prevMark hn hP a = (markList hn hP).prev a (mem_markList hn hP a) := rfl

/-- The complete marked circle is duplicate-free, so backward traversal undoes forward traversal. -/
@[simp]
theorem prevMark_nextMark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : prevMark hn hP (nextMark hn hP a) = a :=
  Cycle.prev_next (markCycle hn hP) (markCycle_nodup hn hP) a (mem_markCycle hn hP a)

@[simp]
theorem nextMark_prevMark (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : nextMark hn hP (prevMark hn hP a) = a :=
  Cycle.next_prev (markCycle hn hP) (markCycle_nodup hn hP) a (mem_markCycle hn hP a)

/-- Actual cyclic successor as a permutation of all physical marks. Its inverse
is the actual predecessor, proved above rather than supplied as a hypothesis. -/
def markSuccessor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) : Equiv.Perm (Mark P) where
  toFun := nextMark hn hP
  invFun := prevMark hn hP
  left_inv := prevMark_nextMark hn hP
  right_inv := nextMark_prevMark hn hP

@[simp]
theorem markSuccessor_apply (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : markSuccessor hn hP a = nextMark hn hP a := rfl

@[simp]
theorem markSuccessor_symm_apply (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : Mark P) : (markSuccessor hn hP).symm a = prevMark hn hP a := rfl

/-- The forward formula advances the sorted index modulo the complete mark count,
including the last/first transition. -/
theorem markSuccessor_getElem (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (i : ℕ) (hi : i < (markList hn hP).length) :
    markSuccessor hn hP ((markList hn hP)[i]'hi) =
      (markList hn hP)[(i + 1) % (markList hn hP).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  change (markList hn hP).next ((markList hn hP)[i]'hi)
    (mem_markList hn hP ((markList hn hP)[i]'hi)) = _
  exact List.next_getElem (markList hn hP) (markList_nodup hn hP) i hi

/-- The inverse formula retreats modulo the same complete mark count, including
its first/last transition. No crossing-nonempty assumption is needed. -/
theorem markSuccessor_symm_getElem (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (i : ℕ) (hi : i < (markList hn hP).length) :
    (markSuccessor hn hP).symm ((markList hn hP)[i]'hi) =
      (markList hn hP)[(i + ((markList hn hP).length - 1)) % (markList hn hP).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  change (markList hn hP).prev ((markList hn hP)[i]'hi) _ = _
  exact List.prev_getElem (markList hn hP) (markList_nodup hn hP) i hi

/-- No original vertex or crossing visit lies strictly in the actual oriented
cyclic gap between a mark and its next mark. The sorted proof covers wraparound. -/
theorem nextMark_no_mark_between (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {a b : Mark P} (hnext : nextMark hn hP a = b) (u : Mark P) :
    ¬ traversalBetween (markPosition hn hP.1 a) (markPosition hn hP.1 u)
      (markPosition hn hP.1 b) := by
  classical
  let d : DecidableEq (Mark P) := inferInstance
  letI := markLinearOrder hn hP
  rw [nextMark_eq_list_next] at hnext
  have hnext' : @List.next (Mark P) d (Finset.univ : Finset (Mark P)).sort a
      ((Finset.mem_sort _).mpr (Finset.mem_univ a)) = b := hnext
  have hd : d = (fun a b : Mark P => LinearOrder.toDecidableEq a b) :=
    Subsingleton.elim _ _
  rw [hd] at hnext'
  have hg := sorted_next_no_cyclic_between (Finset.univ : Finset (Mark P))
    (Finset.mem_univ a) (Finset.mem_univ b) hnext' u (Finset.mem_univ u)
  exact hg

/-- Forward successor edges have no intervening actual mark. -/
theorem markSuccessor_no_mark_between (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a u : Mark P) :
    ¬ traversalBetween (markPosition hn hP.1 a) (markPosition hn hP.1 u)
      (markPosition hn hP.1 (markSuccessor hn hP a)) :=
  nextMark_no_mark_between hn hP rfl u

/-- Backward traversal uses the preceding oriented gap, from the predecessor to
the current mark, and that gap also contains no actual mark. -/
theorem markSuccessor_prev_no_mark_between (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a u : Mark P) :
    ¬ traversalBetween (markPosition hn hP.1 ((markSuccessor hn hP).symm a))
      (markPosition hn hP.1 u) (markPosition hn hP.1 a) :=
  nextMark_no_mark_between hn hP (nextMark_prevMark hn hP a) u

/-- Every actual sorted entry is reached in the successor orbit of the first
entry. Induction follows the concrete forward formula, before wraparound. -/
theorem markSuccessor_sameCycle_getElem (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (i : ℕ) (hi : i < (markList hn hP).length) :
    (markSuccessor hn hP).SameCycle
      ((markList hn hP)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le i) hi))
      ((markList hn hP)[i]'hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      exact Equiv.Perm.SameCycle.refl _ _
  | succ i ih =>
      intro hi
      have hi' : i < (markList hn hP).length := (Nat.lt_succ_self i).trans hi
      have hc := (ih hi').apply_right
      rw [markSuccessor_getElem hn hP i hi'] at hc
      simpa only [Nat.mod_eq_of_lt hi] using hc

/-- With no selected switch, all actual marks lie in one carrier orbit. This
follows from the complete list, including every vertex and crossing visit. -/
theorem markSuccessor_sameCycle (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a b : Mark P) :
    (markSuccessor hn hP).SameCycle a b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_markList hn hP a)
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (mem_markList hn hP b)
  exact (markSuccessor_sameCycle_getElem hn hP i hi).symm.trans
    (markSuccessor_sameCycle_getElem hn hP k hk)

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The original successor cannot fix a mark: its actual orbit contains the
two distinct original vertex marks zero and one. -/
theorem markSuccessor_ne_self (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) : markSuccessor hn hP a ≠ a := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro ha
  have h0 := (markSuccessor_sameCycle hn hP a (Sum.inl (0 : ZMod n))).eq_of_left ha
  have h1 := (markSuccessor_sameCycle hn hP a (Sum.inl (1 : ZMod n))).eq_of_left ha
  have h01 : (0 : ZMod n) = 1 := Sum.inl.inj (h0.symm.trans h1)
  have hz : (0 : ℕ) = 1 := by
    simpa only [ZMod.val_zero, ZMod.val_one] using congrArg ZMod.val h01
  omega

/-- Consecutive actual marks lie in increasing parameter order on one original
edge, or the second mark is precisely the next original vertex. Shifting the
cyclic cut to the first edge proves the same classification across label zero. -/
theorem markSuccessor_position_cases (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) :
    ((markPosition hn hP.1 (markSuccessor hn hP a)).1 = (markPosition hn hP.1 a).1 ∧
      (markPosition hn hP.1 a).2.val <
        (markPosition hn hP.1 (markSuccessor hn hP a)).2.val) ∨
      markSuccessor hn hP a = Sum.inl ((markPosition hn hP.1 a).1 + 1) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  let p := markPosition hn hP.1 a
  let r := markPosition hn hP.1 (markSuccessor hn hP a)
  let i := p.1
  let r' := traversalShift i r
  let z : Set.Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
  have hp : traversalShift i p = ((0 : ZMod n), p.2) := by
    simp [traversalShift, i]
  have hv : traversalShift i (markPosition hn hP.1 (Sum.inl (i + 1))) =
      ((1 : ZMod n), z) := by
    apply Prod.ext
    · change (i + 1) - i = 1
      abel
    · apply Subtype.ext
      rfl
  have hgap : ¬ traversalBetween ((0 : ZMod n), p.2) ((1 : ZMod n), z) r' := by
    intro h
    have hshift : traversalBetween (traversalShift i p)
        (traversalShift i (markPosition hn hP.1 (Sum.inl (i + 1))))
        (traversalShift i r) := by
      simpa only [hp, hv] using h
    exact (markSuccessor_no_mark_between hn hP a (Sum.inl (i + 1)))
      ((traversalBetween_shift i p (markPosition hn hP.1 (Sum.inl (i + 1))) r).mp hshift)
  have hk0 : traversalKey ((0 : ZMod n), p.2) = p.2.val := by
    simp [traversalKey]
  have hk1 : traversalKey ((1 : ZMod n), z) = 1 := by
    simp [traversalKey, z, ZMod.val_one]
  have hne : traversalKey r' ≠ p.2.val := by
    intro he
    have hkey : traversalKey (traversalShift i r) =
        traversalKey (traversalShift i p) := by
      rw [hp, hk0]
      exact he
    have hrp : r = p :=
      (traversalShiftEquiv i).injective (traversalKey_injective hkey)
    exact (markSuccessor_ne_self hn hP a) (markPosition_injective hn hP hrp)
  have hlt : p.2.val < traversalKey r' := by
    by_contra h
    have hle := le_of_not_gt h
    have hstrict := lt_of_le_of_ne hle hne
    apply hgap
    exact Or.inr (Or.inr ⟨by simpa only [hk0] using hstrict,
      by simpa only [hk0, hk1] using p.2.property.2⟩)
  have hle : traversalKey r' ≤ 1 := by
    by_contra h
    have hstrict : 1 < traversalKey r' := lt_of_not_ge h
    apply hgap
    exact Or.inl ⟨by simpa only [hk0, hk1] using p.2.property.2,
      by simpa only [hk1] using hstrict⟩
  have hval : r'.1.val ≤ 1 := by
    have hp0 := r'.2.property.1
    have hval' : (r'.1.val : ℝ) ≤ 1 := by
      dsimp only [traversalKey] at hle
      linarith
    exact_mod_cast hval'
  have hcases : r'.1.val = 0 ∨ r'.1.val = 1 := by omega
  rcases hcases with hzero | hone
  · have hr0 : r'.1 = 0 :=
      ZMod.val_injective n (by simpa only [ZMod.val_zero] using hzero)
    have hri : r.1 = p.1 := by
      have he : r.1 - i = 0 := hr0
      exact sub_eq_zero.mp he
    have hk : traversalKey r' = r.2.val := by
      change (r'.1.val : ℝ) + r.2.val = r.2.val
      rw [hr0, ZMod.val_zero, Nat.cast_zero, zero_add]
    exact Or.inl ⟨hri, by simpa only [hk] using hlt⟩
  · have hr1 : r'.1 = 1 :=
      ZMod.val_injective n (hone.trans (ZMod.val_one n).symm)
    have hrt : r.2.val = 0 := by
      have hp0 : 0 ≤ r.2.val := r.2.property.1
      have hk : traversalKey r' = 1 + r.2.val := by
        change (r'.1.val : ℝ) + r.2.val = 1 + r.2.val
        rw [hr1, ZMod.val_one, Nat.cast_one]
      rw [hk] at hle
      linarith
    have hri : r.1 = i + 1 := by
      have he : r.1 - i = 1 := hr1
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
    right
    apply markPosition_injective hn hP
    change r = markPosition hn hP.1 (Sum.inl (i + 1))
    apply Prod.ext
    · exact hri
    · apply Subtype.ext
      exact hrt

/-- The actual original successor endpoint lies a strictly positive parameter
distance ahead on the starting original edge, up to and including parameter
one. Its parameter is derived from the complete marked successor, not supplied. -/
theorem markSuccessor_subsegment_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) :
    ∃ t : ℝ, (markPosition hn hP.1 a).2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (markPosition hn hP.1 (markSuccessor hn hP a)) =
        edgePoint P (markPosition hn hP.1 a).1 t := by
  rcases markSuccessor_position_cases hn hP a with ⟨hi, ht⟩ | hv
  · refine ⟨(markPosition hn hP.1 (markSuccessor hn hP a)).2.val, ht,
      (markPosition hn hP.1 (markSuccessor hn hP a)).2.property.2.le, ?_⟩
    unfold traversalEvaluation
    rw [hi]
  · refine ⟨1, (markPosition hn hP.1 a).2.property.2, le_rfl, ?_⟩
    rw [hv, markPosition_evaluation_vertex]
    exact (edgePoint_one P (markPosition hn hP.1 a).1).symm

end
end SM.Carrier


#print axioms SM.Carrier.markSuccessor_ne_self
#print axioms SM.Carrier.markSuccessor_position_cases
#print axioms SM.Carrier.markSuccessor_subsegment_data
