import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.TraversalRelabel
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import SM.ContinuousGeometry
import SM.EuclideanPlane

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


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {P : LabelledTuple n}

/-- The other actual visit of the same crossing, chosen from its proved two-visit fiber. -/
def visitTwin (v : Visit P) : Visit P :=
  ⟨v.1, Classical.choose (crossing_other_visit v.1 v.2)⟩

@[simp]
theorem visitTwin_crossing (v : Visit P) : (visitTwin v).1 = v.1 := rfl

/-- The twin is distinct because the chosen crossing member is the other member. -/
theorem visitTwin_ne (v : Visit P) : visitTwin v ≠ v := by
  intro h
  have he := congrArg (fun w : Visit P => w.2.val) h
  exact (Classical.choose_spec (crossing_other_visit v.1 v.2)) (Subtype.ext he)

/-- No visit in this actual crossing fiber is omitted by the two named visits. -/
theorem visit_eq_or_twin (v w : Visit P) (hc : w.1 = v.1) :
    w = v ∨ w = visitTwin v := by
  rcases v with ⟨c, i⟩
  rcases w with ⟨d, j⟩
  change d = c at hc
  subst d
  let k := Classical.choose (crossing_other_visit c i)
  have hik : i ≠ k := (Classical.choose_spec (crossing_other_visit c i)).symm
  rcases crossing_visits_exhaust c i k hik j with he | he
  · exact Or.inl (congrArg (fun l : {k // k ∈ c.val} => (⟨c, l⟩ : Visit P)) he)
  · exact Or.inr (congrArg (fun l : {k // k ∈ c.val} => (⟨c, l⟩ : Visit P)) he)

/-- The distinct visit with the same crossing is uniquely the constructed twin. -/
theorem visitTwin_unique (v w : Visit P) (hc : w.1 = v.1) (hne : w ≠ v) :
    w = visitTwin v :=
  (visit_eq_or_twin v w hc).resolve_left hne

@[simp]
theorem visitTwin_involutive (v : Visit P) : visitTwin (visitTwin v) = v := by
  exact (visitTwin_unique (visitTwin v) v (visitTwin_crossing v).symm
    (visitTwin_ne v).symm).symm

/-- The actual crossing pairing, with the same constructed twin as inverse. -/
def visitTwinPerm : Equiv.Perm (Visit P) where
  toFun := visitTwin
  invFun := visitTwin
  left_inv := visitTwin_involutive
  right_inv := visitTwin_involutive

@[simp]
theorem visitTwinPerm_apply (v : Visit P) : visitTwinPerm v = visitTwin v := rfl

/-- Exchange only the two visits of each selected actual crossing. -/
def selectedVisitTwin (S : Finset (Crossing P)) (v : Visit P) : Visit P :=
  if v.1 ∈ S then visitTwin v else v

theorem selectedVisitTwin_of_mem (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∈ S) : selectedVisitTwin S v = visitTwin v :=
  if_pos hv

theorem selectedVisitTwin_of_not_mem (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∉ S) : selectedVisitTwin S v = v :=
  if_neg hv

@[simp]
theorem selectedVisitTwin_crossing (S : Finset (Crossing P)) (v : Visit P) :
    (selectedVisitTwin S v).1 = v.1 := by
  by_cases hv : v.1 ∈ S <;> simp [selectedVisitTwin, hv]

@[simp]
theorem selectedVisitTwin_involutive (S : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwin S (selectedVisitTwin S v) = v := by
  by_cases hv : v.1 ∈ S <;>
    simp [selectedVisitTwin, hv, visitTwin_crossing, visitTwin_involutive]

/-- This selected permutation is obtained from actual crossing membership and pairing. -/
def selectedVisitTwinPerm (S : Finset (Crossing P)) : Equiv.Perm (Visit P) where
  toFun := selectedVisitTwin S
  invFun := selectedVisitTwin S
  left_inv := selectedVisitTwin_involutive S
  right_inv := selectedVisitTwin_involutive S

@[simp]
theorem selectedVisitTwinPerm_apply (S : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwinPerm S v = selectedVisitTwin S v := rfl

@[simp]
theorem selectedVisitTwin_empty : selectedVisitTwin (∅ : Finset (Crossing P)) = id := by
  funext v
  simp [selectedVisitTwin]

/-- Exactly the visits of unselected crossings are fixed. -/
theorem selectedVisitTwin_eq_self_iff (S : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwin S v = v ↔ v.1 ∉ S := by
  by_cases hv : v.1 ∈ S <;> simp [selectedVisitTwin, hv, visitTwin_ne]

/-- The actual selected swaps commute, even when the supports overlap. -/
theorem selectedVisitTwin_commute (S T : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwin S (selectedVisitTwin T v) =
      selectedVisitTwin T (selectedVisitTwin S v) := by
  by_cases hs : v.1 ∈ S <;> by_cases ht : v.1 ∈ T <;>
    simp [selectedVisitTwin, hs, ht, visitTwin_crossing, visitTwin_involutive]

/-- For disjoint crossing supports, composition exchanges each selected pair once.
This gives the support-union step for order-independent reconnections. -/
theorem selectedVisitTwin_union_of_disjoint (S T : Finset (Crossing P))
    (hST : Disjoint S T) (v : Visit P) :
    selectedVisitTwin (S ∪ T) v = selectedVisitTwin S (selectedVisitTwin T v) := by
  by_cases hs : v.1 ∈ S
  · have ht : v.1 ∉ T := fun ht => (Finset.disjoint_left.mp hST) hs ht
    simp [selectedVisitTwin, Finset.mem_union, hs, ht]
  · by_cases ht : v.1 ∈ T <;>
      simp [selectedVisitTwin, Finset.mem_union, hs, ht, visitTwin_crossing]

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Exchange the two actual visits of each selected crossing, fixing every
original vertex. No independence hypothesis is needed for this permutation. -/
def selectedMarkPerm {P : LabelledTuple n} (S : Finset (Crossing P)) :
    Equiv.Perm (Mark P) :=
  Equiv.sumCongr (Equiv.refl (ZMod n)) (selectedVisitTwinPerm S)

@[simp]
theorem selectedMarkPerm_vertex {P : LabelledTuple n} (S : Finset (Crossing P))
    (i : ZMod n) : selectedMarkPerm S (Sum.inl i) = Sum.inl i := rfl

@[simp]
theorem selectedMarkPerm_visit {P : LabelledTuple n} (S : Finset (Crossing P))
    (v : Visit P) : selectedMarkPerm S (Sum.inr v) = Sum.inr (selectedVisitTwin S v) := rfl

theorem selectedMarkPerm_involutive {P : LabelledTuple n} (S : Finset (Crossing P))
    (a : Mark P) : selectedMarkPerm S (selectedMarkPerm S a) = a := by
  cases a <;> simp

/-- Both visits of a crossing evaluate to the same physical crossing point,
so switching them preserves the geometric endpoint at the reconnection. -/
theorem selectedMarkPerm_evaluation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (markPosition hn hP (selectedMarkPerm S a)) =
      traversalEvaluation P (markPosition hn hP a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, markPosition_evaluation_visit,
      markPosition_evaluation_visit, selectedVisitTwin_crossing]

theorem selectedMarkPerm_commute {P : LabelledTuple n} (S T : Finset (Crossing P))
    (a : Mark P) : selectedMarkPerm S (selectedMarkPerm T a) =
      selectedMarkPerm T (selectedMarkPerm S a) := by
  cases a with
  | inl i => rfl
  | inr v => exact congrArg Sum.inr (selectedVisitTwin_commute S T v)

/-- Disjoint selected supports reconnect each actual outgoing slot once. -/
theorem selectedMarkPerm_union_of_disjoint {P : LabelledTuple n}
    (S T : Finset (Crossing P)) (hST : Disjoint S T) :
    selectedMarkPerm (S ∪ T) = (selectedMarkPerm T).trans (selectedMarkPerm S) := by
  ext a
  cases a with
  | inl i => rfl
  | inr v => exact congrArg Sum.inr (selectedVisitTwin_union_of_disjoint S T hST v)

/-- The source outgoing reconnection rule: at a selected visit, take the
original outgoing arc of its twin; otherwise retain the original outgoing arc. -/
def smoothingSuccessor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Equiv.Perm (Mark P) :=
  (selectedMarkPerm S).trans (markSuccessor hn hP)

theorem smoothingSuccessor_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    smoothingSuccessor hn hP S (Sum.inl i) = markSuccessor hn hP (Sum.inl i) := rfl

theorem smoothingSuccessor_visit_of_mem (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    smoothingSuccessor hn hP S (Sum.inr v) =
      markSuccessor hn hP (Sum.inr (visitTwin v)) := by
  change markSuccessor hn hP (Sum.inr (selectedVisitTwin S v)) = _
  rw [selectedVisitTwin_of_mem S v hv]

theorem smoothingSuccessor_visit_of_not_mem (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP S (Sum.inr v) = markSuccessor hn hP (Sum.inr v) := by
  change markSuccessor hn hP (Sum.inr (selectedVisitTwin S v)) = _
  rw [selectedVisitTwin_of_not_mem S v hv]

theorem smoothingSuccessor_empty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    smoothingSuccessor hn hP ∅ = markSuccessor hn hP := by
  ext a
  cases a with
  | inl i => rfl
  | inr v =>
    change markSuccessor hn hP (Sum.inr (selectedVisitTwin ∅ v)) = _
    rw [selectedVisitTwin_empty]
    rfl

/-- Adding disjoint switches acts on outgoing slots of the already reconnected
successor. This is an equality of the constructed permutations. -/
theorem smoothingSuccessor_union_of_disjoint (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S T : Finset (Crossing P)) (hST : Disjoint S T) :
    smoothingSuccessor hn hP (S ∪ T) =
      (selectedMarkPerm T).trans (smoothingSuccessor hn hP S) := by
  rw [smoothingSuccessor, selectedMarkPerm_union_of_disjoint S T hST]
  rfl

/-- Actual cyclic components are the orbits of the constructed finite successor.
Their geometric regularity and independent-support count remain separate claims. -/
def Component (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) :=
  Quotient (Equiv.Perm.SameCycle.setoid (smoothingSuccessor hn hP S))

/-- A mark belongs to its own successor orbit. Keeping the node identity at a
reconnection implements the incoming-arc ownership convention. -/
def owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) : Component hn hP S :=
  Quotient.mk _ a

theorem owner_eq_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a b : Mark P) :
    owner hn hP S a = owner hn hP S b ↔ (smoothingSuccessor hn hP S).SameCycle a b :=
  by
    constructor
    · intro hab
      exact Quotient.exact hab
    · intro hab
      apply Quotient.sound
      exact hab

theorem owner_successor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    owner hn hP S (smoothingSuccessor hn hP S a) = owner hn hP S a :=
  (owner_eq_iff hn hP S _ _).mpr (Equiv.Perm.SameCycle.refl _ a).apply_left

theorem owner_predecessor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    owner hn hP S ((smoothingSuccessor hn hP S).symm a) = owner hn hP S a :=
  (owner_eq_iff hn hP S _ _).mpr (Equiv.Perm.SameCycle.refl _ a).symm_apply_left

theorem owner_surjective (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Function.Surjective (owner hn hP S) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact ⟨a, rfl⟩

instance componentFintype (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Fintype (Component hn hP S) :=
  Quotient.fintype _

theorem component_card_pos (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : 0 < Fintype.card (Component hn hP S) :=
  Fintype.card_pos_iff.mpr ⟨owner hn hP S (Sum.inl (0 : ZMod n))⟩

/-- The empty support has a single actual component, since the unmodified
successor traverses every mark. -/
theorem component_empty_subsingleton (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) : Subsingleton (Component hn hP ∅) := by
  constructor
  intro q r
  obtain ⟨a, rfl⟩ := owner_surjective hn hP ∅ q
  obtain ⟨b, rfl⟩ := owner_surjective hn hP ∅ r
  apply (owner_eq_iff hn hP ∅ a b).mpr
  rw [smoothingSuccessor_empty]
  exact markSuccessor_sameCycle hn hP a b

theorem component_card_empty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Fintype.card (Component hn hP ∅) = 1 := by
  letI := component_empty_subsingleton hn hP
  letI : Unique (Component hn hP ∅) :=
    uniqueOfSubsingleton (owner hn hP ∅ (Sum.inl (0 : ZMod n)))
  exact Fintype.card_unique

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Difference of two points on the same original oriented edge, with the
parameter difference retained as its exact scalar. -/
theorem edgePoint_sub_edgePoint (P : LabelledTuple n) (i : ZMod n) (s t : ℝ) :
    edgePoint P i t - edgePoint P i s = (t - s) • edge P i := by
  apply Prod.ext <;> simp [edgePoint, smul_eq_mul] <;> ring

/-- Affine interpolation of actual edge points agrees with interpolation of
their parameters. No positivity assumption is needed for this algebraic identity. -/
theorem edgePoint_affine (P : LabelledTuple n) (i : ZMod n) (s t u : ℝ) :
    edgePoint P i s + u • (edgePoint P i t - edgePoint P i s) =
      edgePoint P i (s + u * (t - s)) := by
  apply Prod.ext <;> simp [edgePoint, smul_eq_mul] <;> ring

/-- The actual straight segment from a mark to its smoothed successor.
Its positive original-edge realization is proved in the next packet. -/
def smoothingSegment (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) (u : ℝ) : Plane :=
  traversalEvaluation P (markPosition hn hP.1 a) +
    u • (traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
      traversalEvaluation P (markPosition hn hP.1 a))

@[simp]
theorem smoothingSegment_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSegment hn hP S a 0 = traversalEvaluation P (markPosition hn hP.1 a) := by
  simp [smoothingSegment]

@[simp]
theorem smoothingSegment_one (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSegment hn hP S a 1 =
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) := by
  simp [smoothingSegment]

/-- Every constructed segment joins exactly to the next segment, including
the closing join of an actual successor orbit. -/
theorem smoothingSegment_glue (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSegment hn hP S a 1 =
      smoothingSegment hn hP S (smoothingSuccessor hn hP S a) 0 := by
  rw [smoothingSegment_one, smoothingSegment_zero]

theorem continuous_smoothingSegment (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    Continuous (smoothingSegment hn hP S a) :=
  continuous_const.add (continuous_id.smul continuous_const)

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every actual smoothed outgoing segment is one positive piece of the
original outgoing edge at the selected slot. Physical twin equality identifies
the starting point, without identifying the distinct incoming marks. -/
theorem smoothingSegment_subsegment_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    let p := markPosition hn hP.1 (selectedMarkPerm S a)
    ∃ t : ℝ, p.2.val < t ∧ t ≤ 1 ∧
      traversalEvaluation P (markPosition hn hP.1 a) = edgePoint P p.1 p.2.val ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
        edgePoint P p.1 t ∧
      ∀ u : ℝ, smoothingSegment hn hP S a u = edgePoint P p.1 (p.2.val + u * (t - p.2.val)) := by
  dsimp only
  obtain ⟨t, hst, ht1, he⟩ := markSuccessor_subsegment_data hn hP (selectedMarkPerm S a)
  have hstart : traversalEvaluation P (markPosition hn hP.1 a) =
      edgePoint P (markPosition hn hP.1 (selectedMarkPerm S a)).1
        (markPosition hn hP.1 (selectedMarkPerm S a)).2.val :=
    (selectedMarkPerm_evaluation hn hP.1 S a).symm
  have hend : traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) =
      edgePoint P (markPosition hn hP.1 (selectedMarkPerm S a)).1 t := he
  refine ⟨t, hst, ht1, hstart, hend, ?_⟩
  intro u
  unfold smoothingSegment
  rw [hstart, hend, edgePoint_affine]

/-- The exact endpoint displacement is a strictly positive multiple of the
actual original outgoing edge. The scalar is the proved parameter gap. -/
theorem smoothingSegment_positive_direction (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    ∃ c : ℝ, 0 < c ∧
      traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
        traversalEvaluation P (markPosition hn hP.1 a) =
        c • edge P (markPosition hn hP.1 (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, _, hstart, hend, _⟩ := smoothingSegment_subsegment_data hn hP S a
  refine ⟨t - (markPosition hn hP.1 (selectedMarkPerm S a)).2.val, sub_pos.mpr hst, ?_⟩
  rw [hstart, hend, edgePoint_sub_edgePoint]

theorem smoothingSegment_displacement_ne_zero (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
      traversalEvaluation P (markPosition hn hP.1 a) ≠ 0 := by
  obtain ⟨c, hc, he⟩ := smoothingSegment_positive_direction hn hP S a
  rw [he]
  exact smul_ne_zero (ne_of_gt hc)
    ((g1 hn P hP.1).2.1 (markPosition hn hP.1 (selectedMarkPerm S a)).1)

/-- Positive length uses the Euclidean length of the source plane, not the
product-space norm. -/
theorem smoothingSegment_length_pos (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    0 < euclideanLength
      (traversalEvaluation P (markPosition hn hP.1 (smoothingSuccessor hn hP S a)) -
        traversalEvaluation P (markPosition hn hP.1 a)) :=
  euclideanLength_pos (smoothingSegment_displacement_ne_zero hn hP S a)

/-- Parameters in the unit interval stay on the actual original edge segment. -/
theorem smoothingSegment_mem_edgeSegment (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    smoothingSegment hn hP S a u ∈
      edgeSegment P (markPosition hn hP.1 (selectedMarkPerm S a)).1 := by
  obtain ⟨t, hst, ht1, _, _, hformula⟩ := smoothingSegment_subsegment_data hn hP S a
  let s := (markPosition hn hP.1 (selectedMarkPerm S a)).2.val
  have hs0 : 0 ≤ s := (markPosition hn hP.1 (selectedMarkPerm S a)).2.property.1
  have hgap : 0 ≤ t - s := le_of_lt (sub_pos.mpr hst)
  refine ⟨s + u * (t - s), ?_, ?_, hformula u⟩
  · exact add_nonneg hs0 (mul_nonneg hu0 hgap)
  · have hmul := mul_le_mul_of_nonneg_right hu1 hgap
    nlinarith

/-- Each actual segment traverses its positive parameter interval without
repetition. This is local segment injectivity, not injectivity of a carrier. -/
theorem smoothingSegment_injective (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    Function.Injective (smoothingSegment hn hP S a) := by
  intro u v huv
  obtain ⟨t, hst, _, _, _, hformula⟩ := smoothingSegment_subsegment_data hn hP S a
  rw [hformula u, hformula v] at huv
  have hparam := edgePoint_injective
    ((g1 hn P hP.1).2.1 (markPosition hn hP.1 (selectedMarkPerm S a)).1) huv
  exact mul_right_cancel₀ (ne_of_gt (sub_pos.mpr hst)) (add_left_cancel hparam)

/-- No support can produce a fixed actual mark: its outgoing geometric segment
has nonzero displacement. This uses geometry beyond the abstract split model. -/
theorem smoothingSuccessor_ne_self (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (a : Mark P) :
    smoothingSuccessor hn hP S a ≠ a := by
  intro he
  have hne := smoothingSegment_displacement_ne_zero hn hP S a
  rw [he, sub_self] at hne
  exact hne rfl

end
end SM.Carrier


#print axioms SM.Carrier.smoothingSegment_subsegment_data
#print axioms SM.Carrier.smoothingSegment_positive_direction
#print axioms SM.Carrier.smoothingSegment_displacement_ne_zero
#print axioms SM.Carrier.smoothingSegment_length_pos
#print axioms SM.Carrier.smoothingSegment_mem_edgeSegment
#print axioms SM.Carrier.smoothingSegment_injective
#print axioms SM.Carrier.smoothingSuccessor_ne_self
