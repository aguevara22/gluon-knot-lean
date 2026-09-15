import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Concrete

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
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- On the actual two-visit fiber, selecting this crossing is exactly the
transposition of its constructed pair; all other crossing fibers are fixed. -/
theorem selectedVisitTwin_singleton {P : LabelledTuple n} (v w : Visit P) :
    selectedVisitTwin {v.1} w = Equiv.swap v (visitTwin v) w := by
  by_cases hc : w.1 = v.1
  · rcases visit_eq_or_twin v w hc with hw | hw
    · subst w
      simp [selectedVisitTwin]
    · subst w
      simp [selectedVisitTwin]
  · have hwv : w ≠ v := fun h => hc (congrArg (fun x : Visit P => x.1) h)
    have hwt : w ≠ visitTwin v := by
      intro h
      apply hc
      rw [h, visitTwin_crossing]
    rw [Equiv.swap_apply_of_ne_of_ne hwv hwt]
    simp [selectedVisitTwin, hc]

theorem selectedVisitTwinPerm_singleton {P : LabelledTuple n} (v : Visit P) :
    selectedVisitTwinPerm {v.1} = Equiv.swap v (visitTwin v) := by
  apply Equiv.ext
  intro w
  exact selectedVisitTwin_singleton v w

/-- The full marked permutation fixes original vertices and exchanges exactly
the two distinct actual marks of this crossing. -/
theorem selectedMarkPerm_singleton {P : LabelledTuple n} (v : Visit P) :
    selectedMarkPerm {v.1} =
      Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  rw [selectedMarkPerm, selectedVisitTwinPerm_singleton]
  exact Equiv.Perm.sumCongr_refl_swap v (visitTwin v)

/-- Adding an unselected actual crossing swaps its two outgoing slots in the
current successor. Right multiplication applies that transposition first. -/
theorem smoothingSuccessor_insert (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP (insert v.1 S) =
      smoothingSuccessor hn hP S *
        Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  have hS : insert v.1 S = S ∪ {v.1} := by
    ext c
    simp [or_comm]
  rw [hS, smoothingSuccessor_union_of_disjoint hn hP S {v.1}
    (Finset.disjoint_singleton_right.mpr hv), selectedMarkPerm_singleton]
  rfl

theorem smoothingSuccessor_insert_visit (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP (insert v.1 S) (Sum.inr v) =
      smoothingSuccessor hn hP S (Sum.inr (visitTwin v)) := by
  rw [smoothingSuccessor_insert hn hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left]

theorem smoothingSuccessor_insert_twin (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP (insert v.1 S) (Sum.inr (visitTwin v)) =
      smoothingSuccessor hn hP S (Sum.inr v) := by
  rw [smoothingSuccessor_insert hn hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_right]

/-- Every other marked outgoing slot is unchanged by this one reconnection. -/
theorem smoothingSuccessor_insert_other (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (a : Mark P) (hav : a ≠ Sum.inr v) (hat : a ≠ Sum.inr (visitTwin v)) :
    smoothingSuccessor hn hP (insert v.1 S) a = smoothingSuccessor hn hP S a := by
  rw [smoothingSuccessor_insert hn hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hav hat]

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The constructed actual cyclic successor is exactly the permutation formed
from the complete sorted mark list, on every actual mark. -/
theorem markSuccessor_eq_formPerm (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) : markSuccessor hn hP = (markList hn hP).formPerm := by
  classical
  ext a
  change (markList hn hP).next a (mem_markList hn hP a) = _
  exact (List.formPerm_apply_mem_eq_next (markList_nodup hn hP) a
    (mem_markList hn hP a)).symm

/-- An actual mark can be made the first entry by rotating the complete list.
The rotation is constructed by splitting at its actual occurrence. -/
theorem markList_rotate_start (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a : Mark P) :
    ∃ k : ℕ, ∃ T : List (Mark P), (markList hn hP).rotate k = a :: T := by
  obtain ⟨L, R, he⟩ := List.mem_iff_append.mp (mem_markList hn hP a)
  refine ⟨L.length, R ++ L, ?_⟩
  rw [he, List.rotate_append_length_eq, List.cons_append]

/-- For any distinct actual marks, the complete marked circle has the literal
split-list presentation used by the source. Either intervening list may be empty. -/
theorem markList_rotate_split (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a b : Mark P) (hab : a ≠ b) :
    ∃ k : ℕ, ∃ A B : List (Mark P),
      (markList hn hP).rotate k = a :: (A ++ b :: B) := by
  obtain ⟨k, T, hrot⟩ := markList_rotate_start hn hP a
  have hb : b ∈ a :: T := hrot ▸ (List.mem_rotate.mpr (mem_markList hn hP b))
  have hbT : b ∈ T := (List.mem_cons.mp hb).resolve_left hab.symm
  obtain ⟨A, B, hT⟩ := List.mem_iff_append.mp hbT
  exact ⟨k, A, B, hT ▸ hrot⟩

/-- The actual original successor admits the source's duplicate-free split-list
presentation for arbitrary distinct actual marks. Rotation retains every vertex
and crossing visit, so no supplied representation or current-carrier premise enters. -/
theorem markSuccessor_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (a b : Mark P) (hab : a ≠ b) :
    ∃ A B : List (Mark P),
      (a :: (A ++ b :: B)).Nodup ∧
      (a :: (A ++ b :: B)).formPerm = markSuccessor hn hP ∧
      ∀ m : Mark P, m ∈ a :: (A ++ b :: B) := by
  classical
  obtain ⟨k, A, B, hrot⟩ := markList_rotate_split hn hP a b hab
  refine ⟨A, B, ?_, ?_, ?_⟩
  · rw [← hrot]
    exact List.nodup_rotate.mpr (markList_nodup hn hP)
  · rw [← hrot, List.formPerm_rotate _ (markList_nodup hn hP) k]
    exact (markSuccessor_eq_formPerm hn hP).symm
  · intro m
    rw [← hrot]
    exact List.mem_rotate.mpr (mem_markList hn hP m)

end
end SM.Carrier


namespace SM.Carrier

variable {α : Type*} [DecidableEq α]

/-- Adjacent-transposition products concatenate at their shared endpoint.
No distinctness assumption is needed for this algebraic identity. -/
theorem formPerm_append_shared (L R : List α) (a : α) :
    (L ++ a :: R).formPerm = (L ++ [a]).formPerm * (a :: R).formPerm := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => rfl
    | cons y L =>
      simpa only [List.cons_append, List.formPerm_cons_cons, mul_assoc] using
        congrArg (fun q : Equiv.Perm α => Equiv.swap x y * q) ih

/-- Relabelling a list conjugates its actual adjacent-transposition product. -/
theorem formPerm_map_perm (f : Equiv.Perm α) (L : List α) :
    (L.map f).formPerm = f * L.formPerm * f⁻¹ := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => simp
    | cons y L =>
      change Equiv.swap (f x) (f y) * ((y :: L).map f).formPerm =
        f * (Equiv.swap x y * (y :: L).formPerm) * f⁻¹
      rw [ih, Equiv.swap_apply_apply]
      simp [mul_assoc]

/-- Swapping an absent alternative head changes only the head of a cycle list. -/
theorem formPerm_conj_swap_head (a b : α) (L : List α)
    (ha : a ∉ L) (hb : b ∉ L) :
    Equiv.swap a b * (a :: L).formPerm * Equiv.swap a b = (b :: L).formPerm := by
  have hm : L.map (Equiv.swap a b) = L := by
    calc
      L.map (Equiv.swap a b) = L.map id := by
        apply List.map_congr_left
        intro x hx
        exact Equiv.swap_apply_of_ne_of_ne
          (fun he => ha (he ▸ hx)) (fun he => hb (he ▸ hx))
      _ = L := by simp
  simpa only [List.map_cons, Equiv.swap_apply_left, hm, Equiv.swap_inv] using
    (formPerm_map_perm (Equiv.swap a b) (a :: L)).symm

/-- Disjoint node lists give disjoint permutation supports, including singleton lists. -/
theorem formPerm_disjoint_of_disjoint (L R : List α) (h : L.Disjoint R) :
    Equiv.Perm.Disjoint L.formPerm R.formPerm := by
  intro x
  by_cases hx : x ∈ L
  · exact Or.inr (List.formPerm_apply_of_notMem (fun hr => h hx hr))
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

/-- The two source split lists are duplicate-free and have disjoint node sets.
The original list's exact Nodup hypothesis supplies every endpoint exclusion. -/
theorem splitList_child_data (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: B).Nodup ∧ (b :: A).Nodup ∧ (a :: B).Disjoint (b :: A) := by
  rcases List.nodup_cons.mp h with ⟨ha, hAB⟩
  rcases List.nodup_append'.mp hAB with ⟨hA, hbB, hAd⟩
  rcases List.nodup_cons.mp hbB with ⟨hb, hB⟩
  have haA : a ∉ A := fun hx => ha (List.mem_append.mpr (Or.inl hx))
  have haB : a ∉ B := fun hx =>
    ha (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b hx)))
  have hab : a ≠ b := by
    intro he
    apply ha
    simp [he]
  have hbA : b ∉ A := fun hx => hAd hx List.mem_cons_self
  refine ⟨List.nodup_cons.mpr ⟨haB, hB⟩, List.nodup_cons.mpr ⟨hbA, hA⟩, ?_⟩
  intro x hx hy
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases List.mem_cons.mp hy with he | hy
    · exact hab he
    · exact haA hy
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact hb hx
    · exact hAd hy (List.mem_cons_of_mem b hx)

/-- Switching the two outgoing slots splits the concrete old cyclic list into
exactly the source's two products. Either open arc may be empty. -/
theorem splitList_identity (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: (A ++ b :: B)).formPerm * Equiv.swap a b =
      (a :: B).formPerm * (b :: A).formPerm := by
  obtain ⟨haB, hbA, hd⟩ := splitList_child_data a b A B h
  have haA : a ∉ A := fun hx => h.notMem (List.mem_append.mpr (Or.inl hx))
  have hbB : b ∉ B := h.of_cons.of_append_right.notMem
  have hshort : ((a :: A) ++ [b]).Nodup := by
    have ht : (((a :: A) ++ [b]) ++ B).Nodup := by
      simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using h
    exact ht.of_append_left
  have hrotN : (b :: a :: A).Nodup := by
    simpa only [List.append_nil] using (List.nodup_middle.mp hshort)
  have hrot : ((a :: A) ++ [b]).formPerm = (b :: a :: A).formPerm := by
    simpa only [List.rotate_cons_succ, List.rotate_zero] using
      (List.formPerm_rotate_one (b :: a :: A) hrotN)
  have hconjA := formPerm_conj_swap_head a b A haA hbA.notMem
  have hconjB : Equiv.swap a b * (b :: B).formPerm * Equiv.swap a b =
      (a :: B).formPerm := by
    simpa only [Equiv.swap_comm b a] using
      (formPerm_conj_swap_head b a B hbB haB.notMem)
  calc
    (a :: (A ++ b :: B)).formPerm * Equiv.swap a b =
        (Equiv.swap a b * (a :: A).formPerm * (b :: B).formPerm) *
          Equiv.swap a b := by
      rw [show a :: (A ++ b :: B) = (a :: A) ++ b :: B from rfl,
        formPerm_append_shared, hrot, List.formPerm_cons_cons, Equiv.swap_comm b a]
    _ = (Equiv.swap a b * (a :: A).formPerm * Equiv.swap a b) *
        (Equiv.swap a b * (b :: B).formPerm * Equiv.swap a b) := by
      simp [mul_assoc]
    _ = (b :: A).formPerm * (a :: B).formPerm := by rw [hconjA, hconjB]
    _ = (a :: B).formPerm * (b :: A).formPerm :=
      (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq.symm

/-- A product with a disjoint list cycle remains a cycle on the first node set.
The proof uses integer powers and includes one-node cycles. -/
theorem formPerm_mul_isCycleOn_left (L R : List α) (hL : L.Nodup)
    (hd : L.Disjoint R) :
    (L.formPerm * R.formPerm).IsCycleOn {x | x ∈ L} := by
  have hc := hL.isCycleOn_formPerm
  have hfix : ∀ x ∈ L, R.formPerm x = x := fun x hx =>
    List.formPerm_apply_of_notMem (fun hr => hd hx hr)
  have hz (x : α) (hx : x ∈ L) (k : ℤ) :
      ((L.formPerm * R.formPerm) ^ k) x = (L.formPerm ^ k) x := by
    rw [(formPerm_disjoint_of_disjoint L R hd).commute.mul_zpow,
      Equiv.Perm.mul_apply,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hfix x hx) k]
  refine ⟨hc.1.congr ?_, ?_⟩
  · intro x hx
    exact (show (L.formPerm * R.formPerm) x = L.formPerm x by
      rw [Equiv.Perm.mul_apply, hfix x hx]).symm
  · intro x hx y hy
    obtain ⟨k, hk⟩ := hc.2 hx hy
    exact ⟨k, (hz x hx k).trans hk⟩

/-- The child containing the incoming endpoint a is the complete cycle a,B. -/
theorem splitList_left_isCycleOn (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).IsCycleOn
      {x | x ∈ a :: B} := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  rw [splitList_identity a b A B h]
  exact formPerm_mul_isCycleOn_left (a :: B) (b :: A) hL hd

/-- The child containing the incoming endpoint b is the complete cycle b,A. -/
theorem splitList_right_isCycleOn (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).IsCycleOn
      {x | x ∈ b :: A} := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  rw [splitList_identity a b A B h,
    (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq]
  exact formPerm_mul_isCycleOn_left (b :: A) (a :: B) hR hd.symm

/-- The entire successor orbit of a is exactly its source split list. -/
theorem splitList_left_sameCycle_iff (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) (x : α) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle a x ↔
      x ∈ a :: B := by
  have hc := splitList_left_isCycleOn a b A B h
  constructor
  · rintro ⟨k, rfl⟩
    exact (hc.1.perm_zpow k).mapsTo List.mem_cons_self
  · intro hx
    exact hc.2 List.mem_cons_self hx

/-- The entire successor orbit of b is exactly its source split list. -/
theorem splitList_right_sameCycle_iff (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) (x : α) :
    ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle b x ↔
      x ∈ b :: A := by
  have hc := splitList_right_isCycleOn a b A B h
  constructor
  · rintro ⟨k, rfl⟩
    exact (hc.1.perm_zpow k).mapsTo List.mem_cons_self
  · intro hx
    exact hc.2 List.mem_cons_self hx

/-- The two incoming endpoint marks belong to different successor orbits. -/
theorem splitList_not_sameCycle (a b : α) (A B : List α)
    (h : (a :: (A ++ b :: B)).Nodup) :
    ¬ ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b).SameCycle a b := by
  intro hc
  have hb := (splitList_left_sameCycle_iff a b A B h b).mp hc
  exact (splitList_child_data a b A B h).2.2 hb List.mem_cons_self

end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual full marked traversal, cut at a crossing's actual two visits,
supplies the source split list. Its completeness is proved from the traversal. -/
theorem smoothingSuccessor_singleton_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (v : Visit P) :
    ∃ A B : List (Mark P),
      (Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)).Nodup ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) ∧
      smoothingSuccessor hn hP {v.1} =
        (Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)).formPerm *
          Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  have hv : (Sum.inr v : Mark P) ≠ Sum.inr (visitTwin v) := by
    intro h
    exact (visitTwin_ne v).symm (Sum.inr.inj h)
  obtain ⟨A, B, hN, hperm, hfull⟩ :=
    markSuccessor_splitList hn hP (Sum.inr v) (Sum.inr (visitTwin v)) hv
  refine ⟨A, B, hN, hfull, ?_⟩
  have he := smoothingSuccessor_insert hn hP (∅ : Finset (Crossing P)) v
    (Finset.notMem_empty v.1)
  simpa only [Finset.insert_empty, smoothingSuccessor_empty, hperm] using he

/-- The two incoming owners at one actual selected crossing are distinct. -/
theorem owner_singleton_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) :
    owner hn hP {v.1} (Sum.inr v) ≠ owner hn hP {v.1} (Sum.inr (visitTwin v)) := by
  obtain ⟨A, B, hN, _, he⟩ := smoothingSuccessor_singleton_splitList hn hP v
  intro h
  have hc := (owner_eq_iff hn hP {v.1} _ _).mp h
  rw [he] at hc
  exact splitList_not_sameCycle (Sum.inr v) (Sum.inr (visitTwin v)) A B hN hc

/-- Every actual component of one selected crossing is one of the two endpoint
components. This uses completeness of the actual list, including all vertices. -/
theorem owner_singleton_exhaust (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) (q : Component hn hP {v.1}) :
    q = owner hn hP {v.1} (Sum.inr v) ∨
      q = owner hn hP {v.1} (Sum.inr (visitTwin v)) := by
  obtain ⟨A, B, hN, hfull, he⟩ := smoothingSuccessor_singleton_splitList hn hP v
  obtain ⟨x, rfl⟩ := owner_surjective hn hP {v.1} q
  have hcL (hx : x ∈ Sum.inr v :: B) :
      owner hn hP {v.1} x = owner hn hP {v.1} (Sum.inr v) := by
    apply (owner_eq_iff hn hP {v.1} _ _).mpr
    rw [he]
    exact ((splitList_left_sameCycle_iff (Sum.inr v) (Sum.inr (visitTwin v)) A B hN x).mpr hx).symm
  have hcR (hx : x ∈ Sum.inr (visitTwin v) :: A) :
      owner hn hP {v.1} x = owner hn hP {v.1} (Sum.inr (visitTwin v)) := by
    apply (owner_eq_iff hn hP {v.1} _ _).mpr
    rw [he]
    exact ((splitList_right_sameCycle_iff (Sum.inr v) (Sum.inr (visitTwin v)) A B hN x).mpr hx).symm
  rcases List.mem_cons.mp (hfull x) with hx | hx
  · exact Or.inl (hcL (List.mem_cons.mpr (Or.inl hx)))
  · rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (hcR (List.mem_cons_of_mem _ hx))
    · rcases List.mem_cons.mp hx with hx | hx
      · exact Or.inr (hcR (List.mem_cons.mpr (Or.inl hx)))
      · exact Or.inl (hcL (List.mem_cons_of_mem _ hx))

/-- Exactly two actual successor-orbit components arise from one selected
crossing. No arbitrary cycle representation or component correspondence is assumed. -/
theorem component_card_singleton (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) : Fintype.card (Component hn hP {v.1}) = 2 := by
  have hu : (Finset.univ : Finset (Component hn hP {v.1})) =
      {owner hn hP {v.1} (Sum.inr v), owner hn hP {v.1} (Sum.inr (visitTwin v))} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact owner_singleton_exhaust hn hP v q
  have hc : (Finset.univ : Finset (Component hn hP {v.1})).card = 2 :=
    Finset.card_eq_two.mpr ⟨_, _, owner_singleton_ne hn hP v, hu⟩
  simpa only [Finset.card_univ] using hc

end
end SM.Carrier


#print axioms SM.Carrier.smoothingSuccessor_singleton_splitList
#print axioms SM.Carrier.owner_singleton_ne
#print axioms SM.Carrier.owner_singleton_exhaust
#print axioms SM.Carrier.component_card_singleton
