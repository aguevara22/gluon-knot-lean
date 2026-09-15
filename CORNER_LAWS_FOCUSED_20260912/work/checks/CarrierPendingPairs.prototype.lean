import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Set.Function
import SM.InterlaceSupports
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

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


namespace List

variable {α : Type*}

/-- Filtering respects cyclic rotation, even when the retained prefix or
suffix is empty and even when list entries repeat. -/
theorem IsRotated.filter {l l' : List α} (h : l ~r l') (p : α → Bool) :
    l.filter p ~r l'.filter p := by
  obtain ⟨k, hk, rfl⟩ := isRotated_iff_mod.mp h
  rw [rotate_eq_drop_append_take hk, filter_append]
  have hsplit : l.filter p = (l.take k).filter p ++ (l.drop k).filter p := by
    rw [← filter_append, take_append_drop]
  rw [hsplit]
  exact isRotated_append

end List

namespace Cycle

variable {α β : Type*}

/-- Retain exactly the entries satisfying p in their cyclic order. The
quotient construction uses the proved rotation compatibility of List.filter. -/
def filter (p : α → Bool) : Cycle α → Cycle α :=
  Quotient.map' (List.filter p) (fun _ _ h => h.filter p)

@[simp]
theorem filter_coe (p : α → Bool) (l : List α) :
    filter p (l : Cycle α) = (l.filter p : Cycle α) := rfl

@[simp]
theorem filter_nil (p : α → Bool) : filter p (nil : Cycle α) = nil := rfl

@[simp]
theorem mem_filter {p : α → Bool} {a : α} {s : Cycle α} :
    a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Quotient.inductionOn' s (by simp)

/-- Filtering by a property of the mapped letter commutes with the letter
map. No injectivity is required, so this also applies when two visits carry
the same crossing label. -/
theorem filter_map (p : β → Bool) (f : α → β) (s : Cycle α) :
    (s.map f).filter p = (s.filter (fun a => p (f a))).map f := by
  induction s using Quotient.inductionOn' with
  | _ l =>
    change (((l.map f).filter p : List β) : Cycle β) =
      (((l.filter (fun a => p (f a))).map f : List β) : Cycle β)
    exact congrArg (fun t : List β => (t : Cycle β)) List.filter_map

@[simp]
theorem filter_filter (p q : α → Bool) (s : Cycle α) :
    (s.filter q).filter p = s.filter (fun a => p a && q a) := by
  induction s using Quotient.inductionOn' with
  | _ l =>
    change (((l.filter q).filter p : List α) : Cycle α) =
      ((l.filter (fun a => p a && q a) : List α) : Cycle α)
    exact congrArg (fun t : List α => (t : Cycle α)) List.filter_filter

/-- A filter retaining every occurring entry leaves the cycle unchanged. -/
theorem filter_eq_self (p : α → Bool) (s : Cycle α) :
    (∀ a ∈ s, p a) → s.filter p = s :=
  Quotient.inductionOn' s fun l h =>
    congrArg (fun t : List α => (t : Cycle α)) (List.filter_eq_self.mpr h)

/-- Removing visits cannot introduce repetitions in their cyclic sequence. -/
theorem Nodup.filter {s : Cycle α} (h : s.Nodup) (p : α → Bool) :
    (s.filter p).Nodup := by
  induction s using Quotient.inductionOn' with
  | _ l => exact List.Nodup.filter p h

end Cycle


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The original traversal's cyclic order restricted to one actual successor
orbit. Compatibility with the reconnected successor is a separate invariant. -/
def componentCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) : Cycle (Mark P) :=
  (markCycle hn hP).filter (fun m => decide (owner hn hP T m = q))

/-- Filtering the complete sorted representative represents the inherited
component cycle. The definition is independent of the chosen first mark. -/
theorem componentCycle_eq_filtered_markList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    componentCycle hn hP T q =
      ((markList hn hP).filter (fun m => decide (owner hn hP T m = q)) : Cycle (Mark P)) := rfl

/-- Every actual mark occurs in the original circle, so the sole membership
condition in its inherited component cycle is its actual incoming owner. -/
@[simp]
theorem mem_componentCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) (m : Mark P) :
    m ∈ componentCycle hn hP T q ↔ owner hn hP T m = q := by
  simp [componentCycle, Cycle.mem_filter, mem_markCycle]

/-- Restriction retains the original marked circle's absence of repetitions. -/
theorem componentCycle_nodup (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) :
    (componentCycle hn hP T q).Nodup :=
  (markCycle_nodup hn hP).filter (fun m => decide (owner hn hP T m = q))

/-- Every mark belongs to the inherited cycle of its constructed owner. -/
theorem mem_componentCycle_owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (m : Mark P) :
    m ∈ componentCycle hn hP T (owner hn hP T m) :=
  (mem_componentCycle hn hP T _ m).mpr rfl

/-- Each actual quotient component has a mark representative; filtering cannot
make its inherited component cycle empty. No crossing-nonempty premise enters. -/
theorem componentCycle_nonempty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) :
    ∃ m : Mark P, m ∈ componentCycle hn hP T q := by
  obtain ⟨m, hm⟩ := owner_surjective hn hP T q
  exact ⟨m, (mem_componentCycle hn hP T q m).mpr hm⟩

/-- Distinct actual components have disjoint mark membership in their inherited
cycles, since every incoming mark has one quotient owner. -/
theorem componentCycle_members_disjoint (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q r : Component hn hP T)
    (hqr : q ≠ r) (m : Mark P) :
    m ∈ componentCycle hn hP T q → m ∉ componentCycle hn hP T r := by
  intro hq hr
  exact hqr (((mem_componentCycle hn hP T q m).mp hq).symm.trans
    ((mem_componentCycle hn hP T r m).mp hr))

/-- Distinct quotient components yield distinct inherited cycles. The proof
uses an actual representative of the nonempty component, not a cycle count. -/
theorem componentCycle_injective (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) :
    Function.Injective (componentCycle hn hP T) := by
  intro q r he
  obtain ⟨m, hm⟩ := componentCycle_nonempty hn hP T q
  have hr : m ∈ componentCycle hn hP T r := he ▸ hm
  exact ((mem_componentCycle hn hP T q m).mp hm).symm.trans
    ((mem_componentCycle hn hP T r m).mp hr)

/-- At empty support every actual mark has the unique original component owner,
so filtering retains the complete original marked circle. -/
theorem componentCycle_empty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (q : Component hn hP ∅) : componentCycle hn hP ∅ q = markCycle hn hP := by
  unfold componentCycle
  apply Cycle.filter_eq_self
  intro m _
  have hm : owner hn hP ∅ m = q := (component_empty_subsingleton hn hP).elim _ _
  simp only [hm, decide_true]

/-- A rotation giving the original split-list presentation filters literally
between its two retained endpoints. Both filtered intervening lists may be empty;
this identity makes no claim about the current successor on the filtered cycle. -/
theorem componentCycle_eq_filtered_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B))
    (ha : owner hn hP T a = q) (hb : owner hn hP T b = q) :
    componentCycle hn hP T q =
      (a :: (A.filter (fun m => decide (owner hn hP T m = q)) ++
        b :: B.filter (fun m => decide (owner hn hP T m = q))) : Cycle (Mark P)) := by
  have hc : markCycle hn hP = (a :: (A ++ b :: B) : Cycle (Mark P)) := by
    rw [← hrot]
    exact (markCycle_rotation hn hP k).symm
  rw [componentCycle, hc, Cycle.filter_coe]
  simp [List.filter_append, ha, hb]

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


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The current actual successor follows each component's inherited original
cyclic order. This is an explicit invariant, not part of componentCycle's definition. -/
def InheritsMarkOrder (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) : Prop :=
  ∀ (q : Component hn hP T) (a : Mark P) (ha : a ∈ componentCycle hn hP T q),
    (componentCycle hn hP T q).next (componentCycle_nodup hn hP T q) a ha =
      smoothingSuccessor hn hP T a

/-- The next-point invariant is equivalently the actual filtered cycle's
formPerm action on its members. No assertion is made about nonmembers. -/
theorem inheritsMarkOrder_iff_formPerm (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) :
    InheritsMarkOrder hn hP T ↔
      ∀ (q : Component hn hP T) (a : Mark P) (_ha : a ∈ componentCycle hn hP T q),
        (componentCycle hn hP T q).formPerm (componentCycle_nodup hn hP T q) a =
          smoothingSuccessor hn hP T a := by
  constructor
  · intro h q a ha
    rw [Cycle.formPerm_apply_mem_eq_next _ _ a ha]
    exact h q a ha
  · intro h q a ha
    rw [← Cycle.formPerm_apply_mem_eq_next _ _ a ha]
    exact h q a ha

/-- Before any selected reconnection the inherited component cycle is the
original circle, whose next point is the constructed actual successor. -/
theorem inheritsMarkOrder_empty (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) : InheritsMarkOrder hn hP ∅ := by
  rw [inheritsMarkOrder_iff_formPerm]
  intro q a ha
  have he : (⟨componentCycle hn hP ∅ q, componentCycle_nodup hn hP ∅ q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨markCycle hn hP, markCycle_nodup hn hP⟩ :=
    Subtype.ext (componentCycle_empty hn hP q)
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  rw [hp, smoothingSuccessor_empty]
  exact Cycle.formPerm_apply_mem_eq_next (markCycle hn hP) (markCycle_nodup hn hP)
    a (mem_markCycle hn hP a)

/-- Filtering the original split list by the left child node set retains
exactly a followed by B, including the case that B is empty. -/
theorem filter_splitList_left {α : Type*} [DecidableEq α]
    (a b : α) (A B : List α) (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: (A ++ b :: B)).filter (fun x => decide (x ∈ a :: B)) = a :: B := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  have hA : A.filter (fun x => decide (x ∈ a :: B)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact fun hxl => hd hxl (List.mem_cons_of_mem b hx)
  have hB : B.filter (fun x => decide (x ∈ a :: B)) = B := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact List.mem_cons_of_mem a hx
  have hb : b ∉ a :: B := fun hb => hd hb List.mem_cons_self
  rw [List.filter_cons, List.filter_append, hA, List.filter_cons, hB]
  simp [hb]

/-- Filtering by the other child retains A followed by b. Its rotation is
b followed by A, so this also treats the singleton child when A is empty. -/
theorem filter_splitList_right {α : Type*} [DecidableEq α]
    (a b : α) (A B : List α) (h : (a :: (A ++ b :: B)).Nodup) :
    (a :: (A ++ b :: B)).filter (fun x => decide (x ∈ b :: A)) = A ++ [b] := by
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B h
  have hA : A.filter (fun x => decide (x ∈ b :: A)) = A := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact List.mem_cons_of_mem b hx
  have hB : B.filter (fun x => decide (x ∈ b :: A)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact fun hxr => hd (List.mem_cons_of_mem a hx) hxr
  have ha : a ∉ b :: A := fun ha => hd List.mem_cons_self ha
  rw [List.filter_cons, List.filter_append, hA, List.filter_cons, hB]
  simp [ha]

/-- One actual selected crossing has the two literal inherited child cycles.
Their representations, membership filters and permutation product are derived
from a rotation of the complete original marked circle. -/
theorem componentCycle_singleton_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (v : Visit P) :
    ∃ A B : List (Mark P),
      (Sum.inr v :: B).Nodup ∧ (Sum.inr (visitTwin v) :: A).Nodup ∧
      (Sum.inr v :: B).Disjoint (Sum.inr (visitTwin v) :: A) ∧
      componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr v)) =
        (Sum.inr v :: B : Cycle (Mark P)) ∧
      componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr (visitTwin v))) =
        (Sum.inr (visitTwin v) :: A : Cycle (Mark P)) ∧
      smoothingSuccessor hn hP {v.1} =
        (Sum.inr v :: B).formPerm * (Sum.inr (visitTwin v) :: A).formPerm := by
  classical
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  have hab : a ≠ b := fun he => (visitTwin_ne v).symm (Sum.inr.inj he)
  obtain ⟨k, A, B, hrot⟩ := markList_rotate_split hn hP a b hab
  have hN : (a :: (A ++ b :: B)).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr (markList_nodup hn hP)
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B hN
  have hc : markCycle hn hP = (a :: (A ++ b :: B) : Cycle (Mark P)) := by
    rw [← hrot]
    exact (markCycle_rotation hn hP k).symm
  have hp : (a :: (A ++ b :: B)).formPerm = markSuccessor hn hP := by
    rw [← hrot, List.formPerm_rotate _ (markList_nodup hn hP) k]
    exact (markSuccessor_eq_formPerm hn hP).symm
  have hs : smoothingSuccessor hn hP {v.1} =
      (a :: (A ++ b :: B)).formPerm * Equiv.swap a b := by
    simpa only [Finset.insert_empty, smoothingSuccessor_empty, hp] using
      smoothingSuccessor_insert hn hP (∅ : Finset (Crossing P)) v
        (Finset.notMem_empty v.1)
  have hownerL (m : Mark P) : owner hn hP {v.1} m = owner hn hP {v.1} a ↔
      m ∈ a :: B := by
    rw [owner_eq_iff, hs, Equiv.Perm.sameCycle_comm]
    exact splitList_left_sameCycle_iff a b A B hN m
  have hownerR (m : Mark P) : owner hn hP {v.1} m = owner hn hP {v.1} b ↔
      m ∈ b :: A := by
    rw [owner_eq_iff, hs, Equiv.Perm.sameCycle_comm]
    exact splitList_right_sameCycle_iff a b A B hN m
  have hpL : (fun m => decide (owner hn hP {v.1} m = owner hn hP {v.1} a)) =
      (fun m => decide (m ∈ a :: B)) := by
    funext m
    simp only [hownerL m]
  have hpR : (fun m => decide (owner hn hP {v.1} m = owner hn hP {v.1} b)) =
      (fun m => decide (m ∈ b :: A)) := by
    funext m
    simp only [hownerR m]
  have hcL : componentCycle hn hP {v.1} (owner hn hP {v.1} a) =
      (a :: B : Cycle (Mark P)) := by
    rw [componentCycle, hc, Cycle.filter_coe, hpL]
    refine congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_left a b A B hN))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  have hcR : componentCycle hn hP {v.1} (owner hn hP {v.1} b) =
      (b :: A : Cycle (Mark P)) := by
    rw [componentCycle, hc, Cycle.filter_coe, hpR]
    refine (congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_right a b A B hN))).trans
      (Cycle.coe_eq_coe.mpr (List.isRotated_concat b A))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  exact ⟨A, B, hL, hR, hd, hcL, hcR, hs.trans (splitList_identity a b A B hN)⟩

/-- The inherited-order invariant holds for one actual selected crossing.
Actual owner exhaustion reduces to the two child cycles, and disjointness
makes the full successor product restrict to each child's own formPerm. -/
theorem inheritsMarkOrder_singleton (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (v : Visit P) : InheritsMarkOrder hn hP {v.1} := by
  rw [inheritsMarkOrder_iff_formPerm]
  intro q m hm
  obtain ⟨A, B, hL, hR, hd, hcL, hcR, hs⟩ := componentCycle_singleton_splitList hn hP v
  rcases owner_singleton_exhaust hn hP v q with hq | hq
  · subst q
    have hmL : m ∈ Sum.inr v :: B := by
      rw [hcL] at hm
      exact hm
    have he : (⟨componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr v)),
        componentCycle_nodup hn hP {v.1} (owner hn hP {v.1} (Sum.inr v))⟩ :
        {s : Cycle (Mark P) // s.Nodup}) = ⟨(Sum.inr v :: B : Cycle (Mark P)), hL⟩ :=
      Subtype.ext hcL
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    rw [hp]
    change (Sum.inr v :: B).formPerm m = smoothingSuccessor hn hP {v.1} m
    rw [hs, Equiv.Perm.mul_apply,
      List.formPerm_apply_of_notMem (fun hr => hd hmL hr)]
  · subst q
    have hmR : m ∈ Sum.inr (visitTwin v) :: A := by
      rw [hcR] at hm
      exact hm
    have he : (⟨componentCycle hn hP {v.1} (owner hn hP {v.1} (Sum.inr (visitTwin v))),
        componentCycle_nodup hn hP {v.1} (owner hn hP {v.1} (Sum.inr (visitTwin v)))⟩ :
        {s : Cycle (Mark P) // s.Nodup}) =
        ⟨(Sum.inr (visitTwin v) :: A : Cycle (Mark P)), hR⟩ := Subtype.ext hcR
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    rw [hp]
    change (Sum.inr (visitTwin v) :: A).formPerm m = smoothingSuccessor hn hP {v.1} m
    rw [hs,
      (formPerm_disjoint_of_disjoint (Sum.inr v :: B) (Sum.inr (visitTwin v) :: A) hd).commute.eq,
      Equiv.Perm.mul_apply, List.formPerm_apply_of_notMem (fun hl => hd hl hmR)]

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Any literal representative of an actual inherited component has no repeated marks. -/
theorem componentCycle_list_nodup (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T)
    (L : List (Mark P)) (hL : componentCycle hn hP T q = (L : Cycle (Mark P))) :
    L.Nodup := by
  have hN := componentCycle_nodup hn hP T q
  rw [hL] at hN
  exact hN

/-- The representative's membership is exactly its constructed incoming owner. -/
theorem componentCycle_list_mem_iff (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T)
    (L : List (Mark P)) (hL : componentCycle hn hP T q = (L : Cycle (Mark P)))
    (m : Mark P) : m ∈ L ↔ owner hn hP T m = q := by
  change m ∈ (L : Cycle (Mark P)) ↔ _
  rw [← hL]
  exact mem_componentCycle hn hP T q m

/-- An explicit inherited-order hypothesis gives equality of the representative's
permutation with the current successor on its own marks, not on the whole ambient type. -/
theorem componentCycle_list_eqOn (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (q : Component hn hP T) (L : List (Mark P))
    (hL : componentCycle hn hP T q = (L : Cycle (Mark P))) :
    Set.EqOn L.formPerm (smoothingSuccessor hn hP T) {m | m ∈ L} := by
  have hN := componentCycle_list_nodup hn hP T q L hL
  have he : (⟨componentCycle hn hP T q, componentCycle_nodup hn hP T q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨(L : Cycle (Mark P)), hN⟩ :=
    Subtype.ext hL
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  change (componentCycle hn hP T q).formPerm (componentCycle_nodup hn hP T q) =
    (L : Cycle (Mark P)).formPerm hN at hp
  have hp' : (componentCycle hn hP T q).formPerm
      (componentCycle_nodup hn hP T q) = L.formPerm :=
    hp.trans (Cycle.formPerm_coe L hN)
  intro m hm
  have hmc : m ∈ componentCycle hn hP T q := by
    rw [hL]
    exact hm
  rw [← hp']
  exact (inheritsMarkOrder_iff_formPerm hn hP T).mp hI q m hmc

/-- Distinct marks in one actual component supply the original rotation and
the owner-filtered literal current split list. Its action equality is derived
from the explicit induction invariant. No representation is supplied as input. -/
theorem componentCycle_current_split_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (q : Component hn hP T) (a b : Mark P) (hab : a ≠ b)
    (ha : owner hn hP T a = q) (hb : owner hn hP T b = q) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (markList hn hP).rotate k = a :: (A ++ b :: B) ∧
      let L := a :: (A.filter (fun m => decide (owner hn hP T m = q)) ++
        b :: B.filter (fun m => decide (owner hn hP T m = q)))
      componentCycle hn hP T q = (L : Cycle (Mark P)) ∧ L.Nodup ∧
        (∀ m : Mark P, m ∈ L ↔ owner hn hP T m = q) ∧
        Set.EqOn L.formPerm (smoothingSuccessor hn hP T) {m | m ∈ L} := by
  obtain ⟨k, A, B, hrot⟩ := markList_rotate_split hn hP a b hab
  let L := a :: (A.filter (fun m => decide (owner hn hP T m = q)) ++
    b :: B.filter (fun m => decide (owner hn hP T m = q)))
  have hL : componentCycle hn hP T q = (L : Cycle (Mark P)) :=
    componentCycle_eq_filtered_splitList hn hP T q k a b A B hrot ha hb
  exact ⟨k, A, B, hrot, hL, componentCycle_list_nodup hn hP T q L hL,
    componentCycle_list_mem_iff hn hP T q L hL,
    componentCycle_list_eqOn hn hP T hI q L hL⟩

end
end SM.Carrier


namespace SM.Carrier

/-- A bijectively invariant set is closed in both directions of an ambient
permutation, without any finiteness assumption. -/
theorem perm_bijOn_mem_iff {α : Type*} (f : Equiv.Perm α) (U : Set α)
    (hU : Set.BijOn f U U) (x : α) : f x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    have hi : f⁻¹ (f x) ∈ U := hU.perm_inv.mapsTo hx
    simpa using hi
  · intro hx
    exact hU.mapsTo hx

/-- Agreement on one bijectively invariant set transports the entire orbit
of a member. The other endpoint is unrestricted; outside points are excluded
by integer-power invariance, not by an additional endpoint premise. -/
theorem sameCycle_congr_of_eqOn_bijOn {α : Type*} (f g : Equiv.Perm α) (U : Set α)
    (hU : Set.BijOn f U U) (he : Set.EqOn f g U)
    (x : α) (hx : x ∈ U) (y : α) : g.SameCycle x y ↔ f.SameCycle x y := by
  have hgU : Set.BijOn g U U := hU.congr he
  let hfM : ∀ z, f z ∈ U ↔ z ∈ U := perm_bijOn_mem_iff f U hU
  let hgM : ∀ z, g z ∈ U ↔ z ∈ U := perm_bijOn_mem_iff g U hgU
  have hs : f.subtypePerm hfM = g.subtypePerm hgM := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact he z.property
  constructor
  · rintro ⟨k, hk⟩
    have hy : y ∈ U := hk ▸ (hgU.perm_zpow k).mapsTo hx
    have hc : (g.subtypePerm hgM).SameCycle (⟨x, hx⟩ : U) (⟨y, hy⟩ : U) :=
      Equiv.Perm.sameCycle_subtypePerm.mpr ⟨k, hk⟩
    rw [← hs] at hc
    exact Equiv.Perm.sameCycle_subtypePerm.mp hc
  · rintro ⟨k, hk⟩
    have hy : y ∈ U := hk ▸ (hU.perm_zpow k).mapsTo hx
    have hc : (f.subtypePerm hfM).SameCycle (⟨x, hx⟩ : U) (⟨y, hy⟩ : U) :=
      Equiv.Perm.sameCycle_subtypePerm.mpr ⟨k, hk⟩
    rw [hs] at hc
    exact Equiv.Perm.sameCycle_subtypePerm.mp hc

/-- Local permutation agreement preserves a complete cycle on its marked set.
The result includes singleton cycles and requires no global permutation equality. -/
theorem isCycleOn_of_eqOn {α : Type*} (f g : Equiv.Perm α) (U : Set α)
    (hf : f.IsCycleOn U) (he : Set.EqOn f g U) : g.IsCycleOn U := by
  refine ⟨hf.1.congr he, ?_⟩
  intro x hx y hy
  exact (sameCycle_congr_of_eqOn_bijOn f g U hf.1 he x hx y).mpr (hf.2 hx hy)

variable {α : Type*} [DecidableEq α]

/-- Swapping the two displayed endpoint slots preserves local agreement with
an ambient permutation. Only membership in the literal parent list is used. -/
theorem splitList_ambient_swap_eqOn (f : Equiv.Perm α) (a b : α) (A B : List α)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {x | x ∈ a :: (A ++ b :: B)}) :
    Set.EqOn ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b)
      (f * Equiv.swap a b) {x | x ∈ a :: (A ++ b :: B)} := by
  intro x hx
  change (a :: (A ++ b :: B)).formPerm (Equiv.swap a b x) = f (Equiv.swap a b x)
  apply he
  by_cases hxa : x = a
  · subst x
    simp
  · by_cases hxb : x = b
    · subst x
      simp
    · simpa only [Equiv.swap_apply_of_ne_of_ne hxa hxb] using hx

/-- The ambient switched successor has exactly the left split-list orbit,
even when the surrounding permutation has other moving components. -/
theorem splitList_ambient_left_sameCycle_iff (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) : (f * Equiv.swap a b).SameCycle a x ↔ x ∈ a :: B := by
  have heS := splitList_ambient_swap_eqOn f a b A B he
  have heL : Set.EqOn ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b)
      (f * Equiv.swap a b) {m | m ∈ a :: B} := by
    intro m hm
    apply heS
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a
        (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b hm)))
  exact (sameCycle_congr_of_eqOn_bijOn _ _ {m | m ∈ a :: B}
    (splitList_left_isCycleOn a b A B hN).1 heL a List.mem_cons_self x).trans
      (splitList_left_sameCycle_iff a b A B hN x)

/-- The ambient switched successor has exactly the right split-list orbit;
its description includes a one-mark child when A is empty. -/
theorem splitList_ambient_right_sameCycle_iff (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) : (f * Equiv.swap a b).SameCycle b x ↔ x ∈ b :: A := by
  have heS := splitList_ambient_swap_eqOn f a b A B he
  have heR : Set.EqOn ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b)
      (f * Equiv.swap a b) {m | m ∈ b :: A} := by
    intro m hm
    apply heS
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inr List.mem_cons_self))
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inl hm))
  exact (sameCycle_congr_of_eqOn_bijOn _ _ {m | m ∈ b :: A}
    (splitList_right_isCycleOn a b A B hN).1 heR b List.mem_cons_self x).trans
      (splitList_right_sameCycle_iff a b A B hN x)

/-- The two incoming endpoints are separated in the actual ambient orbits,
not merely in the permutation formed by the isolated parent list. -/
theorem splitList_ambient_not_sameCycle (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)}) :
    ¬ (f * Equiv.swap a b).SameCycle a b := by
  intro hc
  have hb := (splitList_ambient_left_sameCycle_iff f a b A B hN he b).mp hc
  exact (splitList_child_data a b A B hN).2.2 hb List.mem_cons_self

/-- On the left child's actual members, the ambient successor follows that
child's own cyclic list. This is the pointwise form needed for inherited order. -/
theorem splitList_ambient_left_apply (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) (hx : x ∈ a :: B) :
    (f * Equiv.swap a b) x = (a :: B).formPerm x := by
  have hxL : x ∈ a :: (A ++ b :: B) := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a
        (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem b hx)))
  have hd := (splitList_child_data a b A B hN).2.2
  calc
    (f * Equiv.swap a b) x = ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b) x :=
      ((splitList_ambient_swap_eqOn f a b A B he) hxL).symm
    _ = (a :: B).formPerm x := by
      rw [splitList_identity a b A B hN, Equiv.Perm.mul_apply,
        List.formPerm_apply_of_notMem (fun hr => hd hx hr)]

/-- The other ambient child likewise follows its own inherited cyclic list. -/
theorem splitList_ambient_right_apply (f : Equiv.Perm α) (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup)
    (he : Set.EqOn (a :: (A ++ b :: B)).formPerm f {m | m ∈ a :: (A ++ b :: B)})
    (x : α) (hx : x ∈ b :: A) :
    (f * Equiv.swap a b) x = (b :: A).formPerm x := by
  have hxL : x ∈ a :: (A ++ b :: B) := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inr List.mem_cons_self))
    · exact List.mem_cons_of_mem a (List.mem_append.mpr (Or.inl hx))
  have hd := (splitList_child_data a b A B hN).2.2
  calc
    (f * Equiv.swap a b) x = ((a :: (A ++ b :: B)).formPerm * Equiv.swap a b) x :=
      ((splitList_ambient_swap_eqOn f a b A B he) hxL).symm
    _ = (b :: A).formPerm x := by
      rw [splitList_identity a b A B hN,
        (formPerm_disjoint_of_disjoint (a :: B) (b :: A) hd).commute.eq,
        Equiv.Perm.mul_apply, List.formPerm_apply_of_notMem (fun hl => hd hl hx)]

end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual forward successor stays in its incoming owner block for every
support, without independence or inherited-order assumptions. -/
theorem smoothingSuccessor_mapsTo_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    Set.MapsTo (smoothingSuccessor hn hP T)
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} := by
  intro m hm
  exact (owner_successor hn hP T m).trans hm

/-- The inverse actual successor also stays in the same owner block. -/
theorem smoothingSuccessor_symm_mapsTo_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    Set.MapsTo (smoothingSuccessor hn hP T).symm
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} := by
  intro m hm
  exact (owner_predecessor hn hP T m).trans hm

/-- Each actual owner block is invariant bijectively: forward and inverse
preservation provide the restriction of the actual permutation to that block. -/
theorem smoothingSuccessor_bijOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    Set.BijOn (smoothingSuccessor hn hP T)
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} :=
  (smoothingSuccessor hn hP T).bijOn'
    (smoothingSuccessor_mapsTo_owner hn hP T q)
    (smoothingSuccessor_symm_mapsTo_owner hn hP T q)

/-- If a fresh actual crossing's two incoming marks share an old owner, its
insertion changes no outgoing slot in any other actual old owner block. -/
theorem smoothingSuccessor_insert_eqOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v)) :
    Set.EqOn (smoothingSuccessor hn hP (insert v.1 T)) (smoothingSuccessor hn hP T)
      {m | owner hn hP T m = q} := by
  intro m hm
  apply smoothingSuccessor_insert_other hn hP T v hv m
  · intro he
    subst m
    exact hq hm.symm
  · intro he
    subst m
    exact hq (hm.symm.trans hc.symm)

/-- The new actual successor is bijective on every unaffected old owner block,
since its action there agrees with the proved old block bijection. -/
theorem smoothingSuccessor_insert_bijOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v)) :
    Set.BijOn (smoothingSuccessor hn hP (insert v.1 T))
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} :=
  (smoothingSuccessor_insert_eqOn_owner hn hP T v hv hc q hq).bijOn_iff.mpr
    (smoothingSuccessor_bijOn_owner hn hP T q)

/-- Backward traversal on an unaffected old owner block is unchanged as well.
The old inverse remains in that block, where the two forward actions agree. -/
theorem smoothingSuccessor_insert_symm_eqOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v)) :
    Set.EqOn (smoothingSuccessor hn hP (insert v.1 T)).symm (smoothingSuccessor hn hP T).symm
      {m | owner hn hP T m = q} := by
  intro m hm
  have hx : owner hn hP T ((smoothingSuccessor hn hP T).symm m) = q :=
    (owner_predecessor hn hP T m).trans hm
  have he := smoothingSuccessor_insert_eqOn_owner hn hP T v hv hc q hq hx
  apply (smoothingSuccessor hn hP (insert v.1 T)).injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- For a fresh actual selected crossing, an explicit inherited-order invariant
and same-current-component premise give the two exact ambient child orbits and
their successor actions. The original rotation and filtered child lists are constructed. -/
theorem smoothingSuccessor_insert_child_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v))) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (markList hn hP).rotate k = Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B) ∧
      let q := owner hn hP T (Sum.inr v)
      let AL := A.filter (fun m => decide (owner hn hP T m = q))
      let BL := B.filter (fun m => decide (owner hn hP T m = q))
      (Sum.inr v :: BL).Nodup ∧ (Sum.inr (visitTwin v) :: AL).Nodup ∧
      (Sum.inr v :: BL).Disjoint (Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, owner hn hP (insert v.1 T) m =
          owner hn hP (insert v.1 T) (Sum.inr v) ↔ m ∈ Sum.inr v :: BL) ∧
      (∀ m : Mark P, owner hn hP (insert v.1 T) m =
          owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) ↔
          m ∈ Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: BL →
        smoothingSuccessor hn hP (insert v.1 T) m = (Sum.inr v :: BL).formPerm m) ∧
      (∀ m : Mark P, m ∈ Sum.inr (visitTwin v) :: AL →
        smoothingSuccessor hn hP (insert v.1 T) m =
          (Sum.inr (visitTwin v) :: AL).formPerm m) := by
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  let q := owner hn hP T a
  have hab : a ≠ b := fun he => (visitTwin_ne v).symm (Sum.inr.inj he)
  obtain ⟨k, A, B, hrot, hL, hN, hmem, he⟩ :=
    componentCycle_current_split_data hn hP T hI q a b hab rfl hc.symm
  let AL := A.filter (fun m => decide (owner hn hP T m = q))
  let BL := B.filter (fun m => decide (owner hn hP T m = q))
  have hdata := splitList_child_data a b AL BL hN
  refine ⟨k, A, B, hrot, hdata.1, hdata.2.1, hdata.2.2, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [owner_eq_iff, Equiv.Perm.sameCycle_comm, smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_left_sameCycle_iff (smoothingSuccessor hn hP T)
      a b AL BL hN he m
  · intro m
    rw [owner_eq_iff, Equiv.Perm.sameCycle_comm, smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_right_sameCycle_iff (smoothingSuccessor hn hP T)
      a b AL BL hN he m
  · intro m hm
    rw [smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_left_apply (smoothingSuccessor hn hP T)
      a b AL BL hN he m hm
  · intro m hm
    rw [smoothingSuccessor_insert hn hP T v hv]
    exact splitList_ambient_right_apply (smoothingSuccessor hn hP T)
      a b AL BL hN he m hm

/-- An unaffected old owner block remains exactly one new orbit, with no new
outside marks. Both directions use proved invariant-set orbit transport. -/
theorem owner_insert_iff_of_unaffected (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v))
    (m : Mark P) (hm : owner hn hP T m = q) (z : Mark P) :
    owner hn hP (insert v.1 T) z = owner hn hP (insert v.1 T) m ↔
      owner hn hP T z = q := by
  have ht := sameCycle_congr_of_eqOn_bijOn
    (smoothingSuccessor hn hP T) (smoothingSuccessor hn hP (insert v.1 T))
    {x | owner hn hP T x = q} (smoothingSuccessor_bijOn_owner hn hP T q)
    (smoothingSuccessor_insert_eqOn_owner hn hP T v hv hc q hq).symm m hm z
  constructor
  · intro hz
    have hi := (owner_eq_iff hn hP (insert v.1 T) m z).mp hz.symm
    have ho := (owner_eq_iff hn hP T m z).mpr (ht.mp hi)
    exact ho.symm.trans hm
  · intro hz
    have ho := (owner_eq_iff hn hP T m z).mp (hm.trans hz.symm)
    exact ((owner_eq_iff hn hP (insert v.1 T) m z).mpr (ht.mpr ho)).symm

/-- The actual inherited cycle of an unaffected component is unchanged, since
its new owner filter is pointwise the same original-circle predicate. -/
theorem componentCycle_insert_unaffected (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v))
    (m : Mark P) (hm : owner hn hP T m = q) :
    componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) m) =
      componentCycle hn hP T q := by
  unfold componentCycle
  apply congrArg (fun p : Mark P → Bool => (markCycle hn hP).filter p)
  funext z
  exact decide_eq_decide.mpr (owner_insert_iff_of_unaffected hn hP T v hv hc q hq m hm z)

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {P : LabelledTuple n}

/-- For distinct actual crossings and either ordering of each actual visit pair,
noninterlacement is exactly equality of the two open-arc membership statuses. -/
theorem not_interlaces_iff_same_arc_status (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ Interlaces hn hP x y ↔
      (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ↔
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) := by
  constructor
  · intro hNI
    constructor
    · intro h₀
      by_contra h₁
      exact hNI ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀,
        (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁).mpr h₁⟩
    · intro h₁
      by_contra h₀
      exact hNI ⟨hxy, x₀, x₁, y₁, y₀, hx, hy.symm, h₁,
        (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₀).mpr h₀⟩
  · intro hsame hI
    obtain ⟨j, hj, hu⟩ := (interlaces_iff_unique hn hP x y x₀ x₁ hx).mp hI |>.2
    have h₀ : crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ := by
      rcases crossing_visits_exhaust y y₀ y₁ hy j with he | he
      · exact he ▸ hj
      · exact hsame.mpr (he ▸ hj)
    exact hy ((hu y₀ h₀).trans (hu y₁ (hsame.mp h₀)).symm)

/-- The equivalent statuses put both actual visits in one of the two oriented
open arcs. The complement law uses distinct crossing positions, so no endpoint
case is silently discarded. -/
theorem not_interlaces_iff_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ Interlaces hn hP x y ↔
      (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) ∨
      (crossingVisitBetween hn hP.1 x x₁ x₀ y y₀ ∧
        crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) := by
  rw [not_interlaces_iff_same_arc_status hn hP hxy x₀ x₁ hx y₀ y₁ hy,
    crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₀,
    crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁]
  by_cases h₀ : crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ <;>
    by_cases h₁ : crossingVisitBetween hn hP.1 x x₀ x₁ y y₁ <;> simp [h₀, h₁]

/-- No choice of first visit of the second crossing affects its arc membership
when the actual crossings do not interlace. The two input visits may coincide. -/
theorem not_interlaces_all_visits_same_arc (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y) (hNI : ¬ Interlaces hn hP x y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    crossingVisitBetween hn hP.1 x x₀ x₁ y j ↔
      crossingVisitBetween hn hP.1 x x₀ x₁ y k := by
  by_cases hjk : j = k
  · subst k
    exact Iff.rfl
  · exact (not_interlaces_iff_same_arc_status hn hP hxy x₀ x₁ hx j k hjk).mp hNI

/-- Actual independent support supplies noninterlacement for any two distinct
selected crossings; no hypothesis about current carrier ownership is used. -/
theorem independent_crossing_visits_same_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    crossingVisitBetween hn hP.1 x x₀ x₁ y j ↔
      crossingVisitBetween hn hP.1 x x₀ x₁ y k :=
  not_interlaces_all_visits_same_arc hn hP hxy
    ((mem_independentSupports_iff hn hP S).mp hS x hxS y hyS hxy) x₀ x₁ hx j k

/-- The other selected pair is wholly in one original open arc of the selected
pair, the noninterlacement input needed for the source's splitting induction. -/
theorem independent_crossing_visits_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
      crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) ∨
    (crossingVisitBetween hn hP.1 x x₁ x₀ y y₀ ∧
      crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) :=
  (not_interlaces_iff_one_open_arc hn hP hxy x₀ x₁ hx y₀ y₁ hy).mp
    ((mem_independentSupports_iff hn hP S).mp hS x hxS y hyS hxy)

/-- The status equivalence for the constructed actual twin pairing, written
literally in physical traversal positions. The pair inequalities are derived
from the checked construction rather than supplied as extra premises. -/
theorem not_interlaces_iff_twin_same_arc (hn : 3 ≤ n) (hP : Generic P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ Interlaces hn hP v.1 w.1 ↔
      (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 (visitTwin v)) ↔
        traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact not_interlaces_iff_same_arc_status hn hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- Noninterlacement places the actual twin pair together on either the forward
or backward open arc of the other actual twin pair, including wraparound. -/
theorem not_interlaces_iff_twin_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ Interlaces hn hP v.1 w.1 ↔
      (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 (visitTwin v)) ∧
        traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) ∨
      (traversalBetween (visitPosition hn hP.1 (visitTwin v)) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 v) ∧
        traversalBetween (visitPosition hn hP.1 (visitTwin v))
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 v)) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact not_interlaces_iff_one_open_arc hn hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- In an actual independent support, every other selected twin pair lies in
one original oriented open arc of the selected pair. This is a statement about
actual traversal positions, not a supplied current-cycle correspondence. -/
theorem independent_twin_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1) :
    (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 (visitTwin v)) ∧
      traversalBetween (visitPosition hn hP.1 v)
        (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) ∨
    (traversalBetween (visitPosition hn hP.1 (visitTwin v)) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 v) ∧
      traversalBetween (visitPosition hn hP.1 (visitTwin v))
        (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 v)) :=
  (not_interlaces_iff_twin_one_open_arc hn hP v w hvw).mp
    ((mem_independentSupports_iff hn hP S).mp hS v.1 hvS w.1 hwS hvw)

end
end SM.Carrier


namespace SM.Carrier

/-- Two indices below the list length cross its cut at most once when added. -/
theorem mod_add_one_wrap (N p i : ℕ) (hp : p < N) (hi : i < N) :
    (i + p) % N = if i + p < N then i + p else i + p - N := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h), Nat.mod_eq_of_lt (by omega)]

/-- Translating indices around a finite circle preserves the strict arc from
index zero to index j, including the case where that arc crosses the cut. -/
theorem cyclic_mod_add_iff (N k i j : ℕ) (hi : i < N) (hj : j < N) :
    ((k % N < (i + k) % N ∧ (i + k) % N < (j + k) % N) ∨
      ((i + k) % N < (j + k) % N ∧ (j + k) % N < k % N) ∨
      ((j + k) % N < k % N ∧ k % N < (i + k) % N)) ↔
      0 < i ∧ i < j := by
  have hp : k % N < N := Nat.mod_lt k (Nat.zero_lt_of_lt hi)
  have hm (z : ℕ) (hz : z < N) : (z + k) % N = (z + k % N) % N := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hz]
  rw [hm i hi, hm j hj, mod_add_one_wrap N (k % N) i hp hi,
    mod_add_one_wrap N (k % N) j hp hj]
  split_ifs <;> omega

/-- In a sorted finite list, comparisons of rotated entries are comparisons of
their cyclic indices. The order premise comes from the actual finset sort. -/
theorem sorted_rotate_getElem_between_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (k i j : ℕ)
    (hi : i < (s.sort.rotate k).length) (hj : j < (s.sort.rotate k).length) :
    (((s.sort.rotate k)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le i) hi) < (s.sort.rotate k)[i] ∧
        (s.sort.rotate k)[i] < (s.sort.rotate k)[j]) ∨
      ((s.sort.rotate k)[i] < (s.sort.rotate k)[j] ∧
        (s.sort.rotate k)[j] < (s.sort.rotate k)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le i) hi)) ∨
      ((s.sort.rotate k)[j] < (s.sort.rotate k)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le i) hi) ∧
        (s.sort.rotate k)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le i) hi) < (s.sort.rotate k)[i])) ↔
      0 < i ∧ i < j := by
  have hi' : i < s.sort.length := by simpa only [List.length_rotate] using hi
  have hj' : j < s.sort.length := by simpa only [List.length_rotate] using hj
  simp only [List.getElem_rotate, Nat.zero_add, s.sortedLT_sort.getElem_lt_getElem_iff]
  exact cyclic_mod_add_iff s.sort.length k i j hi' hj'

/-- In a duplicate-free literal split list, membership in its first open arc
is exactly a strict index between its two endpoint indices. -/
theorem nodup_split_getElem_mem_iff {α : Type*} (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup) (i : ℕ)
    (hi : i < (a :: (A ++ b :: B)).length) :
    (a :: (A ++ b :: B))[i] ∈ A ↔ 0 < i ∧ i < A.length + 1 := by
  constructor
  · intro hx
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hx
    have hjL : j + 1 < (a :: (A ++ b :: B)).length := by
      simp only [List.length_cons, List.length_append]
      omega
    have heL : (a :: (A ++ b :: B))[j + 1]'hjL = (a :: (A ++ b :: B))[i] := by
      simpa only [List.getElem_cons_succ, List.getElem_append_left hj] using he
    have hji : j + 1 = i := hN.getElem_inj_iff.mp heL
    omega
  · rintro ⟨hi0, hiA⟩
    cases i with
    | zero => omega
    | succ i =>
      have hiA' : i < A.length := by omega
      simpa only [List.getElem_cons_succ, List.getElem_append_left hiA'] using
        (List.getElem_mem hiA' : A[i] ∈ A)

/-- The first open slice of an actual rotated finset sort is exactly the
forward strict cyclic-order arc. Endpoints and wraparound are handled literally. -/
theorem sorted_rotate_split_mem_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (k : ℕ) (a b : α) (A B : List α) (x : α)
    (hr : s.sort.rotate k = a :: (A ++ b :: B)) (hx : x ∈ s) :
    x ∈ A ↔ ((a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ (b < a ∧ a < x)) := by
  have hN : (a :: (A ++ b :: B)).Nodup := by
    rw [← hr]
    exact List.nodup_rotate.mpr (Finset.sort_nodup s _)
  have hxm : x ∈ s.sort.rotate k := List.mem_rotate.mpr ((Finset.mem_sort _).mpr hx)
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxm
  have hiL : i < (a :: (A ++ b :: B)).length := by simpa only [hr] using hi
  have h0 : 0 < (s.sort.rotate k).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hj : A.length + 1 < (s.sort.rotate k).length := by
    rw [hr]
    simp only [List.length_cons, List.length_append]
    omega
  have hzero : (s.sort.rotate k)[(0 : ℕ)]'h0 = a := by
    simp only [hr, List.getElem_cons_zero]
  have hb : (s.sort.rotate k)[A.length + 1]'hj = b := by
    simp only [hr, List.getElem_cons_succ, List.getElem_append_right (Nat.le_refl A.length),
      Nat.sub_self, List.getElem_cons_zero]
  have hslice : x ∈ A ↔ 0 < i ∧ i < A.length + 1 := by
    have he : (a :: (A ++ b :: B))[i]'hiL = x := by simpa only [hr] using hix
    rw [← he]
    exact nodup_split_getElem_mem_iff a b A B hN i hiL
  have horder := sorted_rotate_getElem_between_iff s k i (A.length + 1) hi hj
  rw [hzero, hix, hb] at horder
  exact hslice.trans horder.symm

/-- The complementary literal slice is the reverse strict cyclic-order arc.
Rotating again to b reduces it to the proved forward-slice statement. -/
theorem sorted_rotate_split_reverse_mem_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (k : ℕ) (a b : α) (A B : List α) (x : α)
    (hr : s.sort.rotate k = a :: (A ++ b :: B)) (hx : x ∈ s) :
    x ∈ B ↔ ((b < x ∧ x < a) ∨ (x < a ∧ a < b) ∨ (a < b ∧ b < x)) := by
  have hr' : s.sort.rotate (k + (a :: A).length) = b :: (B ++ a :: A) := by
    rw [← List.rotate_rotate, hr]
    change (((a :: A) ++ (b :: B)).rotate (a :: A).length) = _
    rw [List.rotate_append_length_eq]
    rfl
  exact sorted_rotate_split_mem_iff s (k + (a :: A).length) b a B A x hr' hx

end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- In any actual rotated complete marked list, the open list from a to b
is exactly the strict physical traversal arc, including wraparound. -/
theorem markList_rotate_left_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ A ↔ traversalBetween (markPosition hn hP.1 a) (markPosition hn hP.1 m)
      (markPosition hn hP.1 b) := by
  letI := markLinearOrder hn hP
  have hr : (Finset.univ : Finset (Mark P)).sort.rotate k = a :: (A ++ b :: B) := hrot
  exact sorted_rotate_split_mem_iff Finset.univ k a b A B m hr (Finset.mem_univ m)

/-- The other open list is the reverse oriented physical arc, with both
endpoint marks excluded rather than assigned by a non-strict inequality. -/
theorem markList_rotate_right_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ B ↔ traversalBetween (markPosition hn hP.1 b) (markPosition hn hP.1 m)
      (markPosition hn hP.1 a) := by
  letI := markLinearOrder hn hP
  have hr : (Finset.univ : Finset (Mark P)).sort.rotate k = a :: (A ++ b :: B) := hrot
  exact sorted_rotate_split_reverse_mem_iff Finset.univ k a b A B m hr (Finset.mem_univ m)

/-- Filtering the physical forward arc to one actual component adds precisely
its owner equality. No compatibility with the current successor is assumed. -/
theorem markList_filter_left_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ A.filter (fun x => decide (owner hn hP T x = q)) ↔
      traversalBetween (markPosition hn hP.1 a) (markPosition hn hP.1 m)
        (markPosition hn hP.1 b) ∧ owner hn hP T m = q := by
  simp only [List.mem_filter, decide_eq_true_eq,
    markList_rotate_left_iff hn hP k a b A B hrot m]

theorem markList_filter_right_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ B.filter (fun x => decide (owner hn hP T x = q)) ↔
      traversalBetween (markPosition hn hP.1 b) (markPosition hn hP.1 m)
        (markPosition hn hP.1 a) ∧ owner hn hP T m = q := by
  simp only [List.mem_filter, decide_eq_true_eq,
    markList_rotate_right_iff hn hP k a b A B hrot m]

/-- Actual independence puts another selected twin pair wholly into one
literal original split-list arc. This connects physical noninterlacement to
list membership, without replacing original arcs by current components. -/
theorem independent_twin_same_slice (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k =
      Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A ∧ Sum.inr (visitTwin w) ∈ A) ∨
      (Sum.inr w ∈ B ∧ Sum.inr (visitTwin w) ∈ B) := by
  rcases independent_twin_one_open_arc hn hP hS v w hvS hwS hvw with ha | hb
  · exact Or.inl
      ⟨(markList_rotate_left_iff hn hP k _ _ A B hrot _).mpr ha.1,
        (markList_rotate_left_iff hn hP k _ _ A B hrot _).mpr ha.2⟩
  · exact Or.inr
      ⟨(markList_rotate_right_iff hn hP k _ _ A B hrot _).mpr hb.1,
        (markList_rotate_right_iff hn hP k _ _ A B hrot _).mpr hb.2⟩

/-- When the other selected pair currently has owner q, the proved original
same-arc property puts both visits in one owner-filtered arc. The current-owner
equalities remain explicit inputs for the later simultaneous induction. -/
theorem independent_twin_same_filtered_slice (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1)
    (T : Finset (Crossing P)) (q : Component hn hP T)
    (hqw : owner hn hP T (Sum.inr w) = q)
    (hqt : owner hn hP T (Sum.inr (visitTwin w)) = q)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k =
      Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A.filter (fun x => decide (owner hn hP T x = q)) ∧
      Sum.inr (visitTwin w) ∈ A.filter (fun x => decide (owner hn hP T x = q))) ∨
    (Sum.inr w ∈ B.filter (fun x => decide (owner hn hP T x = q)) ∧
      Sum.inr (visitTwin w) ∈ B.filter (fun x => decide (owner hn hP T x = q))) := by
  simpa only [List.mem_filter, hqw, hqt, decide_true, and_true] using
    independent_twin_same_slice hn hP hS v w hvS hwS hvw k A B hrot

end
end SM.Carrier


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Every selected crossing still awaiting processing has both actual visits
in one current successor component. This invariant refers to current owners. -/
def PendingPairsTogether (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S T : Finset (Crossing P)) : Prop :=
  ∀ w : Visit P, w.1 ∈ S → w.1 ∉ T →
    owner hn hP T (Sum.inr w) = owner hn hP T (Sum.inr (visitTwin w))

/-- Before any reconnection all marks lie in the single original component,
so every pending pair lies together, without an independence assumption. -/
theorem pendingPairsTogether_empty (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) :
    PendingPairsTogether hn hP S ∅ := by
  intro w _ _
  exact (component_empty_subsingleton hn hP).elim _ _

/-- Inserting a fresh selected crossing preserves current-owner equality for
every other pending selected pair. An unaffected owner block is unchanged.
Inside the affected block, independence puts the pair in one actual physical
arc, and the checked filtered child classification gives one new owner. -/
theorem pendingPairsTogether_insert (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (hPending : PendingPairsTogether hn hP S T)
    (v : Visit P) (hvS : v.1 ∈ S) (hv : v.1 ∉ T) :
    PendingPairsTogether hn hP S (insert v.1 T) := by
  intro w hwS hw
  have hwT : w.1 ∉ T := fun hwT => hw (Finset.mem_insert_of_mem hwT)
  have hvw : v.1 ≠ w.1 := by
    intro he
    apply hw
    rw [← he]
    exact Finset.mem_insert_self _ _
  have hc := hPending v hvS hv
  have hwt := hPending w hwS hwT
  by_cases hq : owner hn hP T (Sum.inr w) = owner hn hP T (Sum.inr v)
  · obtain ⟨k, A, B, hrot, hNLeft, hNRight, hdisjoint,
      hleft, hright, hactLeft, hactRight⟩ :=
      smoothingSuccessor_insert_child_data hn hP T hI v hv hc
    have hqt : owner hn hP T (Sum.inr (visitTwin w)) =
        owner hn hP T (Sum.inr v) := hwt.symm.trans hq
    rcases independent_twin_same_filtered_slice hn hP hS v w hvS hwS hvw
      T (owner hn hP T (Sum.inr v)) hq hqt k A B hrot with ha | hb
    · exact ((hright (Sum.inr w)).mpr
        (List.mem_cons_of_mem _ ha.1)).trans
        ((hright (Sum.inr (visitTwin w))).mpr
          (List.mem_cons_of_mem _ ha.2)).symm
    · exact ((hleft (Sum.inr w)).mpr
        (List.mem_cons_of_mem _ hb.1)).trans
        ((hleft (Sum.inr (visitTwin w))).mpr
          (List.mem_cons_of_mem _ hb.2)).symm
  · exact ((owner_insert_iff_of_unaffected hn hP T v hv hc
      (owner hn hP T (Sum.inr w)) hq (Sum.inr w) rfl
      (Sum.inr (visitTwin w))).mpr hwt.symm).symm

end
end SM.Carrier


#print axioms SM.Carrier.PendingPairsTogether
#print axioms SM.Carrier.pendingPairsTogether_empty
#print axioms SM.Carrier.pendingPairsTogether_insert
