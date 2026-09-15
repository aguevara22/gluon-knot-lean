import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
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


#print axioms SM.Carrier.markList_rotate_left_iff
#print axioms SM.Carrier.markList_rotate_right_iff
#print axioms SM.Carrier.markList_filter_left_iff
#print axioms SM.Carrier.markList_filter_right_iff
#print axioms SM.Carrier.independent_twin_same_slice
#print axioms SM.Carrier.independent_twin_same_filtered_slice
