import SM.GaussRelabel
import Mathlib.Data.Multiset.Count

/-! Complete def:gauss: actual traversal circle, actual crossing visits,
geometric cyclic order, exact multiplicities and representative independence. -/

namespace SM

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem gaussList_strictly_sorted (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (gaussList hn hP).Pairwise (fun v w => visitKey hn hP.1 v < visitKey hn hP.1 w) := by
  have hne : (gaussList hn hP).Pairwise (fun v w => v ≠ w) := gaussList_nodup hn hP
  have h := List.pairwise_and_iff.mpr ⟨gaussList_sorted hn hP, hne⟩
  apply h.imp
  intro v w hvw
  rcases hvw.1.lt_or_eq with hlt | heq
  · exact hlt
  · exact (hvw.2 (visitKey_injective hn hP heq)).elim

theorem gaussWord_length (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (gaussWord hn hP).length = 2 * Nat.card (Crossing P) := by
  change ((gaussList hn hP).map Sigma.fst).length = _
  rw [List.length_map]
  exact gaussList_length hn hP

theorem gaussWord_crossing_count (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (c : Crossing P) : (gaussWord hn hP).toMultiset.count c = 2 := by
  simp only [gaussWord, gaussCycle, Cycle.map_coe, Cycle.coe_toMultiset,
    Multiset.coe_count, List.count_eq_countP, List.countP_map]
  exact gaussList_crossing_count hn hP c

/-- The full source definition is bound to one reviewed statement. The
non-strict interval for traversal coordinates is the printed [0,1); crossing
visits themselves satisfy the stronger strict interior inequalities proved here.
No basepoint, arbitrary word, graph or crossing naming is an extra input. -/
theorem gauss_definition (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) :
    (∀ p : TraversalPoint n,
      traversalEvaluation P p = P p.1 + p.2.val • edge P p.1) ∧
    (∀ p q : TraversalPoint n,
      traversalKey p < traversalKey q ↔
        p.1.val < q.1.val ∨ p.1 = q.1 ∧ p.2.val < q.2.val) ∧
    (∀ v : Visit P, 0 < visitParameter v ∧ visitParameter v < 1 ∧
      traversalEvaluation P (visitPosition hn hP.1 v) = crossingPoint v.1) ∧
    Function.Injective (visitPosition hn hP.1) ∧
    (gaussList hn hP).Nodup ∧
    (∀ v : Visit P, v ∈ gaussList hn hP) ∧
    (gaussList hn hP).Pairwise (fun v w => visitKey hn hP.1 v < visitKey hn hP.1 w) ∧
    (gaussList hn hP).length = 2 * Nat.card (Crossing P) ∧
    gaussCycle hn hP = (gaussList hn hP : Cycle (Visit P)) ∧
    gaussWord hn hP = (gaussCycle hn hP).map Sigma.fst ∧
    (gaussWord hn hP).length = 2 * Nat.card (Crossing P) ∧
    (∀ c : Crossing P, (gaussWord hn hP).toMultiset.count c = 2) ∧
    (∀ k : ℕ, ((gaussList hn hP).rotate k : Cycle (Visit P)) = gaussCycle hn hP) ∧
    (∀ a : ZMod n, ∀ p q r : TraversalPoint n,
      traversalBetween (traversalShift a p) (traversalShift a q) (traversalShift a r) ↔
        traversalBetween p q r) ∧
    (∀ a : ZMod n,
      (gaussCycle hn hP).map (visitShiftEquiv a P) =
        gaussCycle hn ((generic_shift a P).mpr hP)) ∧
    (∀ a : ZMod n,
      (gaussWord hn hP).map (crossingShiftEquiv a P) =
        gaussWord hn ((generic_shift a P).mpr hP)) := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨fun _ => rfl, traversalKey_lt_iff, ?_, visitPosition_injective hn hP,
    gaussList_nodup hn hP, mem_gaussList hn hP, gaussList_strictly_sorted hn hP,
    gaussList_length hn hP, rfl, rfl, gaussWord_length hn hP,
    gaussWord_crossing_count hn hP, gaussCycle_rotation hn hP,
    traversalBetween_shift, gaussCycle_shift hn hP, gaussWord_shift hn hP⟩
  intro v
  exact ⟨(visitPosition_interior hn hP.1 v).1, (visitPosition_interior hn hP.1 v).2,
    visitPosition_evaluation hn hP.1 v⟩

end SM
