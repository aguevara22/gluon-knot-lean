import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic

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


#print axioms SM.Carrier.Mark
#print axioms SM.Carrier.markPosition
#print axioms SM.Carrier.markPosition_vertex
#print axioms SM.Carrier.markPosition_visit
#print axioms SM.Carrier.markPosition_evaluation_vertex
#print axioms SM.Carrier.markPosition_evaluation_visit
#print axioms SM.Carrier.markPosition_injective
#print axioms SM.Carrier.markKey
#print axioms SM.Carrier.markKey_vertex
#print axioms SM.Carrier.markKey_visit
#print axioms SM.Carrier.markKey_injective
#print axioms SM.Carrier.markLinearOrder
#print axioms SM.Carrier.markList
#print axioms SM.Carrier.markList_nodup
#print axioms SM.Carrier.mem_markList
#print axioms SM.Carrier.markList_sorted
#print axioms SM.Carrier.markList_length
#print axioms SM.Carrier.markList_nonempty
