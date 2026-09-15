import SM.CarrierComponentCount
import SM.DecompositionDefinition

/-! Source conv:selected-visits (reference/SM/sm-3-statesum.tex:29, frame SM15): the
incoming-visit convention for the ownership of the two visits of a selected crossing.
Main declaration: `SM.selected_visits_convention`.

Notation (the finite successor model of the source proof of lem:carriers, sm-3:97-115, ported
from the previous executor's Carrier lane). `Carrier.Mark P = ZMod n ⊕ Visit P` marks the
traversal circle at every original vertex (`Sum.inl i`) and every crossing visit (`Sum.inr v`);
`Carrier.markPosition` is the traversal point of a mark and `traversalEvaluation P` its point of
the plane; `Carrier.markSuccessor hn hP = ρ` is the successor permutation of the marked circle
(`Carrier.prevMark` its inverse), so the arc from `ρ⁻¹(a)` to `a` is the incoming one-sided arc
at `a` and the arc from `a` to `ρ(a)` its outgoing arc; `Carrier.visitTwin v = b` is the other
visit of the crossing of `v`; `Carrier.selectedMarkPerm S` exchanges the two visits of every
selected crossing and fixes every other mark; `Carrier.smoothingSuccessor hn hP S = ρ_S =
ρ ∘ selectedMarkPerm S` is the reconnected successor (eq. carrierpr:successors); the carriers are
its cycles, `Carrier.Component hn hP S`, and `Carrier.owner hn hP S a` is the carrier to which the
mark `a` is assigned (its own cycle). -/

namespace SM

open Carrier

variable {n : ℕ} [NeZero n]

/-- The printed convention at one independent support `S`. -/
structure SelectedVisitsConventionData (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Prop where
  /-- reconnection at a selected crossing with visits `a = v`, `b = visitTwin v`: the incoming arc
  at `a` continues along the outgoing arc at `b`, and the incoming arc at `b` along the outgoing
  arc at `a` -/
  reconnect_a : ∀ v : Visit P, v.1 ∈ S →
    smoothingSuccessor hn hP S (Sum.inr v) = markSuccessor hn hP (Sum.inr (visitTwin v))
  reconnect_b : ∀ v : Visit P, v.1 ∈ S →
    smoothingSuccessor hn hP S (Sum.inr (visitTwin v)) = markSuccessor hn hP (Sum.inr v)
  /-- the original visit `a` is assigned to the resulting cycle containing the incoming
  one-sided arc at `a`: that arc is traversed, under `ρ_S`, by the mark
  `(ρ_S)⁻¹(a) = selectedMarkPerm S (ρ⁻¹(a))`, which has the same point of the plane as `ρ⁻¹(a)`
  and the same owner as `a` -/
  incoming_arc : ∀ a : Mark P,
    (smoothingSuccessor hn hP S).symm a = selectedMarkPerm S (prevMark hn hP a) ∧
    traversalEvaluation P (markPosition hn hP.1 (selectedMarkPerm S (prevMark hn hP a))) =
      traversalEvaluation P (markPosition hn hP.1 (prevMark hn hP a)) ∧
    owner hn hP S ((smoothingSuccessor hn hP S).symm a) = owner hn hP S a
  /-- unselected visits (and original vertices) retain their ordinary traversal successor -/
  unselected_visit : ∀ v : Visit P, v.1 ∉ S →
    smoothingSuccessor hn hP S (Sum.inr v) = markSuccessor hn hP (Sum.inr v)
  vertex : ∀ i : ZMod n, smoothingSuccessor hn hP S (Sum.inl i) = markSuccessor hn hP (Sum.inl i)
  /-- a selected visit is assigned to one abstract carrier (its own cycle), although the two
  carriers through the smoothing site have the same point of the plane -/
  same_point : ∀ v : Visit P,
    traversalEvaluation P (markPosition hn hP.1 (Sum.inr (visitTwin v))) =
      traversalEvaluation P (markPosition hn hP.1 (Sum.inr v))
  distinct_carriers : ∀ v : Visit P, v.1 ∈ S →
    owner hn hP S (Sum.inr v) ≠ owner hn hP S (Sum.inr (visitTwin v))
  /-- ownership is by cycle of `ρ_S`; the geometric reconnection is `ρ_S` itself -/
  owner_iff : ∀ a b : Mark P,
    owner hn hP S a = owner hn hP S b ↔ (smoothingSuccessor hn hP S).SameCycle a b

theorem selectedVisitsConvention_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) :
    SelectedVisitsConventionData hn hP S where
  reconnect_a := fun v hv => smoothingSuccessor_visit_of_mem hn hP S v hv
  reconnect_b := by
    intro v hv
    have htw : (visitTwin v).1 ∈ S := by rw [visitTwin_crossing]; exact hv
    rw [smoothingSuccessor_visit_of_mem hn hP S (visitTwin v) htw, visitTwin_involutive]
  incoming_arc := by
    intro a
    refine ⟨rfl, ?_, owner_predecessor hn hP S a⟩
    exact selectedMarkPerm_evaluation hn hP.1 S (prevMark hn hP a)
  unselected_visit := fun v hv => smoothingSuccessor_visit_of_not_mem hn hP S v hv
  vertex := fun i => smoothingSuccessor_vertex hn hP S i
  same_point := by
    intro v
    have h := selectedMarkPerm_evaluation hn hP.1 {v.1} (Sum.inr v)
    simpa [selectedMarkPerm_visit, selectedVisitTwin_of_mem _ v (Finset.mem_singleton_self _)] using h
  distinct_carriers := fun v hv => (independent_successor_components hn hP hS).2.2 v hv
  owner_iff := fun a b => owner_eq_iff hn hP S a b

/-- conv:selected-visits for every generic polygon with `n ≥ 3` and every decomposition `S`. -/
def SelectedVisitsConventionDefinitionData : Prop :=
  ∀ k : ℕ, ∀ _ : NeZero k, ∀ hk : 3 ≤ k, ∀ P : LabelledTuple k, ∀ hP : Generic P,
    ∀ S : Finset (Crossing P), IsDecomposition hk hP S → SelectedVisitsConventionData hk hP S

theorem selected_visits_convention : SelectedVisitsConventionDefinitionData :=
  fun _ _ hk _ hP _ hS => selectedVisitsConvention_data hk hP hS

end SM
