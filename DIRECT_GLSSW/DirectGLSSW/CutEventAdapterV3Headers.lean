import DirectGLSSW.MixedEdgeCutInverse
import DirectGLSSW.CutRepresentation

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeChainsV3

open DirectGLSSW
open DirectGLSSW.OrderedCapEvents

/-- Lift the exact increasing cut list to event-index ranks without dropping
either endpoint. -/
noncomputable def cutEventChain {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (i j : EventIndex q n) (hij : i.val < j.val)
    (S : IntervalCutSet i.val j.val) : List (EventIndex q n) := by
  let l := cutSetToIncreasingCuts hij S
  exact i :: l.val.attach.map (fun k =>
    (⟨k.val, lt_trans (increasingCuts_bounds l k.property).2 j.isLt⟩ :
      EventIndex q n)) ++ [j]

abbrev cutEventChain_pairwise_sorted_header : Prop :=
  ∀ {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (i j : EventIndex q n) (hij : i.val < j.val)
    (S : IntervalCutSet i.val j.val),
    List.Pairwise (· < ·) (cutEventChain i j hij S)

abbrev cutEventChain_values_eq_cutVertices_header : Prop :=
  ∀ {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (i j : EventIndex q n) (hij : i.val < j.val)
    (S : IntervalCutSet i.val j.val),
    eventIndexValues (cutEventChain i j hij S) =
      cutVertices i.val j.val S.val

abbrev event_weightedCutTerm_zero_of_arc_order_failure_header : Prop :=
  ∀ {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (i j : EventIndex q n) (hij : i.val < j.val)
    (S : IntervalCutSet i.val j.val) (w : ℕ → ℚ),
    ¬ List.Pairwise
      (fun c d => (eventPair q n c).1 < (eventPair q n d).1)
      (cutEventChain i j hij S) →
    (∏ k ∈ S.val, w k) *
      branchProduct (eventIntervalArray q n) (cutVertices i.val j.val S.val) = 0

#check cutEventChain_pairwise_sorted_header
#check cutEventChain_values_eq_cutVertices_header
#check event_weightedCutTerm_zero_of_arc_order_failure_header

end DirectGLSSW.MixedEdgeChainsV3
