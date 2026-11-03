import DirectGLSSW.CutEventAdapterV3Headers

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeChainsV3

open DirectGLSSW
open DirectGLSSW.OrderedCapEvents
open scoped BigOperators

theorem cutEventChain_values_eq_cutVertices
    {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (i j : EventIndex q n) (hij : i.val < j.val)
    (S : IntervalCutSet i.val j.val) :
    eventIndexValues (cutEventChain i j hij S) =
      cutVertices i.val j.val S.val := by
  classical
  simp [eventIndexValues, cutEventChain, cutSetToIncreasingCuts, cutVertices]

theorem cutEventChain_pairwise_sorted
    {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (i j : EventIndex q n) (hij : i.val < j.val)
    (S : IntervalCutSet i.val j.val) :
    List.Pairwise (· < ·) (cutEventChain i j hij S) := by
  have hvalues : (cutEventChain i j hij S).map Fin.val =
      cutVertices i.val j.val S.val := by
    simpa [eventIndexValues] using
      cutEventChain_values_eq_cutVertices i j hij S
  have hmap : List.Pairwise (· < ·) ((cutEventChain i j hij S).map Fin.val) := by
    rw [hvalues]
    exact cutVertices_pairwise hij (Finset.mem_powerset.mp S.property)
  exact List.Pairwise.imp
    (fun {a b} hab => (Fin.lt_iff_val_lt_val).2 hab)
    ((List.pairwise_map (f := Fin.val) (R := (· < ·))
      (l := cutEventChain i j hij S)).mp hmap)

theorem event_weightedCutTerm_zero_of_arc_order_failure
    {q : ℕ → PlanarPoint ℝ} {n : ℕ}
    (i j : EventIndex q n) (hij : i.val < j.val)
    (S : IntervalCutSet i.val j.val) (w : ℕ → ℚ)
    (hbad : ¬ List.Pairwise
      (fun c d => (eventPair q n c).1 < (eventPair q n d).1)
      (cutEventChain i j hij S)) :
    (∏ k ∈ S.val, w k) *
      branchProduct (eventIntervalArray q n) (cutVertices i.val j.val S.val) = 0 := by
  have hzero := event_branchProduct_zero_of_arc_order_failure
    (cutEventChain i j hij S)
    (cutEventChain_pairwise_sorted i j hij S) hbad
  rw [cutEventChain_values_eq_cutVertices i j hij S] at hzero
  simp [hzero]





end DirectGLSSW.MixedEdgeChainsV3
