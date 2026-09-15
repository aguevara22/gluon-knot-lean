namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- The newborn's incoming parameter tends to one, beyond every parent
crossing parameter on the incoming edge. -/
theorem soft_newborn_after_incoming_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j l : ZMod n) (q : Plane) (hc : IsCrossing P {j - 1, l}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
        softNewbornIncomingParameter P j q ε := by
  have hp := continuousAt_softParentParameter P j (j - 1) l q
    (crossing_edgeParameter_det_ne_zero hn hP hc)
  have hs := (softNewborn_continuousAt_zero hn hP j q).1
  have hz := (softNewborn_values_zero hn hP j q).1
  have hi := crossingParameter_interior hn hP
    (⟨{j - 1, l}, hc⟩ : Crossing P) (j - 1) (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hc] at hi
  exact continuousAt_preserves_strict_order hp hs
    (by simpa only [softParentParameter_zero, hz] using hi.2)

/-- The newborn's return parameter tends to zero, before every parent
crossing parameter on the outgoing edge represented by the return edge. -/
theorem soft_newborn_before_return_visits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j l : ZMod n) (q : Plane) (hc : IsCrossing P {j, l}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), softNewbornReturnParameter P j q ε <
      edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l) := by
  have hp := continuousAt_softParentParameter P j j l q
    (crossing_edgeParameter_det_ne_zero hn hP hc)
  have hs := (softNewborn_continuousAt_zero hn hP j q).2.1
  have hz := (softNewborn_values_zero hn hP j q).2.1
  have hi := crossingParameter_interior hn hP (⟨{j, l}, hc⟩ : Crossing P) j (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hc] at hi
  exact continuousAt_preserves_strict_order hs hp
    (by simpa only [softParentParameter_zero, hz] using hi.1)

/-- One positive interval simultaneously puts all inherited incoming visits
before the newborn and all inherited return visits after it. In the loop
sector the frozen crossing-data theorem identifies these parameters with
the actual newborn visits; the intervening soft edge has no crossings. -/
theorem soft_newborn_small_visit_windows (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → ∀ l : ZMod n,
      (IsCrossing P {j - 1, l} →
        edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
          softNewbornIncomingParameter P j q ε) ∧
      (IsCrossing P {j, l} → softNewbornReturnParameter P j q ε <
        edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ∀ l : ZMod n,
      (IsCrossing P {j - 1, l} →
        edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
          softNewbornIncomingParameter P j q ε) ∧
      (IsCrossing P {j, l} → softNewbornReturnParameter P j q ε <
        edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l)) := by
    apply eventually_all.mpr
    intro l
    apply Filter.Eventually.and
    · by_cases hc : IsCrossing P {j - 1, l}
      · exact (soft_newborn_after_incoming_visits hn hP j l q hc).mono (fun _ h _ => h)
      · exact Eventually.of_forall (fun _ h => (hc h).elim)
    · by_cases hc : IsCrossing P {j, l}
      · exact (soft_newborn_before_return_visits hn hP j l q hc).mono (fun _ h _ => h)
      · exact Eventually.of_forall (fun _ h => (hc h).elim)
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  exact hmem (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using hεδ)

end
end SM
