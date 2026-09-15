namespace SM.Carrier

noncomputable section
variable {n : ℕ} [NeZero n]

/-- An actual incoming segment ending at a visit starts earlier on that
visit's original edge. The alternative next-vertex case is impossible for a
visit endpoint; no selected-status premise is needed for this incoming fact. -/
theorem smoothingSuccessor_incoming_visit_position (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (x : Mark P) (v : Visit P)
    (hx : smoothingSuccessor hn hP S x = Sum.inr v) :
    (markPosition hn hP.1 (selectedMarkPerm S x)).1 = v.2.val ∧
      (markPosition hn hP.1 (selectedMarkPerm S x)).2.val < visitParameter v := by
  have he : markSuccessor hn hP (selectedMarkPerm S x) = Sum.inr v := hx
  rcases markSuccessor_position_cases hn hP (selectedMarkPerm S x) with ⟨hi, ht⟩ | hv
  · constructor
    · simpa only [he, markPosition_visit, visitPosition_edge] using hi.symm
    · simpa only [he, markPosition_visit, visitPosition_parameter] using ht
  · have hbad := he.symm.trans hv
    cases hbad

/-- The actual incoming segment has the visit's exact parameter as its upper
endpoint, with its full affine formula and strictly smaller actual start
parameter. This fixes the matching parameter without a supplied segment witness. -/
theorem smoothingSegment_incoming_visit_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (x : Mark P) (v : Visit P)
    (hx : smoothingSuccessor hn hP S x = Sum.inr v) :
    let p := markPosition hn hP.1 (selectedMarkPerm S x)
    p.1 = v.2.val ∧ 0 ≤ p.2.val ∧ p.2.val < visitParameter v ∧
      traversalEvaluation P (markPosition hn hP.1 x) = edgePoint P v.2.val p.2.val ∧
      ∀ u : ℝ, smoothingSegment hn hP S x u =
        edgePoint P v.2.val (p.2.val + u * (visitParameter v - p.2.val)) := by
  dsimp only
  obtain ⟨hedge, hlt⟩ := smoothingSuccessor_incoming_visit_position hn hP S x v hx
  let s := (markPosition hn hP.1 (selectedMarkPerm S x)).2.val
  have hstart : traversalEvaluation P (markPosition hn hP.1 x) =
      edgePoint P v.2.val s := by
    rw [← selectedMarkPerm_evaluation hn hP.1 S x]
    change edgePoint P (markPosition hn hP.1 (selectedMarkPerm S x)).1 s =
      edgePoint P v.2.val s
    rw [hedge]
  refine ⟨hedge, (markPosition hn hP.1 (selectedMarkPerm S x)).2.property.1,
    hlt, hstart, ?_⟩
  intro u
  unfold smoothingSegment
  rw [hx, hstart]
  change edgePoint P v.2.val s +
      u • (edgePoint P v.2.val (visitParameter v) - edgePoint P v.2.val s) =
    edgePoint P v.2.val (s + u * (visitParameter v - s))
  exact edgePoint_affine P v.2.val s (visitParameter v) u

/-- Across an actual unselected intermediate visit, the incoming upper
parameter and outgoing lower parameter coincide exactly. Both complete affine
segments follow strictly increasing intervals on the same original edge. -/
theorem smoothingSegment_unselected_join_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (x : Mark P) (v : Visit P)
    (hx : smoothingSuccessor hn hP S x = Sum.inr v) (hv : v.1 ∉ S) :
    let p := markPosition hn hP.1 (selectedMarkPerm S x)
    ∃ t : ℝ, p.1 = v.2.val ∧
      markPosition hn hP.1 (selectedMarkPerm S (Sum.inr v)) = visitPosition hn hP.1 v ∧
      0 ≤ p.2.val ∧ p.2.val < visitParameter v ∧ visitParameter v < t ∧ t ≤ 1 ∧
      (∀ u : ℝ, smoothingSegment hn hP S x u =
        edgePoint P v.2.val (p.2.val + u * (visitParameter v - p.2.val))) ∧
      (∀ u : ℝ, smoothingSegment hn hP S (Sum.inr v) u =
        edgePoint P v.2.val (visitParameter v + u * (t - visitParameter v))) := by
  dsimp only
  obtain ⟨hedge, hs0, hsv, hstart, hin⟩ :=
    smoothingSegment_incoming_visit_data hn hP S x v hx
  have hslot : selectedMarkPerm S (Sum.inr v) = Sum.inr v := by
    rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]
  have hpos : markPosition hn hP.1 (selectedMarkPerm S (Sum.inr v)) =
      visitPosition hn hP.1 v := by
    rw [hslot, markPosition_visit]
  obtain ⟨t, hvt, ht1, houtStart, houtEnd, hout⟩ :=
    smoothingSegment_subsegment_data hn hP S (Sum.inr v)
  have hvt' : visitParameter v < t := by
    simpa only [hpos, visitPosition_parameter] using hvt
  have hout' (u : ℝ) : smoothingSegment hn hP S (Sum.inr v) u =
      edgePoint P v.2.val (visitParameter v + u * (t - visitParameter v)) := by
    simpa only [hpos, visitPosition_edge, visitPosition_parameter] using hout u
  exact ⟨t, hedge, hpos, hs0, hsv, hvt', ht1, hin, hout'⟩

end
end SM.Carrier
