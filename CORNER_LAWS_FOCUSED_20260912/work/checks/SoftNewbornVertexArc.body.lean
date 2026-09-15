namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The old attachment vertex as an actual half-open traversal position:
the start of the enlarged soft edge, at parameter zero. -/
def softAttachmentVertexPosition (j : ZMod n) : TraversalPoint (n + 1) :=
  (softOldIndex j j, ⟨0, le_rfl, zero_lt_one⟩)

/-- The inserted vertex as the actual start of the return edge. -/
def softInsertedVertexPosition (j : ZMod n) : TraversalPoint (n + 1) :=
  (softNewIndex j, ⟨0, le_rfl, zero_lt_one⟩)

theorem softAttachmentVertexPosition_evaluation (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) :
    traversalEvaluation (softInsertion P j q ε) (softAttachmentVertexPosition j) = P j := by
  change edgePoint (softInsertion P j q ε) (softOldIndex j j) 0 = P j
  rw [edgePoint_zero, softInsertion_old]

theorem softInsertedVertexPosition_evaluation (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ) :
    traversalEvaluation (softInsertion P j q ε) (softInsertedVertexPosition j) = P j + ε • q := by
  change edgePoint (softInsertion P j q ε) (softNewIndex j) 0 = P j + ε • q
  rw [edgePoint_zero, softInsertion_new]

/-- Exact numerical representatives of the three consecutive enlarged edges.
The return edge crosses the numerical cut precisely when the parent label is zero. -/
theorem soft_vertex_arc_label_values (hn : 3 ≤ n) (j : ZMod n) :
    (softOldIndex j (j - 1)).val = (canonicalPosition j).val ∧
    (softOldIndex j j).val = (canonicalPosition j).val + 1 ∧
    (softNewIndex j).val = if j = 0 then 0 else j.val + 1 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← softParentEdge_of_ne j (j - 1) (prev_ne_self j), softParentEdge_val]
    by_cases hj : j = 0
    · rw [if_pos (Or.inl hj)]
      rfl
    · have hpos := ZMod.val_pos.mpr hj
      have hprev : (j - 1).val = j.val - 1 := canonicalPosition_val_nonzero j hj
      have hlt : (j - 1).val < j.val := by rw [hprev]; omega
      rw [if_pos (Or.inr hlt)]
      rfl
  · rw [softOldIndex_at_attachment]
    exact ZMod.val_natCast_of_lt (by have := (canonicalPosition j).isLt; omega)
  · rw [← softParentEdge_at_attachment j, softParentEdge_val]
    simp only [lt_self_iff_false, or_false]
    by_cases hj : j = 0
    · simp only [if_pos hj, hj, ZMod.val_zero]
    · simp only [if_neg hj]

/-- The actual three enlarged edge labels force the two vertex positions to
occur in this order on the short incoming-to-return arc. The incoming point
may be anywhere in its half-open edge; positivity of the return parameter is
necessary to put the inserted vertex strictly before it. No order is assumed. -/
theorem soft_vertex_arc_of_edges (hn : 3 ≤ n) (j : ZMod n)
    (a b : TraversalPoint (n + 1))
    (ha : a.1 = softOldIndex j (j - 1)) (hb : b.1 = softNewIndex j)
    (hbpos : 0 < b.2.val) :
    traversalBetween a (softAttachmentVertexPosition j) b ∧
    traversalBetween a (softInsertedVertexPosition j) b ∧
    traversalBetween a (softAttachmentVertexPosition j) (softInsertedVertexPosition j) ∧
    traversalBetween (softAttachmentVertexPosition j) (softInsertedVertexPosition j) b := by
  have hlabels := soft_vertex_arc_label_values hn j
  have ham : traversalKey a < traversalKey (softAttachmentVertexPosition j) := by
    apply traversalKey_lt_of_edge_lt
    change a.1.val < (softOldIndex j j).val
    rw [ha, hlabels.1, hlabels.2.1]
    omega
  have hnb : traversalKey (softInsertedVertexPosition j) < traversalKey b := by
    apply (traversalKey_lt_iff _ _).mpr
    exact Or.inr ⟨hb.symm, hbpos⟩
  by_cases hj : j = 0
  · have hba : traversalKey b < traversalKey a := by
      apply traversalKey_lt_of_edge_lt
      rw [hb, ha, hlabels.1, hlabels.2.2, if_pos hj, hj, canonicalPosition_val_zero]
      omega
    exact ⟨Or.inr (Or.inr ⟨hba, ham⟩),
      Or.inr (Or.inl ⟨hnb, hba⟩),
      Or.inr (Or.inr ⟨lt_trans hnb hba, ham⟩),
      Or.inr (Or.inl ⟨hnb, lt_trans hba ham⟩)⟩
  · have hmn : traversalKey (softAttachmentVertexPosition j) <
        traversalKey (softInsertedVertexPosition j) := by
      apply traversalKey_lt_of_edge_lt
      change (softOldIndex j j).val < (softNewIndex j).val
      rw [hlabels.2.1, hlabels.2.2, if_neg hj, canonicalPosition_val_nonzero j hj]
      have hpos := ZMod.val_pos.mpr hj
      omega
    exact ⟨Or.inl ⟨ham, lt_trans hmn hnb⟩,
      Or.inl ⟨lt_trans ham hmn, hnb⟩,
      Or.inl ⟨ham, hmn⟩,
      Or.inl ⟨hmn, hnb⟩⟩

/-- Source newborn arc through M and M_epsilon, using the actual newborn
visits constructed from classification and the loop sector. Child G1 gives
strict interiority. Every cyclic cut, including j = 0, is covered. -/
theorem softNewbornVisits_vertex_arc (hn : 3 ≤ n) {P : LabelledTuple n}
    {j : ZMod n} {q : Plane} {ε : ℝ}
    (hQ : G1 (softInsertion P j q ε)) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (softAttachmentVertexPosition j)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) ∧
    traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (softInsertedVertexPosition j)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) ∧
    traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (softAttachmentVertexPosition j) (softInsertedVertexPosition j) ∧
    traversalBetween (softAttachmentVertexPosition j) (softInsertedVertexPosition j)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) := by
  apply soft_vertex_arc_of_edges hn j
  · rfl
  · rfl
  · exact (softNewbornVisits_interior hn hQ hclass hloop).2.1

end
end SM
