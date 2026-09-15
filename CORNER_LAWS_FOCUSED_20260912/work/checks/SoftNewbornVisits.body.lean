namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
variable {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- The actual visit of the newborn crossing on the incoming enlarged edge. -/
def softNewbornIncomingVisit (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    Visit (softInsertion P j q ε) :=
  ⟨softNewbornCrossing hclass hloop, softOldIndex j (j - 1),
    by simp [softNewbornCrossing]⟩

/-- The actual visit of the same crossing on the return enlarged edge. -/
def softNewbornReturnVisit (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    Visit (softInsertion P j q ε) :=
  ⟨softNewbornCrossing hclass hloop, softNewIndex j,
    by simp [softNewbornCrossing]⟩

theorem softNewbornIncomingVisit_edge (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornIncomingVisit hclass hloop).2.val = softOldIndex j (j - 1) := rfl

theorem softNewbornReturnVisit_edge (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornReturnVisit hclass hloop).2.val = softNewIndex j := rfl

theorem softNewbornVisits_crossing (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornIncomingVisit hclass hloop).1 = softNewbornCrossing hclass hloop ∧
    (softNewbornReturnVisit hclass hloop).1 = softNewbornCrossing hclass hloop := ⟨rfl, rfl⟩

theorem softNewbornVisits_distinct (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    softNewbornIncomingVisit hclass hloop ≠ softNewbornReturnVisit hclass hloop := by
  intro he
  exact softOldIndex_ne_new j (j - 1)
    (congrArg (fun v : Visit (softInsertion P j q ε) => v.2.val) he)

/-- There are exactly these two visits of the newborn crossing; no other
member edge is allowed by its actual two-element support. -/
theorem softNewbornVisits_exhaust (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (w : Visit (softInsertion P j q ε)) (hw : w.1 = softNewbornCrossing hclass hloop) :
    w = softNewbornIncomingVisit hclass hloop ∨ w = softNewbornReturnVisit hclass hloop := by
  have hs : w.1.val = {softOldIndex j (j - 1), softNewIndex j} := congrArg Subtype.val hw
  have hm : w.2.val ∈ ({softOldIndex j (j - 1), softNewIndex j} : Finset (ZMod (n + 1))) :=
    hs ▸ w.2.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hin | hout
  · exact Or.inl (visit_ext hs hin)
  · exact Or.inr (visit_ext hs hout)

/-- The canonical actual visit parameters are exactly the proved Cramer
parameters; this uses actual transversality, not a new parameter choice. -/
theorem softNewbornVisits_parameters (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0) :
    visitParameter (softNewbornIncomingVisit hclass hloop) = softNewbornIncomingParameter P j q ε ∧
    visitParameter (softNewbornReturnVisit hclass hloop) = softNewbornReturnParameter P j q ε := by
  have hdata := softNewborn_crossing_data P j q ε hd (softNewbornCrossing hclass hloop).property
  exact ⟨hdata.1, hdata.2.1⟩

theorem softNewbornVisits_interior (hn : 3 ≤ n)
    (hQ : G1 (softInsertion P j q ε)) (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (0 < visitParameter (softNewbornIncomingVisit hclass hloop) ∧
      visitParameter (softNewbornIncomingVisit hclass hloop) < 1) ∧
    (0 < visitParameter (softNewbornReturnVisit hclass hloop) ∧
      visitParameter (softNewbornReturnVisit hclass hloop) < 1) :=
  ⟨visitPosition_interior (by omega : 3 ≤ n + 1) hQ _,
    visitPosition_interior (by omega : 3 ≤ n + 1) hQ _⟩

/-- The two actual visit edges have precisely the soft edge between them.
Its endpoints evaluate to M and M_epsilon, including at the residue-zero cut. -/
theorem softNewbornVisits_physical_path (hn : 3 ≤ n)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (softNewbornIncomingVisit hclass hloop).2.val + 1 = softOldIndex j j ∧
    softOldIndex j j + 1 = (softNewbornReturnVisit hclass hloop).2.val ∧
    softInsertion P j q ε (softOldIndex j j) = P j ∧
    softInsertion P j q ε (softNewbornReturnVisit hclass hloop).2.val = P j + ε • q := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨?_, softOldIndex_attachment_next j, softInsertion_old P j j q ε,
    softInsertion_new P j q ε⟩
  change softOldIndex j (j - 1) + 1 = softOldIndex j j
  simpa only [sub_add_cancel] using (softOldIndex_next j (j - 1) (prev_ne_self j)).symm

/-- Pointwise use of the proved finite parameter windows. The explicit window
hypothesis is discharged from the actual family in the final interval theorem. -/
theorem softNewbornVisits_inherited_bounds (hn : 3 ≤ n)
    (hQ : G1 (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0)
    (hwin : ∀ l : ZMod n,
      (IsCrossing P {j - 1, l} →
        edgeParameter (softInsertion P j q ε) (softParentEdge j (j - 1)) (softParentEdge j l) <
          softNewbornIncomingParameter P j q ε) ∧
      (IsCrossing P {j, l} → softNewbornReturnParameter P j q ε <
        edgeParameter (softInsertion P j q ε) (softParentEdge j j) (softParentEdge j l)))
    (v : Visit P) :
    (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
      visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
    (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
      visitParameter (softInheritedVisit hp v)) := by
  obtain ⟨l, _, hs⟩ := crossing_pair_of_mem v.1 v.2.val v.2.property
  have hc : IsCrossing P {v.2.val, l} := hs ▸ v.1.property
  have hpar := softNewbornVisits_parameters hclass hloop hd
  have hvpar := softInheritedVisit_parameter hn hp hQ v l hs
  constructor
  · intro hv
    have hc' : IsCrossing P {j - 1, l} := by simpa only [hv] using hc
    rw [hvpar, hpar.1, hv]
    exact (hwin l).1 hc'
  · intro hv
    have hc' : IsCrossing P {j, l} := by simpa only [hv] using hc
    rw [hvpar, hpar.2, hv]
    exact (hwin l).2 hc'

/-- Every child visit is either inherited, when the actual parent-edge arc
lemma excludes it, or one of the two endpoints. Thus the short oriented arc
contains no crossing visit, with no exception at j = 0. -/
theorem softNewbornVisits_no_between (hn : 3 ≤ n)
    (hQ : G1 (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hbound : ∀ v : Visit P,
      (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
      (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v)))
    (w : Visit (softInsertion P j q ε)) :
    ¬ traversalBetween
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop))
      (visitPosition (by omega : 3 ≤ n + 1) hQ w)
      (visitPosition (by omega : 3 ≤ n + 1) hQ (softNewbornReturnVisit hclass hloop)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  by_cases hw : w.1 = softNewbornCrossing hclass hloop
  · rcases softNewbornVisits_exhaust hclass hloop w hw with he | he
    · rw [he]
      unfold traversalBetween
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
    · rw [he]
      unfold traversalBetween
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  · obtain ⟨v, rfl⟩ := (softInheritedVisit_range_loop hn hp hclass hloop w).mpr hw
    apply soft_parent_traversal_arc_empty hn j v.2.val
    · change softOldIndex j (j - 1) = softParentEdge j (j - 1)
      exact (softParentEdge_of_ne j (j - 1) (prev_ne_self j)).symm
    · rfl
    · change softNewIndex j = softParentEdge j j
      exact (softParentEdge_at_attachment j).symm
    · intro hv
      exact ((hbound v).1 hv).le
    · intro hv
      exact ((hbound v).2 hv).le

/-- A single positive interval supplies all actual data and the empty short
arc in the loop sector. The geometric assumptions are exactly parent Generic
and actual admissibility; every window and classification premise is derived. -/
theorem soft_newborn_small_empty_arc (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
      ∃ hp : SoftCrossingPersistence P j q ε,
      ∃ hclass : SoftCrossingClassificationAt P j q ε,
      ∀ hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j,
        (∀ v : Visit P,
          (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
            visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
          (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
            visitParameter (softInheritedVisit hp v))) ∧
        (∀ w : Visit (softInsertion P j q ε),
          ¬ traversalBetween
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
            (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop))) := by
  obtain ⟨δt, hδt, htransport⟩ := soft_small_crossing_transport_data hn hP j q hq
  obtain ⟨δw, hδw, hwindow⟩ := soft_newborn_small_visit_windows hn hP.1 j q
  obtain ⟨δd, hδd, hdet⟩ := softNewborn_small_det_ne hn hP.1 j q
  refine ⟨min δt (min δw δd), lt_min hδt (lt_min hδw hδd), ?_⟩
  intro ε hε hεδ
  have hεt : ε < δt := lt_of_lt_of_le hεδ (min_le_left δt (min δw δd))
  have hεw : ε < δw := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δt (min δw δd)) (min_le_left δw δd))
  have hεd : |ε| < δd := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ
      (le_trans (min_le_right δt (min δw δd)) (min_le_right δw δd))
  obtain ⟨hQ, hp, hclass⟩ := htransport ε hε hεt
  refine ⟨hQ, hp, hclass, ?_⟩
  intro hloop
  have hbound := softNewbornVisits_inherited_bounds hn hQ.1 hp hclass hloop
    (hdet ε hεd) (hwindow ε hε hεw)
  exact ⟨hbound, softNewbornVisits_no_between hn hQ.1 hp hclass hloop hbound⟩

end
end SM
