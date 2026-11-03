import DirectGLSSW.HOMFLY.HOMFYSmoothingContinuationOtherCrossing
import Mathlib.Tactic.FinCases

namespace DirectGLSSW.HOMFLY

private theorem incoming_source_ne_crossing (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : D.arcSource (D.incoming c i) ≠ D.crossingVertex c := by
  intro h
  exact D.arc_endpoints_distinct (D.incoming c i)
    (h.trans (D.incoming_target c i).symm)

private theorem outgoing_target_ne_crossing (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : D.arcTarget (D.outgoing c i) ≠ D.crossingVertex c := by
  intro h
  exact D.arc_endpoints_distinct (D.outgoing c i)
    ((D.outgoing_source c i).trans h.symm)

theorem smoothTargetCode_left0_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcTargetCode D c a = smoothLeftCutCode D c 0 ↔
      a = Sum.inl (D.incoming c 0) := by
  rcases a with e | i
  · by_cases h0 : e = D.incoming c 0
    · subst e
      simp [smoothArcTargetCode, smoothLeftCutCode]
    · by_cases h1 : e = D.incoming c 1
      · subst e
        have hport := (D.four_ports_distinct c).1.symm
        simp [smoothArcTargetCode, smoothLeftCutCode, hport]
      · have htarget : D.arcTarget e ≠ D.crossingVertex c := by
          intro heq
          have hports := (D.crossing_incidence_complete c e).mp (Or.inr heq)
          rcases hports with h | h | h | h
          · exact h0 h
          · exact h1 h
          · exact outgoing_target_ne_crossing D c 0 (by simpa [h] using heq)
          · exact outgoing_target_ne_crossing D c 1 (by simpa [h] using heq)
        simp [smoothArcTargetCode, smoothLeftCutCode, h0, h1, htarget]
  · fin_cases i <;> simp [smoothArcTargetCode, smoothLeftCutCode, smoothRightCutCode]

theorem smoothTargetCode_left1_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcTargetCode D c a = smoothLeftCutCode D c 1 ↔
      a = Sum.inl (D.incoming c 1) := by
  rcases a with e | i
  · by_cases h1 : e = D.incoming c 1
    · subst e
      have hport := ((D.four_ports_distinct c).1).symm
      simp [smoothArcTargetCode, smoothLeftCutCode, hport]
    · by_cases h0 : e = D.incoming c 0
      · subst e
        have hport := (D.four_ports_distinct c).1
        simp [smoothArcTargetCode, smoothLeftCutCode, hport]
      · have htarget : D.arcTarget e ≠ D.crossingVertex c := by
          intro heq
          have hports := (D.crossing_incidence_complete c e).mp (Or.inr heq)
          rcases hports with h | h | h | h
          · exact h0 h
          · exact h1 h
          · exact outgoing_target_ne_crossing D c 0 (by simpa [h] using heq)
          · exact outgoing_target_ne_crossing D c 1 (by simpa [h] using heq)
        simp [smoothArcTargetCode, smoothLeftCutCode, h0, h1, htarget]
  · fin_cases i <;> simp [smoothArcTargetCode, smoothLeftCutCode, smoothRightCutCode]


theorem smoothSourceCode_left0_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcSourceCode D c a = smoothLeftCutCode D c 0 ↔ a = Sum.inr 0 := by
  rcases a with e | i
  · by_cases h0 : e = D.outgoing c 0
    · subst e
      simp [smoothArcSourceCode, smoothLeftCutCode, smoothRightCutCode]
    · by_cases h1 : e = D.outgoing c 1
      · subst e
        have hport := ((D.four_ports_distinct c).2.1).symm
        simp [smoothArcSourceCode, smoothLeftCutCode, smoothRightCutCode, hport]
      · have hsource : D.arcSource e ≠ D.crossingVertex c := by
          intro heq
          have hports := (D.crossing_incidence_complete c e).mp (Or.inl heq)
          rcases hports with h | h | h | h
          · exact incoming_source_ne_crossing D c 0 (by simpa [h] using heq)
          · exact incoming_source_ne_crossing D c 1 (by simpa [h] using heq)
          · exact h0 h
          · exact h1 h
        simp [smoothArcSourceCode, smoothLeftCutCode, h0, h1, hsource]
  · fin_cases i <;> simp [smoothArcSourceCode, smoothLeftCutCode]

theorem smoothSourceCode_left1_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcSourceCode D c a = smoothLeftCutCode D c 1 ↔ a = Sum.inr 1 := by
  rcases a with e | i
  · by_cases h0 : e = D.outgoing c 0
    · subst e
      simp [smoothArcSourceCode, smoothLeftCutCode, smoothRightCutCode]
    · by_cases h1 : e = D.outgoing c 1
      · subst e
        have hport := ((D.four_ports_distinct c).2.1).symm
        simp [smoothArcSourceCode, smoothLeftCutCode, smoothRightCutCode, hport]
      · have hsource : D.arcSource e ≠ D.crossingVertex c := by
          intro heq
          have hports := (D.crossing_incidence_complete c e).mp (Or.inl heq)
          rcases hports with h | h | h | h
          · exact incoming_source_ne_crossing D c 0 (by simpa [h] using heq)
          · exact incoming_source_ne_crossing D c 1 (by simpa [h] using heq)
          · exact h0 h
          · exact h1 h
        simp [smoothArcSourceCode, smoothLeftCutCode, h0, h1, hsource]
  · fin_cases i <;> simp [smoothArcSourceCode, smoothLeftCutCode]

theorem smoothSourceCode_right0_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcSourceCode D c a = smoothRightCutCode D c 0 ↔ a = Sum.inl (D.outgoing c 0) := by
  rcases a with e | i
  · by_cases h0 : e = D.outgoing c 0
    · subst e
      simp [smoothArcSourceCode, smoothRightCutCode]
    · by_cases h1 : e = D.outgoing c 1
      · subst e
        have hport := ((D.four_ports_distinct c).2.1).symm
        simp [smoothArcSourceCode, smoothRightCutCode, hport]
      · have hsource : D.arcSource e ≠ D.crossingVertex c := by
          intro heq
          have hports := (D.crossing_incidence_complete c e).mp (Or.inl heq)
          rcases hports with h | h | h | h
          · exact incoming_source_ne_crossing D c 0 (by simpa [h] using heq)
          · exact incoming_source_ne_crossing D c 1 (by simpa [h] using heq)
          · exact h0 h
          · exact h1 h
        simp [smoothArcSourceCode, smoothRightCutCode, h0, h1, hsource]
  · fin_cases i <;> simp [smoothArcSourceCode, smoothRightCutCode, smoothLeftCutCode]

theorem smoothSourceCode_right1_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcSourceCode D c a = smoothRightCutCode D c 1 ↔ a = Sum.inl (D.outgoing c 1) := by
  rcases a with e | i
  · by_cases h1 : e = D.outgoing c 1
    · subst e
      have hport := ((D.four_ports_distinct c).2.1).symm
      simp [smoothArcSourceCode, smoothRightCutCode, hport]
    · by_cases h0 : e = D.outgoing c 0
      · subst e
        have hport := (D.four_ports_distinct c).2.1
        simp [smoothArcSourceCode, smoothRightCutCode, hport]
      · have hsource : D.arcSource e ≠ D.crossingVertex c := by
          intro heq
          have hports := (D.crossing_incidence_complete c e).mp (Or.inl heq)
          rcases hports with h | h | h | h
          · exact incoming_source_ne_crossing D c 0 (by simpa [h] using heq)
          · exact incoming_source_ne_crossing D c 1 (by simpa [h] using heq)
          · exact h0 h
          · exact h1 h
        simp [smoothArcSourceCode, smoothRightCutCode, h0, h1, hsource]
  · fin_cases i <;> simp [smoothArcSourceCode, smoothRightCutCode, smoothLeftCutCode]

theorem smoothTargetCode_right0_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcTargetCode D c a = smoothRightCutCode D c 0 ↔ a = Sum.inr 1 := by
  rcases a with e | i
  · by_cases h0 : e = D.incoming c 0
    · subst e
      simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode]
    · by_cases h1 : e = D.incoming c 1
      · subst e
        have hinc := ((D.four_ports_distinct c).1).symm
        simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode, hinc]
      · simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode, h0, h1]
  · fin_cases i <;> simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode]

theorem smoothTargetCode_right1_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a : SmoothArcCode D) :
    smoothArcTargetCode D c a = smoothRightCutCode D c 1 ↔ a = Sum.inr 0 := by
  rcases a with e | i
  · by_cases h0 : e = D.incoming c 0
    · subst e
      simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode]
    · by_cases h1 : e = D.incoming c 1
      · subst e
        have hinc := ((D.four_ports_distinct c).1).symm
        simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode, hinc]
      · simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode, h0, h1]
  · fin_cases i <;> simp [smoothArcTargetCode, smoothRightCutCode, smoothLeftCutCode]

theorem smoothArcCode_cutpoint_target_count (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcTargetCode D c a = smoothLeftCutCode D c 0)).card = 1) ∧
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcTargetCode D c a = smoothLeftCutCode D c 1)).card = 1) := by
  constructor
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inl (D.incoming c 0), ?_⟩
    ext a
    simp [smoothTargetCode_left0_fiber]
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inl (D.incoming c 1), ?_⟩
    ext a
    simp [smoothTargetCode_left1_fiber]


theorem smoothArcCode_cutpoint_degree_table (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcSourceCode D c a = smoothLeftCutCode D c 0)).card = 1) ∧
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcSourceCode D c a = smoothLeftCutCode D c 1)).card = 1) ∧
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcSourceCode D c a = smoothRightCutCode D c 0)).card = 1) ∧
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcSourceCode D c a = smoothRightCutCode D c 1)).card = 1) ∧
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcTargetCode D c a = smoothRightCutCode D c 0)).card = 1) ∧
    ((Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcTargetCode D c a = smoothRightCutCode D c 1)).card = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inr 0, ?_⟩
    ext a
    simp [smoothSourceCode_left0_fiber]
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inr 1, ?_⟩
    ext a
    simp [smoothSourceCode_left1_fiber]
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inl (D.outgoing c 0), ?_⟩
    ext a
    simp [smoothSourceCode_right0_fiber]
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inl (D.outgoing c 1), ?_⟩
    ext a
    simp [smoothSourceCode_right1_fiber]
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inr 1, ?_⟩
    ext a
    simp [smoothTargetCode_right0_fiber]
  · rw [Finset.card_eq_one]
    refine ⟨Sum.inr 0, ?_⟩
    ext a
    simp [smoothTargetCode_right1_fiber]

end DirectGLSSW.HOMFLY
