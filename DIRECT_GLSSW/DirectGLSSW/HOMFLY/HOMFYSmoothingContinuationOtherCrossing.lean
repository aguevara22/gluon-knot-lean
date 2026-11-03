import DirectGLSSW.HOMFLY.HOMFYSmoothingCombinatorics
import Mathlib.Tactic.FinCases

namespace DirectGLSSW.HOMFLY

private theorem finTwo_eq_zero_or_one_local (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

noncomputable def smoothContinuationAdjustLocal (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : Equiv.Perm (SmoothArcCode D) := by
  classical
  by_cases h0 : D.through c 0 = 0
  · have h1 : D.through c 1 = 1 := by
      rcases finTwo_eq_zero_or_one_local (D.through c 1) with hv | hv
      · have hbad := (D.through c).injective (h0.trans hv.symm)
        norm_num at hbad
      · exact hv
    exact Equiv.swap (Sum.inl (D.outgoing c 0)) (Sum.inl (D.outgoing c 1)) *
      Equiv.swap (Sum.inl (D.outgoing c 1)) (Sum.inr 1) *
      Equiv.swap (Sum.inl (D.outgoing c 0)) (Sum.inr 0)
  · have hzero : D.through c 0 = 1 := by
      rcases finTwo_eq_zero_or_one_local (D.through c 0) with hv | hv
      · exact False.elim (h0 hv)
      · exact hv
    have hone : D.through c 1 = 0 := by
      rcases finTwo_eq_zero_or_one_local (D.through c 1) with hv | hv
      · exact hv
      · have hbad := (D.through c).injective (hzero.trans hv.symm)
        norm_num at hbad
    exact Equiv.swap (Sum.inl (D.outgoing c 1)) (Sum.inr 0) *
      Equiv.swap (Sum.inl (D.outgoing c 0)) (Sum.inr 1)

noncomputable def smoothContinuationCodeLocal (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : Equiv.Perm (SmoothArcCode D) :=
  smoothContinuationAdjustLocal D c * Equiv.sumCongr D.continuation (Equiv.refl (Fin 2))

theorem smoothContinuationCodeLocal_other_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (d : SmoothCrossingCode D c) (i : Fin 2) :
    smoothContinuationCodeLocal D c (Sum.inl (D.incoming d.val i)) =
      Sum.inl (D.continuation (D.incoming d.val i)) := by
  have hnot0 : D.continuation (D.incoming d.val i) ≠ D.outgoing c 0 := by
    intro heq
    apply d.property
    apply D.crossingVertex_injective
    calc
      D.crossingVertex d.val = D.arcTarget (D.incoming d.val i) :=
        (D.incoming_target d.val i).symm
      _ = D.arcSource (D.continuation (D.incoming d.val i)) :=
        D.continuation_incidence _
      _ = D.arcSource (D.outgoing c 0) := by rw [heq]
      _ = D.crossingVertex c := D.outgoing_source c 0
  have hnot1 : D.continuation (D.incoming d.val i) ≠ D.outgoing c 1 := by
    intro heq
    apply d.property
    apply D.crossingVertex_injective
    calc
      D.crossingVertex d.val = D.arcTarget (D.incoming d.val i) :=
        (D.incoming_target d.val i).symm
      _ = D.arcSource (D.continuation (D.incoming d.val i)) :=
        D.continuation_incidence _
      _ = D.arcSource (D.outgoing c 1) := by rw [heq]
      _ = D.crossingVertex c := D.outgoing_source c 1
  by_cases h0 : D.through c 0 = 0
  · have h1 : D.through c 1 = 1 := by
      rcases finTwo_eq_zero_or_one_local (D.through c 1) with hv | hv
      · have hbad := (D.through c).injective (h0.trans hv.symm)
        norm_num at hbad
      · exact hv
    simp [smoothContinuationCodeLocal, smoothContinuationAdjustLocal, h0, h1,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, hnot0, hnot1]
  · have hzero : D.through c 0 = 1 := by
      rcases finTwo_eq_zero_or_one_local (D.through c 0) with hv | hv
      · exact False.elim (h0 hv)
      · exact hv
    have hone : D.through c 1 = 0 := by
      rcases finTwo_eq_zero_or_one_local (D.through c 1) with hv | hv
      · exact hv
      · have hbad := (D.through c).injective (hzero.trans hv.symm)
        norm_num at hbad
    simp [smoothContinuationCodeLocal, smoothContinuationAdjustLocal, h0, hzero, hone,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, hnot0, hnot1]

theorem smoothContinuationLocal_other_crossing_transition (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (d : SmoothCrossingCode D c) (i : Fin 2) :
    ((smoothArcEquiv D).symm.trans
      ((smoothContinuationCodeLocal D c).trans (smoothArcEquiv D)))
        (smoothArcEquiv D (Sum.inl (D.incoming d.val i))) =
      smoothArcEquiv D (Sum.inl (D.outgoing d.val (D.through d.val i))) := by
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  change smoothArcEquiv D
      (smoothContinuationCodeLocal D c (Sum.inl (D.incoming d.val i))) = _
  rw [smoothContinuationCodeLocal_other_incoming, D.continuation_crossing]



theorem smoothContinuationCodeLocal_eq (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothContinuationCodeLocal D c = smoothContinuationCode D c := by
  rfl

theorem smoothContinuationCodeLocal_incident_incoming_zero (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    smoothContinuationCodeLocal D c (Sum.inl (D.incoming c 0)) = Sum.inr 0 := by
  rw [smoothContinuationCodeLocal_eq]
  exact smoothContinuation_incoming_zero D c

theorem smoothContinuationCodeLocal_incident_incoming_one (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    smoothContinuationCodeLocal D c (Sum.inl (D.incoming c 1)) = Sum.inr 1 := by
  rw [smoothContinuationCodeLocal_eq]
  exact smoothContinuation_incoming_one D c

theorem smoothContinuationCodeLocal_connector_zero (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    smoothContinuationCodeLocal D c (Sum.inr 0) = Sum.inl (D.outgoing c 1) := by
  rw [smoothContinuationCodeLocal_eq]
  exact smoothContinuation_connector_zero D c

theorem smoothContinuationCodeLocal_connector_one (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    smoothContinuationCodeLocal D c (Sum.inr 1) = Sum.inl (D.outgoing c 0) := by
  rw [smoothContinuationCodeLocal_eq]
  exact smoothContinuation_connector_one D c


theorem smoothArcTargetCode_continuationCodeLocal (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : SmoothArcCode D) :
    smoothArcTargetCode D c e =
      smoothArcSourceCode D c (smoothContinuationCodeLocal D c e) := by
  classical
  rcases e with e | i
  · by_cases he0 : e = D.incoming c 0
    · subst e
      rw [smoothContinuationCodeLocal_eq, smoothContinuation_incoming_zero]
      simp [smoothArcTargetCode, smoothArcSourceCode]
    · by_cases he1 : e = D.incoming c 1
      · subst e
        rw [smoothContinuationCodeLocal_eq, smoothContinuation_incoming_one]
        have hinc := ((D.four_ports_distinct c).1).symm
        simp [smoothArcTargetCode, smoothArcSourceCode, smoothLeftCutCode, hinc]
      · have hnot0 : D.continuation e ≠ D.outgoing c 0 := by
          intro heq
          have htarget : D.arcTarget e = D.crossingVertex c := by
            calc
              D.arcTarget e = D.arcSource (D.continuation e) := D.continuation_incidence e
              _ = D.arcSource (D.outgoing c 0) := by rw [heq]
              _ = D.crossingVertex c := D.outgoing_source c 0
          have hport := (D.crossing_incidence_complete c e).mp (Or.inr htarget)
          rcases hport with h | h | h | h
          · exact he0 h
          · exact he1 h
          · subst e
            exact (D.arc_endpoints_distinct (D.outgoing c 0))
              ((D.outgoing_source c 0).trans htarget.symm)
          · subst e
            exact (D.arc_endpoints_distinct (D.outgoing c 1))
              ((D.outgoing_source c 1).trans htarget.symm)
        have hnot1 : D.continuation e ≠ D.outgoing c 1 := by
          intro heq
          have htarget : D.arcTarget e = D.crossingVertex c := by
            calc
              D.arcTarget e = D.arcSource (D.continuation e) := D.continuation_incidence e
              _ = D.arcSource (D.outgoing c 1) := by rw [heq]
              _ = D.crossingVertex c := D.outgoing_source c 1
          have hport := (D.crossing_incidence_complete c e).mp (Or.inr htarget)
          rcases hport with h | h | h | h
          · exact he0 h
          · exact he1 h
          · subst e
            exact (D.arc_endpoints_distinct (D.outgoing c 0))
              ((D.outgoing_source c 0).trans htarget.symm)
          · subst e
            exact (D.arc_endpoints_distinct (D.outgoing c 1))
              ((D.outgoing_source c 1).trans htarget.symm)
        have hmap : smoothContinuationCodeLocal D c (Sum.inl e) =
            Sum.inl (D.continuation e) := by
          have hnot0' := hnot0
          have hnot1' := hnot1
          by_cases h0 : D.through c 0 = 0
          · have h1 : D.through c 1 = 1 := by
              rcases finTwo_eq_zero_or_one_local (D.through c 1) with hv | hv
              · have hbad := (D.through c).injective (h0.trans hv.symm)
                norm_num at hbad
              · exact hv
            simp [smoothContinuationCodeLocal, smoothContinuationAdjustLocal, h0, h1,
              Equiv.Perm.mul_apply, Equiv.swap_apply_def, hnot0', hnot1']
          · have hz : D.through c 0 = 1 := by
              rcases finTwo_eq_zero_or_one_local (D.through c 0) with hv | hv
              · exact False.elim (h0 hv)
              · exact hv
            have ho : D.through c 1 = 0 := by
              rcases finTwo_eq_zero_or_one_local (D.through c 1) with hv | hv
              · exact hv
              · have hbad := (D.through c).injective (hz.trans hv.symm)
                norm_num at hbad
            simp [smoothContinuationCodeLocal, smoothContinuationAdjustLocal, h0, hz, ho,
              Equiv.Perm.mul_apply, Equiv.swap_apply_def, hnot0', hnot1']
        rw [hmap]
        simp [smoothArcTargetCode, smoothArcSourceCode, he0, he1, hnot0, hnot1,
          D.continuation_incidence]
  · fin_cases i <;>
      simp [smoothArcTargetCode, smoothArcSourceCode, smoothContinuationCodeLocal_connector_zero,
        smoothContinuationCodeLocal_connector_one, smoothRightCutCode, smoothLeftCutCode,
        D.four_ports_distinct, (D.four_ports_distinct c).2.1, ((D.four_ports_distinct c).2.1).symm]


private theorem smoothSourceCode_eq_old_crossing_iff (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (d : SmoothCrossingCode D c) (e : Fin D.nArc) :
    smoothArcSourceCode D c (Sum.inl e) = Sum.inl (D.crossingVertex d.val) ↔
      D.arcSource e = D.crossingVertex d.val := by
  have hcv : D.crossingVertex c ≠ D.crossingVertex d.val := by
    intro h
    exact d.property (D.crossingVertex_injective h.symm)
  by_cases h0 : e = D.outgoing c 0
  · subst e
    simp [smoothArcSourceCode, smoothRightCutCode, D.outgoing_source, hcv,
      (D.four_ports_distinct c).2.1, ((D.four_ports_distinct c).2.1).symm]
  · by_cases h1 : e = D.outgoing c 1
    · subst e
      simp [smoothArcSourceCode, smoothRightCutCode, D.outgoing_source, hcv,
      (D.four_ports_distinct c).2.1, ((D.four_ports_distinct c).2.1).symm]
    · simp [smoothArcSourceCode, h0, h1]

private theorem smoothTargetCode_eq_old_crossing_iff (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (d : SmoothCrossingCode D c) (e : Fin D.nArc) :
    smoothArcTargetCode D c (Sum.inl e) = Sum.inl (D.crossingVertex d.val) ↔
      D.arcTarget e = D.crossingVertex d.val := by
  have hcv : D.crossingVertex c ≠ D.crossingVertex d.val := by
    intro h
    exact d.property (D.crossingVertex_injective h.symm)
  by_cases h0 : e = D.incoming c 0
  · subst e
    simp [smoothArcTargetCode, smoothLeftCutCode, D.incoming_target, hcv]
  · by_cases h1 : e = D.incoming c 1
    · subst e
      simp [smoothArcTargetCode, smoothLeftCutCode, D.incoming_target, hcv,
        ((D.four_ports_distinct c).1).symm]
    · simp [smoothArcTargetCode, h0, h1]

theorem smoothArcCode_crossing_incidence_complete (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (d : SmoothCrossingCode D c) (e : SmoothArcCode D) :
    (smoothArcSourceCode D c e = Sum.inl (D.crossingVertex d.val) ∨
      smoothArcTargetCode D c e = Sum.inl (D.crossingVertex d.val)) ↔
      (e = Sum.inl (D.incoming d.val 0) ∨ e = Sum.inl (D.incoming d.val 1) ∨
        e = Sum.inl (D.outgoing d.val 0) ∨ e = Sum.inl (D.outgoing d.val 1)) := by
  rcases e with e | i
  · rw [smoothSourceCode_eq_old_crossing_iff, smoothTargetCode_eq_old_crossing_iff]
    simpa [Sum.inl.injEq] using D.crossing_incidence_complete d.val e
  · fin_cases i
    · have hcv : D.crossingVertex c ≠ D.crossingVertex d.val := by
        intro h
        exact d.property (D.crossingVertex_injective h.symm)
      simp [smoothArcSourceCode, smoothArcTargetCode, smoothLeftCutCode,
        smoothRightCutCode, hcv]
    · simp [smoothArcSourceCode, smoothArcTargetCode, smoothLeftCutCode,
        smoothRightCutCode]

end DirectGLSSW.HOMFLY
