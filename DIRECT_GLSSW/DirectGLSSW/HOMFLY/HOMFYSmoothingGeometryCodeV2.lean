import DirectGLSSW.HOMFLY.HOMFYSmoothingVertexInjective
import DirectGLSSW.HOMFLY.HOMFYSmoothingLocal

namespace DirectGLSSW.HOMFLY

private theorem finTwoGeometryCases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- Fresh target-code definition for the corrected geometric smoothing. Old
arcs retain their frozen endpoints. Connector `i` ends at the right label
matched to the opposite incoming branch, so its geometric endpoint is the
opposite incoming cutpoint in both through-permutation cases. -/
def smoothArcTargetGeometryCode (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    SmoothArcCode D → SmoothVertexCode D
  | Sum.inl e => smoothArcTargetCode D c (Sum.inl e)
  | Sum.inr i => smoothRightCutCode D c (D.through c (otherBranch i))

/-- The frozen continuation is corrected at its two connector exits exactly
when `through` is the swap. The output swap acts only on the selected
crossing's outgoing arc labels. -/
noncomputable def smoothContinuationGeometryAdjust (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : Equiv.Perm (SmoothArcCode D) := by
  classical
  exact if D.through c 0 = 0 then Equiv.refl _ else
    Equiv.swap (Sum.inl (D.outgoing c 0)) (Sum.inl (D.outgoing c 1))

noncomputable def smoothContinuationGeometryCode (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : Equiv.Perm (SmoothArcCode D) :=
  smoothContinuationGeometryAdjust D c * smoothContinuationCodeLocal D c

theorem smoothArcSourceGeometryCode_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (i : Fin 2) :
    smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c (Sum.inr i)) =
      incomingCutPoint D c ε i := by
  fin_cases i <;> simp [smoothArcSourceCode, smoothLeftCutCode,
    smoothVertexPointGeometryCode]

theorem smoothArcTargetGeometryCode_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (i : Fin 2) :
    smoothVertexPointGeometryCode D c ε (smoothArcTargetGeometryCode D c (Sum.inr i)) =
      outgoingCutPoint D c ε (otherBranch i) := by
  have hright (j : Fin 2) :
      smoothVertexPointGeometryCode D c ε (smoothRightCutCode D c j) =
        outgoingCutPoint D c ε ((D.through c).symm j) := by
    fin_cases j <;> simp [smoothRightCutCode, smoothVertexPointGeometryCode]
  rw [smoothArcTargetGeometryCode]
  rw [hright]
  simp only [Equiv.symm_apply_apply]

theorem smoothConnectorGeometryCode_eq_local (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε s : ℝ) (i : Fin 2) :
    DirectGLSSW.affinePoint
      (smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c (Sum.inr i)))
      (smoothVertexPointGeometryCode D c ε (smoothArcTargetGeometryCode D c (Sum.inr i))) s =
      (if i = 0 then smoothingConnectorZero D c ε s else smoothingConnectorOne D c ε s) := by
  rw [smoothArcSourceGeometryCode_connector, smoothArcTargetGeometryCode_connector]
  fin_cases i <;> simp [smoothingConnectorZero, smoothingConnectorOne, otherBranch_zero,
    otherBranch_one]

private theorem through_branch_one_of_zero (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h0 : D.through c 0 = 0) : D.through c 1 = 1 := by
  rcases finTwoGeometryCases (D.through c 1) with h | h
  · have hbad := (D.through c).injective (h0.trans h.symm)
    norm_num at hbad
  · exact h

private theorem through_branch_zero_of_one (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h0 : D.through c 0 ≠ 0) : D.through c 0 = 1 := by
  rcases finTwoGeometryCases (D.through c 0) with h | h
  · exact False.elim (h0 h)
  · exact h

private theorem through_branch_zero_of_swap (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h0 : D.through c 0 ≠ 0) : D.through c 1 = 0 := by
  have h01 := through_branch_zero_of_one D c h0
  rcases finTwoGeometryCases (D.through c 1) with h | h
  · exact h
  · have hbad := (D.through c).injective (h01.trans h.symm)
    norm_num at hbad

theorem smoothContinuationGeometryCode_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    smoothContinuationGeometryCode D c (Sum.inr i) =
      Sum.inl (D.outgoing c (D.through c (otherBranch i))) := by
  by_cases h0 : D.through c 0 = 0
  · have h1 := through_branch_one_of_zero D c h0
    fin_cases i <;> simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust,
      h0, smoothContinuationCodeLocal_connector_zero, smoothContinuationCodeLocal_connector_one,
      otherBranch_zero, otherBranch_one, h1]
  · have h00 := through_branch_zero_of_one D c h0
    have h1 := through_branch_zero_of_swap D c h0
    fin_cases i <;> simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust,
      h0, smoothContinuationCodeLocal_connector_zero, smoothContinuationCodeLocal_connector_one,
      otherBranch_zero, otherBranch_one, h00, h1, Equiv.swap_apply_def]

theorem smoothContinuationGeometryCode_incoming_zero (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    smoothContinuationGeometryCode D c (Sum.inl (D.incoming c 0)) = Sum.inr 0 := by
  by_cases h0 : D.through c 0 = 0
  · simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust, h0,
      smoothContinuationCodeLocal_incident_incoming_zero]
  · simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust, h0,
      smoothContinuationCodeLocal_incident_incoming_zero, Equiv.swap_apply_def]

theorem smoothContinuationGeometryCode_incoming_one (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    smoothContinuationGeometryCode D c (Sum.inl (D.incoming c 1)) = Sum.inr 1 := by
  by_cases h0 : D.through c 0 = 0
  · simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust, h0,
      smoothContinuationCodeLocal_incident_incoming_one]
  · simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust, h0,
      smoothContinuationCodeLocal_incident_incoming_one, Equiv.swap_apply_def]

theorem smoothConnectorGeometryCode_incidence (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    smoothArcTargetGeometryCode D c (Sum.inr i) =
      smoothArcSourceCode D c (smoothContinuationGeometryCode D c (Sum.inr i)) := by
  have hout : D.outgoing c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.1
  have hout' : D.outgoing c 1 ≠ D.outgoing c 0 := hout.symm
  by_cases h0 : D.through c 0 = 0
  · have h1 := through_branch_one_of_zero D c h0
    fin_cases i <;> simp [smoothContinuationGeometryCode_connector,
      smoothArcTargetGeometryCode, smoothArcSourceCode, smoothRightCutCode,
      otherBranch_zero, otherBranch_one, h0, h1, hout, hout']
  · have h00 := through_branch_zero_of_one D c h0
    have h1 := through_branch_zero_of_swap D c h0
    fin_cases i <;> simp [smoothContinuationGeometryCode_connector,
      smoothArcTargetGeometryCode, smoothArcSourceCode, smoothRightCutCode,
      otherBranch_zero, otherBranch_one, h0, h00, h1, hout, hout']

private theorem smoothArcTargetCode_old_ne_rightCut (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc) (j : Fin 2)
    (he0 : e ≠ D.incoming c 0) (he1 : e ≠ D.incoming c 1) :
    smoothArcTargetCode D c (Sum.inl e) ≠ smoothRightCutCode D c j := by
  have htarget : D.arcTarget e ≠ D.crossingVertex c := by
    intro ht
    rcases (D.crossing_incidence_complete c e).mp (Or.inr ht) with hi0 | hi1 | ho0 | ho1
    · exact he0 hi0
    · exact he1 hi1
    · subst e
      exact (D.arc_endpoints_distinct (D.outgoing c 0))
        ((D.outgoing_source c 0).trans ht.symm)
    · subst e
      exact (D.arc_endpoints_distinct (D.outgoing c 1))
        ((D.outgoing_source c 1).trans ht.symm)
  fin_cases j <;> simp [smoothArcTargetCode, he0, he1, htarget,
    smoothRightCutCode]

theorem smoothArcTargetGeometryCode_continuationGeometryCode
    (D : PLLinkDiagram) (c : Fin D.nCrossing) (e : SmoothArcCode D) :
    smoothArcTargetGeometryCode D c e =
      smoothArcSourceCode D c (smoothContinuationGeometryCode D c e) := by
  rcases e with e | i
  · by_cases he0 : e = D.incoming c 0
    · subst e
      rw [smoothArcTargetGeometryCode, smoothContinuationGeometryCode_incoming_zero]
      simp [smoothArcTargetCode, smoothArcSourceCode]
    · by_cases he1 : e = D.incoming c 1
      · subst e
        rw [smoothArcTargetGeometryCode, smoothContinuationGeometryCode_incoming_one]
        simp [smoothArcTargetCode, smoothArcSourceCode, (D.four_ports_distinct c).1.symm]
      · have hlocal := smoothArcTargetCode_continuationCodeLocal D c (Sum.inl e)
        have hout : D.outgoing c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.1
        have hout' : D.outgoing c 1 ≠ D.outgoing c 0 := hout.symm
        have hnot0 : smoothContinuationCodeLocal D c (Sum.inl e) ≠
            Sum.inl (D.outgoing c 0) := by
          intro h
          have hcut : smoothArcTargetCode D c (Sum.inl e) = smoothRightCutCode D c 0 := by
            simpa [h, smoothArcSourceCode, smoothRightCutCode, hout] using hlocal
          exact smoothArcTargetCode_old_ne_rightCut D c e 0 he0 he1 hcut
        have hnot1 : smoothContinuationCodeLocal D c (Sum.inl e) ≠
            Sum.inl (D.outgoing c 1) := by
          intro h
          have hcut : smoothArcTargetCode D c (Sum.inl e) = smoothRightCutCode D c 1 := by
            simpa [h, smoothArcSourceCode, smoothRightCutCode, hout'] using hlocal
          exact smoothArcTargetCode_old_ne_rightCut D c e 1 he0 he1 hcut
        have hadjust : smoothContinuationGeometryAdjust D c
            (smoothContinuationCodeLocal D c (Sum.inl e)) =
              smoothContinuationCodeLocal D c (Sum.inl e) := by
          by_cases h0 : D.through c 0 = 0
          · simp [smoothContinuationGeometryAdjust, h0]
          · simp [smoothContinuationGeometryAdjust, h0, Equiv.swap_apply_def,
              hnot0, hnot1]
        change smoothArcTargetCode D c (Sum.inl e) =
          smoothArcSourceCode D c
            (smoothContinuationGeometryAdjust D c
              (smoothContinuationCodeLocal D c (Sum.inl e)))
        rw [hadjust]
        exact hlocal
  · exact smoothConnectorGeometryCode_incidence D c i

/-- The label and geometric endpoint table, with the two possible
permutations made explicit. -/
theorem smoothArcTargetGeometryCode_through_cases (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (j : Fin 2) :
    (D.through c = Equiv.refl (Fin 2) ∧
      smoothVertexPointGeometryCode D c 1
        (smoothRightCutCode D c j) = outgoingCutPoint D c 1 j) ∨
    (D.through c = Equiv.swap 0 1 ∧
      smoothVertexPointGeometryCode D c 1
        (smoothRightCutCode D c j) = outgoingCutPoint D c 1 (otherBranch j)) := by
  have hcases (f : Equiv.Perm (Fin 2)) :
      f = Equiv.refl (Fin 2) ∨ f = Equiv.swap 0 1 := by
    by_cases h0 : f 0 = 0
    · left
      have h1 : f 1 = 1 := by
        rcases finTwoGeometryCases (f 1) with h | h
        · have hbad := f.injective (h0.trans h.symm)
          norm_num at hbad
        · exact h
      ext i
      fin_cases i <;> simp [h0, h1]
    · right
      have h0' : f 0 = 1 := by
        rcases finTwoGeometryCases (f 0) with h | h
        · exact False.elim (h0 h)
        · exact h
      have h1 : f 1 = 0 := by
        rcases finTwoGeometryCases (f 1) with h | h
        · exact h
        · have hbad := f.injective (h0'.trans h.symm)
          norm_num at hbad
      ext i
      fin_cases i <;> simp [h0', h1]
  rcases hcases (D.through c) with h | h
  · left
    constructor
    · exact h
    · fin_cases j <;> simp [smoothRightCutCode, smoothVertexPointGeometryCode, h,
        otherBranch_zero, otherBranch_one]
  · right
    constructor
    · exact h
    · fin_cases j <;> simp [smoothRightCutCode, smoothVertexPointGeometryCode, h,
        otherBranch_zero, otherBranch_one]

end DirectGLSSW.HOMFLY
