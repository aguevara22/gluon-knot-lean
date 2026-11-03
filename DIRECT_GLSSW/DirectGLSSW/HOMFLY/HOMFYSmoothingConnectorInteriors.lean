import DirectGLSSW.HOMFLY.HOMFYSmoothingGeometryCodeV2
import DirectGLSSW.HOMFLY.HOMFYSmoothingArcInteriors

namespace DirectGLSSW.HOMFLY

private theorem finTwoConnectorCases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

private theorem through_one_of_zero (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h0 : D.through c 0 = 0) : D.through c 1 = 1 := by
  rcases finTwoConnectorCases (D.through c 1) with h | h
  · have hbad := (D.through c).injective (h0.trans h.symm)
    norm_num at hbad
  · exact h

private theorem through_zero_of_swap (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h0 : D.through c 0 ≠ 0) : D.through c 0 = 1 := by
  rcases finTwoConnectorCases (D.through c 0) with h | h
  · exact False.elim (h0 h)
  · exact h

private theorem through_one_of_swap (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h0 : D.through c 0 ≠ 0) : D.through c 1 = 0 := by
  have h01 := through_zero_of_swap D c h0
  rcases finTwoConnectorCases (D.through c 1) with h | h
  · exact h
  · have hbad := (D.through c).injective (h01.trans h.symm)
    norm_num at hbad

private theorem outgoingLabel_eq_of_symm_eq (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (j k : Fin 2) (h : (D.through c).symm j = k) : j = D.through c k := by
  calc
    j = D.through c ((D.through c).symm j) := (Equiv.apply_symm_apply (D.through c) j).symm
    _ = D.through c k := congrArg (D.through c) h

private theorem incident_or_nonincidentArc (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : Fin D.nArc) :
    e = D.incoming c 0 ∨ e = D.incoming c 1 ∨ e = D.outgoing c 0 ∨
      e = D.outgoing c 1 ∨ nonincidentArc D c e := by
  by_cases h0 : e = D.incoming c 0
  · exact Or.inl h0
  · by_cases h1 : e = D.incoming c 1
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : e = D.outgoing c 0
      · exact Or.inr (Or.inr (Or.inl h2))
      · by_cases h3 : e = D.outgoing c 1
        · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
        · have hs : D.arcSource e ≠ D.crossingVertex c := by
            intro h
            have hi := (D.crossing_incidence_complete c e).mp (Or.inl h)
            rcases hi with he | he | he | he
            · exact h0 he
            · exact h1 he
            · exact h2 he
            · exact h3 he
          have ht : D.arcTarget e ≠ D.crossingVertex c := by
            intro h
            have hi := (D.crossing_incidence_complete c e).mp (Or.inr h)
            rcases hi with he | he | he | he
            · exact h0 he
            · exact h1 he
            · exact h2 he
            · exact h3 he
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, h1, h2, h3⟩)))

def smoothGeometryConnectorPoint (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (i : Fin 2) (s : ℝ) : PlanarPoint ℝ :=
  DirectGLSSW.affinePoint
    (smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c (Sum.inr i)))
    (smoothVertexPointGeometryCode D c ε (smoothArcTargetGeometryCode D c (Sum.inr i))) s

noncomputable def smoothGeometryTargetCodeAdjust (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : Equiv.Perm (SmoothArcCode D) := by
  classical
  exact if D.through c 0 = 0 then Equiv.refl _ else
    Equiv.sumCongr (Equiv.refl _) (Equiv.swap (0 : Fin 2) 1)

theorem smoothArcTargetGeometryCode_eq_local_after_adjust (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : SmoothArcCode D) :
    smoothArcTargetGeometryCode D c e =
      smoothArcTargetCode D c (smoothGeometryTargetCodeAdjust D c e) := by
  cases e with
  | inl e =>
    by_cases h0 : D.through c 0 = 0 <;>
      simp [smoothGeometryTargetCodeAdjust, h0, smoothArcTargetGeometryCode,
        smoothArcTargetCode, Equiv.swap_apply_def]
  | inr i =>
    by_cases h0 : D.through c 0 = 0
    · have h1 := through_one_of_zero D c h0
      fin_cases i <;> simp [smoothGeometryTargetCodeAdjust, h0, h1,
        smoothArcTargetGeometryCode, smoothArcTargetCode,
        otherBranch_zero, otherBranch_one]
    · have h01 := through_zero_of_swap D c h0
      have h1 := through_one_of_swap D c h0
      fin_cases i <;> simp [smoothGeometryTargetCodeAdjust, h0, h01, h1,
        smoothArcTargetGeometryCode, smoothArcTargetCode,
        otherBranch_zero, otherBranch_one, Equiv.swap_apply_def]

noncomputable def smoothGeometryTargetIndexAdjust (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : Equiv.Perm (Fin (D.nArc + 2)) :=
  (smoothArcEquiv D).symm.trans
    ((smoothGeometryTargetCodeAdjust D c).trans (smoothArcEquiv D))

noncomputable def smoothGeometryArcTargetAux (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nArc + 2) → Fin (D.nVertex + 3) := fun e =>
  smoothVertexEquiv D c
    (smoothArcTargetGeometryCode D c ((smoothArcEquiv D).symm e))

theorem smoothGeometryArcTargetAux_eq_adjusted_old (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin (D.nArc + 2)) :
    smoothGeometryArcTargetAux D c e =
      smoothArcTargetAux D c (smoothGeometryTargetIndexAdjust D c e) := by
  simp [smoothGeometryArcTargetAux, smoothGeometryTargetIndexAdjust,
    smoothArcTargetAux, smoothArcTargetGeometryCode_eq_local_after_adjust,
    Equiv.trans_apply, Equiv.symm_apply_apply]

theorem smoothGeometryIncomingDegreeOne (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : Fin (D.nVertex + 3))
    (hv : ∀ d : Fin (D.nCrossing - 1), smoothCrossingVertexAux D c d ≠ v) :
    (incomingArcs (smoothGeometryArcTargetAux D c) v).card = 1 := by
  classical
  let q := smoothGeometryTargetIndexAdjust D c
  let A := smoothGeometryArcTargetAux D c
  let B := smoothArcTargetAux D c
  have hab (e : Fin (D.nArc + 2)) : A e = B (q e) :=
    smoothGeometryArcTargetAux_eq_adjusted_old D c e
  let eSub : {e : Fin (D.nArc + 2) // A e = v} ≃
      {e : Fin (D.nArc + 2) // B e = v} := {
    toFun := fun x => ⟨q x.val, by rw [← hab x.val]; exact x.property⟩
    invFun := fun x => ⟨q.symm x.val, by
      rw [hab, Equiv.apply_symm_apply]
      exact x.property⟩
    left_inv := by intro x; apply Subtype.ext; simp [q]
    right_inv := by intro x; apply Subtype.ext; simp [q]
  }
  have hcard : Fintype.card {e : Fin (D.nArc + 2) // A e = v} =
      Fintype.card {e : Fin (D.nArc + 2) // B e = v} := Fintype.card_congr eSub
  have hregular := smoothRegularDegreeOne D c v hv
  have htargetCard : (incomingArcs A v).card = (incomingArcs B v).card := by
    rw [← Fintype.card_of_subtype (p := fun e : Fin (D.nArc + 2) => A e = v)
      (incomingArcs A v) (by
      intro e
      simp [incomingArcs])]
    rw [← Fintype.card_of_subtype (p := fun e : Fin (D.nArc + 2) => B e = v)
      (incomingArcs B v) (by
      intro e
      simp [incomingArcs])]
    exact hcard
  rw [htargetCard]
  exact hregular.1

theorem smoothGeometryRegularDegreeOne (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : Fin (D.nVertex + 3))
    (hv : ∀ d : Fin (D.nCrossing - 1), smoothCrossingVertexAux D c d ≠ v) :
    (incomingArcs (smoothGeometryArcTargetAux D c) v).card = 1 ∧
      (outgoingArcs (smoothArcSourceAux D c) v).card = 1 := by
  exact ⟨smoothGeometryIncomingDegreeOne D c v hv,
    (smoothRegularDegreeOne D c v hv).2⟩

theorem smoothGeometryConnectorPoint_eq_local (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε s : ℝ) (i : Fin 2) :
    smoothGeometryConnectorPoint D c ε i s =
      (if i = 0 then smoothingConnectorZero D c ε s else smoothingConnectorOne D c ε s) :=
  smoothConnectorGeometryCode_eq_local D c ε s i

theorem smoothGeometryConnectors_interiors_disjoint (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (i j : Fin 2) (hij : i ≠ j) (s t : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠ smoothGeometryConnectorPoint D c ε j t := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij (by apply Fin.ext; rfl))
  · intro h
    change smoothGeometryConnectorPoint D c ε 0 s =
      smoothGeometryConnectorPoint D c ε 1 t at h
    have h0 : smoothGeometryConnectorPoint D c ε 0 s =
        smoothingConnectorZero D c ε s := by
      change _ = _
      exact smoothConnectorGeometryCode_eq_local D c ε s 0
    have h1 : smoothGeometryConnectorPoint D c ε 1 t =
        smoothingConnectorOne D c ε t := by
      change _ = _
      exact smoothConnectorGeometryCode_eq_local D c ε t 1
    exact crossing_cut_connector_disjoint D c hε (h0.symm.trans (h.trans h1))
  · intro h
    change smoothGeometryConnectorPoint D c ε 1 s =
      smoothGeometryConnectorPoint D c ε 0 t at h
    have h0 : smoothGeometryConnectorPoint D c ε 0 t =
        smoothingConnectorZero D c ε t := by
      change _ = _
      exact smoothConnectorGeometryCode_eq_local D c ε t 0
    have h1 : smoothGeometryConnectorPoint D c ε 1 s =
        smoothingConnectorOne D c ε s := by
      change _ = _
      exact smoothConnectorGeometryCode_eq_local D c ε s 1
    exact crossing_cut_connector_disjoint D c hε (h0.symm.trans (h.symm.trans h1))
  · exact False.elim (hij (by apply Fin.ext; rfl))

theorem smoothGeometryConnector_oldArc_disjoint_nonincident
    (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε ρ : ℝ)
    (hε : 0 < ε) (hερ : ε < ρ) (hεcut : ε < crossingCutoffRadius D c)
    (hclear : ∀ ε', 0 < ε' → ε' < ρ → ∀ s, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ e, nonincidentArc D c e →
        smoothingConnectorZero D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) ∧
        smoothingConnectorOne D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)))
    (i : Fin 2) (e : Fin D.nArc) (he : nonincidentArc D c e)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠ smoothCodeArcPoint D c ε (Sum.inl e) t := by
  intro h
  obtain ⟨u, hu0, hu1, hu⟩ :=
    smoothOldArcInterior_lies_oldInterior D c ε e t hε hεcut ht0 ht1
  have hseg : smoothGeometryConnectorPoint D c ε i s ∈
      closedSegmentTrace (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) := by
    refine ⟨u, ⟨le_of_lt hu0, le_of_lt hu1⟩, ?_⟩
    have hloc : smoothGeometryConnectorPoint D c ε i s =
        (if i = 0 then smoothingConnectorZero D c ε s else smoothingConnectorOne D c ε s) :=
      smoothGeometryConnectorPoint_eq_local D c ε s i
    exact hu.symm.trans h.symm
  have hnot := hclear ε hε hερ s ⟨le_of_lt hs0, le_of_lt hs1⟩ e he
  by_cases hi : i = 0
  · subst i
    have hloc : smoothGeometryConnectorPoint D c ε 0 s = smoothingConnectorZero D c ε s :=
      smoothConnectorGeometryCode_eq_local D c ε s 0
    have hseg0 : smoothingConnectorZero D c ε s ∈
        closedSegmentTrace (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) :=
      Set.mem_of_eq_of_mem hloc.symm hseg
    exact hnot.1 hseg0
  · have hi1 : i = 1 := by
      rcases finTwoConnectorCases i with h0 | h1
      · exact False.elim (hi h0)
      · exact h1
    subst i
    have hloc : smoothGeometryConnectorPoint D c ε 1 s = smoothingConnectorOne D c ε s :=
      smoothConnectorGeometryCode_eq_local D c ε s 1
    have hseg1 : smoothingConnectorOne D c ε s ∈
        closedSegmentTrace (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) :=
      Set.mem_of_eq_of_mem hloc.symm hseg
    exact hnot.2 hseg1

theorem smoothGeometryIncomingOldArcPoint (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (i : Fin 2) (s : ℝ) :
    smoothCodeArcPoint D c ε (Sum.inl (D.incoming c i)) s =
      DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c i)))
        (incomingCutPoint D c ε i) s := by
  fin_cases i
  · have hs : D.arcSource (D.incoming c 0) ≠ D.crossingVertex c := by
      intro h
      exact (D.arc_endpoints_distinct (D.incoming c 0)) (h.trans (D.incoming_target c 0).symm)
    simp [smoothCodeArcPoint, smoothArcSourceCode, smoothArcTargetCode,
      smoothLeftCutCode, smoothVertexPointGeometryCode, hs,
      (D.four_ports_distinct c).2.2 0 0, (D.four_ports_distinct c).2.2 0 1]
  · have hs : D.arcSource (D.incoming c 1) ≠ D.crossingVertex c := by
      intro h
      exact (D.arc_endpoints_distinct (D.incoming c 1)) (h.trans (D.incoming_target c 1).symm)
    have h01 : D.incoming c 1 ≠ D.incoming c 0 := (D.four_ports_distinct c).1.symm
    simp [smoothCodeArcPoint, smoothArcSourceCode, smoothArcTargetCode,
      smoothLeftCutCode, smoothVertexPointGeometryCode, hs, h01,
      (D.four_ports_distinct c).2.2 1 0, (D.four_ports_distinct c).2.2 1 1]

theorem smoothGeometryOutgoingOldArcPoint (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (j : Fin 2) (s : ℝ) :
    smoothCodeArcPoint D c ε (Sum.inl (D.outgoing c j)) s =
      DirectGLSSW.affinePoint (outgoingCutPoint D c ε ((D.through c).symm j))
        (D.vertexPoint (D.arcTarget (D.outgoing c j))) s := by
  fin_cases j
  · have ht : D.arcTarget (D.outgoing c 0) ≠ D.crossingVertex c := by
      intro h
      exact (D.arc_endpoints_distinct (D.outgoing c 0)) ((D.outgoing_source c 0).trans h.symm)
    simp [smoothCodeArcPoint, smoothArcSourceCode, smoothArcTargetCode,
      smoothRightCutCode, smoothVertexPointGeometryCode, ht,
      ((D.four_ports_distinct c).2.2 0 0).symm,
      ((D.four_ports_distinct c).2.2 1 0).symm]
  · have ht : D.arcTarget (D.outgoing c 1) ≠ D.crossingVertex c := by
      intro h
      exact (D.arc_endpoints_distinct (D.outgoing c 1)) ((D.outgoing_source c 1).trans h.symm)
    have hout : D.outgoing c 1 ≠ D.outgoing c 0 := (D.four_ports_distinct c).2.1.symm
    simp [smoothCodeArcPoint, smoothArcSourceCode, smoothArcTargetCode,
      smoothRightCutCode, smoothVertexPointGeometryCode, ht, hout,
      ((D.four_ports_distinct c).2.2 0 1).symm,
      ((D.four_ports_distinct c).2.2 1 1).symm]

theorem smoothGeometryConnector_incomingOldArc_disjoint (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (i j : Fin 2)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠
      smoothCodeArcPoint D c ε (Sum.inl (D.incoming c j)) t := by
  fin_cases i <;> fin_cases j
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s =
        smoothingConnectorZero D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 0
    have hold := smoothGeometryIncomingOldArcPoint D c ε 0 t
    have heq : smoothingConnectorZero D c ε s =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
          (incomingCutPoint D c ε 0) t := hconn.symm.trans (h.trans hold)
    obtain ⟨hs, ht⟩ := connectorZero_meets_incomingZero_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq
    exact (ne_of_gt hs0) hs
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s =
        smoothingConnectorZero D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 0
    have hold := smoothGeometryIncomingOldArcPoint D c ε 1 t
    have heq : smoothingConnectorZero D c ε s =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
          (incomingCutPoint D c ε 1) t := hconn.symm.trans (h.trans hold)
    exact connectorZero_avoids_incomingOne D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s =
        smoothingConnectorOne D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 1
    have hold := smoothGeometryIncomingOldArcPoint D c ε 0 t
    have heq : smoothingConnectorOne D c ε s =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
          (incomingCutPoint D c ε 0) t := hconn.symm.trans (h.trans hold)
    exact connectorOne_avoids_incomingZero D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s =
        smoothingConnectorOne D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 1
    have hold := smoothGeometryIncomingOldArcPoint D c ε 1 t
    have heq : smoothingConnectorOne D c ε s =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
          (incomingCutPoint D c ε 1) t := hconn.symm.trans (h.trans hold)
    obtain ⟨hs, ht⟩ := connectorOne_meets_incomingOne_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq
    exact (ne_of_gt hs0) hs

theorem smoothGeometryConnector_outgoingOldArc_disjoint (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (i j : Fin 2)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠
      smoothCodeArcPoint D c ε (Sum.inl (D.outgoing c j)) t := by
  by_cases hi : i = 0
  · subst i
    by_cases hk : (D.through c).symm j = 1
    · have hj : j = D.through c 1 := outgoingLabel_eq_of_symm_eq D c j 1 hk
      subst j
      intro h
      have hconn : smoothGeometryConnectorPoint D c ε 0 s =
          smoothingConnectorZero D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 0
      have hold := smoothGeometryOutgoingOldArcPoint D c ε (D.through c 1) t
      have hold' : smoothCodeArcPoint D c ε
          (Sum.inl (D.outgoing c (D.through c 1))) t =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 1)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) t := by
        simpa using hold
      have heq : smoothingConnectorZero D c ε s =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 1)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) t :=
        hconn.symm.trans (h.trans hold')
      obtain ⟨hs, ht⟩ := connectorZero_meets_outgoingOne_only_endpoint D c
        hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq
      exact (ne_of_gt ht0) ht
    · have hk0 : (D.through c).symm j = 0 := by
        rcases finTwoConnectorCases ((D.through c).symm j) with h0 | h1
        · exact h0
        · exact False.elim (hk h1)
      have hj : j = D.through c 0 := outgoingLabel_eq_of_symm_eq D c j 0 hk0
      subst j
      intro h
      have hconn : smoothGeometryConnectorPoint D c ε 0 s =
          smoothingConnectorZero D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 0
      have hold := smoothGeometryOutgoingOldArcPoint D c ε (D.through c 0) t
      have hold' : smoothCodeArcPoint D c ε
          (Sum.inl (D.outgoing c (D.through c 0))) t =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 0)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) t := by
        simpa using hold
      have heq : smoothingConnectorZero D c ε s =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 0)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) t :=
        hconn.symm.trans (h.trans hold')
      exact connectorZero_avoids_outgoingZero D c hε hεcut
        ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq
  · have hi1 : i = 1 := by
      rcases finTwoConnectorCases i with h0 | h1
      · exact False.elim (hi h0)
      · exact h1
    subst i
    by_cases hk : (D.through c).symm j = 0
    · have hj : j = D.through c 0 := outgoingLabel_eq_of_symm_eq D c j 0 hk
      subst j
      intro h
      have hconn : smoothGeometryConnectorPoint D c ε 1 s =
          smoothingConnectorOne D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 1
      have hold := smoothGeometryOutgoingOldArcPoint D c ε (D.through c 0) t
      have hold' : smoothCodeArcPoint D c ε
          (Sum.inl (D.outgoing c (D.through c 0))) t =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 0)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) t := by
        simpa using hold
      have heq : smoothingConnectorOne D c ε s =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 0)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) t :=
        hconn.symm.trans (h.trans hold')
      obtain ⟨hs, ht⟩ := connectorOne_meets_outgoingZero_only_endpoint D c
        hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq
      exact (ne_of_gt ht0) ht
    · have hk1 : (D.through c).symm j = 1 := by
        rcases finTwoConnectorCases ((D.through c).symm j) with h0 | h1
        · exact False.elim (hk h0)
        · exact h1
      have hj : j = D.through c 1 := outgoingLabel_eq_of_symm_eq D c j 1 hk1
      subst j
      intro h
      have hconn : smoothGeometryConnectorPoint D c ε 1 s =
          smoothingConnectorOne D c ε s := smoothConnectorGeometryCode_eq_local D c ε s 1
      have hold := smoothGeometryOutgoingOldArcPoint D c ε (D.through c 1) t
      have hold' : smoothCodeArcPoint D c ε
          (Sum.inl (D.outgoing c (D.through c 1))) t =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 1)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) t := by
        simpa using hold
      have heq : smoothingConnectorOne D c ε s =
          DirectGLSSW.affinePoint (outgoingCutPoint D c ε 1)
            (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) t :=
        hconn.symm.trans (h.trans hold')
      exact connectorOne_avoids_outgoingOne D c hε hεcut
        ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨le_of_lt ht0, le_of_lt ht1⟩ heq

theorem smoothGeometryConnector_oldArc_disjoint (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε ρ : ℝ) (hε : 0 < ε) (hερ : ε < ρ)
    (hεcut : ε < crossingCutoffRadius D c)
    (hclear : ∀ ε', 0 < ε' → ε' < ρ → ∀ s, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ e, nonincidentArc D c e →
        smoothingConnectorZero D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) ∧
        smoothingConnectorOne D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)))
    (i : Fin 2) (e : Fin D.nArc)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠ smoothCodeArcPoint D c ε (Sum.inl e) t := by
  rcases incident_or_nonincidentArc D c e with he0 | he1 | ho0 | ho1 | hnon
  · subst e
    exact smoothGeometryConnector_incomingOldArc_disjoint D c ε hε hεcut i 0 s t hs0 hs1 ht0 ht1
  · subst e
    exact smoothGeometryConnector_incomingOldArc_disjoint D c ε hε hεcut i 1 s t hs0 hs1 ht0 ht1
  · subst e
    exact smoothGeometryConnector_outgoingOldArc_disjoint D c ε hε hεcut i 0 s t hs0 hs1 ht0 ht1
  · subst e
    exact smoothGeometryConnector_outgoingOldArc_disjoint D c ε hε hεcut i 1 s t hs0 hs1 ht0 ht1
  · exact smoothGeometryConnector_oldArc_disjoint_nonincident D c ε ρ hε hερ hεcut
      hclear i e hnon s t hs0 hs1 ht0 ht1

def smoothGeometryCodeArcPoint (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (e : SmoothArcCode D) (s : ℝ) : PlanarPoint ℝ :=
  DirectGLSSW.affinePoint
    (smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c e))
    (smoothVertexPointGeometryCode D c ε (smoothArcTargetGeometryCode D c e)) s

theorem smoothGeometryCodeArcPoint_old (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (e : Fin D.nArc) (s : ℝ) :
    smoothGeometryCodeArcPoint D c ε (Sum.inl e) s = smoothCodeArcPoint D c ε (Sum.inl e) s := rfl

theorem smoothGeometryCodeArcPoint_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (i : Fin 2) (s : ℝ) :
    smoothGeometryCodeArcPoint D c ε (Sum.inr i) s = smoothGeometryConnectorPoint D c ε i s := rfl

theorem smoothGeometryCodeArc_interiors_disjoint (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε ρ : ℝ) (hε : 0 < ε) (hερ : ε < ρ)
    (hεcut : ε < crossingCutoffRadius D c)
    (hclear : ∀ ε', 0 < ε' → ε' < ρ → ∀ s, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ e, nonincidentArc D c e →
        smoothingConnectorZero D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) ∧
        smoothingConnectorOne D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)))
    (e f : SmoothArcCode D) (hef : e ≠ f) (s t : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothGeometryCodeArcPoint D c ε e s ≠ smoothGeometryCodeArcPoint D c ε f t := by
  cases e with
  | inl e₀ =>
    cases f with
    | inl f₀ =>
      exact smoothOldArcCode_interiors_disjoint D c ε hε hεcut e₀ f₀ (by
        intro h
        exact hef (congrArg Sum.inl h)) s t hs0 hs1 ht0 ht1
    | inr j =>
      intro h
      exact smoothGeometryConnector_oldArc_disjoint D c ε ρ hε hερ hεcut hclear j e₀
        t s ht0 ht1 hs0 hs1 h.symm
  | inr i =>
    cases f with
    | inl f₀ =>
      intro h
      exact smoothGeometryConnector_oldArc_disjoint D c ε ρ hε hερ hεcut hclear i f₀
        s t hs0 hs1 ht0 ht1 h
    | inr j =>
      exact smoothGeometryConnectors_interiors_disjoint D c ε hε i j (by
        intro h
        exact hef (congrArg Sum.inr h)) s t hs0 hs1 ht0 ht1

theorem smoothGeometryArcCode_source_target_ne (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : SmoothArcCode D) :
    smoothArcSourceCode D c e ≠ smoothArcTargetGeometryCode D c e := by
  cases e with
  | inl e =>
    simpa [smoothArcTargetGeometryCode] using smoothArcCode_source_target_ne D c (Sum.inl e)
  | inr i =>
    fin_cases i
    · rcases finTwoConnectorCases (D.through c 1) with h | h <;>
        simp [smoothArcSourceCode, smoothArcTargetGeometryCode,
          smoothLeftCutCode, smoothRightCutCode, h]
    · rcases finTwoConnectorCases (D.through c 0) with h | h <;>
        simp [smoothArcSourceCode, smoothArcTargetGeometryCode,
          smoothLeftCutCode, smoothRightCutCode, h]

theorem smoothContinuationGeometryCode_other_incoming_transition (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (d : SmoothCrossingCode D c) (i : Fin 2) :
    smoothContinuationGeometryCode D c (Sum.inl (D.incoming d.val i)) =
      Sum.inl (D.outgoing d.val (D.through d.val i)) := by
  have hbase : smoothContinuationCodeLocal D c (Sum.inl (D.incoming d.val i)) =
      Sum.inl (D.outgoing d.val (D.through d.val i)) := by
    rw [smoothContinuationCodeLocal_other_incoming, D.continuation_crossing]
  have hnot0 : smoothContinuationCodeLocal D c (Sum.inl (D.incoming d.val i)) ≠
      Sum.inl (D.outgoing c 0) := by
    intro h
    have hout : D.outgoing d.val (D.through d.val i) = D.outgoing c 0 :=
      Sum.inl.inj (hbase.symm.trans h)
    have hc : d.val = c := by
      apply D.crossingVertex_injective
      calc
        D.crossingVertex d.val = D.arcTarget (D.incoming d.val i) :=
          (D.incoming_target d.val i).symm
        _ = D.arcSource (D.outgoing d.val (D.through d.val i)) :=
          (D.incoming_target d.val i).trans
            (D.outgoing_source d.val (D.through d.val i)).symm
        _ = D.arcSource (D.outgoing c 0) := congrArg D.arcSource hout
        _ = D.crossingVertex c := D.outgoing_source c 0
    exact d.property hc
  have hnot1 : smoothContinuationCodeLocal D c (Sum.inl (D.incoming d.val i)) ≠
      Sum.inl (D.outgoing c 1) := by
    intro h
    have hout : D.outgoing d.val (D.through d.val i) = D.outgoing c 1 :=
      Sum.inl.inj (hbase.symm.trans h)
    have hc : d.val = c := by
      apply D.crossingVertex_injective
      calc
        D.crossingVertex d.val = D.arcTarget (D.incoming d.val i) :=
          (D.incoming_target d.val i).symm
        _ = D.arcSource (D.outgoing d.val (D.through d.val i)) :=
          (D.incoming_target d.val i).trans
            (D.outgoing_source d.val (D.through d.val i)).symm
        _ = D.arcSource (D.outgoing c 1) := congrArg D.arcSource hout
        _ = D.crossingVertex c := D.outgoing_source c 1
    exact d.property hc
  have hout0 : D.outgoing d.val (D.through d.val i) ≠ D.outgoing c 0 := by
    intro h
    apply hnot0
    exact hbase.trans (congrArg Sum.inl h)
  have hout1 : D.outgoing d.val (D.through d.val i) ≠ D.outgoing c 1 := by
    intro h
    apply hnot1
    exact hbase.trans (congrArg Sum.inl h)
  by_cases h0 : D.through c 0 = 0
  · simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust, h0, hbase]
  · simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust, h0,
      Equiv.swap_apply_def, hnot0, hnot1, hout0, hout1, hbase]

end DirectGLSSW.HOMFLY
