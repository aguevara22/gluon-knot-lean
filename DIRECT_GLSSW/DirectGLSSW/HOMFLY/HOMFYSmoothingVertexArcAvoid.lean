import DirectGLSSW.HOMFLY.HOMFYSmoothingConnectorInteriors

namespace DirectGLSSW.HOMFLY

private theorem affineTarget_not_interior (a b : PlanarPoint ℝ) (hab : a ≠ b)
    (t : ℝ) (ht : t < 1) : b ≠ DirectGLSSW.affinePoint a b t := by
  intro h
  have hinj := DirectGLSSW.affinePoint_injective a b hab
  have heq : DirectGLSSW.affinePoint a b 1 = DirectGLSSW.affinePoint a b t := by
    rw [DirectGLSSW.affinePoint_one]
    exact h
  have hparam := hinj heq
  linarith

private theorem affineSource_not_interior (a b : PlanarPoint ℝ) (hab : a ≠ b)
    (t : ℝ) (ht : 0 < t) : a ≠ DirectGLSSW.affinePoint a b t := by
  intro h
  have hinj := DirectGLSSW.affinePoint_injective a b hab
  have heq : DirectGLSSW.affinePoint a b 0 = DirectGLSSW.affinePoint a b t := by
    rw [DirectGLSSW.affinePoint_zero]
    exact h
  have hparam := hinj heq
  linarith

theorem smoothGeometryConnector_incomingCutpoint_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (i j : Fin 2) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠ incomingCutPoint D c ε j := by
  fin_cases i <;> fin_cases j
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s = smoothingConnectorZero D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : incomingCutPoint D c ε 0 =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
          (incomingCutPoint D c ε 0) 1 := by rw [DirectGLSSW.affinePoint_one]
    have heq := hconn.symm.trans (h.trans hcut)
    obtain ⟨hs, _⟩ := connectorZero_meets_incomingZero_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
    exact (ne_of_gt hs0) hs
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s = smoothingConnectorZero D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : incomingCutPoint D c ε 1 =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
          (incomingCutPoint D c ε 1) 1 := by rw [DirectGLSSW.affinePoint_one]
    have heq := hconn.symm.trans (h.trans hcut)
    exact connectorZero_avoids_incomingOne D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s = smoothingConnectorOne D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : incomingCutPoint D c ε 0 =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
          (incomingCutPoint D c ε 0) 1 := by rw [DirectGLSSW.affinePoint_one]
    have heq := hconn.symm.trans (h.trans hcut)
    exact connectorOne_avoids_incomingZero D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s = smoothingConnectorOne D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : incomingCutPoint D c ε 1 =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
          (incomingCutPoint D c ε 1) 1 := by rw [DirectGLSSW.affinePoint_one]
    have heq := hconn.symm.trans (h.trans hcut)
    obtain ⟨hs, _⟩ := connectorOne_meets_incomingOne_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
    exact (ne_of_gt hs0) hs

theorem smoothGeometryConnector_outgoingCutpoint_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (i j : Fin 2) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠ outgoingCutPoint D c ε j := by
  fin_cases i <;> fin_cases j
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s = smoothingConnectorZero D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : outgoingCutPoint D c ε 0 =
        DirectGLSSW.affinePoint (outgoingCutPoint D c ε 0)
          (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) 0 := by
      rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hcut)
    exact connectorZero_avoids_outgoingZero D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s = smoothingConnectorZero D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : outgoingCutPoint D c ε 1 =
        DirectGLSSW.affinePoint (outgoingCutPoint D c ε 1)
          (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) 0 := by
      rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hcut)
    obtain ⟨hs, _⟩ := connectorZero_meets_outgoingOne_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
    exact (ne_of_lt hs1) hs
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s = smoothingConnectorOne D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : outgoingCutPoint D c ε 0 =
        DirectGLSSW.affinePoint (outgoingCutPoint D c ε 0)
          (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 0)))) 0 := by
      rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hcut)
    obtain ⟨hs, _⟩ := connectorOne_meets_outgoingZero_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
    exact (ne_of_lt hs1) hs
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s = smoothingConnectorOne D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hcut : outgoingCutPoint D c ε 1 =
        DirectGLSSW.affinePoint (outgoingCutPoint D c ε 1)
          (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c 1)))) 0 := by
      rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hcut)
    exact connectorOne_avoids_outgoingOne D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq

theorem smoothGeometryConnector_incomingSource_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (i j : Fin 2) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    smoothGeometryConnectorPoint D c ε i s ≠
      D.vertexPoint (D.arcSource (D.incoming c j)) := by
  fin_cases i <;> fin_cases j
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s = smoothingConnectorZero D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hsource : D.vertexPoint (D.arcSource (D.incoming c 0)) =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
          (incomingCutPoint D c ε 0) 0 := by rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hsource)
    obtain ⟨_, ht⟩ := connectorZero_meets_incomingZero_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
    exact (by norm_num : (0 : ℝ) ≠ 1) ht

  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 0 s = smoothingConnectorZero D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hsource : D.vertexPoint (D.arcSource (D.incoming c 1)) =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
          (incomingCutPoint D c ε 1) 0 := by rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hsource)
    exact connectorZero_avoids_incomingOne D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s = smoothingConnectorOne D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hsource : D.vertexPoint (D.arcSource (D.incoming c 0)) =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
          (incomingCutPoint D c ε 0) 0 := by rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hsource)
    exact connectorOne_avoids_incomingZero D c hε hεcut
      ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
  · intro h
    have hconn : smoothGeometryConnectorPoint D c ε 1 s = smoothingConnectorOne D c ε s := by
      simpa [smoothGeometryConnectorPoint_eq_local]
    have hsource : D.vertexPoint (D.arcSource (D.incoming c 1)) =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
          (incomingCutPoint D c ε 1) 0 := by rw [DirectGLSSW.affinePoint_zero]
    have heq := hconn.symm.trans (h.trans hsource)
    obtain ⟨_, ht⟩ := connectorOne_meets_incomingOne_only_endpoint D c
      hε hεcut ⟨le_of_lt hs0, le_of_lt hs1⟩ ⟨by norm_num, by norm_num⟩ heq
    exact (by norm_num : (0 : ℝ) ≠ 1) ht

theorem smoothOldVertex_connector_interior_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε ρ : ℝ) (hε : 0 < ε) (hερ : ε < ρ)
    (hεcut : ε < crossingCutoffRadius D c)
    (hclear : ∀ ε', 0 < ε' → ε' < ρ → ∀ s, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ e, nonincidentArc D c e →
        smoothingConnectorZero D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) ∧
        smoothingConnectorOne D c ε' s ∉ closedSegmentTrace
          (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)))
    (v : Fin D.nVertex) (hv : v ≠ D.crossingVertex c) (i : Fin 2)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    smoothVertexPointGeometryCode D c ε (Sum.inl v) ≠
      smoothGeometryConnectorPoint D c ε i s := by
  have hpoint : smoothVertexPointGeometryCode D c ε (Sum.inl v) = D.vertexPoint v := by
    simp [smoothVertexPointGeometryCode, hv]
  have hexists : ∃ e : Fin D.nArc, D.arcSource e = v := by
    by_cases hc : ∃ d, D.crossingVertex d = v
    · obtain ⟨d, hd⟩ := hc
      exact ⟨D.outgoing d 0, by simp [D.outgoing_source, hd]⟩
    · have hvn : ∀ d, D.crossingVertex d ≠ v := by
        intro d hd
        exact hc ⟨d, hd⟩
      have hcard := (D.regular_degree_one v hvn).2
      have hpos : 0 < (outgoingArcs D.arcSource v).card := by
        rw [hcard]
        norm_num
      obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
      exact ⟨e, by simpa [outgoingArcs] using he⟩
  obtain ⟨e, hesrc⟩ := hexists
  intro h
  have hgeomv : smoothGeometryConnectorPoint D c ε i s = D.vertexPoint v :=
    h.symm.trans hpoint
  have hno0 : e ≠ D.outgoing c 0 := by
    intro he
    have hsource := congrArg D.arcSource he
    rw [D.outgoing_source] at hsource
    exact hv (hesrc.symm.trans hsource)
  have hno1 : e ≠ D.outgoing c 1 := by
    intro he
    have hsource := congrArg D.arcSource he
    rw [D.outgoing_source] at hsource
    exact hv (hesrc.symm.trans hsource)
  by_cases hi0 : e = D.incoming c 0
  · have hvsrc : D.vertexPoint v = D.vertexPoint (D.arcSource (D.incoming c 0)) := by
      rw [← hesrc, hi0]
    exact (smoothGeometryConnector_incomingSource_avoid D c ε hε hεcut i 0 s hs0 hs1)
      (by rw [hgeomv, hvsrc])
  · by_cases hi1 : e = D.incoming c 1
    · have hvsrc : D.vertexPoint v = D.vertexPoint (D.arcSource (D.incoming c 1)) := by
        rw [← hesrc, hi1]
      exact (smoothGeometryConnector_incomingSource_avoid D c ε hε hεcut i 1 s hs0 hs1)
        (by rw [hgeomv, hvsrc])
    · by_cases ho0 : e = D.outgoing c 0
      · have hbad : v = D.crossingVertex c := by
          calc
            v = D.arcSource e := hesrc.symm
            _ = D.crossingVertex c := by rw [ho0, D.outgoing_source]
        exact (hv hbad).elim
      · by_cases ho1 : e = D.outgoing c 1
        · have hbad : v = D.crossingVertex c := by
            calc
              v = D.arcSource e := hesrc.symm
              _ = D.crossingVertex c := by rw [ho1, D.outgoing_source]
          exact (hv hbad).elim
        · have hnon : nonincidentArc D c e := ⟨hi0, hi1, hno0, hno1⟩
          have hnot := hclear ε hε hερ s ⟨le_of_lt hs0, le_of_lt hs1⟩ e hnon
          by_cases hi : i = 0
          · subst i
            have hloc : smoothGeometryConnectorPoint D c ε 0 s =
                smoothingConnectorZero D c ε s := smoothGeometryConnectorPoint_eq_local D c ε s 0
            have hseg : smoothingConnectorZero D c ε s ∈ closedSegmentTrace
                (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) := by
              refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
              calc
                DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
                    (D.vertexPoint (D.arcTarget e)) 0 = D.vertexPoint (D.arcSource e) :=
                  DirectGLSSW.affinePoint_zero _ _
                _ = D.vertexPoint v := congrArg D.vertexPoint hesrc
                _ = smoothGeometryConnectorPoint D c ε 0 s := hgeomv.symm
                _ = smoothingConnectorZero D c ε s := hloc
            exact hnot.1 hseg
          · have hi1' : i = 1 := by
              fin_cases i <;> simp_all
            subst i
            have hloc : smoothGeometryConnectorPoint D c ε 1 s =
                smoothingConnectorOne D c ε s := smoothGeometryConnectorPoint_eq_local D c ε s 1
            have hseg : smoothingConnectorOne D c ε s ∈ closedSegmentTrace
                (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) := by
              refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
              calc
                DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
                    (D.vertexPoint (D.arcTarget e)) 0 = D.vertexPoint (D.arcSource e) :=
                  DirectGLSSW.affinePoint_zero _ _
                _ = D.vertexPoint v := congrArg D.vertexPoint hesrc
                _ = smoothGeometryConnectorPoint D c ε 1 s := hgeomv.symm
                _ = smoothingConnectorOne D c ε s := hloc
            exact hnot.2 hseg
theorem smoothCutLabel_connector_interior_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (k : Fin 4) (i : Fin 2)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c k) ≠
      smoothGeometryConnectorPoint D c ε i s := by
  fin_cases k
  · have hlabel : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 0) =
        incomingCutPoint D c ε 0 := by simp [smoothCutLabelCode, smoothVertexPointGeometryCode]
    intro h
    apply smoothGeometryConnector_incomingCutpoint_avoid D c ε hε hεcut i 0 s hs0 hs1
    calc
      smoothGeometryConnectorPoint D c ε i s =
          smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 0) := h.symm
      _ = incomingCutPoint D c ε 0 := hlabel
  · have hlabel : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 1) =
        incomingCutPoint D c ε 1 := by simp [smoothCutLabelCode, smoothVertexPointGeometryCode]
    intro h
    apply smoothGeometryConnector_incomingCutpoint_avoid D c ε hε hεcut i 1 s hs0 hs1
    calc
      smoothGeometryConnectorPoint D c ε i s =
          smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 1) := h.symm
      _ = incomingCutPoint D c ε 1 := hlabel
  · have hlabel : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 2) =
        outgoingCutPoint D c ε ((D.through c).symm 0) := by
      simp [smoothCutLabelCode, smoothVertexPointGeometryCode]
    intro h
    apply smoothGeometryConnector_outgoingCutpoint_avoid D c ε hε hεcut i
      ((D.through c).symm 0) s hs0 hs1
    calc
      smoothGeometryConnectorPoint D c ε i s =
          smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 2) := h.symm
      _ = outgoingCutPoint D c ε ((D.through c).symm 0) := hlabel
  · have hlabel : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 3) =
        outgoingCutPoint D c ε ((D.through c).symm 1) := by
      simp [smoothCutLabelCode, smoothVertexPointGeometryCode]
    intro h
    apply smoothGeometryConnector_outgoingCutpoint_avoid D c ε hε hεcut i
      ((D.through c).symm 1) s hs0 hs1
    calc
      smoothGeometryConnectorPoint D c ε i s =
          smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 3) := h.symm
      _ = outgoingCutPoint D c ε ((D.through c).symm 1) := hlabel

theorem smoothCutLabel_matchingOldArc_interior_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (k : Fin 4) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c k) ≠
      smoothGeometryCodeArcPoint D c ε (Sum.inl (smoothCutLabelArc D c k)) t := by
  fin_cases k
  · obtain ⟨u, hu0, hu1, hu⟩ := smoothCutLabel_interior D c ε hε hεcut 0
    have hcut : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 0) =
        incomingCutPoint D c ε 0 := by
      simp [smoothCutLabelCode, smoothVertexPointGeometryCode]
    have hsource : D.vertexPoint (D.arcSource (D.incoming c 0)) ≠ incomingCutPoint D c ε 0 := by
      intro h
      apply D.vertices_avoid_arc_interiors (D.arcSource (D.incoming c 0))
        (D.incoming c 0) u hu0 hu1
      calc
        D.vertexPoint (D.arcSource (D.incoming c 0)) = incomingCutPoint D c ε 0 := h
        _ = smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 0) := hcut.symm
        _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
            (D.vertexPoint (D.arcTarget (D.incoming c 0))) u := hu
    intro h
    have hpoint : incomingCutPoint D c ε 0 =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
          (incomingCutPoint D c ε 0) t := by
      calc
        incomingCutPoint D c ε 0 =
            smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 0) := hcut.symm
        _ = smoothGeometryCodeArcPoint D c ε (Sum.inl (D.incoming c 0)) t := h
        _ = smoothCodeArcPoint D c ε (Sum.inl (D.incoming c 0)) t :=
          smoothGeometryCodeArcPoint_old D c ε (D.incoming c 0) t
        _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 0)))
            (incomingCutPoint D c ε 0) t := smoothGeometryIncomingOldArcPoint D c ε 0 t
    exact affineTarget_not_interior _ _ hsource t ht1 hpoint
  · obtain ⟨u, hu0, hu1, hu⟩ := smoothCutLabel_interior D c ε hε hεcut 1
    have hcut : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 1) =
        incomingCutPoint D c ε 1 := by
      simp [smoothCutLabelCode, smoothVertexPointGeometryCode]
    have hsource : D.vertexPoint (D.arcSource (D.incoming c 1)) ≠ incomingCutPoint D c ε 1 := by
      intro h
      apply D.vertices_avoid_arc_interiors (D.arcSource (D.incoming c 1))
        (D.incoming c 1) u hu0 hu1
      calc
        D.vertexPoint (D.arcSource (D.incoming c 1)) = incomingCutPoint D c ε 1 := h
        _ = smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 1) := hcut.symm
        _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
            (D.vertexPoint (D.arcTarget (D.incoming c 1))) u := hu
    intro h
    have hpoint : incomingCutPoint D c ε 1 =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
          (incomingCutPoint D c ε 1) t := by
      calc
        incomingCutPoint D c ε 1 =
            smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 1) := hcut.symm
        _ = smoothGeometryCodeArcPoint D c ε (Sum.inl (D.incoming c 1)) t := h
        _ = smoothCodeArcPoint D c ε (Sum.inl (D.incoming c 1)) t :=
          smoothGeometryCodeArcPoint_old D c ε (D.incoming c 1) t
        _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c 1)))
            (incomingCutPoint D c ε 1) t := smoothGeometryIncomingOldArcPoint D c ε 1 t
    exact affineTarget_not_interior _ _ hsource t ht1 hpoint
  · obtain ⟨u, hu0, hu1, hu⟩ := smoothCutLabel_interior D c ε hε hεcut 2
    let i := (D.through c).symm 0
    have hi : D.through c i = 0 := Equiv.apply_symm_apply (D.through c) 0
    have hcut : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 2) =
        outgoingCutPoint D c ε i := by
      simpa [smoothCutLabelCode, smoothVertexPointGeometryCode, i]
    have htarget : outgoingCutPoint D c ε i ≠
        D.vertexPoint (D.arcTarget (D.outgoing c 0)) := by
      intro h
      apply D.vertices_avoid_arc_interiors (D.arcTarget (D.outgoing c 0))
        (D.outgoing c 0) u hu0 hu1
      calc
        D.vertexPoint (D.arcTarget (D.outgoing c 0)) = outgoingCutPoint D c ε i := h.symm
        _ = smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 2) := hcut.symm
        _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.outgoing c 0)))
            (D.vertexPoint (D.arcTarget (D.outgoing c 0))) u := by simpa [i, hi] using hu
    intro h
    have hpoint : outgoingCutPoint D c ε i =
        DirectGLSSW.affinePoint (outgoingCutPoint D c ε i)
          (D.vertexPoint (D.arcTarget (D.outgoing c 0))) t := by
      calc
        outgoingCutPoint D c ε i =
            smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 2) := hcut.symm
        _ = smoothGeometryCodeArcPoint D c ε (Sum.inl (D.outgoing c 0)) t := h
        _ = smoothCodeArcPoint D c ε (Sum.inl (D.outgoing c 0)) t :=
          smoothGeometryCodeArcPoint_old D c ε (D.outgoing c 0) t
        _ = DirectGLSSW.affinePoint (outgoingCutPoint D c ε i)
            (D.vertexPoint (D.arcTarget (D.outgoing c 0))) t := by
              simpa [i, hi] using smoothGeometryOutgoingOldArcPoint D c ε 0 t
    exact affineSource_not_interior _ _ htarget t ht0 hpoint
  · obtain ⟨u, hu0, hu1, hu⟩ := smoothCutLabel_interior D c ε hε hεcut 3
    let i := (D.through c).symm 1
    have hi : D.through c i = 1 := Equiv.apply_symm_apply (D.through c) 1
    have hcut : smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 3) =
        outgoingCutPoint D c ε i := by
      simp [smoothCutLabelCode, smoothVertexPointGeometryCode, i]
    have htarget : outgoingCutPoint D c ε i ≠
        D.vertexPoint (D.arcTarget (D.outgoing c 1)) := by
      intro h
      apply D.vertices_avoid_arc_interiors (D.arcTarget (D.outgoing c 1))
        (D.outgoing c 1) u hu0 hu1
      calc
        D.vertexPoint (D.arcTarget (D.outgoing c 1)) = outgoingCutPoint D c ε i := h.symm
        _ = smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 3) := hcut.symm
        _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.outgoing c 1)))
            (D.vertexPoint (D.arcTarget (D.outgoing c 1))) u := by simpa [i, hi] using hu
    intro h
    have hpoint : outgoingCutPoint D c ε i =
        DirectGLSSW.affinePoint (outgoingCutPoint D c ε i)
          (D.vertexPoint (D.arcTarget (D.outgoing c 1))) t := by
      calc
        outgoingCutPoint D c ε i =
            smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c 3) := hcut.symm
        _ = smoothGeometryCodeArcPoint D c ε (Sum.inl (D.outgoing c 1)) t := h
        _ = smoothCodeArcPoint D c ε (Sum.inl (D.outgoing c 1)) t :=
          smoothGeometryCodeArcPoint_old D c ε (D.outgoing c 1) t
        _ = DirectGLSSW.affinePoint (outgoingCutPoint D c ε i)
            (D.vertexPoint (D.arcTarget (D.outgoing c 1))) t := by
              simpa [i, hi] using smoothGeometryOutgoingOldArcPoint D c ε 1 t
    exact affineSource_not_interior _ _ htarget t ht0 hpoint

theorem smoothCutLabel_otherOldArc_interior_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (k : Fin 4) (e : Fin D.nArc)
    (he : smoothCutLabelArc D c k ≠ e) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c k) ≠
      smoothGeometryCodeArcPoint D c ε (Sum.inl e) t := by
  obtain ⟨s, hs0, hs1, hcut⟩ := smoothCutLabel_interior D c ε hε hεcut k
  obtain ⟨t', ht'0, ht'1, hold⟩ :=
    smoothOldArcInterior_lies_oldInterior D c ε e t hε hεcut ht0 ht1
  intro h
  apply D.arc_interiors_disjoint (smoothCutLabelArc D c k) e he s t'
    hs0 hs1 ht'0 ht'1
  calc
    DirectGLSSW.affinePoint
        (D.vertexPoint (D.arcSource (smoothCutLabelArc D c k)))
        (D.vertexPoint (D.arcTarget (smoothCutLabelArc D c k))) s =
      smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c k) := hcut.symm
    _ = smoothGeometryCodeArcPoint D c ε (Sum.inl e) t := h
    _ = smoothCodeArcPoint D c ε (Sum.inl e) t :=
      smoothGeometryCodeArcPoint_old D c ε e t
    _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) t' := hold

theorem smoothCutLabel_oldArc_interior_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (k : Fin 4) (e : Fin D.nArc)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothVertexPointGeometryCode D c ε (smoothCutLabelCode D c k) ≠
      smoothGeometryCodeArcPoint D c ε (Sum.inl e) t := by
  by_cases he : smoothCutLabelArc D c k = e
  · subst e
    exact smoothCutLabel_matchingOldArc_interior_avoid D c ε hε hεcut k t ht0 ht1
  · exact smoothCutLabel_otherOldArc_interior_avoid D c ε hε hεcut k e he t ht0 ht1

theorem smoothOldVertex_oldArc_interior_avoid (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε < crossingCutoffRadius D c) (v : Fin D.nVertex)
    (hv : v ≠ D.crossingVertex c) (e : Fin D.nArc) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    smoothVertexPointGeometryCode D c ε (Sum.inl v) ≠
      smoothGeometryCodeArcPoint D c ε (Sum.inl e) t := by
  have hpoint : smoothVertexPointGeometryCode D c ε (Sum.inl v) = D.vertexPoint v := by
    simp [smoothVertexPointGeometryCode, hv]
  obtain ⟨t', ht'0, ht'1, hold⟩ :=
    smoothOldArcInterior_lies_oldInterior D c ε e t hε hεcut ht0 ht1
  intro heq
  apply D.vertices_avoid_arc_interiors v e t' ht'0 ht'1
  calc
    D.vertexPoint v = smoothVertexPointGeometryCode D c ε (Sum.inl v) := hpoint.symm
    _ = smoothGeometryCodeArcPoint D c ε (Sum.inl e) t := heq
    _ = smoothCodeArcPoint D c ε (Sum.inl e) t :=
      smoothGeometryCodeArcPoint_old D c ε e t
    _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) t' := hold

end DirectGLSSW.HOMFLY
