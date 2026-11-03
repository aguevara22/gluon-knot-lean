import PrincipalTurning
import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- Each retained arc is an oriented nondegenerate subsegment of its old arc. -/
theorem smoothOldArc_endpoints_ordered (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (e : Fin D.nArc)
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) :
    ∃ u v : ℝ, u < v ∧
      smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c (Sum.inl e)) =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) u ∧
      smoothVertexPointGeometryCode D c ε (smoothArcTargetCode D c (Sum.inl e)) =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) v := by
  let a := D.vertexPoint (D.arcSource e)
  let b := D.vertexPoint (D.arcTarget e)
  by_cases hout0 : e = D.outgoing c 0
  · have hcut := smoothOutgoingCutPoint_interior D c ε hε hεr ((D.through c).symm 0)
    obtain ⟨u, hu0, hu1, hu⟩ := hcut
    have hthrough : D.through c ((D.through c).symm 0) = 0 := Equiv.apply_symm_apply (D.through c) 0
    have hsource : D.arcSource e = D.crossingVertex c := by rw [hout0, D.outgoing_source]
    have hu' : outgoingCutPoint D c ε ((D.through c).symm 0) =
        DirectGLSSW.affinePoint a b u := by
      simpa [a, b, smoothingCenter, hout0, hthrough, hsource, D.outgoing_source] using hu
    have hspoint : smoothVertexPointGeometryCode D c ε
        (smoothArcSourceCode D c (Sum.inl e)) = outgoingCutPoint D c ε ((D.through c).symm 0) := by
      simp [smoothArcSourceCode, hout0, smoothRightCutCode, smoothVertexPointGeometryCode]
    have htarget : D.arcTarget e ≠ D.crossingVertex c := by
      intro ht
      exact (D.arc_endpoints_distinct e) (hsource.trans ht.symm)
    have htpoint : smoothVertexPointGeometryCode D c ε
        (smoothArcTargetCode D c (Sum.inl e)) = b := by
      have hnotin0 : D.outgoing c 0 ≠ D.incoming c 0 :=
        (D.four_ports_distinct c).2.2 0 0 |>.symm
      have hnotin1 : D.outgoing c 0 ≠ D.incoming c 1 :=
        (D.four_ports_distinct c).2.2 1 0 |>.symm
      have htarget' : D.arcTarget (D.outgoing c 0) ≠ D.crossingVertex c := by
        simpa [hout0] using htarget
      simp [smoothArcTargetCode, hout0, smoothVertexPointGeometryCode, b, htarget',
        hnotin0, hnotin1]
    have htpoint' : smoothVertexPointGeometryCode D c ε
        (smoothArcTargetCode D c (Sum.inl e)) = DirectGLSSW.affinePoint a b 1 := by
      simpa [DirectGLSSW.affinePoint_one] using htpoint
    exact ⟨u, 1, hu1, hspoint.trans hu', htpoint'⟩
  · by_cases hout1 : e = D.outgoing c 1
    · have hcut := smoothOutgoingCutPoint_interior D c ε hε hεr ((D.through c).symm 1)
      obtain ⟨u, hu0, hu1, hu⟩ := hcut
      have hthrough : D.through c ((D.through c).symm 1) = 1 := Equiv.apply_symm_apply (D.through c) 1
      have hsource : D.arcSource e = D.crossingVertex c := by rw [hout1, D.outgoing_source]
      have hu' : outgoingCutPoint D c ε ((D.through c).symm 1) =
          DirectGLSSW.affinePoint a b u := by
        simpa [a, b, smoothingCenter, hout1, hthrough, hsource, D.outgoing_source] using hu
      have hspoint : smoothVertexPointGeometryCode D c ε
          (smoothArcSourceCode D c (Sum.inl e)) = outgoingCutPoint D c ε ((D.through c).symm 1) := by
        have hne : D.outgoing c 1 ≠ D.outgoing c 0 := (D.four_ports_distinct c).2.1.symm
        simp [smoothArcSourceCode, hout0, hout1, smoothRightCutCode,
          smoothVertexPointGeometryCode, hne]
      have htarget : D.arcTarget e ≠ D.crossingVertex c := by
        intro ht
        exact (D.arc_endpoints_distinct e) (hsource.trans ht.symm)
      have hnotin0 : D.outgoing c 1 ≠ D.incoming c 0 :=
        (D.four_ports_distinct c).2.2 0 1 |>.symm
      have hnotin1 : D.outgoing c 1 ≠ D.incoming c 1 :=
        (D.four_ports_distinct c).2.2 1 1 |>.symm
      have htarget' : D.arcTarget (D.outgoing c 1) ≠ D.crossingVertex c := by
        simpa [hout1] using htarget
      have htpoint : smoothVertexPointGeometryCode D c ε
          (smoothArcTargetCode D c (Sum.inl e)) = b := by
        simp [smoothArcTargetCode, hout1, smoothVertexPointGeometryCode, b, htarget,
          hnotin0, hnotin1, htarget']
      have htpoint' : smoothVertexPointGeometryCode D c ε
          (smoothArcTargetCode D c (Sum.inl e)) = DirectGLSSW.affinePoint a b 1 := by
        simpa [DirectGLSSW.affinePoint_one] using htpoint
      exact ⟨u, 1, hu1, hspoint.trans hu', htpoint'⟩
    · by_cases hin0 : e = D.incoming c 0
      · have hcut := smoothIncomingCutPoint_interior D c ε hε hεr 0
        obtain ⟨v, hv0, hv1, hv⟩ := hcut
        have htarget : D.arcTarget e = D.crossingVertex c := by rw [hin0, D.incoming_target]
        have hv' : incomingCutPoint D c ε 0 = DirectGLSSW.affinePoint a b v := by
          simpa [a, b, smoothingCenter, hin0, htarget, D.incoming_target] using hv
        have hspoint : smoothVertexPointGeometryCode D c ε
            (smoothArcSourceCode D c (Sum.inl e)) = a := by
          have hsrc : D.arcSource e ≠ D.crossingVertex c := by
            intro h
            exact (D.arc_endpoints_distinct e) (by rw [h, htarget])
          simp [smoothArcSourceCode, hout0, hout1, smoothVertexPointGeometryCode, a, hsrc]
        have htpoint : smoothVertexPointGeometryCode D c ε
            (smoothArcTargetCode D c (Sum.inl e)) = incomingCutPoint D c ε 0 := by
          simp [smoothArcTargetCode, hin0, smoothLeftCutCode, smoothVertexPointGeometryCode]
        refine ⟨0, v, hv0, ?_, htpoint.trans hv'⟩
        simpa only [DirectGLSSW.affinePoint_zero] using hspoint
      · by_cases hin1 : e = D.incoming c 1
        · have hcut := smoothIncomingCutPoint_interior D c ε hε hεr 1
          obtain ⟨v, hv0, hv1, hv⟩ := hcut
          have htarget : D.arcTarget e = D.crossingVertex c := by rw [hin1, D.incoming_target]
          have hv' : incomingCutPoint D c ε 1 = DirectGLSSW.affinePoint a b v := by
            simpa [a, b, smoothingCenter, hin1, htarget, D.incoming_target] using hv
          have hspoint : smoothVertexPointGeometryCode D c ε
              (smoothArcSourceCode D c (Sum.inl e)) = a := by
            have hsrc : D.arcSource e ≠ D.crossingVertex c := by
              intro h
              exact (D.arc_endpoints_distinct e) (by rw [h, htarget])
            simp [smoothArcSourceCode, hout0, hout1, smoothVertexPointGeometryCode, a, hsrc]
          have htpoint : smoothVertexPointGeometryCode D c ε
              (smoothArcTargetCode D c (Sum.inl e)) = incomingCutPoint D c ε 1 := by
            have hne : D.incoming c 1 ≠ D.incoming c 0 := (D.four_ports_distinct c).1.symm
            simp [smoothArcTargetCode, hin1, smoothLeftCutCode, smoothVertexPointGeometryCode, hne]
          refine ⟨0, v, hv0, ?_, htpoint.trans hv'⟩
          simpa only [DirectGLSSW.affinePoint_zero] using hspoint
        · have hsrc : D.arcSource e ≠ D.crossingVertex c := by
            intro hsourceeq
            rcases (D.crossing_incidence_complete c e).mp (Or.inl hsourceeq) with hport | hport | hport | hport
            · have htarget : D.arcTarget e = D.crossingVertex c := by rw [hport, D.incoming_target]
              exact (D.arc_endpoints_distinct e) (hsourceeq.trans htarget.symm)
            · have htarget : D.arcTarget e = D.crossingVertex c := by rw [hport, D.incoming_target]
              exact (D.arc_endpoints_distinct e) (hsourceeq.trans htarget.symm)
            · exact hout0 hport
            · exact hout1 hport
          have htarget : D.arcTarget e ≠ D.crossingVertex c := by
            intro h
            rcases (D.crossing_incidence_complete c e).mp (Or.inr h) with hport | hport | hport | hport
            · exact hin0 hport
            · exact hin1 hport
            · have hs : D.arcSource e = D.crossingVertex c := by rw [hport, D.outgoing_source]
              exact (D.arc_endpoints_distinct e) (hs.trans h.symm)
            · have hs : D.arcSource e = D.crossingVertex c := by rw [hport, D.outgoing_source]
              exact (D.arc_endpoints_distinct e) (hs.trans h.symm)
          have hspoint : smoothVertexPointGeometryCode D c ε
              (smoothArcSourceCode D c (Sum.inl e)) = a := by
            simp [smoothArcSourceCode, hout0, hout1, smoothVertexPointGeometryCode, a, hsrc]
          have htpoint : smoothVertexPointGeometryCode D c ε
              (smoothArcTargetCode D c (Sum.inl e)) = b := by
            simp [smoothArcTargetCode, hin0, hin1, smoothVertexPointGeometryCode, b, htarget]
          have hspoint' : smoothVertexPointGeometryCode D c ε
              (smoothArcSourceCode D c (Sum.inl e)) = DirectGLSSW.affinePoint a b 0 := by
            simpa [DirectGLSSW.affinePoint_zero] using hspoint
          have htpoint' : smoothVertexPointGeometryCode D c ε
              (smoothArcTargetCode D c (Sum.inl e)) = DirectGLSSW.affinePoint a b 1 := by
            simpa [DirectGLSSW.affinePoint_one] using htpoint
          exact ⟨0, 1, by norm_num, hspoint', htpoint'⟩

/-- The full retained displacement is a positive multiple of the old displacement. -/
theorem smoothOldArc_displacement_positive (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (e : Fin D.nArc)
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) :
    ∃ α : ℝ, 0 < α ∧
      smoothVertexPointGeometryCode D c ε (smoothArcTargetCode D c (Sum.inl e)) -
        smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c (Sum.inl e)) =
      α • (D.vertexPoint (D.arcTarget e) - D.vertexPoint (D.arcSource e)) := by
  obtain ⟨u, v, huv, hs, ht⟩ := smoothOldArc_endpoints_ordered D c ε e hε hεr
  refine ⟨v - u, sub_pos.mpr huv, ?_⟩
  rw [ht, hs]
  ext <;> simp [DirectGLSSW.affinePoint] <;> ring

/-- Every actual retained arc has the same direction after the constructor's shortening. -/
theorem smoothCrossing_old_arcVector_positive (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc) :
    ∃ α : ℝ, 0 < α ∧
      PrincipalTurning.arcVector (smoothCrossing D c)
        (smoothArcEquiv D (Sum.inl e)) =
      (α : ℂ) * PrincipalTurning.arcVector D e := by
  have hεr : smoothEpsilon D c < crossingCutoffRadius D c :=
    lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)
  obtain ⟨α, hα, hvec⟩ := smoothOldArc_displacement_positive D c
    (smoothEpsilon D c) e (smoothEpsilon_pos D c) hεr
  refine ⟨α, hα, ?_⟩
  have hre := congrArg Prod.fst hvec
  have him := congrArg Prod.snd hvec
  simp only [PrincipalTurning.arcVector, smoothCrossing, smoothVertexPoint,
    smoothArcSource, smoothArcTarget, Equiv.symm_apply_apply]
  apply Complex.ext
  · simpa using hre
  · simpa using him

end DirectGLSSW.HOMFLY




