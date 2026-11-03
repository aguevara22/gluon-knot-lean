import DirectGLSSW.HOMFLY.HOMFYSmoothingOtherCrossingTangent
import Mathlib.Tactic.Linarith

namespace DirectGLSSW.HOMFLY

private theorem affine_between_affine (a b : PlanarPoint ℝ) (u v s : ℝ) :
    DirectGLSSW.affinePoint (DirectGLSSW.affinePoint a b u)
      (DirectGLSSW.affinePoint a b v) s =
    DirectGLSSW.affinePoint a b (u + s * (v - u)) := by
  ext <;> simp [DirectGLSSW.affinePoint] <;> ring

theorem smoothOldArcInterior_lies_oldInterior (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (e : Fin D.nArc) (s : ℝ)
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ t, 0 < t ∧ t < 1 ∧
      DirectGLSSW.affinePoint
          (smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c (Sum.inl e)))
          (smoothVertexPointGeometryCode D c ε (smoothArcTargetCode D c (Sum.inl e))) s =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) t := by
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
    have hparam : 0 < u + s * (1 - u) ∧ u + s * (1 - u) < 1 := by
      constructor
      · nlinarith
      · nlinarith
    refine ⟨u + s * (1 - u), hparam.1, hparam.2, ?_⟩
    rw [hspoint, hu', htpoint']
    rw [affine_between_affine]
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
      have hparam : 0 < u + s * (1 - u) ∧ u + s * (1 - u) < 1 := by
        constructor <;> nlinarith
      refine ⟨u + s * (1 - u), hparam.1, hparam.2, ?_⟩
      rw [hspoint, hu', htpoint']
      rw [affine_between_affine]
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
        have hparam : 0 < s * v ∧ s * v < 1 := by constructor <;> nlinarith
        have hspoint' : smoothVertexPointGeometryCode D c ε
            (smoothArcSourceCode D c (Sum.inl e)) = DirectGLSSW.affinePoint a b 0 := by
          simpa [DirectGLSSW.affinePoint_zero] using hspoint
        refine ⟨s * v, hparam.1, hparam.2, ?_⟩
        rw [hspoint', htpoint, hv']
        rw [affine_between_affine]
        congr 1 <;> ring
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
          have hparam : 0 < s * v ∧ s * v < 1 := by constructor <;> nlinarith
          have hspoint' : smoothVertexPointGeometryCode D c ε
              (smoothArcSourceCode D c (Sum.inl e)) = DirectGLSSW.affinePoint a b 0 := by
            simpa [DirectGLSSW.affinePoint_zero] using hspoint
          refine ⟨s * v, hparam.1, hparam.2, ?_⟩
          rw [hspoint', htpoint, hv']
          rw [affine_between_affine]
          simpa [a, b]
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
          refine ⟨s, hs0, hs1, ?_⟩
          rw [hspoint', htpoint', affine_between_affine]
          simpa [a, b]

end DirectGLSSW.HOMFLY
