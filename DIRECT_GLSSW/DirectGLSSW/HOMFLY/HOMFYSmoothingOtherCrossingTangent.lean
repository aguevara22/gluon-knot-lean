import DirectGLSSW.HOMFLY.HOMFYSmoothingVertexInjective
import DirectGLSSW.HOMFLY.HOMFYSmoothingArcEndpointDistinct
import Mathlib.Tactic.Linarith

namespace DirectGLSSW.HOMFLY

private theorem point_sub_affinePoint (a b : PlanarPoint ℝ) (t : ℝ) :
    b - DirectGLSSW.affinePoint a b t = (1 - t) • (b - a) := by
  ext <;> simp [DirectGLSSW.affinePoint] <;> ring

private theorem affinePoint_sub_point (a b : PlanarPoint ℝ) (t : ℝ) :
    DirectGLSSW.affinePoint a b t - a = t • (b - a) := by
  ext <;> simp [DirectGLSSW.affinePoint] <;> ring

private theorem crossingVertex_ne_of_ne {D : PLLinkDiagram} {c d : Fin D.nCrossing}
    (h : d ≠ c) : D.crossingVertex d ≠ D.crossingVertex c := by
  intro heq
  exact h (D.crossingVertex_injective heq)

theorem smoothIncomingSourceVector_positive_multiple (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (i : Fin 2) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) (hdc : d ≠ c) :
    ∃ α : ℝ, 0 < α ∧
      D.vertexPoint (D.crossingVertex d) -
        smoothVertexPointGeometryCode D c ε
          (smoothArcSourceCode D c (Sum.inl (D.incoming d i))) =
        α • (D.vertexPoint (D.crossingVertex d) -
          D.vertexPoint (D.arcSource (D.incoming d i))) := by
  let e := D.incoming d i
  change ∃ α : ℝ, 0 < α ∧
    D.vertexPoint (D.crossingVertex d) -
      smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c (Sum.inl e)) =
    α • (D.vertexPoint (D.crossingVertex d) - D.vertexPoint (D.arcSource e))
  have htarget : D.arcTarget e = D.crossingVertex d := D.incoming_target d i
  have hcv : D.crossingVertex d ≠ D.crossingVertex c := crossingVertex_ne_of_ne hdc
  by_cases he0 : e = D.outgoing c 0
  · rw [he0]
    let j : Fin 2 := (D.through c).symm 0
    have hj : D.through c j = 0 := Equiv.apply_symm_apply (D.through c) 0
    have hcut := smoothOutgoingCutPoint_interior D c ε hε hεr j
    rcases hcut with ⟨t, ht0, ht1, hcut⟩
    have htarget' : D.arcTarget (D.outgoing c (D.through c j)) = D.crossingVertex d := by
      rw [hj]
      change D.arcTarget e = _ at htarget
      rw [he0] at htarget
      exact htarget
    have hcut' : outgoingCutPoint D c ε j =
        DirectGLSSW.affinePoint (D.vertexPoint (D.crossingVertex c))
          (D.vertexPoint (D.crossingVertex d)) t := by
      simpa [smoothingCenter, htarget'] using hcut
    refine ⟨1 - t, by linarith, ?_⟩
    have hpoint : smoothVertexPointGeometryCode D c ε
        (smoothArcSourceCode D c (Sum.inl (D.outgoing c 0))) = outgoingCutPoint D c ε j := by
      simp [smoothArcSourceCode, smoothRightCutCode, smoothVertexPointGeometryCode, j, hj]
    rw [hpoint, hcut', point_sub_affinePoint]
    simp [e, htarget, D.outgoing_source]
  · by_cases he1 : e = D.outgoing c 1
    · rw [he1]
      let j : Fin 2 := (D.through c).symm 1
      have hj : D.through c j = 1 := Equiv.apply_symm_apply (D.through c) 1
      have hcut := smoothOutgoingCutPoint_interior D c ε hε hεr j
      rcases hcut with ⟨t, ht0, ht1, hcut⟩
      have htarget' : D.arcTarget (D.outgoing c (D.through c j)) = D.crossingVertex d := by
        rw [hj]
        change D.arcTarget e = _ at htarget
        rw [he1] at htarget
        exact htarget
      have hcut' : outgoingCutPoint D c ε j =
          DirectGLSSW.affinePoint (D.vertexPoint (D.crossingVertex c))
            (D.vertexPoint (D.crossingVertex d)) t := by
        simpa [smoothingCenter, htarget'] using hcut
      refine ⟨1 - t, by linarith, ?_⟩
      have hpoint : smoothVertexPointGeometryCode D c ε
          (smoothArcSourceCode D c (Sum.inl (D.outgoing c 1))) = outgoingCutPoint D c ε j := by
        have houteq : D.outgoing c 1 ≠ D.outgoing c 0 :=
          (D.four_ports_distinct c).2.1.symm
        simp [smoothArcSourceCode, smoothRightCutCode, smoothVertexPointGeometryCode, j, hj, houteq]
      rw [hpoint, hcut', point_sub_affinePoint]
      simp [e, htarget, D.outgoing_source]
    · have hsrc : D.arcSource e ≠ D.crossingVertex c := by
        intro hs
        have hinc := (D.crossing_incidence_complete c e).mp (Or.inl hs)
        rcases hinc with h | h | h | h
        · have hs' : D.arcSource (D.incoming c 0) = D.crossingVertex c := by
            simpa [h] using hs
          exact (D.arc_endpoints_distinct (D.incoming c 0))
            (hs'.trans (D.incoming_target c 0).symm)
        · have hs' : D.arcSource (D.incoming c 1) = D.crossingVertex c := by
            simpa [h] using hs
          exact (D.arc_endpoints_distinct (D.incoming c 1))
            (hs'.trans (D.incoming_target c 1).symm)
        · exact he0 h
        · exact he1 h
      refine ⟨1, by norm_num, ?_⟩
      have hpoint : smoothVertexPointGeometryCode D c ε
          (smoothArcSourceCode D c (Sum.inl e)) = D.vertexPoint (D.arcSource e) := by
        simp [smoothArcSourceCode, he0, he1, smoothVertexPointGeometryCode, hsrc]
      rw [hpoint]
      simp [e, htarget]

theorem smoothOutgoingTargetVector_positive_multiple (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (i : Fin 2) (ε : ℝ)
    (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) (hdc : d ≠ c) :
    ∃ β : ℝ, 0 < β ∧
      smoothVertexPointGeometryCode D c ε
          (smoothArcTargetCode D c (Sum.inl (D.outgoing d i))) -
        D.vertexPoint (D.crossingVertex d) =
        β • (D.vertexPoint (D.arcTarget (D.outgoing d i)) -
          D.vertexPoint (D.crossingVertex d)) := by
  let e := D.outgoing d i
  change ∃ β : ℝ, 0 < β ∧
    smoothVertexPointGeometryCode D c ε (smoothArcTargetCode D c (Sum.inl e)) -
      D.vertexPoint (D.crossingVertex d) =
    β • (D.vertexPoint (D.arcTarget e) - D.vertexPoint (D.crossingVertex d))
  have hsource : D.arcSource e = D.crossingVertex d := D.outgoing_source d i
  have hcv : D.crossingVertex d ≠ D.crossingVertex c := crossingVertex_ne_of_ne hdc
  by_cases he0 : e = D.incoming c 0
  · rw [he0]
    have hcut := smoothIncomingCutPoint_interior D c ε hε hεr 0
    rcases hcut with ⟨t, ht0, ht1, hcut⟩
    have hsource' : D.arcSource (D.incoming c 0) = D.crossingVertex d := by
      rw [← he0]
      exact hsource
    have hcut' : incomingCutPoint D c ε 0 =
        DirectGLSSW.affinePoint (D.vertexPoint (D.crossingVertex d))
          (D.vertexPoint (D.crossingVertex c)) t := by
      simpa [smoothingCenter, hsource'] using hcut
    refine ⟨t, ht0, ?_⟩
    have hpoint : smoothVertexPointGeometryCode D c ε
        (smoothArcTargetCode D c (Sum.inl (D.incoming c 0))) = incomingCutPoint D c ε 0 := by
      simp [smoothArcTargetCode, smoothLeftCutCode, smoothVertexPointGeometryCode]
    have htarget' : D.arcTarget e = D.crossingVertex c := by
      rw [he0]
      exact D.incoming_target c 0
    rw [hpoint, hcut', affinePoint_sub_point]
    simp [D.incoming_target]
  · by_cases he1 : e = D.incoming c 1
    · rw [he1]
      have hcut := smoothIncomingCutPoint_interior D c ε hε hεr 1
      rcases hcut with ⟨t, ht0, ht1, hcut⟩
      have hsource' : D.arcSource (D.incoming c 1) = D.crossingVertex d := by
        rw [← he1]
        exact hsource
      have hcut' : incomingCutPoint D c ε 1 =
          DirectGLSSW.affinePoint (D.vertexPoint (D.crossingVertex d))
            (D.vertexPoint (D.crossingVertex c)) t := by
        simpa [smoothingCenter, hsource'] using hcut
      refine ⟨t, ht0, ?_⟩
      have hpoint : smoothVertexPointGeometryCode D c ε
          (smoothArcTargetCode D c (Sum.inl (D.incoming c 1))) = incomingCutPoint D c ε 1 := by
        have hne : D.incoming c 1 ≠ D.incoming c 0 := (D.four_ports_distinct c).1.symm
        simp [smoothArcTargetCode, smoothLeftCutCode, smoothVertexPointGeometryCode, hne]
      have htarget' : D.arcTarget e = D.crossingVertex c := by
        rw [he1]
        exact D.incoming_target c 1
      rw [hpoint, hcut', affinePoint_sub_point]
      simp [D.incoming_target]
    · have htargetOld : D.arcTarget e ≠ D.crossingVertex c := by
        intro ht
        have hinc := (D.crossing_incidence_complete c e).mp (Or.inr ht)
        rcases hinc with h | h | h | h
        · exact he0 h
        · exact he1 h
        · have hs' : D.arcSource e = D.crossingVertex c := by rw [h, D.outgoing_source]
          exact (D.arc_endpoints_distinct e) (hs'.trans ht.symm)
        · have hs' : D.arcSource e = D.crossingVertex c := by rw [h, D.outgoing_source]
          exact (D.arc_endpoints_distinct e) (hs'.trans ht.symm)
      refine ⟨1, by norm_num, ?_⟩
      have hpoint : smoothVertexPointGeometryCode D c ε
          (smoothArcTargetCode D c (Sum.inl e)) = D.vertexPoint (D.arcTarget e) := by
        simp [smoothArcTargetCode, smoothLeftCutCode, smoothVertexPointGeometryCode, he0, he1, htargetOld]
      rw [hpoint]
      simp [e, hsource]

end DirectGLSSW.HOMFLY
