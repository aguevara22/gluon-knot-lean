import DirectGLSSW.HOMFLY.HOMFYSmoothingVertexInjective

namespace DirectGLSSW.HOMFLY

theorem smoothArcCode_source_target_ne (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (e : SmoothArcCode D) : smoothArcSourceCode D c e ≠ smoothArcTargetCode D c e := by
  rcases e with e | i
  · by_cases ho0 : e = D.outgoing c 0
    · subst e
      simp only [smoothArcSourceCode, smoothArcTargetCode, if_pos rfl]
      have hnot0 : D.incoming c 0 ≠ D.outgoing c 0 := (D.four_ports_distinct c).2.2 0 0
      have hnot1 : D.incoming c 1 ≠ D.outgoing c 0 := (D.four_ports_distinct c).2.2 1 0
      simp [smoothRightCutCode, hnot0.symm, hnot1.symm]
    · by_cases ho1 : e = D.outgoing c 1
      · subst e
        simp only [smoothArcSourceCode, if_neg ho0, if_pos rfl]
        have hnot0 : D.incoming c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.2 0 1
        have hnot1 : D.incoming c 1 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.2 1 1
        simp [smoothArcTargetCode, smoothRightCutCode, hnot0.symm, hnot1.symm]
      · by_cases hi0 : e = D.incoming c 0
        · subst e
          have hsrc : D.arcSource (D.incoming c 0) ≠ D.crossingVertex c := by
            intro h
            exact (D.arc_endpoints_distinct (D.incoming c 0))
              (by rw [h, D.incoming_target])
          simp [smoothArcSourceCode, smoothArcTargetCode, smoothLeftCutCode, ho0, ho1, hsrc]
        · by_cases hi1 : e = D.incoming c 1
          · subst e
            simp [smoothArcSourceCode, smoothArcTargetCode, smoothLeftCutCode, ho0, ho1, hi0]
          · have hsrc : D.arcSource e ≠ D.arcTarget e := D.arc_endpoints_distinct e
            simp [smoothArcSourceCode, smoothArcTargetCode, ho0, ho1, hi0, hi1, hsrc]
  · fin_cases i <;> simp [smoothArcSourceCode, smoothArcTargetCode,
      smoothLeftCutCode, smoothRightCutCode]

end DirectGLSSW.HOMFLY
