import DirectGLSSW.HOMFLY.HOMFYSmoothingDegreeFin

namespace DirectGLSSW.HOMFLY

theorem smoothTargetCode_oldVertex_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : Fin D.nVertex) (hvc : D.crossingVertex c ≠ v) (a : SmoothArcCode D) :
    smoothArcTargetCode D c a = Sum.inl v ↔
      ∃ e : Fin D.nArc, a = Sum.inl e ∧ D.arcTarget e = v := by
  rcases a with e | i
  · by_cases h0 : e = D.incoming c 0
    · subst e
      simp [smoothArcTargetCode, smoothLeftCutCode, D.incoming_target, hvc]
    · by_cases h1 : e = D.incoming c 1
      · subst e
        simp [smoothArcTargetCode, smoothLeftCutCode, D.incoming_target, hvc, ((D.four_ports_distinct c).1).symm]
      · simp [smoothArcTargetCode, h0, h1]
  · fin_cases i <;> simp [smoothArcTargetCode, smoothRightCutCode]

theorem smoothSourceCode_oldVertex_fiber (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : Fin D.nVertex) (hvc : D.crossingVertex c ≠ v) (a : SmoothArcCode D) :
    smoothArcSourceCode D c a = Sum.inl v ↔
      ∃ e : Fin D.nArc, a = Sum.inl e ∧ D.arcSource e = v := by
  rcases a with e | i
  · by_cases h0 : e = D.outgoing c 0
    · subst e
      simp [smoothArcSourceCode, smoothRightCutCode, D.outgoing_source, hvc]
    · by_cases h1 : e = D.outgoing c 1
      · subst e
        simp [smoothArcSourceCode, smoothRightCutCode, D.outgoing_source, hvc, ((D.four_ports_distinct c).2.1).symm]
      · simp [smoothArcSourceCode, h0, h1]
  · fin_cases i <;> simp [smoothArcSourceCode, smoothLeftCutCode, smoothRightCutCode, hvc]

theorem smoothTargetFin_oldVertex_card (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : Fin D.nVertex) (hvc : D.crossingVertex c ≠ v) :
    (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcTargetFinCode D c e = smoothVertexEquiv D c (Sum.inl v))).card =
    (incomingArcs D.arcTarget v).card := by
  classical
  let S := incomingArcs D.arcTarget v
  let T := Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
    smoothArcTargetFinCode D c e = smoothVertexEquiv D c (Sum.inl v))
  have hcard := Finset.card_bij
    (s := S) (t := T)
    (fun e _ => smoothArcEquiv D (Sum.inl e))
    (by
      intro e he
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [smoothArcTargetFinCode, Equiv.symm_apply_apply]
      change smoothVertexEquiv D c
          (smoothArcTargetCode D c (Sum.inl e)) = smoothVertexEquiv D c (Sum.inl v)
      apply congrArg (smoothVertexEquiv D c)
      have he' : D.arcTarget e = v := (Finset.mem_filter.mp he).2
      have hf := (smoothTargetCode_oldVertex_fiber D c v hvc (Sum.inl e)).2
      exact hf ⟨e, rfl, he'⟩)
    (by
      intro e he f hf hEq
      have := (smoothArcEquiv D).injective hEq
      exact Sum.inl.inj this)
    (by
      intro b hb
      have hb' : smoothArcTargetFinCode D c b = smoothVertexEquiv D c (Sum.inl v) :=
        (Finset.mem_filter.mp hb).2
      let a := (smoothArcEquiv D).symm b
      have hcode : smoothArcTargetCode D c a = Sum.inl v := by
        apply (smoothVertexEquiv D c).injective
        simpa [smoothArcTargetFinCode, a] using hb'
      rcases (smoothTargetCode_oldVertex_fiber D c v hvc a).mp hcode with ⟨e, ha, hev⟩
      refine ⟨e, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev⟩
      · change smoothArcEquiv D (Sum.inl e) = b
        calc
          smoothArcEquiv D (Sum.inl e) = smoothArcEquiv D a := congrArg (smoothArcEquiv D) ha.symm
          _ = b := Equiv.apply_symm_apply (smoothArcEquiv D) b)
  simpa [S, T] using hcard.symm

end DirectGLSSW.HOMFLY
