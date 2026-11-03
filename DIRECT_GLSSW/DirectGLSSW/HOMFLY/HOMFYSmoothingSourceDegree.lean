import DirectGLSSW.HOMFLY.HOMFYSmoothingDegreeOrdinary

namespace DirectGLSSW.HOMFLY

theorem smoothSourceFin_oldVertex_card (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : Fin D.nVertex) (hvc : D.crossingVertex c ≠ v) :
    (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcSourceFinCode D c e = smoothVertexEquiv D c (Sum.inl v))).card =
    (outgoingArcs D.arcSource v).card := by
  classical
  let S := outgoingArcs D.arcSource v
  let T := Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
    smoothArcSourceFinCode D c e = smoothVertexEquiv D c (Sum.inl v))
  have hcard := Finset.card_bij
    (s := S) (t := T)
    (fun e _ => smoothArcEquiv D (Sum.inl e))
    (by
      intro e he
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [smoothArcSourceFinCode, Equiv.symm_apply_apply]
      apply congrArg (smoothVertexEquiv D c)
      have he' : D.arcSource e = v := (Finset.mem_filter.mp he).2
      exact (smoothSourceCode_oldVertex_fiber D c v hvc (Sum.inl e)).2 ⟨e, rfl, he'⟩)
    (by
      intro e he f hf hEq
      have := (smoothArcEquiv D).injective hEq
      exact Sum.inl.inj this)
    (by
      intro b hb
      have hb' : smoothArcSourceFinCode D c b = smoothVertexEquiv D c (Sum.inl v) :=
        (Finset.mem_filter.mp hb).2
      let a := (smoothArcEquiv D).symm b
      have hcode : smoothArcSourceCode D c a = Sum.inl v := by
        apply (smoothVertexEquiv D c).injective
        simpa [smoothArcSourceFinCode, a] using hb'
      rcases (smoothSourceCode_oldVertex_fiber D c v hvc a).mp hcode with ⟨e, ha, hev⟩
      refine ⟨e, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev⟩
      · change smoothArcEquiv D (Sum.inl e) = b
        calc
          smoothArcEquiv D (Sum.inl e) = smoothArcEquiv D a := congrArg (smoothArcEquiv D) ha.symm
          _ = b := Equiv.apply_symm_apply (smoothArcEquiv D) b)
  simpa [S, T] using hcard.symm

end DirectGLSSW.HOMFLY
