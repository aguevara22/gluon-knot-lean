import DirectGLSSW.HOMFLY.HOMFYSmoothingDegree

namespace DirectGLSSW.HOMFLY

noncomputable def smoothArcTargetFinCode (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nArc + 2) → Fin (D.nVertex + 3) := fun e =>
  smoothVertexEquiv D c (smoothArcTargetCode D c ((smoothArcEquiv D).symm e))

noncomputable def smoothArcSourceFinCode (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nArc + 2) → Fin (D.nVertex + 3) := fun e =>
  smoothVertexEquiv D c (smoothArcSourceCode D c ((smoothArcEquiv D).symm e))

private theorem targetFin_fiber_card (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : SmoothVertexCode D)
    (hcard : (Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcTargetCode D c a = v)).card = 1) :
    (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcTargetFinCode D c e = smoothVertexEquiv D c v)).card = 1 := by
  classical
  have h := Finset.card_equiv (smoothArcEquiv D).symm
    (s := Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcTargetFinCode D c e = smoothVertexEquiv D c v))
    (t := Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcTargetCode D c a = v)) (by
      intro e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (smoothVertexEquiv D c
        (smoothArcTargetCode D c ((smoothArcEquiv D).symm e)) =
          smoothVertexEquiv D c v) ↔
        smoothArcTargetCode D c ((smoothArcEquiv D).symm e) = v
      constructor
      · intro hEq
        exact (smoothVertexEquiv D c).injective hEq
      · intro hEq
        exact congrArg (smoothVertexEquiv D c) hEq)
  exact h.trans hcard

private theorem sourceFin_fiber_card (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (v : SmoothVertexCode D)
    (hcard : (Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcSourceCode D c a = v)).card = 1) :
    (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcSourceFinCode D c e = smoothVertexEquiv D c v)).card = 1 := by
  classical
  have h := Finset.card_equiv (smoothArcEquiv D).symm
    (s := Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcSourceFinCode D c e = smoothVertexEquiv D c v))
    (t := Finset.univ.filter (fun a : SmoothArcCode D =>
      smoothArcSourceCode D c a = v)) (by
      intro e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (smoothVertexEquiv D c
        (smoothArcSourceCode D c ((smoothArcEquiv D).symm e)) =
          smoothVertexEquiv D c v) ↔
        smoothArcSourceCode D c ((smoothArcEquiv D).symm e) = v
      constructor
      · intro hEq
        exact (smoothVertexEquiv D c).injective hEq
      · intro hEq
        exact congrArg (smoothVertexEquiv D c) hEq)
  exact h.trans hcard

theorem smoothCutpointFin_degree_table (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcTargetFinCode D c e = smoothVertexEquiv D c (smoothLeftCutCode D c 0))).card = 1) ∧
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcTargetFinCode D c e = smoothVertexEquiv D c (smoothLeftCutCode D c 1))).card = 1) ∧
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcSourceFinCode D c e = smoothVertexEquiv D c (smoothLeftCutCode D c 0))).card = 1) ∧
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcSourceFinCode D c e = smoothVertexEquiv D c (smoothLeftCutCode D c 1))).card = 1) ∧
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcTargetFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 0))).card = 1) ∧
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcTargetFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 1))).card = 1) ∧
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcSourceFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 0))).card = 1) ∧
    ((Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
      smoothArcSourceFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 1))).card = 1) := by
  classical
  have hleft := smoothArcCode_cutpoint_target_count D c
  have hcode := smoothArcCode_cutpoint_degree_table D c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact targetFin_fiber_card D c _ hleft.1
  · exact targetFin_fiber_card D c _ hleft.2
  · exact sourceFin_fiber_card D c _ hcode.1
  · exact sourceFin_fiber_card D c _ hcode.2.1
  · exact targetFin_fiber_card D c _ hcode.2.2.2.2.1
  · exact targetFin_fiber_card D c _ hcode.2.2.2.2.2
  · exact sourceFin_fiber_card D c _ hcode.2.2.1
  · exact sourceFin_fiber_card D c _ hcode.2.2.2.1

end DirectGLSSW.HOMFLY
