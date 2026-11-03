import DirectGLSSW.HOMFLY.HOMFYSmoothingSourceDegree
import Mathlib.Tactic.FinCases

namespace DirectGLSSW.HOMFLY

noncomputable def smoothCrossingVertexAux (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) → Fin (D.nVertex + 3) := fun d =>
  smoothVertexEquiv D c (Sum.inl (D.crossingVertex ((smoothCrossingEquiv D c).symm d).val))

noncomputable def smoothArcTargetAux (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nArc + 2) → Fin (D.nVertex + 3) := fun e =>
  smoothVertexEquiv D c (smoothArcTargetCode D c ((smoothArcEquiv D).symm e))

noncomputable def smoothArcSourceAux (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fin (D.nArc + 2) → Fin (D.nVertex + 3) := fun e =>
  smoothVertexEquiv D c (smoothArcSourceCode D c ((smoothArcEquiv D).symm e))

theorem smoothRegularDegreeOne (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    ∀ v : Fin (D.nVertex + 3),
      (∀ d : Fin (D.nCrossing - 1), smoothCrossingVertexAux D c d ≠ v) →
      (incomingArcs (smoothArcTargetAux D c) v).card = 1 ∧
        (outgoingArcs (smoothArcSourceAux D c) v).card = 1 := by
  classical
  intro v hv
  let x := (smoothVertexEquiv D c).symm v
  have hx : smoothVertexEquiv D c x = v := Equiv.apply_symm_apply (smoothVertexEquiv D c) v
  rcases x with v0 | i
  · by_cases hsel : v0 = D.crossingVertex c
    · subst v0
      rw [← hx]
      have htable := smoothCutpointFin_degree_table D c
      constructor
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcTargetFinCode D c e = smoothVertexEquiv D c (Sum.inl (D.crossingVertex c)))).card = 1
        simpa [smoothLeftCutCode] using htable.1
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcSourceFinCode D c e = smoothVertexEquiv D c (Sum.inl (D.crossingVertex c)))).card = 1
        simpa [smoothLeftCutCode] using htable.2.2.1
    · have hD : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ v0 := by
        intro d
        by_cases hd : d = c
        · subst d
          intro heq
          exact hsel heq.symm
        · let d' := smoothCrossingEquiv D c ⟨d, hd⟩
          intro heq
          have heq' : smoothCrossingVertexAux D c d' = v := by
            simpa [smoothCrossingVertexAux, d', heq] using hx
          exact (hv d') heq'
      have hreg := D.regular_degree_one v0 hD
      have hvc : D.crossingVertex c ≠ v0 := fun heq => hsel heq.symm
      rw [← hx]
      constructor
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcTargetFinCode D c e = smoothVertexEquiv D c (Sum.inl v0))).card = 1
        rw [smoothTargetFin_oldVertex_card D c v0 hvc]
        exact hreg.1
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcSourceFinCode D c e = smoothVertexEquiv D c (Sum.inl v0))).card = 1
        rw [smoothSourceFin_oldVertex_card D c v0 hvc]
        exact hreg.2
  · fin_cases i
    · rw [← hx]
      have htable := smoothCutpointFin_degree_table D c
      constructor
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcTargetFinCode D c e = smoothVertexEquiv D c (smoothLeftCutCode D c 1))).card = 1
        simpa [smoothLeftCutCode] using htable.2.1
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcSourceFinCode D c e = smoothVertexEquiv D c (smoothLeftCutCode D c 1))).card = 1
        simpa [smoothLeftCutCode] using htable.2.2.2.1
    · rw [← hx]
      have htable := smoothCutpointFin_degree_table D c
      constructor
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcTargetFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 0))).card = 1
        simpa [smoothRightCutCode] using htable.2.2.2.2.1
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcSourceFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 0))).card = 1
        simpa [smoothRightCutCode] using htable.2.2.2.2.2.2.1
    · rw [← hx]
      have htable := smoothCutpointFin_degree_table D c
      constructor
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcTargetFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 1))).card = 1
        simpa [smoothRightCutCode] using htable.2.2.2.2.2.1
      · change (Finset.univ.filter (fun e : Fin (D.nArc + 2) =>
          smoothArcSourceFinCode D c e = smoothVertexEquiv D c (smoothRightCutCode D c 1))).card = 1
        simpa [smoothRightCutCode] using htable.2.2.2.2.2.2.2

end DirectGLSSW.HOMFLY
