import DirectGLSSW.HOMFLY.HOMFYSmoothingClearance
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

namespace DirectGLSSW.HOMFLY

/-- Old vertex labels with three added slots. The old selected crossing-vertex
slot is repurposed as the first cutoff point. -/
abbrev SmoothVertexCode (D : PLLinkDiagram) := Fin D.nVertex ⊕ Fin 3

/-- All old arc labels together with the two new smoothing connectors. -/
abbrev SmoothArcCode (D : PLLinkDiagram) := Fin D.nArc ⊕ Fin 2

/-- The remaining crossing labels after deleting the selected crossing. -/
abbrev SmoothCrossingCode (D : PLLinkDiagram) (c : Fin D.nCrossing) :=
  {d : Fin D.nCrossing // d ≠ c}

noncomputable def smoothVertexEquiv (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    SmoothVertexCode D ≃ Fin (D.nVertex + 3) :=
  Fintype.equivFinOfCardEq (by simp [SmoothVertexCode])

noncomputable def smoothArcEquiv (D : PLLinkDiagram) :
    SmoothArcCode D ≃ Fin (D.nArc + 2) :=
  Fintype.equivFinOfCardEq (by simp [SmoothArcCode])

private theorem smoothCrossingCode_card (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Fintype.card (SmoothCrossingCode D c) = D.nCrossing - 1 := by
  classical
  simp [SmoothCrossingCode, Fintype.card_subtype_compl]

noncomputable def smoothCrossingEquiv (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    SmoothCrossingCode D c ≃ Fin (D.nCrossing - 1) :=
  Fintype.equivFinOfCardEq (smoothCrossingCode_card D c)

def smoothLeftCutCode (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    SmoothVertexCode D :=
  if i = 0 then Sum.inl (D.crossingVertex c) else Sum.inr ⟨0, by decide⟩

def smoothRightCutCode (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    SmoothVertexCode D :=
  if i = 0 then Sum.inr ⟨1, by decide⟩ else Sum.inr ⟨2, by decide⟩

def smoothVertexPointCode (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ) :
    SmoothVertexCode D → PlanarPoint ℝ
  | Sum.inl v => if v = D.crossingVertex c then incomingCutPoint D c ε 0 else D.vertexPoint v
  | Sum.inr i => if i = 0 then incomingCutPoint D c ε 1 else
      if i = 1 then outgoingCutPoint D c ε 0 else outgoingCutPoint D c ε 1

def smoothArcSourceCode (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    SmoothArcCode D → SmoothVertexCode D
  | Sum.inl e =>
      if e = D.outgoing c 0 then smoothRightCutCode D c 0 else
      if e = D.outgoing c 1 then smoothRightCutCode D c 1 else Sum.inl (D.arcSource e)
  | Sum.inr i => if i = 0 then smoothLeftCutCode D c 0 else smoothLeftCutCode D c 1

def smoothArcTargetCode (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    SmoothArcCode D → SmoothVertexCode D
  | Sum.inl e =>
      if e = D.incoming c 0 then smoothLeftCutCode D c 0 else
      if e = D.incoming c 1 then smoothLeftCutCode D c 1 else Sum.inl (D.arcTarget e)
  | Sum.inr i => if i = 0 then smoothRightCutCode D c 1 else smoothRightCutCode D c 0

private theorem finTwo_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

private noncomputable def smoothContinuationAdjust (D : PLLinkDiagram)
    (c : Fin D.nCrossing) : Equiv.Perm (SmoothArcCode D) := by
  classical
  have hout : D.outgoing c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.1
  by_cases h0 : D.through c 0 = 0
  · have h1 : D.through c 1 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · have hbad := (D.through c).injective (h0.trans hv.symm)
        norm_num at hbad
      · exact hv
    exact Equiv.swap (Sum.inl (D.outgoing c 0)) (Sum.inl (D.outgoing c 1)) *
      Equiv.swap (Sum.inl (D.outgoing c 1)) (Sum.inr 1) *
      Equiv.swap (Sum.inl (D.outgoing c 0)) (Sum.inr 0)
  · have hzero : D.through c 0 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 0) with hv | hv
      · exact False.elim (h0 hv)
      · exact hv
    have hone : D.through c 1 = 0 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · exact hv
      · have hbad := (D.through c).injective (hzero.trans hv.symm)
        norm_num at hbad
    exact Equiv.swap (Sum.inl (D.outgoing c 1)) (Sum.inr 0) *
      Equiv.swap (Sum.inl (D.outgoing c 0)) (Sum.inr 1)

noncomputable def smoothContinuationCode (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Equiv.Perm (SmoothArcCode D) :=
  smoothContinuationAdjust D c * Equiv.sumCongr D.continuation (Equiv.refl (Fin 2))

theorem smoothContinuation_incoming_zero (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothContinuationCode D c (Sum.inl (D.incoming c 0)) = Sum.inr 0 := by
  classical
  have hout : D.outgoing c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.1
  by_cases h0 : D.through c 0 = 0
  · have h1 : D.through c 1 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · have hbad := (D.through c).injective (h0.trans hv.symm)
        norm_num at hbad
      · exact hv
    have hmap : smoothContinuationAdjust D c (Sum.inl (D.outgoing c 0)) = Sum.inr 0 := by
      simp [smoothContinuationAdjust, h0, h1, Equiv.swap_apply_def, hout, hout.symm]
    change smoothContinuationAdjust D c (Sum.inl (D.continuation (D.incoming c 0))) = _
    rw [D.continuation_crossing, h0]
    exact hmap
  · have hzero : D.through c 0 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 0) with hv | hv
      · exact False.elim (h0 hv)
      · exact hv
    have hone : D.through c 1 = 0 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · exact hv
      · have hbad := (D.through c).injective (hzero.trans hv.symm)
        norm_num at hbad
    have hmap : smoothContinuationAdjust D c (Sum.inl (D.outgoing c 1)) = Sum.inr 0 := by
      simp [smoothContinuationAdjust, h0, hzero, hone, Equiv.swap_apply_def, hout, hout.symm]
    change smoothContinuationAdjust D c (Sum.inl (D.continuation (D.incoming c 0))) = _
    rw [D.continuation_crossing, hzero]
    exact hmap

theorem smoothContinuation_incoming_one (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothContinuationCode D c (Sum.inl (D.incoming c 1)) = Sum.inr 1 := by
  classical
  have hout : D.outgoing c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.1
  by_cases h0 : D.through c 0 = 0
  · have h1 : D.through c 1 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · have hbad := (D.through c).injective (h0.trans hv.symm)
        norm_num at hbad
      · exact hv
    have hmap : smoothContinuationAdjust D c (Sum.inl (D.outgoing c 1)) = Sum.inr 1 := by
      simp [smoothContinuationAdjust, h0, h1, Equiv.swap_apply_def, hout, hout.symm]
    change smoothContinuationAdjust D c (Sum.inl (D.continuation (D.incoming c 1))) = _
    rw [D.continuation_crossing, h1]
    exact hmap
  · have hzero : D.through c 0 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 0) with hv | hv
      · exact False.elim (h0 hv)
      · exact hv
    have hone : D.through c 1 = 0 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · exact hv
      · have hbad := (D.through c).injective (hzero.trans hv.symm)
        norm_num at hbad
    have hmap : smoothContinuationAdjust D c (Sum.inl (D.outgoing c 0)) = Sum.inr 1 := by
      simp [smoothContinuationAdjust, h0, hzero, hone, Equiv.swap_apply_def, hout, hout.symm]
    change smoothContinuationAdjust D c (Sum.inl (D.continuation (D.incoming c 1))) = _
    rw [D.continuation_crossing, hone]
    exact hmap

theorem smoothContinuation_connector_zero (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothContinuationCode D c (Sum.inr 0) = Sum.inl (D.outgoing c 1) := by
  classical
  have hout : D.outgoing c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.1
  by_cases h0 : D.through c 0 = 0
  · have h1 : D.through c 1 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · have hbad := (D.through c).injective (h0.trans hv.symm)
        norm_num at hbad
      · exact hv
    simp [smoothContinuationCode, Equiv.Perm.mul_apply, smoothContinuationAdjust, h0, h1,
      Equiv.swap_apply_def, hout, hout.symm]
  · have hzero : D.through c 0 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 0) with hv | hv
      · exact False.elim (h0 hv)
      · exact hv
    have hone : D.through c 1 = 0 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · exact hv
      · have hbad := (D.through c).injective (hzero.trans hv.symm)
        norm_num at hbad
    simp [smoothContinuationCode, Equiv.Perm.mul_apply, smoothContinuationAdjust, h0, hzero, hone,
      Equiv.swap_apply_def, hout, hout.symm]

theorem smoothContinuation_connector_one (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    smoothContinuationCode D c (Sum.inr 1) = Sum.inl (D.outgoing c 0) := by
  classical
  have hout : D.outgoing c 0 ≠ D.outgoing c 1 := (D.four_ports_distinct c).2.1
  by_cases h0 : D.through c 0 = 0
  · have h1 : D.through c 1 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · have hbad := (D.through c).injective (h0.trans hv.symm)
        norm_num at hbad
      · exact hv
    simp [smoothContinuationCode, Equiv.Perm.mul_apply, smoothContinuationAdjust, h0, h1,
      Equiv.swap_apply_def, hout, hout.symm]
  · have hzero : D.through c 0 = 1 := by
      rcases finTwo_eq_zero_or_one (D.through c 0) with hv | hv
      · exact False.elim (h0 hv)
      · exact hv
    have hone : D.through c 1 = 0 := by
      rcases finTwo_eq_zero_or_one (D.through c 1) with hv | hv
      · exact hv
      · have hbad := (D.through c).injective (hzero.trans hv.symm)
        norm_num at hbad
    simp [smoothContinuationCode, Equiv.Perm.mul_apply, smoothContinuationAdjust, h0, hzero, hone,
      Equiv.swap_apply_def, hout, hout.symm]









end DirectGLSSW.HOMFLY
