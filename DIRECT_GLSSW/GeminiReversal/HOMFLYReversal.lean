import GeminiReversal.SmoothingReversal
import PositivePolygonTurns
import BranchIsoSmoothing
import GeminiLowest.Solution

set_option autoImplicit false

noncomputable section

namespace DirectGLSSW

open GeminiReversalContract
open GeometricSmoothingWeights
open HOMFLY
open HOMFLY.PolygonDrawing
open HOMFLY.PolygonDrawingBridge
open HOMFLY.PrincipalTurning
open HOMFLY.Coefficients
open HOMFLY.BranchSignedDiagramIso
open HOMFLY.SmoothingCornerGeometry
open EventSegmentGeometry
open PermutationOrbits
open scoped BigOperators

section PartA_TurnsAndCrossings

variable {n : ℕ}

theorem positivePolygonEventDiagram_nCrossing_reversePolygon
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    (positivePolygonEventDiagram (reversePolygon q) (cyclicGeneric_reversePolygon q hq)).nCrossing =
      (positivePolygonEventDiagram q hq).nCrossing := by
  change Fintype.card (PolygonCrossing (reversePolygon q)) = Fintype.card (PolygonCrossing q)
  exact (Fintype.card_congr (crossingRevEquiv q)).symm

def positiveArcRevEquiv (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    Fin (positivePolygonEventDiagram q hq).nArc ≃
      Fin (positivePolygonEventDiagram (reversePolygon q) (cyclicGeneric_reversePolygon q hq)).nArc :=
  (eventFin q).symm.trans
    ((polygonEventSuccessor q hq.g2).trans
      ((eventVertexRev q).trans (eventFin (reversePolygon q))))

theorem positiveArcRevEquiv_eventFin (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (x : PolygonEvent q) :
    positiveArcRevEquiv q hq (eventFin q x) =
      eventFin (reversePolygon q) (eventVertexRev q (polygonEventSuccessor q hq.g2 x)) := by
  change (eventFin (reversePolygon q))
    ((eventVertexRev q) ((polygonEventSuccessor q hq.g2) ((eventFin q).symm ((eventFin q) x)))) = _
  rw [Equiv.symm_apply_apply]

theorem polygonEventEdge_eventVertexRev_successor
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (x : PolygonEvent q) :
    polygonEventEdge (reversePolygon q)
      (eventVertexRev q (polygonEventSuccessor q hq.g2 x)) =
      edgeRev (polygonEventEdge q x) := by
  have hs := EventSegmentGeometry.polygonEventSuccessor_sameEdge_next_or_nextAnchor
    q hq.g2 hq.size_ge_three x
  dsimp at hs
  rcases hs with ⟨hey, hxy, _⟩ | ⟨hy_anc, _⟩
  · cases hy_cases : polygonEventSuccessor q hq.g2 x with
    | inl ey =>
      have h0 : polygonEventParameter q (polygonEventSuccessor q hq.g2 x) = 0 := by
        simp [hy_cases, polygonEventParameter]
      have hbounds := (polygonEventParameter_bounds q x).1
      linarith
    | inr wy =>
      have hwy_edge : crossingVisitEdge q wy = polygonEventEdge q x := by
        rw [hy_cases] at hey
        exact hey
      rw [eventVertexRev_inr, polygonEventEdge, crossingVisitEdge_visitRevEquiv, hwy_edge]
  · rw [hy_anc, eventVertexRev_inl]
    rfl

private def toComplexPoint (p : PlanarPoint ℝ) : ℂ := ⟨p.1, p.2⟩

private theorem toComplexPoint_smul (s : ℝ) (p : PlanarPoint ℝ) :
    toComplexPoint (s • p) = (s : ℂ) * toComplexPoint p := by
  apply Complex.ext <;> simp [toComplexPoint, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

private theorem toComplexPoint_neg (p : PlanarPoint ℝ) :
    toComplexPoint (-p) = -toComplexPoint p := by
  apply Complex.ext <;> simp [toComplexPoint]

private theorem principalArcVector_eq_toComplexPoint (D : PLLinkDiagram) (e : Fin D.nArc) :
    PrincipalTurning.arcVector D e =
      toComplexPoint (SmoothingCornerGeometry.arcVector D e) := rfl

private theorem complex_det_eq_planarDet (p₁ p₂ : PlanarPoint ℝ) :
    (toComplexPoint p₁).re * (toComplexPoint p₂).im -
      (toComplexPoint p₁).im * (toComplexPoint p₂).re =
      planarDet p₁ p₂ := rfl

theorem turn_positivePolygonEventDiagram_reversePolygon
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (x : PolygonEvent q) :
    turn (positivePolygonEventDiagram (reversePolygon q) (cyclicGeneric_reversePolygon q hq))
      (positiveArcRevEquiv q hq
        ((positivePolygonEventDiagram q hq).continuation (eventFin q x))) =
      -turn (positivePolygonEventDiagram q hq) (eventFin q x) := by
  let hqr := cyclicGeneric_reversePolygon q hq
  let D := positivePolygonEventDiagram q hq
  let D_rev := positivePolygonEventDiagram (reversePolygon q) hqr
  let y := polygonEventSuccessor q hq.g2 x
  let z := polygonEventSuccessor q hq.g2 y
  let y_rev := eventVertexRev q y
  let z_rev := eventVertexRev q z
  have hcont_D : D.continuation (eventFin q x) = eventFin q y :=
    polygonEventDiagram_continuation q hq x
  have he_rev : positiveArcRevEquiv q hq (eventFin q y) = eventFin (reversePolygon q) z_rev :=
    positiveArcRevEquiv_eventFin q hq y
  have hcont_z_rev : polygonEventSuccessor (reversePolygon q) hqr.g2 z_rev = y_rev :=
    polygonEventSuccessor_reversePolygon_intertwine q hq y
  have hcont_D_rev : D_rev.continuation (eventFin (reversePolygon q) z_rev) =
      eventFin (reversePolygon q) y_rev := by
    change (polygonEventDiagram (reversePolygon q) hqr).continuation
      (eventFin (reversePolygon q) z_rev) = eventFin (reversePolygon q) y_rev
    rw [polygonEventDiagram_continuation (reversePolygon q) hqr z_rev, hcont_z_rev]
  unfold turn
  rw [hcont_D, he_rev, hcont_D_rev]
  rw [principalArcVector_eq_toComplexPoint, principalArcVector_eq_toComplexPoint,
    principalArcVector_eq_toComplexPoint, principalArcVector_eq_toComplexPoint]
  rw [positivePolygonEventDiagram_arcVector (reversePolygon q) hqr y_rev,
    positivePolygonEventDiagram_arcVector (reversePolygon q) hqr z_rev,
    positivePolygonEventDiagram_arcVector q hq y,
    positivePolygonEventDiagram_arcVector q hq x]
  rw [toComplexPoint_smul, toComplexPoint_smul, toComplexPoint_smul, toComplexPoint_smul]
  rw [turn_positive_rescale _ _ _ _
      (stepScale_pos (reversePolygon q) hqr y_rev)
      (stepScale_pos (reversePolygon q) hqr z_rev),
    turn_positive_rescale _ _ _ _
      (stepScale_pos q hq y)
      (stepScale_pos q hq x)]
  rw [polygonEventEdge_eventVertexRev_successor q hq x,
    polygonEventEdge_eventVertexRev_successor q hq y,
    cyclicTangent_reversePolygon_edgeRev q (polygonEventEdge q x),
    cyclicTangent_reversePolygon_edgeRev q (polygonEventEdge q y),
    toComplexPoint_neg, toComplexPoint_neg, neg_div_neg_eq]
  rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor
      q hq.g2 hq.size_ge_three x with ⟨h_edge, _⟩ | ⟨h_y, _⟩
  · have h_eq : polygonEventEdge q y = polygonEventEdge q x := h_edge
    rw [h_eq]
    have h_nz : toComplexPoint (cyclicTangent q (polygonEventEdge q x)) ≠ 0 := by
      intro h0
      have h1 : (toComplexPoint (cyclicTangent q (polygonEventEdge q x))).re = 0 := by
        rw [h0]; rfl
      have h2 : (toComplexPoint (cyclicTangent q (polygonEventEdge q x))).im = 0 := by
        rw [h0]; rfl
      exact cyclicTangent_ne_zero hq.size_ge_three q hq.g1 (polygonEventEdge q x) (Prod.ext h1 h2)
    rw [div_self h_nz, Complex.arg_one, neg_zero]
  · have h_edge_y : polygonEventEdge q y = cyclicSuccessor (polygonEventEdge q x) := by
      change polygonEventEdge q (polygonEventSuccessor q hq.g2 x) = _
      rw [h_y]
      rfl
    rw [h_edge_y]
    have hdet :
        (toComplexPoint (cyclicTangent q (polygonEventEdge q x))).re *
          (toComplexPoint (cyclicTangent q (cyclicSuccessor (polygonEventEdge q x)))).im -
        (toComplexPoint (cyclicTangent q (polygonEventEdge q x))).im *
          (toComplexPoint (cyclicTangent q (cyclicSuccessor (polygonEventEdge q x)))).re ≠ 0 := by
      rw [complex_det_eq_planarDet]
      exact cyclic_turn_det_ne_zero hq.size_ge_three q hq.g1 (polygonEventEdge q x)
    have hcancel := reciprocal_turns_cancel_of_det
      (toComplexPoint (cyclicTangent q (polygonEventEdge q x)))
      (toComplexPoint (cyclicTangent q (cyclicSuccessor (polygonEventEdge q x))))
      hdet
    linarith

theorem totalTurn_positivePolygonEventDiagram_reversePolygon
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    totalTurn (positivePolygonEventDiagram (reversePolygon q) (cyclicGeneric_reversePolygon q hq)) =
      -totalTurn (positivePolygonEventDiagram q hq) := by
  unfold totalTurn
  let ev := ((positivePolygonEventDiagram q hq).continuation).trans (positiveArcRevEquiv q hq)
  rw [← Equiv.sum_comp ev, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  obtain ⟨x, rfl⟩ := (eventFin q).surjective e
  exact turn_positivePolygonEventDiagram_reversePolygon q hq x

theorem turnInteger_positivePolygonEventDiagram_reversePolygon
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    turnInteger (positivePolygonEventDiagram (reversePolygon q) (cyclicGeneric_reversePolygon q hq)) =
      -turnInteger (positivePolygonEventDiagram q hq) := by
  apply turnInteger_unique
  rw [totalTurn_positivePolygonEventDiagram_reversePolygon q hq,
    totalTurn_eq_turnInteger (positivePolygonEventDiagram q hq)]
  push_cast
  ring

end PartA_TurnsAndCrossings

namespace HOMFLY

open BranchSignedDiagramIso
open Coefficients

structure ReversedDiagramIso (D E : PLLinkDiagram) where
  arcEquiv : Fin D.nArc ≃ Fin E.nArc
  crossingEquiv : Fin D.nCrossing ≃ Fin E.nCrossing
  branchEquiv : (c : Fin D.nCrossing) → Equiv.Perm (Fin 2)
  incoming_map : ∀ (c : Fin D.nCrossing) (i : Fin 2),
    arcEquiv (D.continuation (D.incoming c i)) = E.incoming (crossingEquiv c) (branchEquiv c i)
  continuation_map : ∀ (e : Fin D.nArc),
    E.continuation (arcEquiv (D.continuation e)) = arcEquiv e
  overBranch_map : ∀ (c : Fin D.nCrossing),
    E.overBranch (crossingEquiv c) = branchEquiv c (D.overBranch c)
  crossingSign_map : ∀ (c : Fin D.nCrossing),
    crossingSign E (crossingEquiv c) = crossingSign D c

namespace ReversedDiagramIso

variable {D E : PLLinkDiagram}

theorem incoming_eq_continuation_symm (I : ReversedDiagramIso D E)
    (c : Fin D.nCrossing) (i : Fin 2) :
    I.arcEquiv (D.incoming c i) =
      E.continuation (E.incoming (I.crossingEquiv c) (I.branchEquiv c i)) := by
  rw [← I.incoming_map c i, I.continuation_map]

theorem continuation_symm_map (I : ReversedDiagramIso D E) (e : Fin D.nArc) :
    I.arcEquiv (D.continuation.symm e) = E.continuation (I.arcEquiv e) := by
  have h := I.continuation_map (D.continuation.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

def symm (I : ReversedDiagramIso D E) : ReversedDiagramIso E D where
  arcEquiv := I.arcEquiv.symm
  crossingEquiv := I.crossingEquiv.symm
  branchEquiv c' := (I.branchEquiv (I.crossingEquiv.symm c')).symm
  incoming_map c' i' := by
    let c := I.crossingEquiv.symm c'
    let i := (I.branchEquiv c).symm i'
    have hc : I.crossingEquiv c = c' := I.crossingEquiv.apply_symm_apply c'
    have hi : I.branchEquiv c i = i' := (I.branchEquiv c).apply_symm_apply i'
    apply I.arcEquiv.injective
    rw [Equiv.apply_symm_apply]
    have h := I.incoming_eq_continuation_symm c i
    rw [hc, hi] at h
    exact h.symm
  continuation_map e' := by
    apply I.arcEquiv.injective
    apply E.continuation.injective
    rw [I.continuation_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  overBranch_map c' := by
    let c := I.crossingEquiv.symm c'
    have hc : I.crossingEquiv c = c' := I.crossingEquiv.apply_symm_apply c'
    have h := I.overBranch_map c
    rw [hc] at h
    change D.overBranch c = (I.branchEquiv c).symm (E.overBranch c')
    rw [h, Equiv.symm_apply_apply]
  crossingSign_map c' := by
    let c := I.crossingEquiv.symm c'
    have hc : I.crossingEquiv c = c' := I.crossingEquiv.apply_symm_apply c'
    exact (I.crossingSign_map c).symm.trans (by rw [hc])

def switch (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    ReversedDiagramIso (switchCrossing D c) (switchCrossing E (I.crossingEquiv c)) where
  arcEquiv := I.arcEquiv
  crossingEquiv := I.crossingEquiv
  branchEquiv := I.branchEquiv
  incoming_map := I.incoming_map
  continuation_map := I.continuation_map
  overBranch_map x := by
    by_cases hx : x = c
    · rw [hx]
      change Function.update E.overBranch (I.crossingEquiv c)
        (otherBranch (E.overBranch (I.crossingEquiv c))) (I.crossingEquiv c) =
        I.branchEquiv c (Function.update D.overBranch c (otherBranch (D.overBranch c)) c)
      rw [Function.update_self, Function.update_self, I.overBranch_map c, branch_other]
    · have hx' : I.crossingEquiv x ≠ I.crossingEquiv c := fun h => hx (I.crossingEquiv.injective h)
      change Function.update E.overBranch (I.crossingEquiv c)
        (otherBranch (E.overBranch (I.crossingEquiv c))) (I.crossingEquiv x) =
        I.branchEquiv x (Function.update D.overBranch c (otherBranch (D.overBranch c)) x)
      rw [Function.update_of_ne hx', Function.update_of_ne hx, I.overBranch_map x]
  crossingSign_map x := by
    by_cases hx : x = c
    · rw [hx]
      exact (crossingSign_switchCrossing E (I.crossingEquiv c)).trans
        ((congrArg Sign.reverse (I.crossingSign_map c)).trans
          (crossingSign_switchCrossing D c).symm)
    · have hx' : I.crossingEquiv x ≠ I.crossingEquiv c := fun h => hx (I.crossingEquiv.injective h)
      exact (crossingSign_switchCrossing_of_ne E (I.crossingEquiv c) (I.crossingEquiv x) hx').trans
        ((I.crossingSign_map x).trans (crossingSign_switchCrossing_of_ne D c x hx).symm)

def otherBranchEquiv : Equiv.Perm (Fin 2) where
  toFun := otherBranch
  invFun := otherBranch
  left_inv := otherBranch_involutive
  right_inv := otherBranch_involutive

@[simp]
theorem otherBranchEquiv_apply (i : Fin 2) : otherBranchEquiv i = otherBranch i := rfl

def retainedEquiv (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    {d : Fin D.nCrossing // d ≠ c} ≃ {d : Fin E.nCrossing // d ≠ I.crossingEquiv c} where
  toFun d := ⟨I.crossingEquiv d.val, fun h => d.property (I.crossingEquiv.injective h)⟩
  invFun d := ⟨I.crossingEquiv.symm d.val, fun h => d.property (by simpa using congrArg I.crossingEquiv h)⟩
  left_inv d := by apply Subtype.ext; simp
  right_inv d := by apply Subtype.ext; simp

def smoothArcEquiv (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    Fin (D.nArc + 2) ≃ Fin (E.nArc + 2) :=
  (_root_.DirectGLSSW.HOMFLY.smoothArcEquiv D).symm.trans
    ((Equiv.sumCongr I.arcEquiv (otherBranchEquiv.trans (I.branchEquiv c))).trans
      (_root_.DirectGLSSW.HOMFLY.smoothArcEquiv E))

def smoothCrossingEquiv (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    Fin (D.nCrossing - 1) ≃ Fin (E.nCrossing - 1) :=
  (_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm.trans
    ((I.retainedEquiv c).trans
      (_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv E (I.crossingEquiv c)))

theorem smooth_code (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) (x : SmoothArcCode D) :
    smoothContinuationGeometryCode E (I.crossingEquiv c)
      ((Equiv.sumCongr I.arcEquiv (otherBranchEquiv.trans (I.branchEquiv c)))
        (smoothContinuationGeometryCode D c x)) =
      (Equiv.sumCongr I.arcEquiv (otherBranchEquiv.trans (I.branchEquiv c))) x := by
  let c' := I.crossingEquiv c
  cases x with
  | inl a =>
    by_cases ha : ∃ i : Fin 2, a = D.incoming c i
    · obtain ⟨i, rfl⟩ := ha
      rw [incoming_code D c i]
      simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply, otherBranchEquiv_apply]
      rw [smoothContinuationGeometryCode_connector,
        ← E.continuation_crossing c' (otherBranch (I.branchEquiv c (otherBranch i))),
        ← branch_other (I.branchEquiv c) (otherBranch i),
        otherBranch_involutive,
        ← I.incoming_eq_continuation_symm c i]
      rfl
    · have hd : ∀ i : Fin 2, a ≠ D.incoming c i := by simpa only [not_exists] using ha
      have hd' : ∀ j : Fin 2, I.arcEquiv (D.continuation a) ≠ E.incoming c' j := by
        intro j h_eq
        let k := (I.branchEquiv c).symm j
        have hk : I.branchEquiv c k = j := (I.branchEquiv c).apply_symm_apply j
        rw [← hk, ← I.incoming_map c k] at h_eq
        exact hd k (D.continuation.injective (I.arcEquiv.injective h_eq))
      rw [smoothContinuationGeometryCode_other_arc D c a hd]
      simp only [Equiv.sumCongr_apply, Sum.map_inl]
      rw [smoothContinuationGeometryCode_other_arc E c' _ hd', I.continuation_map a]
  | inr i =>
    rw [smoothContinuationGeometryCode_connector, ← D.continuation_crossing c (otherBranch i)]
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.trans_apply, otherBranchEquiv_apply]
    rw [I.incoming_map c (otherBranch i), incoming_code E c' (I.branchEquiv c (otherBranch i))]

theorem smooth_continuation (I : ReversedDiagramIso D E) (c : Fin D.nCrossing)
    (e : Fin (D.nArc + 2)) :
    (smoothCrossing E (I.crossingEquiv c)).continuation
      (I.smoothArcEquiv c ((smoothCrossing D c).continuation e)) =
      I.smoothArcEquiv c e := by
  have h := I.smooth_code c ((_root_.DirectGLSSW.HOMFLY.smoothArcEquiv D).symm e)
  simp only [smoothArcEquiv, smoothCrossing, smoothContinuation,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  exact congrArg (_root_.DirectGLSSW.HOMFLY.smoothArcEquiv E) h

def smooth (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    ReversedDiagramIso (smoothCrossing D c) (smoothCrossing E (I.crossingEquiv c)) where
  arcEquiv := I.smoothArcEquiv c
  crossingEquiv := I.smoothCrossingEquiv c
  branchEquiv x := I.branchEquiv ((_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm x).val
  incoming_map x i := by
    obtain ⟨⟨y, hy⟩, rfl⟩ := (_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).surjective x
    have hnot : ∀ j : Fin 2, D.incoming y i ≠ D.incoming c j :=
      fun j => incoming_ne_of_crossing_ne D c y hy i j
    rw [Gemini.smoothCrossing_incoming_retained D c y hy i,
      Gemini.smooth_step_of_ne D c (D.incoming y i) hnot]
    simpa [smoothArcEquiv, smoothCrossingEquiv, smoothCrossing, smoothIncoming, retainedEquiv] using
      congrArg (fun e => _root_.DirectGLSSW.HOMFLY.smoothArcEquiv E (Sum.inl e)) (I.incoming_map y i)
  continuation_map := I.smooth_continuation c
  overBranch_map x := by
    simpa [smoothCrossingEquiv, smoothCrossing, retainedEquiv] using
      I.overBranch_map ((_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm x).val
  crossingSign_map x := by
    let od := (_root_.DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm x
    let oe := I.retainedEquiv c od
    have hd := crossingSign_smoothRetained D c od.val od.property
    have he := crossingSign_smoothRetained E (I.crossingEquiv c) oe.val oe.property
    calc
      crossingSign (smoothCrossing E (I.crossingEquiv c)) (I.smoothCrossingEquiv c x) =
        crossingSign E oe.val := he
      _ = crossingSign E (I.crossingEquiv od.val) := rfl
      _ = crossingSign D od.val := I.crossingSign_map od.val
      _ = crossingSign (smoothCrossing D c) x := by simpa [od] using hd.symm

end ReversedDiagramIso

end HOMFLY

section PartB_PositivePolygonReversedIso

variable {n : ℕ}

def crossingBranchPerm (q : Fin n → PlanarPoint ℝ) (c : PolygonCrossing q) :
    Equiv.Perm (Fin 2) :=
  if edgeRev c.val.1 < edgeRev c.val.2 then
    Equiv.refl (Fin 2)
  else
    HOMFLY.ReversedDiagramIso.otherBranchEquiv

theorem eventVertexRev_visit (q : Fin n → PlanarPoint ℝ) (c : PolygonCrossing q) (i : Fin 2) :
    eventVertexRev q (visit q c i) =
      visit (reversePolygon q) (crossingRevEquiv q c) (crossingBranchPerm q c i) := by
  rw [visit, visit, eventVertexRev_inr]
  unfold visitRevEquiv visitRevMap crossingBranchPerm
  by_cases h : edgeRev c.val.1 < edgeRev c.val.2 <;> fin_cases i <;> simp [h, otherBranch]

theorem positivePolygonEventDiagram_incoming (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (c : PolygonCrossing q) (i : Fin 2) :
    (positivePolygonEventDiagram q hq).incoming (crossingFin q c) i =
      eventFin q (incoming q hq c i) := by
  simp only [positivePolygonEventDiagram, positiveDiagram, polygonEventDiagram,
    incomingIndex, Equiv.symm_apply_apply]

theorem positivePolygonEventDiagram_continuation_incoming
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (c : PolygonCrossing q) (i : Fin 2) :
    (positivePolygonEventDiagram q hq).continuation
      ((positivePolygonEventDiagram q hq).incoming (crossingFin q c) i) =
      eventFin q (visit q c i) := by
  rw [positivePolygonEventDiagram_incoming]
  change (polygonEventDiagram q hq).continuation (eventFin q (incoming q hq c i)) = _
  rw [polygonEventDiagram_continuation, incoming, Equiv.apply_symm_apply]

def positivePolygonReversedDiagramIso (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    HOMFLY.ReversedDiagramIso
      (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram (reversePolygon q) (cyclicGeneric_reversePolygon q hq)) where
  arcEquiv := positiveArcRevEquiv q hq
  crossingEquiv :=
    (crossingFin q).symm.trans
      ((crossingRevEquiv q).trans (crossingFin (reversePolygon q)))
  branchEquiv c := crossingBranchPerm q ((crossingFin q).symm c)
  incoming_map c i := by
    let hqr := cyclicGeneric_reversePolygon q hq
    obtain ⟨x, rfl⟩ := (crossingFin q).surjective c
    change positiveArcRevEquiv q hq
      ((positivePolygonEventDiagram q hq).continuation
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q x) i)) =
      (positivePolygonEventDiagram (reversePolygon q) hqr).incoming
        (crossingFin (reversePolygon q) (crossingRevEquiv q ((crossingFin q).symm (crossingFin q x))))
        (crossingBranchPerm q ((crossingFin q).symm (crossingFin q x)) i)
    rw [Equiv.symm_apply_apply,
      positivePolygonEventDiagram_continuation_incoming q hq x i,
      positiveArcRevEquiv_eventFin q hq (visit q x i),
      positivePolygonEventDiagram_incoming (reversePolygon q) hqr
        (crossingRevEquiv q x) (crossingBranchPerm q x i)]
    congr 1
    rw [incoming, ← eventVertexRev_visit q x i]
    exact (Equiv.eq_symm_apply _).mpr
      (polygonEventSuccessor_reversePolygon_intertwine q hq (visit q x i))
  continuation_map e := by
    let hqr := cyclicGeneric_reversePolygon q hq
    obtain ⟨x, rfl⟩ := (eventFin q).surjective e
    have hcont : (positivePolygonEventDiagram q hq).continuation (eventFin q x) =
        eventFin q (polygonEventSuccessor q hq.g2 x) :=
      polygonEventDiagram_continuation q hq x
    rw [hcont, positiveArcRevEquiv_eventFin, positiveArcRevEquiv_eventFin]
    change (polygonEventDiagram (reversePolygon q) hqr).continuation _ = _
    rw [polygonEventDiagram_continuation,
      polygonEventSuccessor_reversePolygon_intertwine q hq (polygonEventSuccessor q hq.g2 x)]
  overBranch_map c := by
    let hqr := cyclicGeneric_reversePolygon q hq
    obtain ⟨x, rfl⟩ := (crossingFin q).surjective c
    change (positivePolygonEventDiagram (reversePolygon q) hqr).overBranch
      (crossingFin (reversePolygon q) (crossingRevEquiv q ((crossingFin q).symm (crossingFin q x)))) =
      crossingBranchPerm q ((crossingFin q).symm (crossingFin q x))
        ((positivePolygonEventDiagram q hq).overBranch (crossingFin q x))
    rw [Equiv.symm_apply_apply,
      positivePolygonEventDiagram_overBranch (reversePolygon q) hqr (crossingRevEquiv q x),
      positivePolygonEventDiagram_overBranch q hq x]
    unfold crossingBranchPerm crossingRevEquiv crossingRevMap
    by_cases hlt : edgeRev x.val.1 < edgeRev x.val.2
    · simp only [Equiv.coe_fn_mk, hlt, ↓reduceIte, Equiv.refl_apply,
        min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt),
        cyclicTangent_reversePolygon_edgeRev]
      have hdet : planarDet (-cyclicTangent q x.val.1) (-cyclicTangent q x.val.2) =
          planarDet (cyclicTangent q x.val.1) (cyclicTangent q x.val.2) := by
        simp [planarDet]
      rw [hdet]
    · simp only [Equiv.coe_fn_mk, hlt, ↓reduceIte, HOMFLY.ReversedDiagramIso.otherBranchEquiv_apply,
        min_eq_right (not_lt.mp hlt), max_eq_left (not_lt.mp hlt),
        cyclicTangent_reversePolygon_edgeRev]
      have hdet : planarDet (-cyclicTangent q x.val.2) (-cyclicTangent q x.val.1) =
          -planarDet (cyclicTangent q x.val.1) (cyclicTangent q x.val.2) := by
        simp [planarDet]; ring
      rw [hdet]
      have hnz : planarDet (cyclicTangent q x.val.1) (cyclicTangent q x.val.2) ≠ 0 :=
        crossing_transverse hq.size_ge_three q hq.g1 x
      by_cases hd : 0 < planarDet (cyclicTangent q x.val.1) (cyclicTangent q x.val.2)
      · have hnd : ¬ (0 < -planarDet (cyclicTangent q x.val.1) (cyclicTangent q x.val.2)) := by
          linarith
        simp [hd, hnd, otherBranch]
      · have hnd : 0 < -planarDet (cyclicTangent q x.val.1) (cyclicTangent q x.val.2) := by
          rcases lt_or_gt_of_ne hnz with hneg | hpos
          · linarith
          · exact False.elim (hd hpos)
        simp [hd, hnd, otherBranch]
  crossingSign_map c := by
    let hqr := cyclicGeneric_reversePolygon q hq
    exact (positiveDiagram_crossingSign (polygonEventDiagram (reversePolygon q) hqr) _).trans
      (positiveDiagram_crossingSign (polygonEventDiagram q hq) c).symm

end PartB_PositivePolygonReversedIso

namespace HOMFLY

open BranchSignedDiagramIso
open Coefficients

attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  PermutationOrbits.componentFintype D.continuation

namespace ReversedDiagramIso

variable {D E : PLLinkDiagram}

def componentEquiv (I : ReversedDiagramIso D E) :
    diagramComponent D ≃ diagramComponent E :=
  componentEquivOfReverseIntertwining I.arcEquiv D.continuation E.continuation I.continuation_map

theorem componentEquiv_componentOf (I : ReversedDiagramIso D E) (e : Fin D.nArc) :
    I.componentEquiv (componentOf D.continuation e) =
      componentOf E.continuation (I.arcEquiv e) :=
  componentEquivOfReverseIntertwining_componentOf
    I.arcEquiv D.continuation E.continuation I.continuation_map e

theorem componentCount_eq (I : ReversedDiagramIso D E) :
    diagramComponentCount E = diagramComponentCount D :=
  (componentCount_eq_of_reverse_intertwining
    I.arcEquiv D.continuation E.continuation I.continuation_map).symm

theorem nArc_eq (I : ReversedDiagramIso D E) :
    E.nArc = D.nArc := by
  simpa using (Fintype.card_congr I.arcEquiv).symm

theorem descendingUnlinkValue_eq (I : ReversedDiagramIso D E) :
    descendingUnlinkValue E = descendingUnlinkValue D := by
  unfold descendingUnlinkValue
  rw [I.nArc_eq, I.componentCount_eq]

theorem sameCycle_iff (I : ReversedDiagramIso D E) (x y : Fin D.nArc) :
    E.continuation.SameCycle (I.arcEquiv x) (I.arcEquiv y) ↔
      D.continuation.SameCycle x y :=
  sameCycle_iff_of_reverse_intertwining
    I.arcEquiv D.continuation E.continuation I.continuation_map x y

theorem sameCycle_continuation_self (G : PLLinkDiagram) (e : Fin G.nArc) :
    G.continuation.SameCycle (G.continuation e) e :=
  Equiv.Perm.SameCycle.symm ⟨(1 : ℤ), by simp⟩

theorem sameCycle_incoming_iff (I : ReversedDiagramIso D E)
    (c : Fin D.nCrossing) (i j : Fin 2) :
    E.continuation.SameCycle
      (E.incoming (I.crossingEquiv c) (I.branchEquiv c i))
      (E.incoming (I.crossingEquiv c) (I.branchEquiv c j)) ↔
      D.continuation.SameCycle (D.incoming c i) (D.incoming c j) := by
  rw [← I.incoming_map c i, ← I.incoming_map c j, I.sameCycle_iff]
  constructor
  · intro h
    exact (sameCycle_continuation_self D (D.incoming c i)).symm.trans
      (h.trans (sameCycle_continuation_self D (D.incoming c j)))
  · intro h
    exact (sameCycle_continuation_self D (D.incoming c i)).trans
      (h.trans (sameCycle_continuation_self D (D.incoming c j)).symm)

theorem sameCycle_crossing_iff (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    E.continuation.SameCycle
      (E.incoming (I.crossingEquiv c) 0)
      (E.incoming (I.crossingEquiv c) 1) ↔
      D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1) := by
  have h := I.sameCycle_incoming_iff c 0 1
  generalize hb : I.branchEquiv c 0 = b0 at h
  have hb1 : I.branchEquiv c 1 = otherBranch b0 := by
    rw [← hb]
    exact branch_other (I.branchEquiv c) 0
  rw [hb1] at h
  fin_cases b0
  · exact h
  · exact ⟨fun hE => h.mp hE.symm, fun hD => (h.mpr hD).symm⟩

theorem componentEquiv_incoming (I : ReversedDiagramIso D E)
    (c : Fin D.nCrossing) (i : Fin 2) :
    I.componentEquiv (componentOf D.continuation (D.incoming c i)) =
      componentOf E.continuation (E.incoming (I.crossingEquiv c) (I.branchEquiv c i)) := by
  rw [← I.incoming_map c i, ← I.componentEquiv_componentOf]
  congr 1
  exact ((componentOf_eq_iff D.continuation _ _).mpr
    (sameCycle_continuation_self D (D.incoming c i))).symm

theorem pow_continuation_cancel (I : ReversedDiagramIso D E) (e : Fin D.nArc) (m : ℕ) :
    (E.continuation ^ m) (I.arcEquiv ((D.continuation ^ m) e)) = I.arcEquiv e :=
  intertwine_pow_cancel I.arcEquiv D.continuation E.continuation I.continuation_map m e

theorem pow_sub_step (I : ReversedDiagramIso D E) (a : Fin D.nArc) {t L : ℕ} (ht : t ≤ L) :
    (E.continuation ^ (L - t)) (I.arcEquiv (D.continuation ((D.continuation ^ L) a))) =
      I.arcEquiv (D.continuation ((D.continuation ^ t) a)) := by
  have h1 : D.continuation ((D.continuation ^ L) a) =
      (D.continuation ^ (L - t)) (D.continuation ((D.continuation ^ t) a)) := by
    rw [← Equiv.Perm.mul_apply D.continuation (D.continuation ^ L), ← pow_succ',
      ← Equiv.Perm.mul_apply D.continuation (D.continuation ^ t), ← pow_succ',
      ← Equiv.Perm.mul_apply (D.continuation ^ (L - t)), ← pow_add,
      show L - t + (t + 1) = L + 1 by omega]
  rw [h1]
  exact I.pow_continuation_cancel (D.continuation ((D.continuation ^ t) a)) (L - t)

theorem fibre_card_incoming_eq (I : ReversedDiagramIso D E)
    (c : Fin D.nCrossing) (i : Fin 2) :
    Fintype.card (Fibre E.continuation
      (componentOf E.continuation (E.incoming (I.crossingEquiv c) (I.branchEquiv c i)))) =
      Fintype.card (Fibre D.continuation
        (componentOf D.continuation (D.incoming c i))) := by
  have h1 : Fintype.card (Fibre E.continuation
      (componentOf E.continuation (I.arcEquiv (D.continuation (D.incoming c i))))) =
      Fintype.card (Fibre D.continuation
        (componentOf D.continuation (D.continuation (D.incoming c i)))) :=
    (Fintype.card_congr (fibreEquivOfReverseIntertwining
      I.arcEquiv D.continuation E.continuation I.continuation_map
      (D.continuation (D.incoming c i)))).symm
  have hcomp : componentOf D.continuation (D.continuation (D.incoming c i)) =
      componentOf D.continuation (D.incoming c i) :=
    (componentOf_eq_iff D.continuation _ _).mpr
      (sameCycle_continuation_self D (D.incoming c i))
  rw [I.incoming_map c i, hcomp] at h1
  exact h1

theorem pivotSwitchFactor_eq (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    pivotSwitchFactor E (I.crossingEquiv c) = pivotSwitchFactor D c := by
  unfold pivotSwitchFactor
  rw [I.crossingSign_map c]

theorem pivotSmoothFactor_eq (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) :
    pivotSmoothFactor E (I.crossingEquiv c) = pivotSmoothFactor D c := by
  unfold pivotSmoothFactor
  rw [I.crossingSign_map c]

theorem candidateEvaluator_eq_of_switch_and_smooth (I : ReversedDiagramIso D E)
    (hD : 0 < D.nArc) (hE : 0 < E.nArc) (c : Fin D.nCrossing)
    (h_sw : Gemini.candidateEvaluator (switchCrossing E (I.crossingEquiv c)) hE =
      Gemini.candidateEvaluator (switchCrossing D c) hD)
    (h_sm : Gemini.candidateEvaluator (smoothCrossing E (I.crossingEquiv c))
        (by change 0 < E.nArc + 2; omega) =
      Gemini.candidateEvaluator (smoothCrossing D c) (by change 0 < D.nArc + 2; omega)) :
    Gemini.candidateEvaluator E hE = Gemini.candidateEvaluator D hD := by
  rw [GeminiLowest.candidateEvaluator_pivot_expansion E hE (I.crossingEquiv c),
    GeminiLowest.candidateEvaluator_pivot_expansion D hD c,
    I.pivotSwitchFactor_eq c, I.pivotSmoothFactor_eq c, h_sw, h_sm]

private theorem fin_cast_val {m k : ℕ} (h : m = k) (x : Fin m) :
    (Equiv.cast (congrArg Fin h) x).val = x.val := by
  subst h
  rfl

def reversedComponentTraversal (I : ReversedDiagramIso D E) (U : BasedTraversal D) :
    BasedTraversal E where
  componentIndex :=
    I.componentEquiv.symm.trans
      (U.componentIndex.trans (Equiv.cast (congrArg Fin I.componentCount_eq.symm)))
  baseArc C' := Classical.choice (fibreNonempty E.continuation C')

theorem reversedComponentTraversal_componentIndex_incoming_val
    (I : ReversedDiagramIso D E) (U : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    ((I.reversedComponentTraversal U).componentIndex
      (componentOf E.continuation (E.incoming (I.crossingEquiv c) (I.branchEquiv c i)))).val =
      (U.componentIndex (componentOf D.continuation (D.incoming c i))).val := by
  rw [← I.componentEquiv_incoming c i]
  change (Equiv.cast (congrArg Fin I.componentCount_eq.symm)
    (U.componentIndex (I.componentEquiv.symm
      (I.componentEquiv (componentOf D.continuation (D.incoming c i)))))).val = _
  rw [Equiv.symm_apply_apply]
  exact fin_cast_val I.componentCount_eq.symm _

end ReversedDiagramIso

theorem firstVisitedBranch_eq_of_rankBefore {G : PLLinkDiagram} (T : BasedTraversal G)
    (c : Fin G.nCrossing) (i : Fin 2)
    (h : rankBefore (visitRank T (G.incoming c i))
      (visitRank T (G.incoming c (otherBranch i)))) :
    firstVisitedBranch T c = i := by
  have hfirst := firstVisitedBranch_is_first T c
  generalize hf : firstVisitedBranch T c = j at hfirst
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (rankBefore_asymm h hfirst)
  · exact False.elim (rankBefore_asymm h hfirst)
  · rfl

theorem rankBefore_of_topProtected_of_not_topProtected
    (G : PLLinkDiagram) (U : BasedTraversal G) (c : Fin G.nCrossing) (i : Fin 2)
    (a b : Fin G.nArc)
    (ha : Gemini.TopProtected G U c i a)
    (hb : ¬ Gemini.TopProtected G U c i b) :
    rankBefore (visitRank U a) (visitRank U b) := by
  have hb1 : ¬ rankBefore (visitRank U b) (visitRank U (G.incoming c (otherBranch i))) :=
    fun h => hb (Or.inl h)
  have hb2 : b ≠ G.incoming c (otherBranch i) :=
    fun h => hb (Or.inr h)
  have hne : visitRank U (G.incoming c (otherBranch i)) ≠ visitRank U b :=
    fun h => hb2 (visitRank_injective U h.symm)
  have hlt_b : rankBefore (visitRank U (G.incoming c (otherBranch i))) (visitRank U b) :=
    (rankBefore_total_of_ne hne).resolve_right hb1
  rcases ha with hlt_a | rfl
  · exact Gemini.rankBefore_trans hlt_a hlt_b
  · exact hlt_b

theorem pivotSwitchFactor_add_pivotSmoothFactor_mul_unlinkFactor
    (G : PLLinkDiagram) (c : Fin G.nCrossing) :
    pivotSwitchFactor G c + pivotSmoothFactor G c * unlinkFactor = 1 := by
  unfold pivotSwitchFactor pivotSmoothFactor unlinkFactor
  cases crossingSign G c
  · calc
      aMonomial * aMonomial + -(aMonomial * zMonomial) * ((aMonomial - aInvMonomial) * zInvMonomial) =
          aMonomial * aMonomial - aMonomial * (zMonomial * zInvMonomial) * (aMonomial - aInvMonomial) := by ring
      _ = aMonomial * aMonomial - aMonomial * 1 * (aMonomial - aInvMonomial) := by
          rw [zMonomial_mul_zInvMonomial]
      _ = aMonomial * aInvMonomial := by ring
      _ = 1 := aMonomial_mul_aInvMonomial
  · calc
      aInvMonomial * aInvMonomial + (aInvMonomial * zMonomial) * ((aMonomial - aInvMonomial) * zInvMonomial) =
          aInvMonomial * aInvMonomial + aInvMonomial * (zMonomial * zInvMonomial) * (aMonomial - aInvMonomial) := by ring
      _ = aInvMonomial * aInvMonomial + aInvMonomial * 1 * (aMonomial - aInvMonomial) := by
          rw [zMonomial_mul_zInvMonomial]
      _ = aMonomial * aInvMonomial := by ring
      _ = 1 := aMonomial_mul_aInvMonomial

theorem candidateEvaluator_topLoop_deletion_not_bad
    (G : PLLinkDiagram) (hG : 0 < G.nArc)
    (U : BasedTraversal G) (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (hbad : ∀ y ∈ badCrossings U, ∀ j : Fin 2, ¬ Gemini.TopProtected G U c i (G.incoming y j)) :
    unlinkFactor * Gemini.candidateEvaluator G hG =
      Gemini.candidateEvaluator (smoothCrossing G c) (by change 0 < G.nArc + 2; omega) := by
  have h1 := Gemini.topLoop_deletion
    (Gemini.all_lowerCrossingEvaluatorSkeinIH G.nCrossing) G le_rfl U c hself i hroot hbad
  rw [Gemini.candidateEvaluator_eq_traversal Gemini.all_lowerCrossingEvaluatorSkeinIH G hG U,
    Gemini.candidateEvaluator_eq_traversal Gemini.all_lowerCrossingEvaluatorSkeinIH
      (smoothCrossing G c) (by change 0 < G.nArc + 2; omega) (smoothChildBasedTraversal G c)]
  exact h1

theorem candidateEvaluator_topLoop_deletion_any_c
    (G : PLLinkDiagram) (hG : 0 < G.nArc)
    (U : BasedTraversal G) (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2)
    (hroot : (U.baseArc (componentOf G.continuation (G.incoming c i))).val = G.incoming c i)
    (hbad : ∀ y ∈ badCrossings U, y ≠ c → ∀ j : Fin 2, ¬ Gemini.TopProtected G U c i (G.incoming y j)) :
    unlinkFactor * Gemini.candidateEvaluator G hG =
      Gemini.candidateEvaluator (smoothCrossing G c) (by change 0 < G.nArc + 2; omega) := by
  by_cases hc : c ∈ badCrossings U
  · have hbad_sw : ∀ y ∈ badCrossings (switchTraversal U c), ∀ j : Fin 2,
        ¬ Gemini.TopProtected (switchCrossing G c) (switchTraversal U c) c i
          ((switchCrossing G c).incoming y j) := by
      intro y hy j
      rw [badCrossings_switch_erase U c hc] at hy
      exact hbad y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy) j
    have hsw := candidateEvaluator_topLoop_deletion_not_bad
      (switchCrossing G c) hG (switchTraversal U c) c hself i hroot hbad_sw
    have hiso : Gemini.candidateEvaluator (smoothCrossing (switchCrossing G c) c)
        (by change 0 < G.nArc + 2; omega) =
        Gemini.candidateEvaluator (smoothCrossing G c) (by change 0 < G.nArc + 2; omega) :=
      Gemini.candidateEvaluator_signedDiagramIso Gemini.all_lowerCrossingEvaluatorSkeinIH
        (smoothCrossing (switchCrossing G c) c) (smoothCrossing G c)
        (by change 0 < G.nArc + 2; omega) (by change 0 < G.nArc + 2; omega)
        (smoothSwitchSameSignedDiagramIso G c)
    rw [hiso] at hsw
    calc
      unlinkFactor * Gemini.candidateEvaluator G hG =
          pivotSwitchFactor G c * (unlinkFactor * Gemini.candidateEvaluator (switchCrossing G c) hG) +
            pivotSmoothFactor G c * unlinkFactor *
              Gemini.candidateEvaluator (smoothCrossing G c) (by change 0 < G.nArc + 2; omega) := by
        rw [GeminiLowest.candidateEvaluator_pivot_expansion G hG c]
        ring
      _ = (pivotSwitchFactor G c + pivotSmoothFactor G c * unlinkFactor) *
            Gemini.candidateEvaluator (smoothCrossing G c) (by change 0 < G.nArc + 2; omega) := by
        rw [hsw]
        ring
      _ = Gemini.candidateEvaluator (smoothCrossing G c) (by change 0 < G.nArc + 2; omega) := by
        rw [pivotSwitchFactor_add_pivotSmoothFactor_mul_unlinkFactor G c, one_mul]
  · exact candidateEvaluator_topLoop_deletion_not_bad G hG U c hself i hroot
      (fun y hy j => hbad y hy (fun h => hc (h ▸ hy)) j)

def topComponentWeight (G : PLLinkDiagram) (c : Fin G.nCrossing) (i : Fin 2)
    (C : diagramComponent G) : ℕ :=
  if C = componentOf G.continuation (G.incoming c i) then 0 else 1

def topComponentBaseArc (G : PLLinkDiagram) (c : Fin G.nCrossing) (i : Fin 2)
    (C : diagramComponent G) :
    {e : Fin G.nArc // componentOf G.continuation e = C} :=
  if h : C = componentOf G.continuation (G.incoming c i) then
    ⟨G.incoming c i, h.symm⟩
  else
    Classical.choice (fibreNonempty G.continuation C)

def topComponentTraversal (G : PLLinkDiagram) (c : Fin G.nCrossing) (i : Fin 2) :
    BasedTraversal G where
  componentIndex := Gemini.equivFinOfWeight (topComponentWeight G c i)
  baseArc := topComponentBaseArc G c i

def loopLength (G : PLLinkDiagram) (c : Fin G.nCrossing) (i : Fin 2) : ℕ :=
  visitPosition (topComponentTraversal G c i) (G.incoming c (otherBranch i))

theorem topComponentTraversal_root (G : PLLinkDiagram) (c : Fin G.nCrossing) (i : Fin 2) :
    ((topComponentTraversal G c i).baseArc
      (componentOf G.continuation (G.incoming c i))).val = G.incoming c i := by
  dsimp [topComponentTraversal, topComponentBaseArc]
  rw [dif_pos rfl]

@[simp]
theorem topComponentTraversal_switch (G : PLLinkDiagram) (c x : Fin G.nCrossing) (i : Fin 2) :
    switchTraversal (topComponentTraversal G c i) x =
      topComponentTraversal (switchCrossing G x) c i := rfl

@[simp]
theorem loopLength_switch (G : PLLinkDiagram) (c x : Fin G.nCrossing) (i : Fin 2) :
    loopLength (switchCrossing G x) c i = loopLength G c i := rfl

theorem topProtected_topComponentTraversal_iff
    (G : PLLinkDiagram) (c : Fin G.nCrossing)
    (hself : G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (i : Fin 2) (b : Fin G.nArc) :
    Gemini.TopProtected G (topComponentTraversal G c i) c i b ↔
      ∃ t ≤ loopLength G c i, (G.continuation ^ t) (G.incoming c i) = b := by
  let U := topComponentTraversal G c i
  have hroot := topComponentTraversal_root G c i
  have hcomp_d1 : componentOf G.continuation (G.incoming c (otherBranch i)) =
      componentOf G.continuation (G.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle G c hself i).symm
  constructor
  · intro hb
    have hle_idx := Gemini.topProtected_component_le G U c hself i b hb
    have hcomp_b : componentOf G.continuation b =
        componentOf G.continuation (G.incoming c i) :=
      Classical.byContradiction fun hne => by
        have hlt_w : topComponentWeight G c i (componentOf G.continuation (G.incoming c i)) <
            topComponentWeight G c i (componentOf G.continuation b) := by
          simp [topComponentWeight, hne]
        have hlt_idx : U.componentIndex (componentOf G.continuation (G.incoming c i)) <
            U.componentIndex (componentOf G.continuation b) :=
          Gemini.equivFinOfWeight_lt_of_lt (topComponentWeight G c i) hlt_w
        exact not_lt_of_ge hle_idx hlt_idx
    have hle_vp : visitPosition U b ≤ loopLength G c i :=
      (Gemini.topProtected_same_component_iff G U c hself i b hcomp_b).mp hb
    refine ⟨visitPosition U b, hle_vp, ?_⟩
    have hrec := visitPosition_reconstruct U b
    rwa [hcomp_b, hroot] at hrec
  · rintro ⟨t, ht, rfl⟩
    have hd1 : Gemini.TopProtected G U c i (G.incoming c (otherBranch i)) :=
      Gemini.topProtected_d1 G U c i
    have hp := Gemini.topProtected_of_pow_le G U c i (G.incoming c (otherBranch i)) hd1 t ht
    rwa [hcomp_d1, hroot] at hp

theorem loopLength_lt_of_pow_le
    (D : PLLinkDiagram) (c y : Fin D.nCrossing) (i j : Fin 2)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    {t₁ t₂ : ℕ} (ht₁ : t₁ ≤ t₂)
    (ht₂ : t₂ < loopLength D c i)
    (hy₁ : (D.continuation ^ t₁) (D.incoming c i) = D.incoming y j)
    (hy₂ : (D.continuation ^ t₂) (D.incoming c i) = D.incoming y (otherBranch j)) :
    D.continuation.SameCycle (D.incoming y 0) (D.incoming y 1) ∧
      loopLength D y j < loopLength D c i := by
  have hdiff : (D.continuation ^ (t₂ - t₁)) (D.incoming y j) = D.incoming y (otherBranch j) := by
    rw [← hy₁, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel ht₁, hy₂]
  have hsc_j : D.continuation.SameCycle (D.incoming y j) (D.incoming y (otherBranch j)) :=
    ⟨((t₂ - t₁ : ℕ) : ℤ), by simpa [zpow_natCast] using hdiff⟩
  have hsc : D.continuation.SameCycle (D.incoming y 0) (D.incoming y 1) := by
    fin_cases j
    · exact hsc_j
    · exact hsc_j.symm
  have hcomp_y : componentOf D.continuation (D.incoming y j) =
      componentOf D.continuation (D.incoming c i) := by
    rw [← hy₁]
    exact componentOf_pow_apply D.continuation t₁ (D.incoming c i)
  have hcomp_d1 : componentOf D.continuation (D.incoming c (otherBranch i)) =
      componentOf D.continuation (D.incoming c i) :=
    (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle D c hself i).symm
  have hlt_card : loopLength D c i <
      Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming y j))) := by
    have h := Gemini.visitPosition_lt_card
      (topComponentTraversal D c i) (D.incoming c (otherBranch i))
    rwa [hcomp_d1, ← hcomp_y] at h
  have hvp : loopLength D y j = t₂ - t₁ :=
    Gemini.visitPosition_eq_of_pow (topComponentTraversal D y j)
      (D.incoming y j) (D.incoming y (otherBranch j)) (t₂ - t₁)
      (topComponentTraversal_root D y j) (by omega) hdiff
  exact ⟨hsc, by omega⟩

theorem not_both_topProtected_of_minimal_loopLength
    (D : PLLinkDiagram) (c y : Fin D.nCrossing) (i : Fin 2)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hmin : ∀ (z : Fin D.nCrossing) (k : Fin 2),
      D.continuation.SameCycle (D.incoming z 0) (D.incoming z 1) →
      loopLength D c i ≤ loopLength D z k)
    (hyc : y ≠ c)
    (h0 : Gemini.TopProtected D (topComponentTraversal D c i) c i (D.incoming y 0))
    (h1 : Gemini.TopProtected D (topComponentTraversal D c i) c i (D.incoming y 1)) :
    False := by
  obtain ⟨t₀, ht₀, hy₀⟩ := (topProtected_topComponentTraversal_iff D c hself i (D.incoming y 0)).mp h0
  obtain ⟨t₁, ht₁, hy₁⟩ := (topProtected_topComponentTraversal_iff D c hself i (D.incoming y 1)).mp h1
  let L := loopLength D c i
  have hL_eq : (D.continuation ^ L) (D.incoming c i) = D.incoming c (otherBranch i) := by
    have hcomp_d1 : componentOf D.continuation (D.incoming c (otherBranch i)) =
        componentOf D.continuation (D.incoming c i) :=
      (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle D c hself i).symm
    have hrec := visitPosition_reconstruct
      (topComponentTraversal D c i) (D.incoming c (otherBranch i))
    rwa [hcomp_d1, topComponentTraversal_root D c i] at hrec
  have ht₀_ne : t₀ ≠ L := by
    intro hEq
    rw [hEq, hL_eq] at hy₀
    exact incoming_ne_of_crossing_ne D c y hyc 0 (otherBranch i) hy₀.symm
  have ht₁_ne : t₁ ≠ L := by
    intro hEq
    rw [hEq, hL_eq] at hy₁
    exact incoming_ne_of_crossing_ne D c y hyc 1 (otherBranch i) hy₁.symm
  have ht₀_lt : t₀ < L := lt_of_le_of_ne ht₀ ht₀_ne
  have ht₁_lt : t₁ < L := lt_of_le_of_ne ht₁ ht₁_ne
  rcases le_total t₀ t₁ with hle | hle
  · obtain ⟨hy_sc, hy_lt⟩ := loopLength_lt_of_pow_le D c y i 0 hself hle ht₁_lt hy₀ hy₁
    exact not_lt_of_ge (hmin y 0 hy_sc) hy_lt
  · obtain ⟨hy_sc, hy_lt⟩ := loopLength_lt_of_pow_le D c y i 1 hself hle ht₀_lt hy₁ hy₀
    exact not_lt_of_ge (hmin y 1 hy_sc) hy_lt

theorem ReversedDiagramIso.loopLength_eq {D E : PLLinkDiagram}
    (I : ReversedDiagramIso D E) (c : Fin D.nCrossing) (i : Fin 2)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    loopLength E (I.crossingEquiv c) (I.branchEquiv c (otherBranch i)) =
      loopLength D c i := by
  let c' := I.crossingEquiv c
  let i' := I.branchEquiv c (otherBranch i)
  let L := loopLength D c i
  have hL_eq : (D.continuation ^ L) (D.incoming c i) = D.incoming c (otherBranch i) := by
    have hcomp_d1 : componentOf D.continuation (D.incoming c (otherBranch i)) =
        componentOf D.continuation (D.incoming c i) :=
      (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle D c hself i).symm
    have hrec := visitPosition_reconstruct
      (topComponentTraversal D c i) (D.incoming c (otherBranch i))
    rwa [hcomp_d1, topComponentTraversal_root D c i] at hrec
  have hstep := I.pow_sub_step (D.incoming c i) (Nat.zero_le L)
  rw [Nat.sub_zero, hL_eq, I.incoming_map c (otherBranch i), pow_zero,
    Equiv.Perm.one_apply, I.incoming_map c i] at hstep
  have hother : I.branchEquiv c i = otherBranch i' := by
    change I.branchEquiv c i = otherBranch (I.branchEquiv c (otherBranch i))
    rw [← branch_other (I.branchEquiv c) (otherBranch i), otherBranch_involutive]
  rw [hother] at hstep
  have hcard_E : Fintype.card (Fibre E.continuation
      (componentOf E.continuation (E.incoming c' i'))) =
      Fintype.card (Fibre D.continuation
        (componentOf D.continuation (D.incoming c (otherBranch i)))) :=
    I.fibre_card_incoming_eq c (otherBranch i)
  have hlt_L : L < Fintype.card (Fibre E.continuation
      (componentOf E.continuation (E.incoming c' i'))) := by
    rw [hcard_E]
    exact Gemini.visitPosition_lt_card
      (topComponentTraversal D c i) (D.incoming c (otherBranch i))
  exact Gemini.visitPosition_eq_of_pow (topComponentTraversal E c' i')
    (E.incoming c' i') (E.incoming c' (otherBranch i')) L
    (topComponentTraversal_root E c' i') hlt_L hstep

theorem ReversedDiagramIso.topProtected_incoming_iff {D E : PLLinkDiagram}
    (I : ReversedDiagramIso D E) (c y : Fin D.nCrossing) (i j : Fin 2)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hyc : y ≠ c) :
    let c' := I.crossingEquiv c
    let i' := I.branchEquiv c (otherBranch i)
    Gemini.TopProtected E (topComponentTraversal E c' i') c' i'
      (E.incoming (I.crossingEquiv y) (I.branchEquiv y j)) ↔
      Gemini.TopProtected D (topComponentTraversal D c i) c i (D.incoming y j) := by
  intro c' i'
  have hself_E : E.continuation.SameCycle (E.incoming c' 0) (E.incoming c' 1) :=
    (I.sameCycle_crossing_iff c).mpr hself
  rw [topProtected_topComponentTraversal_iff E c' hself_E i',
    topProtected_topComponentTraversal_iff D c hself i,
    I.loopLength_eq c i hself]
  let L := loopLength D c i
  have hL_eq : (D.continuation ^ L) (D.incoming c i) = D.incoming c (otherBranch i) := by
    have hcomp_d1 : componentOf D.continuation (D.incoming c (otherBranch i)) =
        componentOf D.continuation (D.incoming c i) :=
      (componentOf_eq_iff _ _ _).mpr (rootCut_sameCycle D c hself i).symm
    have hrec := visitPosition_reconstruct
      (topComponentTraversal D c i) (D.incoming c (otherBranch i))
    rwa [hcomp_d1, topComponentTraversal_root D c i] at hrec
  have horbit : ∀ {t : ℕ}, t ≤ L →
      (E.continuation ^ (L - t)) (E.incoming c' i') =
        I.arcEquiv (D.continuation ((D.continuation ^ t) (D.incoming c i))) := by
    intro t ht
    have h := I.pow_sub_step (D.incoming c i) ht
    rwa [hL_eq, I.incoming_map c (otherBranch i)] at h
  constructor
  · rintro ⟨s, hs, hs_eq⟩
    have hyc' : I.crossingEquiv y ≠ c' := fun h => hyc (I.crossingEquiv.injective h)
    have hs_ne_zero : s ≠ 0 := by
      intro hs0
      rw [hs0, pow_zero, Equiv.Perm.one_apply] at hs_eq
      exact incoming_ne_of_crossing_ne E c' (I.crossingEquiv y) hyc'
        (I.branchEquiv y j) i' hs_eq.symm
    refine ⟨L - s, Nat.sub_le L s, ?_⟩
    have hstep := horbit (Nat.sub_le L s)
    rw [show L - (L - s) = s by omega, hs_eq, ← I.incoming_map y j] at hstep
    exact D.continuation.injective (I.arcEquiv.injective hstep.symm)
  · rintro ⟨t, ht, ht_eq⟩
    refine ⟨L - t, Nat.sub_le L t, ?_⟩
    rw [horbit ht, ht_eq, I.incoming_map y j]

private theorem not_sameCycle_incoming_otherBranch
    {G : PLLinkDiagram} (c : Fin G.nCrossing)
    (hno_self : ¬ G.continuation.SameCycle (G.incoming c 0) (G.incoming c 1))
    (j : Fin 2) :
    ¬ G.continuation.SameCycle (G.incoming c j) (G.incoming c (otherBranch j)) := by
  fin_cases j
  · exact hno_self
  · exact fun h => hno_self h.symm

theorem ReversedDiagramIso.badCrossings_empty_of_no_self
    {D E : PLLinkDiagram} (I : ReversedDiagramIso D E)
    (hno_self : ∀ c : Fin D.nCrossing, ¬ D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (U : BasedTraversal D) (hU : badCrossings U = ∅) :
    badCrossings (I.reversedComponentTraversal U) = ∅ := by
  rw [badCrossings_eq_empty_iff_firstVisited_over] at hU ⊢
  intro c'
  obtain ⟨c, rfl⟩ := I.crossingEquiv.surjective c'
  let j := firstVisitedBranch U c
  have hfirst_D : rankBefore (visitRank U (D.incoming c j))
      (visitRank U (D.incoming c (otherBranch j))) :=
    firstVisitedBranch_is_first U c
  have hne_comp : componentOf D.continuation (D.incoming c j) ≠
      componentOf D.continuation (D.incoming c (otherBranch j)) := by
    intro hEq
    exact not_sameCycle_incoming_otherBranch c (hno_self c) j
      ((componentOf_eq_iff D.continuation _ _).mp hEq)
  have hlt_D : U.componentIndex (componentOf D.continuation (D.incoming c j)) <
      U.componentIndex (componentOf D.continuation (D.incoming c (otherBranch j))) := by
    rcases hfirst_D with hlt | ⟨hEq, _⟩
    · exact hlt
    · exact False.elim (hne_comp (U.componentIndex.injective hEq))
  have hlt_E : (I.reversedComponentTraversal U).componentIndex
      (componentOf E.continuation (E.incoming (I.crossingEquiv c) (I.branchEquiv c j))) <
      (I.reversedComponentTraversal U).componentIndex
        (componentOf E.continuation
          (E.incoming (I.crossingEquiv c) (I.branchEquiv c (otherBranch j)))) := by
    change ((I.reversedComponentTraversal U).componentIndex _).val <
      ((I.reversedComponentTraversal U).componentIndex _).val
    rw [I.reversedComponentTraversal_componentIndex_incoming_val U c j,
      I.reversedComponentTraversal_componentIndex_incoming_val U c (otherBranch j)]
    exact hlt_D
  have hrb_E : rankBefore
      (visitRank (I.reversedComponentTraversal U)
        (E.incoming (I.crossingEquiv c) (I.branchEquiv c j)))
      (visitRank (I.reversedComponentTraversal U)
        (E.incoming (I.crossingEquiv c) (otherBranch (I.branchEquiv c j)))) := by
    rw [← branch_other (I.branchEquiv c) j]
    exact Or.inl hlt_E
  have hfb_E := firstVisitedBranch_eq_of_rankBefore
    (I.reversedComponentTraversal U) (I.crossingEquiv c) (I.branchEquiv c j) hrb_E
  rw [hfb_E, I.overBranch_map c]
  exact congrArg (I.branchEquiv c) (hU c)

theorem ReversedDiagramIso.badCrossings_disjoint_of_minimal_loopLength
    {D E : PLLinkDiagram} (I : ReversedDiagramIso D E)
    (c : Fin D.nCrossing) (i : Fin 2)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hmin : ∀ (z : Fin D.nCrossing) (k : Fin 2),
      D.continuation.SameCycle (D.incoming z 0) (D.incoming z 1) →
      loopLength D c i ≤ loopLength D z k)
    (hU_D : badCrossings (topComponentTraversal D c i) = ∅) :
    let c' := I.crossingEquiv c
    let i' := I.branchEquiv c (otherBranch i)
    let U_E := topComponentTraversal E c' i'
    ∀ y' ∈ badCrossings U_E, y' ≠ c' → ∀ j' : Fin 2,
      ¬ Gemini.TopProtected E U_E c' i' (E.incoming y' j') := by
  intro c' i' U_E y' hy'_bad hy'c' j' hprot_E
  obtain ⟨y, rfl⟩ := I.crossingEquiv.surjective y'
  obtain ⟨j, rfl⟩ := (I.branchEquiv y).surjective j'
  have hyc : y ≠ c := fun h => hy'c' (congrArg I.crossingEquiv h)
  let U_D := topComponentTraversal D c i
  have hprot_D : Gemini.TopProtected D U_D c i (D.incoming y j) :=
    (I.topProtected_incoming_iff c y i j hself hyc).mp hprot_E
  have hnot_D : ¬ Gemini.TopProtected D U_D c i (D.incoming y (otherBranch j)) := by
    intro hprot_other
    fin_cases j
    · exact not_both_topProtected_of_minimal_loopLength D c y i hself hmin hyc hprot_D hprot_other
    · exact not_both_topProtected_of_minimal_loopLength D c y i hself hmin hyc hprot_other hprot_D
  have hnot_E : ¬ Gemini.TopProtected E U_E c' i'
      (E.incoming (I.crossingEquiv y) (I.branchEquiv y (otherBranch j))) :=
    fun h => hnot_D ((I.topProtected_incoming_iff c y i (otherBranch j) hself hyc).mp h)
  have hrb_D := rankBefore_of_topProtected_of_not_topProtected
    D U_D c i (D.incoming y j) (D.incoming y (otherBranch j)) hprot_D hnot_D
  have hfb_D : firstVisitedBranch U_D y = j :=
    firstVisitedBranch_eq_of_rankBefore U_D y j hrb_D
  have hrb_E : rankBefore (visitRank U_E (E.incoming (I.crossingEquiv y) (I.branchEquiv y j)))
      (visitRank U_E (E.incoming (I.crossingEquiv y) (otherBranch (I.branchEquiv y j)))) := by
    rw [← branch_other (I.branchEquiv y) j]
    exact rankBefore_of_topProtected_of_not_topProtected E U_E c' i' _ _ hprot_E hnot_E
  have hfb_E : firstVisitedBranch U_E (I.crossingEquiv y) = I.branchEquiv y j :=
    firstVisitedBranch_eq_of_rankBefore U_E (I.crossingEquiv y) (I.branchEquiv y j) hrb_E
  have hover_D : firstVisitedBranch U_D y = D.overBranch y :=
    (badCrossings_eq_empty_iff_firstVisited_over U_D).mp hU_D y
  have hover_E : firstVisitedBranch U_E (I.crossingEquiv y) =
      E.overBranch (I.crossingEquiv y) := by
    rw [hfb_E, I.overBranch_map y, ← hover_D, hfb_D]
  have hy'_not_bad : ¬ badAt U_E (I.crossingEquiv y) := fun h => h hover_E
  exact hy'_not_bad (Finset.mem_filter.mp hy'_bad).2

theorem candidateEvaluator_reversedDiagramIso_no_self_aux
    {m : ℕ}
    (ih_n : ∀ (D₁ E₁ : PLLinkDiagram), D₁.nCrossing < m →
      (hD₁ : 0 < D₁.nArc) → (hE₁ : 0 < E₁.nArc) →
      ReversedDiagramIso D₁ E₁ →
      Gemini.candidateEvaluator E₁ hE₁ = Gemini.candidateEvaluator D₁ hD₁) :
    ∀ k : ℕ, ∀ (D E : PLLinkDiagram), D.nCrossing = m →
      (hD : 0 < D.nArc) → (hE : 0 < E.nArc) →
      ReversedDiagramIso D E →
      (∀ c : Fin D.nCrossing, ¬ D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) →
      ∀ (U : BasedTraversal D),
      (badCrossings U).card = k →
      Gemini.candidateEvaluator E hE = Gemini.candidateEvaluator D hD := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih_k =>
    intro D E hD_m hD hE I hno_self U hk
    by_cases hne : (badCrossings U).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hlt_k : (badCrossings (switchTraversal U x)).card < k := by
        have hcard := badCrossings_switch_card U x hx
        omega
      have hsw := ih_k _ hlt_k (switchCrossing D x) (switchCrossing E (I.crossingEquiv x))
        hD_m hD hE (I.switch x) hno_self (switchTraversal U x) rfl
      have hlt_m : (smoothCrossing D x).nCrossing < m := by
        have hdrop := smoothCrossing_crossing_count_drop D x
        omega
      have hsm := ih_n (smoothCrossing D x) (smoothCrossing E (I.crossingEquiv x)) hlt_m
        (by change 0 < D.nArc + 2; omega)
        (by change 0 < E.nArc + 2; omega)
        (I.smooth x)
      exact I.candidateEvaluator_eq_of_switch_and_smooth hD hE x hsw hsm
    · have hEmpty_D : badCrossings U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hEmpty_E : badCrossings (I.reversedComponentTraversal U) = ∅ :=
        I.badCrossings_empty_of_no_self hno_self U hEmpty_D
      rw [Gemini.candidateEvaluator_eq_traversal Gemini.all_lowerCrossingEvaluatorSkeinIH D hD U,
        Gemini.candidateEvaluator_eq_traversal Gemini.all_lowerCrossingEvaluatorSkeinIH E hE
          (I.reversedComponentTraversal U),
        descendingLaurentEvaluator_terminal D U (by simp [hEmpty_D]),
        descendingLaurentEvaluator_terminal E (I.reversedComponentTraversal U) (by simp [hEmpty_E]),
        I.descendingUnlinkValue_eq]

theorem candidateEvaluator_reversedDiagramIso_min_loop_aux
    {m : ℕ}
    (ih_n : ∀ (D₁ E₁ : PLLinkDiagram), D₁.nCrossing < m →
      (hD₁ : 0 < D₁.nArc) → (hE₁ : 0 < E₁.nArc) →
      ReversedDiagramIso D₁ E₁ →
      Gemini.candidateEvaluator E₁ hE₁ = Gemini.candidateEvaluator D₁ hD₁) :
    ∀ k : ℕ, ∀ (D E : PLLinkDiagram), D.nCrossing = m →
      (hD : 0 < D.nArc) → (hE : 0 < E.nArc) →
      ReversedDiagramIso D E →
      ∀ (c : Fin D.nCrossing) (i : Fin 2),
      D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1) →
      (∀ (z : Fin D.nCrossing) (j : Fin 2),
        D.continuation.SameCycle (D.incoming z 0) (D.incoming z 1) →
        loopLength D c i ≤ loopLength D z j) →
      (badCrossings (topComponentTraversal D c i)).card = k →
      Gemini.candidateEvaluator E hE = Gemini.candidateEvaluator D hD := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih_k =>
    intro D E hD_m hD hE I c i hself hmin hk
    by_cases hne : (badCrossings (topComponentTraversal D c i)).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hlt_k : (badCrossings (topComponentTraversal (switchCrossing D x) c i)).card < k := by
        rw [← topComponentTraversal_switch D c x i]
        have hcard := badCrossings_switch_card (topComponentTraversal D c i) x hx
        omega
      have hsw := ih_k _ hlt_k (switchCrossing D x) (switchCrossing E (I.crossingEquiv x))
        hD_m hD hE (I.switch x) c i hself hmin rfl
      have hlt_m : (smoothCrossing D x).nCrossing < m := by
        have hdrop := smoothCrossing_crossing_count_drop D x
        omega
      have hsm := ih_n (smoothCrossing D x) (smoothCrossing E (I.crossingEquiv x)) hlt_m
        (by change 0 < D.nArc + 2; omega)
        (by change 0 < E.nArc + 2; omega)
        (I.smooth x)
      exact I.candidateEvaluator_eq_of_switch_and_smooth hD hE x hsw hsm
    · have hEmpty_D : badCrossings (topComponentTraversal D c i) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      let c' := I.crossingEquiv c
      let i' := I.branchEquiv c (otherBranch i)
      let U_E := topComponentTraversal E c' i'
      have hself_E : E.continuation.SameCycle (E.incoming c' 0) (E.incoming c' 1) :=
        (I.sameCycle_crossing_iff c).mpr hself
      have hbad_E := I.badCrossings_disjoint_of_minimal_loopLength c i hself hmin hEmpty_D
      have hbad_D : ∀ y ∈ badCrossings (topComponentTraversal D c i), y ≠ c → ∀ j : Fin 2,
          ¬ Gemini.TopProtected D (topComponentTraversal D c i) c i (D.incoming y j) := by
        intro y hy
        rw [hEmpty_D] at hy
        exact False.elim (Finset.not_mem_empty y hy)
      have hdel_E := candidateEvaluator_topLoop_deletion_any_c E hE U_E c' hself_E i'
        (topComponentTraversal_root E c' i') hbad_E
      have hdel_D := candidateEvaluator_topLoop_deletion_any_c D hD
        (topComponentTraversal D c i) c hself i
        (topComponentTraversal_root D c i) hbad_D
      have hlt_m : (smoothCrossing D c).nCrossing < m := by
        have hdrop := smoothCrossing_crossing_count_drop D c
        omega
      have hsm := ih_n (smoothCrossing D c) (smoothCrossing E (I.crossingEquiv c)) hlt_m
        (by change 0 < D.nArc + 2; omega)
        (by change 0 < E.nArc + 2; omega)
        (I.smooth c)
      apply Gemini.unlinkFactor_mul_injective
      rw [hdel_E, hdel_D, hsm]

theorem candidateEvaluator_reversedDiagramIso_self_aux
    {m : ℕ}
    (ih_n : ∀ (D₁ E₁ : PLLinkDiagram), D₁.nCrossing < m →
      (hD₁ : 0 < D₁.nArc) → (hE₁ : 0 < E₁.nArc) →
      ReversedDiagramIso D₁ E₁ →
      Gemini.candidateEvaluator E₁ hE₁ = Gemini.candidateEvaluator D₁ hD₁) :
    ∀ L : ℕ, ∀ (D E : PLLinkDiagram), D.nCrossing = m →
      (hD : 0 < D.nArc) → (hE : 0 < E.nArc) →
      ReversedDiagramIso D E →
      ∀ (c : Fin D.nCrossing) (i : Fin 2),
      D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1) →
      loopLength D c i = L →
      Gemini.candidateEvaluator E hE = Gemini.candidateEvaluator D hD := by
  intro L
  induction L using Nat.strong_induction_on with
  | h L ih_L =>
    intro D E hD_m hD hE I c i hself hL
    by_cases hlt : ∃ (y : Fin D.nCrossing) (j : Fin 2),
        D.continuation.SameCycle (D.incoming y 0) (D.incoming y 1) ∧ loopLength D y j < L
    · obtain ⟨y, j, hy_self, hy_lt⟩ := hlt
      exact ih_L (loopLength D y j) hy_lt D E hD_m hD hE I y j hy_self rfl
    · push_neg at hlt
      have hmin : ∀ (z : Fin D.nCrossing) (j : Fin 2),
          D.continuation.SameCycle (D.incoming z 0) (D.incoming z 1) →
          loopLength D c i ≤ loopLength D z j := by
        intro z j hz
        rw [hL]
        exact hlt z j hz
      exact candidateEvaluator_reversedDiagramIso_min_loop_aux ih_n
        (badCrossings (topComponentTraversal D c i)).card
        D E hD_m hD hE I c i hself hmin rfl

theorem candidateEvaluator_reversedDiagramIso_aux :
    ∀ m : ℕ, ∀ (D E : PLLinkDiagram), D.nCrossing = m →
      (hD : 0 < D.nArc) → (hE : 0 < E.nArc) →
      ReversedDiagramIso D E →
      Gemini.candidateEvaluator E hE = Gemini.candidateEvaluator D hD := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih_m =>
    intro D E hD_m hD hE I
    have ih_n : ∀ (D₁ E₁ : PLLinkDiagram), D₁.nCrossing < m →
        (hD₁ : 0 < D₁.nArc) → (hE₁ : 0 < E₁.nArc) →
        ReversedDiagramIso D₁ E₁ →
        Gemini.candidateEvaluator E₁ hE₁ = Gemini.candidateEvaluator D₁ hD₁ :=
      fun D₁ E₁ hlt hD₁ hE₁ I₁ => ih_m D₁.nCrossing hlt D₁ E₁ rfl hD₁ hE₁ I₁
    by_cases hself : ∃ c : Fin D.nCrossing, D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)
    · obtain ⟨c, hc⟩ := hself
      exact candidateEvaluator_reversedDiagramIso_self_aux ih_n
        (loopLength D c 0) D E hD_m hD hE I c 0 hc rfl
    · push_neg at hself
      exact candidateEvaluator_reversedDiagramIso_no_self_aux ih_n
        (badCrossings (chooseBasedTraversal D)).card
        D E hD_m hD hE I hself (chooseBasedTraversal D) rfl

theorem candidateEvaluator_reversedDiagramIso {D E : PLLinkDiagram}
    (hD : 0 < D.nArc) (hE : 0 < E.nArc) (I : ReversedDiagramIso D E) :
    Gemini.candidateEvaluator E hE = Gemini.candidateEvaluator D hD :=
  candidateEvaluator_reversedDiagramIso_aux D.nCrossing D E rfl hD hE I

end HOMFLY

section PartD_Targets6And7

variable {n : ℕ}

theorem candidateEvaluator_positivePolygonEventDiagram_reversePolygon
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    Gemini.candidateEvaluator
      (positivePolygonEventDiagram (reversePolygon q) (cyclicGeneric_reversePolygon q hq))
      (positivePolygonEventDiagram_nArc_pos (reversePolygon q) (cyclicGeneric_reversePolygon q hq)) =
      Gemini.candidateEvaluator
        (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq) :=
  HOMFLY.candidateEvaluator_reversedDiagramIso
    (positivePolygonEventDiagram_nArc_pos q hq)
    (positivePolygonEventDiagram_nArc_pos (reversePolygon q) (cyclicGeneric_reversePolygon q hq))
    (positivePolygonReversedDiagramIso q hq)

theorem prescribedCorner_reversePolygon
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    prescribedCorner (reversePolygon q) (cyclicGeneric_reversePolygon q hq) =
      prescribedCorner q hq := by
  unfold prescribedCorner
  rw [candidateEvaluator_positivePolygonEventDiagram_reversePolygon q hq,
    positivePolygonEventDiagram_nCrossing_reversePolygon q hq,
    turnInteger_positivePolygonEventDiagram_reversePolygon q hq,
    abs_neg]

theorem homfly_reversal_thm :
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∃ hqr : CyclicGeneric (reversePolygon q),
        (positivePolygonEventDiagram (reversePolygon q) hqr).nCrossing =
          (positivePolygonEventDiagram q hq).nCrossing ∧
        totalTurn (positivePolygonEventDiagram (reversePolygon q) hqr) =
          - totalTurn (positivePolygonEventDiagram q hq) ∧
        turnInteger (positivePolygonEventDiagram (reversePolygon q) hqr) =
          - turnInteger (positivePolygonEventDiagram q hq) ∧
        Gemini.candidateEvaluator (positivePolygonEventDiagram (reversePolygon q) hqr)
          (positivePolygonEventDiagram_nArc_pos _ hqr) =
          Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
            (positivePolygonEventDiagram_nArc_pos _ hq) ∧
        prescribedCorner (reversePolygon q) hqr = prescribedCorner q hq := by
  intro n q hq
  refine ⟨cyclicGeneric_reversePolygon q hq,
    positivePolygonEventDiagram_nCrossing_reversePolygon q hq,
    totalTurn_positivePolygonEventDiagram_reversePolygon q hq,
    turnInteger_positivePolygonEventDiagram_reversePolygon q hq,
    candidateEvaluator_positivePolygonEventDiagram_reversePolygon q hq,
    prescribedCorner_reversePolygon q hq⟩

theorem right_turning_reduction_thm :
    GLSSWRootIndependence →
      ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (hAux : auxiliaryGenericity q hq),
        StrictRight q →
        (∀ (p : Fin n → PlanarPoint ℝ) (hp : CyclicGeneric p)
          (hAuxP : auxiliaryGenericity p hp), StrictLeft p →
            normalizedPrimitive p hp hAuxP = (prescribedCorner p hp : ℚ)) →
        normalizedPrimitive q hq hAux = (prescribedCorner q hq : ℚ) := by
  intro hRI n q hq hAux hRight hLeftIdentity
  let hqr := cyclicGeneric_reversePolygon q hq
  let hAuxR := auxiliaryGenericity_reversePolygon q hq hAux
  have hLeft : StrictLeft (reversePolygon q) :=
    (strictLeft_reversePolygon_iff q).mpr hRight
  have hId := hLeftIdentity (reversePolygon q) hqr hAuxR hLeft
  rw [normalizedPrimitive_reversePolygon hRI q hq hAux,
    prescribedCorner_reversePolygon q hq] at hId
  exact hId

end PartD_Targets6And7

end DirectGLSSW




