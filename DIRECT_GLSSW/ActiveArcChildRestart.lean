import UniformPrimitiveChart
import ActiveArcChildAuxiliary
import ActiveArcUniformChild
import ActiveArcCutCrossings

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.ChildRestart
open DirectGLSSW
open DirectGLSSW.ActiveArc.Cursor
open DirectGLSSW.ActiveArc.Split
open DirectGLSSW.ActiveArc.SingletonWords
open DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW.GeometricSmoothingWeights
open DirectGLSSW.ExposedOpenPrimitive
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY.Coefficients
attribute [local instance] Classical.propDecidable

private theorem child_crossing_card_lt_local
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    Fintype.card (PolygonCrossing (child q hR c hc.1 hcut)) <
      Fintype.card (Crossing q) := by
  classical
  let f := childCrossingToOriginal q hR c hc.1 hcut
  have hf : Function.Injective f := childCrossingToOriginal_injective q hR c hc.1 hcut
  have hnot : ∀ d, f d ≠ c := by
    intro d he
    have hd := childCrossingToOriginal_inChild q hR c hc.1 hcut d
    change InChild q c (f d) at hd
    rw [he] at hd
    exact crossing_not_inChild q c hc.1 hd
  exact Fintype.card_lt_of_injective_of_not_mem f hf (b:=c) (by
    rintro ⟨d,hd⟩
    exact hnot d hd)

/-- The actual first-under detached child admits a uniform exposed primitive
restart whose literal cut-arc crossing count is strictly smaller than the
original active arc. The chart's normalized sum and prescribed coefficient
outputs are retained in the witness for downstream consumers. -/
theorem exists_actual_under_child_exposed_restart
    {a b : ℕ} (hRI : GLSSWRootIndependence)
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val = a)
    (hG1 : cyclicNoncollinear q) (hAux : Primitive.ClosedAuxiliary q hR)
    (hu : crossingUnder q (polygonCrossingOfArc q c) =
      (polygonCrossingOfArc q c).val.1)
    (hleft : ∀ i : Fin (a+b), i.val<a →
      0 < planarDet (q i.succ.castSucc-q i.castSucc.castSucc)
        (q i.succ.succ-q i.succ.castSucc)) :
    ∃ m : ℕ, ∃ Q : Fin (m+2) → PlanarPoint ℝ, ∃ hQ : CyclicGeneric Q,
    ∃ hAuxQ : auxiliaryGenericity Q hQ,
      (∀ i, 0 < planarDet (cyclicTangent Q i)
        (cyclicTangent Q (cyclicSuccessor i))) ∧
      LeftExposed Q 0 ∧
      Fintype.card (Crossing (cutArc Q 0)) < Fintype.card (Crossing q) ∧
      (-1 : ℚ)^(m+2) * separatingSmoothingSum Q hQ hAuxQ =
        (-1 : ℚ)^(a+1) * separatingSmoothingSum (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) ∧
      coeff (candidateEvaluator (positivePolygonEventDiagram Q hQ)
        (positivePolygonEventDiagram_nArc_pos Q hQ))
        (1-((positivePolygonEventDiagram Q hQ).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram Q hQ)|) 0 =
      coeff (candidateEvaluator
        (positivePolygonEventDiagram (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux))
        (positivePolygonEventDiagram_nArc_pos _ _))
        (1-((positivePolygonEventDiagram
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram
            (child q hR c hc.1 hcut)
            (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux))|) 0 := by
  let Qc := child q hR c hc.1 hcut
  let hQc := child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux
  let hAuxQc := child_auxiliaryGenericity q hR c hc hcut hAux
  have hleftQc := child_all_turns_pos q hR c hc hcut hG1 hu hleft
  obtain ⟨m,Q,hQ,hAuxQ,hleftQ,heQ,hcount,hsum,hcoeff⟩ :=
    exists_uniform_exposed_primitive_corner_chart hRI Qc hQc hleftQc hAuxQc
  have hcrossQ : Fintype.card (Crossing (cutArc Q 0)) =
      Fintype.card (PolygonCrossing Q) :=
    Fintype.card_congr (exposedCrossingEquiv Q 0 hQ heQ)
  have hchildCount : Fintype.card (PolygonCrossing Qc) < Fintype.card (Crossing q) :=
    child_crossing_card_lt_local q hR c hc hcut
  have hdiagramQ : (positivePolygonEventDiagram Q hQ).nCrossing =
      Fintype.card (PolygonCrossing Q) := by
    rfl
  have hdiagramChild : (positivePolygonEventDiagram Qc hQc).nCrossing =
      Fintype.card (PolygonCrossing Qc) := by
    rfl
  have hlt : Fintype.card (Crossing (cutArc Q 0)) < Fintype.card (Crossing q) := by
    rw [hcrossQ, ← hdiagramQ, hcount, hdiagramChild]
    exact hchildCount
  exact ⟨m,Q,hQ,hAuxQ,hleftQ,heQ,hlt,hsum,hcoeff⟩

end DirectGLSSW.ActiveArc.ChildRestart
