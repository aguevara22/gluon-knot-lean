import TruncationPositiveEvaluator
import DirectGLSSW.TruncationAmplitudeCrossings
import DirectGLSSW.TruncationFixedScaleCrossings
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open TruncationDirection TruncationEdgeLift Coefficients
attribute [local instance] Classical.propDecidable

/-- The existing actual left-corner truncation family preserves every normalized
positive-diagram evaluator and its actual retained crossing count. -/
theorem exists_leftCorner_truncation_evaluator_crossings
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a)) :
    ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
          ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
            polygonAmplitude (truncateCyclicCorner q a p scale ε) ht = -polygonAmplitude q hq ∧
            (positivePolygonEventDiagram q hq).nCrossing =
              (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) ht).nCrossing ∧
            ∀ (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff),
              IsNormalizedDescendingSkeinEvaluator H →
              H (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq) =
                H (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) ht)
                  (positivePolygonEventDiagram_nArc_pos _ ht) := by
  obtain ⟨scale,hscale,δ,hδ,hfam⟩ := exists_leftCorner_truncation_amplitude_crossings hRI q hq a p hp hturn
  refine ⟨scale,hscale,δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hs1,ht,hamp,E,hlabels,hpoint⟩ := hfam ε hε hεδ
  have hleft (c : PolygonCrossing q) := congrArg Prod.fst (hlabels c)
  have hright (c : PolygonCrossing q) := congrArg Prod.snd (hlabels c)
  refine ⟨hε1,hs1,ht,hamp,truncation_positive_crossing_count q hq a p scale ε ht E,?_⟩
  intro H hH
  exact truncation_positive_normalizedEvaluator q hq a p hp scale ε hε hε1
    (mul_pos hε hscale) hs1 ht E hleft hright hpoint H hH

/-- The existing actual left-corner truncation family preserves every normalized
positive-diagram evaluator and its actual retained crossing count. -/
theorem exists_fixedScale_leftCorner_truncation_evaluator_crossings
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a))
    (scale : ℝ) (hscale : 0 < scale)
    (havoid : ∀ x : Fin n, x ≠ a →
      planarDet (scale • (q (cyclicSuccessor a) - q a) - (q p - q a)) (q x - q a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
          ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
            polygonAmplitude (truncateCyclicCorner q a p scale ε) ht = -polygonAmplitude q hq ∧
            (positivePolygonEventDiagram q hq).nCrossing =
              (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) ht).nCrossing ∧
            ∀ (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff),
              IsNormalizedDescendingSkeinEvaluator H →
              H (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq) =
                H (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) ht)
                  (positivePolygonEventDiagram_nArc_pos _ ht) := by
  obtain ⟨δ,hδ,hfam⟩ := TruncationFixedScaleCrossings.exists_fixedScale_leftCorner_truncation_amplitude_crossings hRI q hq a p hp hturn scale hscale havoid
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hs1,ht,hamp,E,hlabels,hpoint⟩ := hfam ε hε hεδ
  have hleft (c : PolygonCrossing q) := congrArg Prod.fst (hlabels c)
  have hright (c : PolygonCrossing q) := congrArg Prod.snd (hlabels c)
  refine ⟨hε1,hs1,ht,hamp,truncation_positive_crossing_count q hq a p scale ε ht E,?_⟩
  intro H hH
  exact truncation_positive_normalizedEvaluator q hq a p hp scale ε hε hε1
    (mul_pos hε hscale) hs1 ht E hleft hright hpoint H hH
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
