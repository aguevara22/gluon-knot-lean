import SupportingTruncationExposure
import TruncationKnotFamily
import TruncationPositiveTurn
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open TruncationDirection ExposedOpenPrimitive Coefficients
attribute [local instance] Classical.propDecidable

/-- The original uniformly-left polygon itself supplies a supporting truncation
family.  Exposure, amplitude, crossing number, rotation, and normalized evaluator
preservation are conclusions about the same literal truncated polygon. -/
theorem exists_supporting_truncation_knot_family
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i))) :
    ∃ a p : Fin n, cyclicSuccessor p = a ∧ ∃ scale : ℝ, 0 < scale ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
        ∃ hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε),
          LeftExposed (truncateCyclicCorner q a p scale ε) a.castSucc ∧
          polygonAmplitude (truncateCyclicCorner q a p scale ε) hQ = -polygonAmplitude q hq ∧
          (positivePolygonEventDiagram q hq).nCrossing =
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ).nCrossing ∧
          PrincipalTurning.totalTurn
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
            PrincipalTurning.totalTurn (positivePolygonEventDiagram q hq) ∧
          PrincipalTurning.turnInteger
            (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ) =
            PrincipalTurning.turnInteger (positivePolygonEventDiagram q hq) ∧
          ∀ (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff),
            IsNormalizedDescendingSkeinEvaluator H →
            H (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram_nArc_pos q hq) =
              H (positivePolygonEventDiagram (truncateCyclicCorner q a p scale ε) hQ)
                (positivePolygonEventDiagram_nArc_pos _ hQ) := by
  obtain ⟨a,p,hp,scale,hs,hsupport⟩ := exists_supporting_left_corner_scale q hq hleft
  have ht : 0 < planarDet (q a-q p) (q (cyclicSuccessor a)-q a) := by
    simpa only [cyclicTangent,hp] using hleft p
  obtain ⟨δK,hδK,hK⟩ := exists_fixedScale_leftCorner_truncation_evaluator_crossings
    hRI q hq a p hp ht scale hs (fun x hx => ne_of_gt (hsupport x hx))
  obtain ⟨δE,hδE,hE⟩ := exists_small_truncation_leftExposed q a p scale hsupport
  refine ⟨a,p,hp,scale,hs,min δK δE,lt_min hδK hδE,?_⟩
  intro ε hε hεδ
  obtain ⟨hε1,hs1,hQ,hamp,hcount,hH⟩ := hK ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  refine ⟨hε1,hs1,hQ,hE ε hε (lt_of_lt_of_le hεδ (min_le_right _ _)),hamp,hcount,?_,?_,hH⟩
  · exact truncate_positive_totalTurn_eq q hq a p hp scale ε hε hε1 (mul_pos hε hs) hs1 hQ ht
  · exact truncate_positive_turnInteger_eq q hq a p hp scale ε hε hε1 (mul_pos hε hs) hs1 hQ ht
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
