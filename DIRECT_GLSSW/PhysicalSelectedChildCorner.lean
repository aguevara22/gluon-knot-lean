import PhysicalSelectedChildWord
import PointWordCoefficientCongruence
import UniformCornerG
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.ExposedChart ExposedOpenPrimitive
open Coefficients PrincipalTurning GeometricSmoothingWeights
attribute [local instance] Classical.propDecidable
variable {n A a b : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)

include hc

/-- Actual canonical knot child value equals the prescribed corner of the
literal physical split child. The selected-event origin condition is internal
and is intended to be discharged by the physical first-event producer. -/
theorem detachedValue_eq_physical_child_corner_of_selected_origin
    (hRI : GLSSWRootIndependence)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq)
    (hs : A+(a+b)=n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1)
    (hM : Regular (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ))
    (d : Crossing (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ))
    (hd0 : d.val.1=0) (hdcut : d.val.2.val=a)
    (horigin : crossingFin q (exposedCrossingEquiv q 0 hq he
      (suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
        A (a+b) hs θ h0 h1 d).val) = h.crossingOrigin c) :
    ∃ hP : CyclicGeneric
      (child (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ) hM d hd0 hdcut),
    MarkedG.detachedValue t c =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram
        (child (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ) hM d hd0 hdcut) hP)
        (positivePolygonEventDiagram_nArc_pos _ hP))
        (1-((positivePolygonEventDiagram
          (child (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ) hM d hd0 hdcut) hP).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram
            (child (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ) hM d hd0 hdcut) hP)|) 0 := by
  have hA := closedAuxiliary_of_parent q 0 hq he hAux
  let R := canonicalDetachedRestriction t c
  let Q := historicalSharpPolygon q hq h c hc R
  obtain ⟨hQ,hlQ,hcount,heval,hrow⟩ := canonical_actual_recursive_child q hq h c hc hleft he hA
  have hw := historicalSharpPolygon_eq_physical_child_of_selected_origin
    q hq he h c hc R hA hs θ h0 h1 hM d hd0 hdcut horigin
  have hP := cyclicGeneric_of_pointWord_eq Q hQ _ hw
  refine ⟨hP,?_⟩
  have hAuxQ : auxiliaryGenericity Q hQ :=
    canonical_historical_child_auxiliaryGenericity q hq h c hc he hA
  obtain ⟨F,hF,_,_,hcorner,hnegative⟩ := uniform_polygon_corner_evaluation hRI Q hQ hlQ hAuxQ
  have hv : MarkedG.detachedValue t c =
      -coeff (framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
        (positivePolygonEventDiagram_nArc_pos _ hQ)
        (componentOf (positivePolygonEventDiagram Q hQ).continuation
          ⟨0,positivePolygonEventDiagram_nArc_pos _ hQ⟩)) 0 0 := by
    change -coeff (framedKnotRow Gemini.candidateEvaluator R.diagram R.nonempty
      (componentOf R.diagram.continuation ⟨0,R.nonempty⟩)) 0 0 = _
    rw [hrow]
  exact hv.trans (hnegative.trans (hcorner.symm.trans
    (prescribed_corner_of_pointWord_eq Q hQ _ hP hw)))
end DirectGLSSW.HOMFLY.ProcessedExposedChild
