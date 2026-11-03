import HOMFLYRowExtraction
import ProcessedBadCrossingPositive
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.HOMFLYRowExtractionProbe
open Coefficients LowestRowContract

theorem actual_initial_history_row
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ c : Fin D.nCrossing, crossingSign D c = .pos)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (ht : 0 < t.1.nArc) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) :
    aMonomial * zRow (Gemini.candidateEvaluator t.1 ht) 0 -
      aInvMonomial * zRow (Gemini.candidateEvaluator (switchCrossing t.1 c) ht) 0 =
      zRow (Gemini.candidateEvaluator (smoothCrossing t.1 c)
        (by change 0 < t.1.nArc + 2; omega)) (-1) := by
  simpa using candidateEvaluator_positive_skein_row t.1 ht c
    (h.bad_crossing_positive_of_initial D T hconn hpos t c hc) 0
end DirectGLSSW.HOMFLY.HOMFLYRowExtractionProbe
set_option pp.all true
set_option pp.proofs true
set_option pp.maxSteps 1000000
#check @DirectGLSSW.HOMFLY.zRow_apply

#check @DirectGLSSW.HOMFLY.zRow_sub

#check @DirectGLSSW.HOMFLY.zRow_aMonomial_mul

#check @DirectGLSSW.HOMFLY.zRow_aInvMonomial_mul

#check @DirectGLSSW.HOMFLY.zRow_zMonomial_mul

#check @DirectGLSSW.HOMFLY.normalizedEvaluator_positive_skein_row

#check @DirectGLSSW.HOMFLY.candidateEvaluator_positive_skein_row

#check @DirectGLSSW.HOMFLY.HOMFLYRowExtractionProbe.actual_initial_history_row

