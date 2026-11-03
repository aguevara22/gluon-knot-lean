import PLArcSubdivision
import HOMFLYArcContractionEvaluator

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ) (ht0 : 0<t) (ht1 : t<1)

/-- Collapse the two physical subarcs back to their actual original arc. -/
def subdivideArc_contraction : SignedArcContraction (subdivideArc D e t ht0 ht1) D where
  deleted := e.castSucc
  retained := Fin.last D.nArc
  distinct := Fin.ne_of_lt (Fin.castSucc_lt_last e)
  successor := continuation_selected_first D e
  arcMap := collapse D e
  arcMap_surjective := collapse_surjective D e
  arcMap_fibers := collapse_fibers D e
  crossingEquiv := Equiv.refl _
  deleted_not_incoming := selected_first_half_not_incoming D e
  incoming_map := collapse_incoming D e
  outgoing_map := collapse_outgoing D e
  continuation_map := collapse_continuation D e
  through_map := fun _=>rfl
  overBranch_map := fun _=>rfl
  crossingSign_map := subdivideArc_crossingSign D e t ht0 ht1

/-- The accepted concrete normalized evaluator is unchanged by arbitrary physical arc subdivision. -/
theorem subdivideArc_candidateEvaluator :
    Gemini.candidateEvaluator (subdivideArc D e t ht0 ht1) (Nat.zero_lt_succ _) =
      Gemini.candidateEvaluator D (by have := e.isLt;omega) :=
  (subdivideArc_contraction D e t ht0 ht1).candidateEvaluator_eq _ _
end DirectGLSSW.HOMFLY.ArcSubdivision
