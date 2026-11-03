import SplitCircleOldRestriction
import HOMFLYSignedIsoNormalized

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW DirectGLSSW.PermutationOrbits GeminiLowest

variable (D : PLLinkDiagram) (R : ℝ)
  (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
  (hright : ∀ v : Fin (rightTriangle R).nVertex,
    R < ((rightTriangle R).vertexPoint v).1)
  (hD : 0 < D.nArc)

private theorem joinedNextOld (e : Fin D.nArc) :
    (J D R hleft hright).continuation ((A D R hleft hright) (.inl e)) =
      (A D R hleft hright) (.inl (D.continuation e)) := by
  change (A D R hleft hright)
    (continuationCode D R ((A D R hleft hright).symm ((A D R hleft hright) (.inl e)))) = _
  simp [continuationCode]

private theorem joinedCrossingSign (c : Fin D.nCrossing) :
    crossingSign (J D R hleft hright) c = crossingSign D c := by
  unfold crossingSign crossingDet strandTangent
  simp [J, joinedDiagram, vertexPointCode, sourceCode, arcEquiv, vertexEquiv]

/-- The original block of the literal adjoined-circle diagram is signed-isomorphic
 to the original diagram, including crossing signs from geometric tangents. -/
def leftRestrictionSignedIso :
    SignedDiagramIso (restrictSublink (J D R hleft hright)
      (B D R hleft hright hD)) D where
  arcEquiv := leftRestrictedArcEquiv D R hleft hright hD
  crossingEquiv := leftCrossingEquiv D R hleft hright hD
  incoming_map := by
    intro c i
    apply Sum.inl_injective
    apply (A D R hleft hright).injective
    rw [leftRestrictedArcEquiv_val]
    change sublinkOldArc (J D R hleft hright) (B D R hleft hright hD)
      (sublinkIncomingIndex (J D R hleft hright) (B D R hleft hright hD) c i) = _
    rw [sublink_old_incoming]
    rfl
  outgoing_map := by
    intro c i
    apply Sum.inl_injective
    apply (A D R hleft hright).injective
    rw [leftRestrictedArcEquiv_val]
    change sublinkOldArc (J D R hleft hright) (B D R hleft hright hD)
      (sublinkOutgoingIndex (J D R hleft hright) (B D R hleft hright hD) c i) = _
    rw [sublink_old_outgoing]
    rfl
  continuation_map := by
    intro e
    apply Sum.inl_injective
    apply (A D R hleft hright).injective
    rw [leftRestrictedArcEquiv_val]
    change sublinkOldArc (J D R hleft hright) (B D R hleft hright hD)
      ((sublinkNext (J D R hleft hright) (B D R hleft hright hD)) e) = _
    rw [sublink_old_next]
    rw [← leftRestrictedArcEquiv_val]
    exact joinedNextOld D R hleft hright _
  through_map := by intro c; rfl
  overBranch_map := by intro c; rfl
  crossingSign_map := by
    intro c
    rw [sublink_crossing_sign_preserved]
    exact joinedCrossingSign D R hleft hright _

end DirectGLSSW.HOMFLY.SplitCircleConstructor

