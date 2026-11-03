import HOMFLYArcContractionSmoothMaps

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
namespace SignedArcContraction
variable {D E : PLLinkDiagram} (R : SignedArcContraction D E)

theorem smooth_incoming_map (c : Fin D.nCrossing)
    (d : Fin (D.nCrossing - 1)) (i : Fin 2) :
    R.smoothArcMap ((smoothCrossing D c).incoming d i) =
      (smoothCrossing E (R.crossingEquiv c)).incoming (R.smoothCrossingEquiv c d) i := by
  let oldD := (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
  simpa [smoothCrossingEquiv, smoothArcMap, smoothCodeMap, smoothCrossing,
    smoothIncoming, smoothArcEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    retainedCrossingEquiv, oldD] using R.incoming_map oldD.val i

theorem smooth_outgoing_map (c : Fin D.nCrossing)
    (d : Fin (D.nCrossing - 1)) (i : Fin 2) :
    R.smoothArcMap ((smoothCrossing D c).outgoing d i) =
      (smoothCrossing E (R.crossingEquiv c)).outgoing (R.smoothCrossingEquiv c d) i := by
  let oldD := (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
  simpa [smoothCrossingEquiv, smoothArcMap, smoothCodeMap, smoothCrossing,
    smoothOutgoing, smoothArcEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    retainedCrossingEquiv, oldD] using R.outgoing_map oldD.val i

theorem smooth_through_map (c : Fin D.nCrossing) (d : Fin (D.nCrossing - 1)) :
    (smoothCrossing D c).through d =
      (smoothCrossing E (R.crossingEquiv c)).through (R.smoothCrossingEquiv c d) := by
  let oldD := (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
  simpa [smoothCrossingEquiv, smoothCrossing, smoothThrough,
    Equiv.trans_apply, Equiv.symm_apply_apply, retainedCrossingEquiv, oldD] using R.through_map oldD.val

theorem smooth_overBranch_map (c : Fin D.nCrossing) (d : Fin (D.nCrossing - 1)) :
    (smoothCrossing D c).overBranch d =
      (smoothCrossing E (R.crossingEquiv c)).overBranch (R.smoothCrossingEquiv c d) := by
  let oldD := (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
  simpa [smoothCrossingEquiv, smoothCrossing, retainedCrossingEquiv, oldD] using R.overBranch_map oldD.val

theorem smooth_crossingSign_map (c : Fin D.nCrossing) (d : Fin (D.nCrossing - 1)) :
    crossingSign (smoothCrossing D c) d =
      crossingSign (smoothCrossing E (R.crossingEquiv c)) (R.smoothCrossingEquiv c d) := by
  let oldD := (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
  let oldE := R.retainedCrossingEquiv c oldD
  have hD := crossingSign_smoothRetained D c oldD.val oldD.property
  have hE := crossingSign_smoothRetained E (R.crossingEquiv c) oldE.val oldE.property
  have hlabel : DirectGLSSW.HOMFLY.smoothCrossingEquiv E (R.crossingEquiv c) oldE =
      R.smoothCrossingEquiv c d := rfl
  calc
    crossingSign (smoothCrossing D c) d = crossingSign D oldD.val := by simpa [oldD] using hD
    _ = crossingSign E (R.crossingEquiv oldD.val) := R.crossingSign_map oldD.val
    _ = crossingSign E oldE.val := rfl
    _ = crossingSign (smoothCrossing E (R.crossingEquiv c)) (R.smoothCrossingEquiv c d) := by
      rw [← hlabel]
      exact hE.symm

theorem smooth_deleted_not_incoming (c : Fin D.nCrossing)
    (d : Fin (D.nCrossing - 1)) (i : Fin 2) :
    (smoothCrossing D c).incoming d i ≠ R.smoothDeleted := by
  let oldD := (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
  have hp := R.deleted_not_incoming oldD.val i
  intro h
  apply hp
  have hm := R.smooth_incoming_map c d i
  have hcode := congrArg (fun x => (smoothArcEquiv D).symm x) h
  simp only [smoothDeleted, smoothArcMap, Equiv.symm_apply_apply] at hcode
  -- Unfolding the smoothing coordinate definitions identifies this source port.
  simpa [smoothCrossingEquiv, smoothCrossing, smoothIncoming,
    smoothArcEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    retainedCrossingEquiv, oldD] using hcode

/-- Smoothing retains the incoming-only contraction certificate on the actual
children. Independent geometric radius choices require no equality here. -/
def smooth (c : Fin D.nCrossing) :
    SignedArcContraction (smoothCrossing D c) (smoothCrossing E (R.crossingEquiv c)) where
  deleted := R.smoothDeleted
  retained := R.smoothRetained
  distinct := R.smooth_selected_distinct
  successor := R.smooth_selected_successor c
  arcMap := R.smoothArcMap
  arcMap_surjective := R.smoothArcMap_surjective
  arcMap_fibers := R.smoothArcMap_fibers
  crossingEquiv := R.smoothCrossingEquiv c
  deleted_not_incoming := R.smooth_deleted_not_incoming c
  incoming_map := R.smooth_incoming_map c
  outgoing_map := R.smooth_outgoing_map c
  continuation_map := R.smooth_continuation_map c
  through_map := R.smooth_through_map c
  overBranch_map := R.smooth_overBranch_map c
  crossingSign_map := R.smooth_crossingSign_map c

end SignedArcContraction
end
end DirectGLSSW.HOMFLY



