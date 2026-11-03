import HOMFLYRegularDeletionSmoothMaps

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
namespace SignedRegularDeletion
variable {D E : PLLinkDiagram} (R : SignedRegularDeletion D E)

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

theorem smooth_selected_not_ports (c : Fin D.nCrossing) (d : Fin (D.nCrossing - 1)) (i : Fin 2) :
    (smoothCrossing D c).incoming d i ≠ R.smoothDeleted ∧
    (smoothCrossing D c).incoming d i ≠ R.smoothRetained ∧
    (smoothCrossing D c).outgoing d i ≠ R.smoothDeleted ∧
    (smoothCrossing D c).outgoing d i ≠ R.smoothRetained := by
  let oldD := (DirectGLSSW.HOMFLY.smoothCrossingEquiv D c).symm d
  have hp := R.selected_not_ports oldD.val i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; exact hp.1 (Sum.inl.inj ((smoothArcEquiv D).injective h))
  · intro h; exact hp.2.1 (Sum.inl.inj ((smoothArcEquiv D).injective h))
  · intro h; exact hp.2.2.1 (Sum.inl.inj ((smoothArcEquiv D).injective h))
  · intro h; exact hp.2.2.2 (Sum.inl.inj ((smoothArcEquiv D).injective h))

/-- Smoothing retains the explicit signed regular deletion on the actual two
children. Independent geometric radius choices require no equality here. -/
def smooth (c : Fin D.nCrossing) :
    SignedRegularDeletion (smoothCrossing D c) (smoothCrossing E (R.crossingEquiv c)) where
  deleted := R.smoothDeleted
  retained := R.smoothRetained
  distinct := R.smooth_selected_distinct
  successor := R.smooth_selected_successor c
  arcMap := R.smoothArcMap
  arcMap_surjective := R.smoothArcMap_surjective
  arcMap_fibers := R.smoothArcMap_fibers
  crossingEquiv := R.smoothCrossingEquiv c
  selected_not_ports := R.smooth_selected_not_ports c
  incoming_map := R.smooth_incoming_map c
  outgoing_map := R.smooth_outgoing_map c
  continuation_map := R.smooth_continuation_map c
  through_map := R.smooth_through_map c
  overBranch_map := R.smooth_overBranch_map c
  crossingSign_map := R.smooth_crossingSign_map c

end SignedRegularDeletion
end
end DirectGLSSW.HOMFLY



