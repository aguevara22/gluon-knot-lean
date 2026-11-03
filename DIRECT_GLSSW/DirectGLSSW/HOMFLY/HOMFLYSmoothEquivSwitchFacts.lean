import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY

theorem smoothArcEquiv_switch (D : PLLinkDiagram) (d : Fin D.nCrossing) :
    smoothArcEquiv (switchCrossing D d) = smoothArcEquiv D := by
  rfl

theorem smoothCrossingEquiv_switch (D : PLLinkDiagram) (d c : Fin D.nCrossing) :
    smoothCrossingEquiv (switchCrossing D d) c = smoothCrossingEquiv D c := by
  rfl


theorem smoothIncoming_switch (D : PLLinkDiagram) (d c : Fin D.nCrossing) :
    smoothIncoming (switchCrossing D d) c = smoothIncoming D c := by
  funext x i
  unfold smoothIncoming
  simp only [smoothArcEquiv_switch, smoothCrossingEquiv_switch]
  simp [switchCrossing]

theorem smoothOutgoing_switch (D : PLLinkDiagram) (d c : Fin D.nCrossing) :
    smoothOutgoing (switchCrossing D d) c = smoothOutgoing D c := by
  funext x i
  unfold smoothOutgoing
  simp only [smoothArcEquiv_switch, smoothCrossingEquiv_switch]
  simp [switchCrossing]

theorem smoothThrough_switch (D : PLLinkDiagram) (d c : Fin D.nCrossing) :
    smoothThrough (switchCrossing D d) c = smoothThrough D c := by
  funext x
  unfold smoothThrough
  simp only [smoothCrossingEquiv_switch]
  simp [switchCrossing]


theorem smoothContinuationGeometryCode_switch (D : PLLinkDiagram)
    (d c : Fin D.nCrossing) :
    smoothContinuationGeometryCode (switchCrossing D d) c =
      smoothContinuationGeometryCode D c := by
  simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust,
    smoothContinuationCodeLocal, smoothContinuationAdjustLocal, switchCrossing]

theorem smoothContinuation_switch (D : PLLinkDiagram)
    (d c : Fin D.nCrossing) :
    smoothContinuation (switchCrossing D d) c = smoothContinuation D c := by
  simp [smoothContinuation, smoothContinuationGeometryCode_switch,
    smoothArcEquiv_switch]


theorem smoothOverBranch (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    (smoothCrossing D c).overBranch =
      fun x => D.overBranch ((smoothCrossingEquiv D c).symm x).val := by
  rfl

theorem smoothContinuationProjection (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    (smoothCrossing D c).continuation = smoothContinuation D c := by
  rfl

end DirectGLSSW.HOMFLY









