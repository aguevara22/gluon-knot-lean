import GeometricCursorBoundary
import PhysicalSuffixCrossingData
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- Opening at zero preserves the actual parameter of the lower visit. -/
theorem exposed_lower_parameter {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (z : ActiveArc.Crossing (cutArc q 0)) :
    polygonEventParameter q (visit q (exposedCrossingEquiv q 0 hq he z) 0)=
      ActiveArc.leftParameter (cutArc q 0) z := by
  obtain ⟨j,hj,hp⟩ := exposed_lower_visit_parameter q hq he z
  have hfirst := exposedCrossing_firstEdge q hq he z
  have hv := congrArg Fin.val hj
  have hlabel : (edgeLabel 0 (ActiveArc.visitEdge (cutArc q 0) (z,false))).val=z.val.1.val+1 := by
    exact zero_edgeLabel_val _
  rw [hlabel] at hv
  fin_cases j
  · exact hp
  · have hh := (exposedCrossingEquiv q 0 hq he z).property.1
    change (exposedCrossingEquiv q 0 hq he z).val.1.val<
      (exposedCrossingEquiv q 0 hq he z).val.2.val at hh
    change (exposedCrossingEquiv q 0 hq he z).val.2.val=z.val.1.val+1 at hv
    omega

/-- The first-edge physical crossing has its literal original event and affine
parameter. This does not use first-bad selection or a history cursor choice. -/
theorem physical_first_original_event {n m : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (A : ℕ) (hs : A+m=n)
    (θ : ℝ) (h0 : 0≤θ) (h1 : θ<1)
    (c : ActiveArc.Crossing (ActiveArc.Cursor.moveStart
      (ActiveArc.Split.suffixWord (cutArc q 0) A m hs) θ)) (hc : c.val.1=0) :
    let z := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
      A m hs θ h0 h1 c).val
    let x := visit q (exposedCrossingEquiv q 0 hq he z) 0
    (polygonEventEdge q x).val=A+1 ∧
    polygonEventParameter q x=θ+(1-θ)*ActiveArc.leftParameter
      (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) A m hs) θ) c := by
  dsimp only
  constructor
  · change (exposedCrossingEquiv q 0 hq he _).val.1.val=A+1
    rw [exposedCrossing_firstEdge]
    have H := ActiveArc.Split.suffixWordCrossingEquiv_left_label
      (cutArc q 0) (cutArc_regular q 0 hq) A m hs θ h0 h1 c
    rw [hc] at H
    simpa using congrArg (fun v : ℕ => v+1) H
  · rw [exposed_lower_parameter]
    exact suffixWordCrossingEquiv_leftParameter q (cutArc_regular q 0 hq) A m hs θ h0 h1 c hc
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
