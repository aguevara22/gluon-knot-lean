import HOMFLYRegularEndpointTransport
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open DirectGLSSW.PermutationOrbits

/-- Exact component extraction preserves both regular endpoints of a retained arc. -/
theorem LowestRowContract.ComponentRestriction.regular_arc_endpoints
    {D : PLLinkDiagram} {C : diagramComponent D}
    (R : LowestRowContract.ComponentRestriction D C) (e : Fin R.diagram.nArc)
    (hs : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcSource (R.arcEquiv e).val)
    (ht : ∀ d : Fin D.nCrossing, D.crossingVertex d ≠ D.arcTarget (R.arcEquiv e).val) :
    (∀ d : Fin R.diagram.nCrossing, R.diagram.crossingVertex d ≠ R.diagram.arcSource e) ∧
    (∀ d : Fin R.diagram.nCrossing, R.diagram.crossingVertex d ≠ R.diagram.arcTarget e) := by
  constructor
  · apply R.regular_vertex
    simpa only [R.source_eq] using hs
  · apply R.regular_vertex
    simpa only [R.target_eq] using ht

/-- Exclusion of an actual smoothing connector excludes both of its corner vertices. -/
theorem smooth_connector_endpoints_not_component (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (C : diagramComponent (smoothCrossing D c))
    (hne : componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inr i)) ≠ C) :
    (¬ ∃ a : LowestRowContract.ComponentArc (smoothCrossing D c) C,
      (smoothCrossing D c).arcSource a.val =
        (smoothCrossing D c).arcSource (smoothArcEquiv D (Sum.inr i))) ∧
    (¬ ∃ a : LowestRowContract.ComponentArc (smoothCrossing D c) C,
      (smoothCrossing D c).arcSource a.val =
        (smoothCrossing D c).arcTarget (smoothArcEquiv D (Sum.inr i))) := by
  constructor
  · exact regular_vertex_not_componentVertex _ C _
      (smooth_connector_source_regular D c i) _ (Or.inl rfl) hne
  · exact regular_vertex_not_componentVertex _ C _
      (smooth_connector_target_regular D c i) _ (Or.inr rfl) hne

end DirectGLSSW.HOMFLY
