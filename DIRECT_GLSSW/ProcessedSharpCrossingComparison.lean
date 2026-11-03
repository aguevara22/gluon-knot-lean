import ProcessedSharpInterval
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- The actual support contains one selected crossing, hence is nonalternating. -/
theorem sharpSupport_nonalternating :
    PolygonNonalternation.polygonNonalternating q hq.g2 (sharpSupport q hq h c) := by
  intro a ha b hb hab
  have ha' := Finset.mem_singleton.mp ha
  have hb' := Finset.mem_singleton.mp hb
  exact (hab (ha'.trans hb'.symm)).elim

def historicalSharpDiagram : PLLinkDiagram :=
  SharpDaughter.sharpDaughterDiagram q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R) (sharpSupport_nonalternating q hq h c)

/-- Both maps are constructed from actual retained ports; no matching-crossing
certificate is supplied. -/
def historicalSharpCrossingEquiv :
    Fin R.diagram.nCrossing ≃ Fin (historicalSharpDiagram q hq h c hc R).nCrossing :=
  (h.detachedCrossingEquiv c hc R).trans
    ((sharpCrossingIntervalEquiv q hq h c hc R).symm.trans
      (SharpDaughter.crossingEquiv q hq (sharpSupport q hq h c)
        (sharpIntervalComponent q hq h c hc R)).symm)

theorem historicalSharpCrossingEquiv_origin (d : Fin R.diagram.nCrossing) :
    SharpDaughter.oldCrossing q hq (sharpSupport q hq h c)
      (sharpIntervalComponent q hq h c hc R)
      (historicalSharpCrossingEquiv q hq h c hc R d) =
    h.detachedCrossingOrigin c R d := by
  exact congrArg Subtype.val
    ((SharpDaughter.crossingEquiv q hq (sharpSupport q hq h c)
      (sharpIntervalComponent q hq h c hc R)).apply_symm_apply
      ((sharpCrossingIntervalEquiv q hq h c hc R).symm (h.detachedCrossingEquiv c hc R d)))

/-- Exact through, over and sign data for the actual sharp subdivision diagram. -/
theorem historicalSharpCrossingEquiv_data (d : Fin R.diagram.nCrossing) :
    R.diagram.through d = (historicalSharpDiagram q hq h c hc R).through
      (historicalSharpCrossingEquiv q hq h c hc R d) ∧
    R.diagram.overBranch d = (historicalSharpDiagram q hq h c hc R).overBranch
      (historicalSharpCrossingEquiv q hq h c hc R d) ∧
    crossingSign R.diagram d = crossingSign (historicalSharpDiagram q hq h c hc R)
      (historicalSharpCrossingEquiv q hq h c hc R d) := by
  have ho := historicalSharpCrossingEquiv_origin q hq h c hc R d
  refine ⟨?_,?_,?_⟩
  · exact (h.detachedCrossingOrigin_through c R d).trans
      (congrArg (positivePolygonEventDiagram q hq).through ho).symm
  · exact (h.detachedCrossingOrigin_over c hc R d).trans
      (congrArg (positivePolygonEventDiagram q hq).overBranch ho).symm
  · calc
      crossingSign R.diagram d = crossingSign (positivePolygonEventDiagram q hq)
          (h.detachedCrossingOrigin c R d) := h.detachedCrossingOrigin_sign c hc R d
      _ = Sign.pos := positivePolygonEventDiagram_crossingSign q hq _
      _ = _ := (SharpDaughter.sharpDaughterDiagram_crossingSign q hq
        (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R)
        (sharpSupport_nonalternating q hq h c) _).symm

/-- Matching incoming ports have the same produced original interval position. -/
theorem historicalSharpCrossingEquiv_incoming (d : Fin R.diagram.nCrossing) (i : Fin 2) :
    ∃ j : Fin (detachedOrbitSize t c R-1),
      detachedOldOrbitArc c R j = R.diagram.incoming d i ∧
      h.detachedOriginalArc c hc R j =
        SharpDaughter.oldArc q hq (sharpSupport q hq h c)
          (sharpIntervalComponent q hq h c hc R)
          ((historicalSharpDiagram q hq h c hc R).incoming
            (historicalSharpCrossingEquiv q hq h c hc R d) i) := by
  obtain ⟨j,hj,hj'⟩ := h.detachedCrossingOrigin_incoming_position c hc R d i
  refine ⟨j,hj,?_⟩
  change _ = SharpDaughter.oldArc q hq (sharpSupport q hq h c)
    (sharpIntervalComponent q hq h c hc R)
    (SharpDaughter.incomingIndex q hq (sharpSupport q hq h c)
      (sharpIntervalComponent q hq h c hc R) (historicalSharpCrossingEquiv q hq h c hc R d) i)
  rw [SharpDaughter.old_incoming,historicalSharpCrossingEquiv_origin]
  exact hj'
end DirectGLSSW.HOMFLY.ProcessedExposedChild
