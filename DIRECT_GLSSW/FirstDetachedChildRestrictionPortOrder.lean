import FirstDetachedChildPortOrder
import ComponentRestrictionOrbits

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.LowestRowContract HOMFLY.ComponentRestrictionComparison PermutationOrbits
attribute [local instance] Classical.propDecidable

private theorem restriction_same_component {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) (r a : Fin R.diagram.nArc) :
    componentOf R.diagram.continuation a=componentOf R.diagram.continuation r := by
  let y : Fibre D.continuation (componentOf D.continuation (arcEmbedding R r)) :=
    ⟨arcEmbedding R a,(R.arcEquiv a).property.trans (R.arcEquiv r).property.symm⟩
  let x:=(rootedFibreEquiv R r).symm y
  have he : arcEmbedding R x.val=arcEmbedding R a := by
    have h:=congrArg Subtype.val ((rootedFibreEquiv R r).apply_symm_apply y)
    exact h
  have hx : x.val=a := arcEmbedding_injective R he
  exact hx ▸ x.property

private theorem orbitPosition_root_eq {α : Type*} [Fintype α] (p : Equiv.Perm α)
    (r s : α) (hrs : r=s) (x : Fibre p (componentOf p r)) (y : Fibre p (componentOf p s))
    (hxy : x.val=y.val) : ((orbitEnumeration p r).symm x).val=((orbitEnumeration p s).symm y).val := by
  subst s
  have h : x=y := Subtype.ext hxy
  subst y
  rfl

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : CyclicGeneric q) (hR : Regular q)
variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)
variable (R : ComponentRestriction
  (smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c)))
  (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)))

/-- The exact restriction arc corresponding to actual connector 1. -/
def firstDetachedChildRestrictionRoot : Fin R.diagram.nArc :=
  R.arcEquiv.symm ⟨smoothArcEquiv (positivePolygonEventDiagram q hQ) (Sum.inr (1 : Fin 2)),rfl⟩

theorem firstDetachedChildRestrictionRoot_embedding :
    arcEmbedding R (firstDetachedChildRestrictionRoot q hQ c R) =
      smoothArcEquiv (positivePolygonEventDiagram q hQ) (Sum.inr (1 : Fin 2)) :=
  congrArg Subtype.val (R.arcEquiv.apply_symm_apply _)

/-- Literal restricted incoming arc of the specified physical child crossing. -/
def firstDetachedChildRestrictionIncomingFibre
    (d : PolygonCrossing (child q hR c hfirst hcut)) (i : Fin 2) :
    Fibre R.diagram.continuation
      (componentOf R.diagram.continuation (firstDetachedChildRestrictionRoot q hQ c R)) :=
  ⟨R.diagram.incoming (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d)) i,
    restriction_same_component R _ _⟩

/-- The exact restriction preserves the actual connector-rooted physical port rank. -/
theorem firstDetachedChildRestrictionIncoming_position
    (d : PolygonCrossing (child q hR c hfirst hcut)) (i : Fin 2) :
    ((orbitEnumeration R.diagram.continuation (firstDetachedChildRestrictionRoot q hQ c R)).symm
      (firstDetachedChildRestrictionIncomingFibre q hQ hR c hfirst hcut R d i)).val =
    ((orbitEnumeration (smoothCrossing (positivePolygonEventDiagram q hQ) (crossingFin q (polygonCrossingOfArc q c))).continuation
      (smoothArcEquiv (positivePolygonEventDiagram q hQ) (Sum.inr (1 : Fin 2)))).symm
      (firstDetachedChildIncomingFibre q hQ hR c hfirst hcut d i)).val := by
  let r:=firstDetachedChildRestrictionRoot q hQ c R
  let x:=firstDetachedChildRestrictionIncomingFibre q hQ hR c hfirst hcut R d i
  have ht:=rootedOrbitPosition_transport R r x
  refine ht.symm.trans (orbitPosition_root_eq _ _ _
    (firstDetachedChildRestrictionRoot_embedding q hQ c R) (rootedFibreEquiv R r x)
    (firstDetachedChildIncomingFibre q hQ hR c hfirst hcut d i) ?_)
  rw [rootedFibreEquiv_val]
  change (R.arcEquiv (R.diagram.incoming (R.crossingEquiv.symm (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut d)) i)).val=_
  rw [R.incoming_eq,R.crossingEquiv.apply_symm_apply]
  rfl

/-- Every actual component restriction has the sharp child's physical port order,
with the root explicitly pulled back from the genuine smoothing connector. -/
theorem firstDetachedChildRestriction_incoming_orbitPosition_lt_iff
    (d e : PolygonCrossing (child q hR c hfirst hcut)) (i j : Fin 2) :
    ((orbitEnumeration R.diagram.continuation (firstDetachedChildRestrictionRoot q hQ c R)).symm
      (firstDetachedChildRestrictionIncomingFibre q hQ hR c hfirst hcut R d i)).val <
    ((orbitEnumeration R.diagram.continuation (firstDetachedChildRestrictionRoot q hQ c R)).symm
      (firstDetachedChildRestrictionIncomingFibre q hQ hR c hfirst hcut R e j)).val ↔
    (polygonEventOrder (child q hR c hfirst hcut) (child_noTriple q hR c hfirst hcut)).lt
      (PolygonDrawing.visit (child q hR c hfirst hcut) d i) (PolygonDrawing.visit (child q hR c hfirst hcut) e j) := by
  rw [firstDetachedChildRestrictionIncoming_position,firstDetachedChildRestrictionIncoming_position]
  exact firstDetachedChild_incoming_orbitPosition_lt_iff q hQ hR c hfirst hcut d e i j
end DirectGLSSW.ActiveArc.Split
