import ProcessedChildOriginalWord
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
namespace MarkedParentStep

/-- Every current crossing is an actual retained old crossing. The map is total
and injective even though the smoothing operation deletes its selected crossing. -/
def crossingOrigin {s t : MarkedParentState} (step : MarkedParentStep s t) :
    Fin t.1.nCrossing ↪ Fin s.1.nCrossing :=
  match step with
  | .switched _ _ _ _ => Function.Embedding.refl _
  | @smoothed D T S c hc hgood R =>
    { toFun := fun d => ((smoothCrossingEquiv D c).symm (R.crossingEquiv d).val).val
      inj' := by
        intro d e hde
        apply R.crossingEquiv.injective
        apply Subtype.ext
        apply (smoothCrossingEquiv D c).symm.injective
        exact Subtype.ext hde }

theorem crossingOrigin_incoming {s t : MarkedParentState} (step : MarkedParentStep s t)
    (d : Fin t.1.nCrossing) (i : Fin 2) :
    step.arcOrigin (t.1.incoming d i) = some (s.1.incoming (step.crossingOrigin d) i) := by
  cases step with
  | switched S c hc hgood => rfl
  | @smoothed D T S c hc hgood R =>
    let old := (smoothCrossingEquiv D c).symm (R.crossingEquiv d).val
    change smoothOldArcOrigin D (R.arcEquiv (R.diagram.incoming d i)).val =
      some (D.incoming old.val i)
    rw [R.incoming_eq]
    change smoothOldArcOrigin D (smoothArcEquiv D (Sum.inl (D.incoming old.val i))) = _
    simp only [smoothOldArcOrigin,Equiv.symm_apply_apply]

theorem crossingOrigin_outgoing {s t : MarkedParentState} (step : MarkedParentStep s t)
    (d : Fin t.1.nCrossing) (i : Fin 2) :
    step.arcOrigin (t.1.outgoing d i) = some (s.1.outgoing (step.crossingOrigin d) i) := by
  cases step with
  | switched S c hc hgood => rfl
  | @smoothed D T S c hc hgood R =>
    let old := (smoothCrossingEquiv D c).symm (R.crossingEquiv d).val
    change smoothOldArcOrigin D (R.arcEquiv (R.diagram.outgoing d i)).val =
      some (D.outgoing old.val i)
    rw [R.outgoing_eq]
    change smoothOldArcOrigin D (smoothArcEquiv D (Sum.inl (D.outgoing old.val i))) = _
    simp only [smoothOldArcOrigin,Equiv.symm_apply_apply]

theorem crossingOrigin_point {s t : MarkedParentState} (step : MarkedParentStep s t)
    (d : Fin t.1.nCrossing) :
    t.1.vertexPoint (t.1.crossingVertex d) =
      s.1.vertexPoint (s.1.crossingVertex (step.crossingOrigin d)) := by
  cases step with
  | switched S c hc hgood => rfl
  | @smoothed D T S c hc hgood R =>
    let old := (smoothCrossingEquiv D c).symm (R.crossingEquiv d).val
    change R.diagram.vertexPoint (R.diagram.crossingVertex d) = D.vertexPoint (D.crossingVertex old.val)
    rw [R.vertexPoint_eq,R.crossingVertex_eq]
    change smoothVertexPointGeometryCode D c (smoothEpsilon D c)
      ((smoothVertexEquiv D c).symm (smoothVertexEquiv D c (Sum.inl (D.crossingVertex old.val)))) = _
    have hne : D.crossingVertex old.val ≠ D.crossingVertex c :=
      fun hh => old.property (D.crossingVertex_injective hh)
    simp only [Equiv.symm_apply_apply,smoothVertexPointGeometryCode,if_neg hne]

theorem crossingOrigin_through {s t : MarkedParentState} (step : MarkedParentStep s t)
    (d : Fin t.1.nCrossing) : t.1.through d = s.1.through (step.crossingOrigin d) := by
  cases step with
  | switched S c hc hgood => rfl
  | @smoothed D T S c hc hgood R => exact R.through_eq d

end MarkedParentStep
end DirectGLSSW.HOMFLY
