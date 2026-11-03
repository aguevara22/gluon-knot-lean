import SmoothingOldArcSubsegment
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Exact component restriction preserves both physical endpoints, including
vertices demoted from mixed crossings. -/
theorem componentRestriction_arc_endpoints {D : PLLinkDiagram} {C : Component D.continuation}
    (R : ComponentRestriction D C) (e : Fin R.diagram.nArc) :
    R.diagram.vertexPoint (R.diagram.arcSource e) = D.vertexPoint (D.arcSource (R.arcEquiv e).val) ∧
    R.diagram.vertexPoint (R.diagram.arcTarget e) = D.vertexPoint (D.arcTarget (R.arcEquiv e).val) := by
  constructor <;> simp only [R.vertexPoint_eq,R.source_eq,R.target_eq]

/-- An actual old arc in one physical parent step is a nondegenerate forward
subsegment of the arc selected by literal old-code decoding. -/
theorem MarkedParentStep.arcOrigin_subsegment {s t : MarkedParentState}
    (step : MarkedParentStep s t) (e : Fin t.1.nArc) (a : Fin s.1.nArc)
    (ha : step.arcOrigin e = some a) :
    ∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
      t.1.vertexPoint (t.1.arcSource e) =
        affinePoint (s.1.vertexPoint (s.1.arcSource a)) (s.1.vertexPoint (s.1.arcTarget a)) u ∧
      t.1.vertexPoint (t.1.arcTarget e) =
        affinePoint (s.1.vertexPoint (s.1.arcSource a)) (s.1.vertexPoint (s.1.arcTarget a)) v := by
  cases step with
  | switched S c hc hgood =>
    have hea : e=a := Option.some.inj ha
    subst a
    refine ⟨0,1,le_rfl,zero_lt_one,le_rfl,?_,?_⟩ <;> simp [affinePoint] <;> rfl
  | @smoothed D T S c hc hgood R =>
    have hea := (smoothOldArcOrigin_some_iff D (R.arcEquiv e).val a).mp ha
    obtain ⟨u,v,hu,huv,hv,hs,ht⟩ := smooth_old_arc_subsegment D c a
    refine ⟨u,v,hu,huv,hv,?_,?_⟩
    · change R.diagram.vertexPoint (R.diagram.arcSource e) = _
      rw [(componentRestriction_arc_endpoints R e).1,hea]
      exact hs
    · change R.diagram.vertexPoint (R.diagram.arcTarget e) = _
      rw [(componentRestriction_arc_endpoints R e).2,hea]
      exact ht

end DirectGLSSW.HOMFLY
