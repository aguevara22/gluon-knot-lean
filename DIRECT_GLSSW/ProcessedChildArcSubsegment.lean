import ProcessedArcSubsegmentTrace
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Every old-code arc of the next actual detached child lies in order on one
original ancestor segment. Ancestry is produced from actual historical mark
exclusion; no coordinate or order identification is supplied. -/
theorem MarkedParentTrace.detached_old_arc_subsegment {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (e : Fin R.diagram.nArc) (a : Fin t.1.nArc)
    (hea : (smoothArcEquiv t.1).symm (R.arcEquiv e).val = Sum.inl a) :
    ∃ (a₀ : Fin s.1.nArc) (u v : ℝ), h.arcOrigin a = some a₀ ∧
      0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
      R.diagram.vertexPoint (R.diagram.arcSource e) =
        affinePoint (s.1.vertexPoint (s.1.arcSource a₀)) (s.1.vertexPoint (s.1.arcTarget a₀)) u ∧
      R.diagram.vertexPoint (R.diagram.arcTarget e) =
        affinePoint (s.1.vertexPoint (s.1.arcSource a₀)) (s.1.vertexPoint (s.1.arcTarget a₀)) v := by
  obtain ⟨a₀,ha₀⟩ := h.detached_old_arc_has_origin c hc R e a hea
  obtain ⟨u,v,hu,huv,hv,has,hat⟩ := h.arcOrigin_subsegment a a₀ ha₀
  obtain ⟨r,z,hr,hrz,hz,hes,het⟩ := smooth_old_arc_subsegment t.1 c a
  have he : (R.arcEquiv e).val = smoothArcEquiv t.1 (Sum.inl a) := by
    simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv t.1) hea
  have hends := componentRestriction_arc_endpoints R e
  rw [he] at hends
  obtain ⟨h0,hlt,h1,hcs,hct⟩ := affine_subsegment_comp
    (s.1.vertexPoint (s.1.arcSource a₀)) (s.1.vertexPoint (s.1.arcTarget a₀))
    u v r z hu huv hv hr hrz hz
  refine ⟨a₀,u+(v-u)*r,u+(v-u)*z,ha₀,h0,hlt,h1,?_,?_⟩
  · rw [hends.1,hes,has,hat]
    exact hcs
  · rw [hends.2,het,has,hat]
    exact hct

end DirectGLSSW.HOMFLY
