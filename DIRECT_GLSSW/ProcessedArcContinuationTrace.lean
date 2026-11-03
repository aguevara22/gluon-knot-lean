import ProcessedArcContinuationStep
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- A finite literal history reflects continuation between arcs with original
ancestors. No original adjacency or order is supplied. -/
theorem MarkedParentTrace.arcOrigin_continuation {s t : MarkedParentState}
    (h : MarkedParentTrace s t) :
    ∀ (e f : Fin t.1.nArc) (a b : Fin s.1.nArc),
      t.1.continuation e = f → h.arcOrigin e = some a → h.arcOrigin f = some b →
      s.1.continuation a = b := by
  induction h with
  | nil s =>
    intro e f a b hef hea hfb
    have he := Option.some.inj hea
    have hf := Option.some.inj hfb
    subst a
    subst b
    exact hef
  | cons step tail ih =>
    intro e f a b hef hea hfb
    cases hecode : tail.arcOrigin e with
    | none => simp [MarkedParentTrace.arcOrigin,hecode] at hea
    | some a' =>
      cases hfcode : tail.arcOrigin f with
      | none => simp [MarkedParentTrace.arcOrigin,hfcode] at hfb
      | some b' =>
        have ha : step.arcOrigin a' = some a := by
          simpa only [MarkedParentTrace.arcOrigin,hecode,Option.some_bind] using hea
        have hb : step.arcOrigin b' = some b := by
          simpa only [MarkedParentTrace.arcOrigin,hfcode,Option.some_bind] using hfb
        exact step.arcOrigin_continuation a' b' a b (ih e f a' b' hef hecode hfcode) ha hb

/-- Consecutive old-code arcs in the actual next detached child have consecutive
original ancestors, produced by historical marked-arc exclusion. -/
theorem MarkedParentTrace.detached_old_arcs_continuation {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (e f : Fin R.diagram.nArc) (a b : Fin t.1.nArc)
    (hef : R.diagram.continuation e = f)
    (hea : (smoothArcEquiv t.1).symm (R.arcEquiv e).val = Sum.inl a)
    (hfb : (smoothArcEquiv t.1).symm (R.arcEquiv f).val = Sum.inl b) :
    ∃ a₀ b₀ : Fin s.1.nArc, h.arcOrigin a = some a₀ ∧ h.arcOrigin b = some b₀ ∧
      s.1.continuation a₀ = b₀ := by
  obtain ⟨a₀,ha₀⟩ := h.detached_old_arc_has_origin c hc R e a hea
  obtain ⟨b₀,hb₀⟩ := h.detached_old_arc_has_origin c hc R f b hfb
  have he : (R.arcEquiv e).val = smoothArcEquiv t.1 (Sum.inl a) := by
    simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv t.1) hea
  have hf : (R.arcEquiv f).val = smoothArcEquiv t.1 (Sum.inl b) := by
    simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv t.1) hfb
  have hcont := R.continuation_eq e
  rw [hef,he,hf] at hcont
  have hab := smooth_old_continuation_reflect t.1 c a b hcont.symm
  exact ⟨a₀,b₀,ha₀,hb₀,h.arcOrigin_continuation a b a₀ b₀ hab ha₀ hb₀⟩

end DirectGLSSW.HOMFLY
