import ProcessedArcOriginTrace
import SmoothingOldTurns
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable

/-- Consecutive old codes in the literal smoothing were already consecutive.
An incoming cut port instead has a fresh connector successor, so cannot satisfy
the actual old-code successor equality. -/
theorem smooth_old_continuation_reflect (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (a b : Fin D.nArc)
    (hab : (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a)) =
      smoothArcEquiv D (Sum.inl b)) : D.continuation a = b := by
  have hn : ∀ i : Fin 2, a ≠ D.incoming c i := by
    intro i hi
    rw [hi,Gemini.smooth_step_incoming] at hab
    have hf := (smoothArcEquiv D).injective hab
    cases hf
  rw [old_arc_continuation D c a hn] at hab
  exact Sum.inl.inj ((smoothArcEquiv D).injective hab)

/-- One actual parent step reflects continuation on arcs with literal old origins. -/
theorem MarkedParentStep.arcOrigin_continuation {s t : MarkedParentState}
    (step : MarkedParentStep s t) (e f : Fin t.1.nArc) (a b : Fin s.1.nArc)
    (hef : t.1.continuation e = f)
    (hea : step.arcOrigin e = some a) (hfb : step.arcOrigin f = some b) :
    s.1.continuation a = b := by
  cases step with
  | switched S c hc hgood =>
    have he := Option.some.inj hea
    have hf := Option.some.inj hfb
    subst a
    subst b
    exact hef
  | @smoothed D T S c hc hgood R =>
    have he := (smoothOldArcOrigin_some_iff D (R.arcEquiv e).val a).mp hea
    have hf := (smoothOldArcOrigin_some_iff D (R.arcEquiv f).val b).mp hfb
    apply smooth_old_continuation_reflect D c a b
    have hcont := R.continuation_eq e
    rw [hef,hf,he] at hcont
    exact hcont.symm

end DirectGLSSW.HOMFLY
