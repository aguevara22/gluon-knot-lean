import ProcessedCrossingOriginTrace
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

def smoothedRestrictionCrossingOrigin (D : PLLinkDiagram) (c : Fin D.nCrossing)
    {C : diagramComponent (smoothCrossing D c)} (R : ComponentRestriction (smoothCrossing D c) C) :
    Fin R.diagram.nCrossing ↪ Fin D.nCrossing where
  toFun d := ((smoothCrossingEquiv D c).symm (R.crossingEquiv d).val).val
  inj' := by
    intro d e hde
    apply R.crossingEquiv.injective
    apply Subtype.ext
    apply (smoothCrossingEquiv D c).symm.injective
    exact Subtype.ext hde

theorem smoothedRestrictionCrossingOrigin_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing)
    {C : diagramComponent (smoothCrossing D c)} (R : ComponentRestriction (smoothCrossing D c) C)
    (d : Fin R.diagram.nCrossing) (i : Fin 2) :
    smoothOldArcOrigin D (R.arcEquiv (R.diagram.incoming d i)).val =
      some (D.incoming (smoothedRestrictionCrossingOrigin D c R d) i) := by
  rw [R.incoming_eq]
  change smoothOldArcOrigin D (smoothArcEquiv D (Sum.inl _)) = _
  simp only [smoothOldArcOrigin,Equiv.symm_apply_apply]
  rfl

/-- If both actual incoming arcs survive in one exact component of a self-cut,
their crossing survives there too. The cut crossing itself is excluded by the
proved separation of its two incoming ports into different components. -/
theorem smoothedRestrictionCrossingOrigin_complete (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    {C : diagramComponent (smoothCrossing D c)} (R : ComponentRestriction (smoothCrossing D c) C)
    (d : Fin D.nCrossing)
    (hports : ∀ i : Fin 2, ∃ e : Fin R.diagram.nArc,
      smoothOldArcOrigin D (R.arcEquiv e).val = some (D.incoming d i)) :
    ∃ e : Fin R.diagram.nCrossing, smoothedRestrictionCrossingOrigin D c R e = d := by
  have hcomp (i : Fin 2) : componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl (D.incoming d i))) = C := by
    obtain ⟨e,he⟩ := hports i
    have hm := (smoothOldArcOrigin_some_iff D (R.arcEquiv e).val _).mp he
    exact hm ▸ (R.arcEquiv e).property
  have hd : d ≠ c := by
    intro hdc
    subst d
    have hconn (i : Fin 2) : componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr i)) = C := by
      have hh := componentOf_apply (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inl (D.incoming c i)))
      rw [Gemini.smooth_step_incoming] at hh
      exact hh.trans (hcomp i)
    have hh : rootSelfCutComponents D c hself 0 (Sum.inl false) =
        rootSelfCutComponents D c hself 0 (Sum.inl true) :=
      ((rootSelfCutComponents_false D c hself 0).trans (hconn 0)).trans
        ((rootSelfCutComponents_true D c hself 0).trans (hconn (otherBranch 0))).symm
    have hbad := (rootSelfCutComponents D c hself 0).injective hh
    cases hbad
  let e : ComponentCrossing (smoothCrossing D c) C := ⟨smoothCrossingEquiv D c ⟨d,hd⟩,by
    intro i
    rw [parentRoot_retained_incoming]
    exact hcomp i⟩
  refine ⟨R.crossingEquiv.symm e,?_⟩
  change ((smoothCrossingEquiv D c).symm (R.crossingEquiv (R.crossingEquiv.symm e)).val).val = d
  simp only [Equiv.apply_symm_apply,e,Equiv.symm_apply_apply]

end DirectGLSSW.HOMFLY
