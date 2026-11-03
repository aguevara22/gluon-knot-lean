import ProcessedParentHistory
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract ProcessedParentMarks
attribute [local instance] Classical.propDecidable

/-- Literal old-label decoding of the actual smoothing arc equivalence. -/
def smoothOldArcOrigin (D : PLLinkDiagram) (e : Fin (D.nArc+2)) : Option (Fin D.nArc) :=
  match (smoothArcEquiv D).symm e with
  | Sum.inl a => some a
  | Sum.inr _ => none

theorem smoothOldArcOrigin_some_iff (D : PLLinkDiagram) (e : Fin (D.nArc+2))
    (a : Fin D.nArc) :
    smoothOldArcOrigin D e = some a ↔ e = smoothArcEquiv D (Sum.inl a) := by
  constructor
  · intro he
    cases hcode : (smoothArcEquiv D).symm e with
    | inl b =>
      have hb : b=a := Option.some.inj (by simpa only [smoothOldArcOrigin,hcode] using he)
      have h := congrArg (smoothArcEquiv D) hcode
      simpa only [Equiv.apply_symm_apply,hb] using h
    | inr i => simp [smoothOldArcOrigin,hcode] at he
  · intro he
    subst e
    simp only [smoothOldArcOrigin,Equiv.symm_apply_apply]

namespace MarkedParentStep

/-- Switches preserve an actual arc label. Smoothing followed by actual
restriction decodes an old arc or the newly born connector. -/
def arcOrigin {s t : MarkedParentState} (step : MarkedParentStep s t) :
    Fin t.1.nArc → Option (Fin s.1.nArc) :=
  match step with
  | .switched _ _ _ _ => fun e => some e
  | @smoothed D T S c hc hgood R => fun e => smoothOldArcOrigin D (R.arcEquiv e).val

theorem arcOrigin_some_injective {s t : MarkedParentState} (step : MarkedParentStep s t)
    (e f : Fin t.1.nArc) (a : Fin s.1.nArc)
    (he : step.arcOrigin e = some a) (hf : step.arcOrigin f = some a) : e=f := by
  cases step with
  | switched S c hc hgood => exact Option.some.inj (he.trans hf.symm)
  | smoothed S c hc hgood R =>
    apply R.arcEquiv.injective
    apply Subtype.ext
    exact ((smoothOldArcOrigin_some_iff _ _ _).mp he).trans
      ((smoothOldArcOrigin_some_iff _ _ _).mp hf).symm

theorem arcOrigin_markEmbedding {s t : MarkedParentState} (step : MarkedParentStep s t)
    (x : StateMarks s) : step.arcOrigin (step.markEmbedding x).val = some x.val := by
  cases step with
  | switched S c hc hgood => rfl
  | @smoothed D T S c hc hgood R =>
    change smoothOldArcOrigin D (R.arcEquiv (S.liftOldMark c hc R x)).val = some x.val
    rw [S.liftOldMark_map]
    simp only [smoothOldArcOrigin,Equiv.symm_apply_apply]

/-- The only parent-restriction connector is its actual newly marked one. -/
theorem arcOrigin_none_marked {s t : MarkedParentState} (step : MarkedParentStep s t)
    (e : Fin t.1.nArc) (he : step.arcOrigin e = none) : e ∈ t.2.2.marks := by
  cases step with
  | switched S c hc hgood => cases he
  | @smoothed D T S c hc hgood R =>
    change smoothOldArcOrigin D (R.arcEquiv e).val = none at he
    cases hcode : (smoothArcEquiv D).symm (R.arcEquiv e).val with
    | inl a => simp [smoothOldArcOrigin,hcode] at he
    | inr i =>
      have hmap : (R.arcEquiv e).val = smoothArcEquiv D (Sum.inr i) := by
        simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv D) hcode
      have hC := (R.arcEquiv e).property
      rw [hmap] at hC
      have hi : i = firstVisitedBranch T c := by
        by_cases hieq : i = firstVisitedBranch T c
        · exact hieq
        exfalso
        have hother := Gemini.eq_otherBranch_of_ne i (firstVisitedBranch T c) hieq
        have hbad : rootSelfCutComponents D c (S.connected _ _) (firstVisitedBranch T c)
            (Sum.inl true) =
            rootSelfCutComponents D c (S.connected _ _) (firstVisitedBranch T c)
            (Sum.inl false) := by
          rw [rootSelfCutComponents_true,rootSelfCutComponents_false]
          simpa only [hother] using hC
        have hbad' := (rootSelfCutComponents D c (S.connected _ _) (firstVisitedBranch T c)).injective hbad
        cases hbad'
      have heq : e = liftConnector D T c R := by
        apply R.arcEquiv.injective
        apply Subtype.ext
        rw [hmap,hi,liftConnector_map]
      rw [heq]
      exact Finset.mem_insert_self _ _

end MarkedParentStep
end DirectGLSSW.HOMFLY
