import ProcessedArcContinuationTrace
import ComponentRestrictionConnected
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

/-- The actual connector in the detached component, obtained by the exact
component arc equivalence rather than a supplied distinguished arc. -/
def detachedConnector (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))) : Fin R.diagram.nArc :=
  R.arcEquiv.symm ⟨smoothArcEquiv t.1 (Sum.inr (otherBranch (firstVisitedBranch t.2.1 c))),
    (rootSelfCutComponents_true t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c)).symm⟩

theorem detachedConnector_map (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    (R.arcEquiv (detachedConnector t c R)).val =
      smoothArcEquiv t.1 (Sum.inr (otherBranch (firstVisitedBranch t.2.1 c))) := by
  simp only [detachedConnector,Equiv.apply_symm_apply]

/-- Exactly one actual detached arc has a fresh smoothing code. -/
theorem detached_fresh_code_iff (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (e : Fin R.diagram.nArc) (i : Fin 2) :
    (smoothArcEquiv t.1).symm (R.arcEquiv e).val = Sum.inr i ↔
      e = detachedConnector t c R ∧ i = otherBranch (firstVisitedBranch t.2.1 c) := by
  constructor
  · intro hcode
    have hmap : (R.arcEquiv e).val = smoothArcEquiv t.1 (Sum.inr i) := by
      simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv t.1) hcode
    have hC := (R.arcEquiv e).property
    rw [hmap] at hC
    have hne : i ≠ firstVisitedBranch t.2.1 c := by
      intro hi
      rw [hi,← rootSelfCutComponents_false t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c)] at hC
      have hbad := (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c)).injective hC
      cases hbad
    have hi := Gemini.eq_otherBranch_of_ne i (firstVisitedBranch t.2.1 c) hne
    refine ⟨?_,hi⟩
    apply R.arcEquiv.injective
    apply Subtype.ext
    rw [hmap,hi,detachedConnector_map]
  · rintro ⟨rfl,rfl⟩
    rw [detachedConnector_map,Equiv.symm_apply_apply]

/-- All and only the remaining actual arcs have an old code. -/
theorem detached_old_code_iff (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true))) (e : Fin R.diagram.nArc) :
    (∃ a : Fin t.1.nArc, (smoothArcEquiv t.1).symm (R.arcEquiv e).val = Sum.inl a) ↔
      e ≠ detachedConnector t c R := by
  constructor
  · rintro ⟨a,ha⟩ he
    rw [he,detachedConnector_map,Equiv.symm_apply_apply] at ha
    cases ha
  · intro he
    cases hcode : (smoothArcEquiv t.1).symm (R.arcEquiv e).val with
    | inl a => exact ⟨a,rfl⟩
    | inr i => exact (he ((detached_fresh_code_iff t c R e i).mp hcode).1).elim

end DirectGLSSW.HOMFLY
