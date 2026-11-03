import MarkedSuffixCoordinates
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

theorem markedOrbitRoot_eq (t : MarkedParentState) (a b : Fin t.1.nArc) :
    markedOrbitRoot t a = markedOrbitRoot t b := by
  unfold markedOrbitRoot
  rw [(componentOf_eq_iff _ _ _).mpr (t.2.2.connected a b)]

/-- Both genuine operations retain the stored original root as an old arc. -/
theorem MarkedParentStep.arcOrigin_root {s t : MarkedParentState} (step : MarkedParentStep s t)
    (a : Fin t.1.nArc) (b : Fin s.1.nArc) :
    step.arcOrigin (markedOrbitRoot t a) = some (markedOrbitRoot s b) := by
  cases step with
  | @switched D T S c hc hgood =>
    change some (markedOrbitRoot ⟨D,T,S⟩ a) = some (markedOrbitRoot ⟨D,T,S⟩ b)
    rw [markedOrbitRoot_eq ⟨D,T,S⟩ a b]
  | @smoothed D T S c hc hgood R =>
    change smoothOldArcOrigin D (R.arcEquiv (R.traversalRoot
      (parentRootSelfSmoothingTraversal D T c (S.connected _ _)))).val =
      some (markedOrbitRoot ⟨D,T,S⟩ b)
    rw [R.parentRestriction_original_root]
    simp only [smoothOldArcOrigin,Equiv.symm_apply_apply]
    congr 1
    exact markedOrbitRoot_eq ⟨D,T,S⟩ _ b

/-- Stored-root ancestry along the actual finite history. A final crossing
supplies a concrete arc in each intermediate diagram; no default arc is chosen. -/
theorem MarkedParentTrace.arcOrigin_root {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) :
    h.arcOrigin (markedOrbitRoot t (t.1.incoming c 0)) =
      some (markedOrbitRoot s (s.1.incoming (h.crossingOrigin c) 0)) := by
  induction h with
  | nil s => rfl
  | @cons s t u step tail ih =>
    change (tail.arcOrigin (markedOrbitRoot u (u.1.incoming c 0))).bind step.arcOrigin = _
    rw [ih,Option.some_bind]
    exact step.arcOrigin_root _ _

end DirectGLSSW.HOMFLY
