import ProcessedRootOrigin
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

/-- The current stored root is on the continuing side, not the detached side. -/
theorem markedState_root_not_detached (t : MarkedParentState) (c : Fin t.1.nCrossing) :
    componentOf (smoothCrossing t.1 c).continuation
      (smoothArcEquiv t.1 (Sum.inl
        (t.2.1.baseArc (componentOf t.1.continuation (t.1.incoming c 0))).val)) ≠
      rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true) := by
  have he : componentOf t.1.continuation (t.1.incoming c 0) =
      componentOf t.1.continuation (t.1.incoming c (firstVisitedBranch t.2.1 c)) :=
    (componentOf_eq_iff _ _ _).mpr (t.2.2.connected _ _)
  rw [he,firstVisited_original_root_component]
  intro hh
  have hh' := (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
    (firstVisitedBranch t.2.1 c)).injective hh
  cases hh'

/-- Every position of the actual detached original interval avoids the original
stored root. This is derived from physical restriction and ancestry, not order. -/
theorem MarkedParentTrace.detachedOriginalArc_ne_baseArc {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (i : Fin (detachedOrbitSize t c R-1)) :
    h.detachedOriginalArc c hc R i ≠
      (s.2.1.baseArc (componentOf s.1.continuation
        (s.1.incoming (h.crossingOrigin c) 0))).val := by
  intro hi
  have hcur : detachedOldOrbitCode c R i =
      (t.2.1.baseArc (componentOf t.1.continuation (t.1.incoming c 0))).val :=
    h.arcOrigin_some_injective _ _ _
      ((h.detachedOriginalArc_spec c hc R i).trans (congrArg some hi))
      (h.arcOrigin_baseArc c)
  have hmap : (R.arcEquiv (detachedOldOrbitArc c R i)).val =
      smoothArcEquiv t.1 (Sum.inl (detachedOldOrbitCode c R i)) := by
    simpa only [Equiv.apply_symm_apply] using
      congrArg (smoothArcEquiv t.1) (detachedOldOrbitCode_spec c R i)
  have hmem := (R.arcEquiv (detachedOldOrbitArc c R i)).property
  rw [hmap,hcur] at hmem
  exact markedState_root_not_detached t c hmem
end DirectGLSSW.HOMFLY
