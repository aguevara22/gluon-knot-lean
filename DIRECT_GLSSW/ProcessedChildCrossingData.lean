import ProcessedCrossingDataTrace
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

include hc in
/-- The original current crossing underlying a next-child crossing has no
processed incoming port: such a port would belong to the excluded old prefix. -/
theorem detachedCrossing_incoming_not_marked (d : Fin R.diagram.nCrossing) (i : Fin 2) :
    t.1.incoming (smoothedRestrictionCrossingOrigin t.1 c R d) i ∉ t.2.2.marks := by
  intro hi
  let old := (smoothCrossingEquiv t.1 c).symm (R.crossingEquiv d).val
  have he : smoothCrossingEquiv t.1 c old = (R.crossingEquiv d).val :=
    (smoothCrossingEquiv t.1 c).apply_symm_apply _
  let x : StateMarks t := ⟨t.1.incoming old.val i,hi⟩
  have hne := t.2.2.mark_not_detached c hc x
  have hp := (R.crossingEquiv d).property i
  rw [←he,parentRoot_retained_incoming] at hp
  exact hne hp

theorem MarkedParentTrace.detachedCrossingOrigin_through (d : Fin R.diagram.nCrossing) :
    R.diagram.through d = s.1.through (h.detachedCrossingOrigin c R d) := by
  exact (R.through_eq d).trans (h.crossingOrigin_through _)

include hc in
theorem MarkedParentTrace.detachedCrossingOrigin_over (d : Fin R.diagram.nCrossing) :
    R.diagram.overBranch d = s.1.overBranch (h.detachedCrossingOrigin c R d) := by
  rcases h.crossingOrigin_over_or_marked (smoothedRestrictionCrossingOrigin t.1 c R d) with heq | ⟨i,hi⟩
  · exact (R.overBranch_eq d).trans heq
  · exact (detachedCrossing_incoming_not_marked c hc R d i hi).elim

include hc in
theorem MarkedParentTrace.detachedCrossingOrigin_sign (d : Fin R.diagram.nCrossing) :
    crossingSign R.diagram d = crossingSign s.1 (h.detachedCrossingOrigin c R d) := by
  rcases h.crossingOrigin_sign_or_marked (smoothedRestrictionCrossingOrigin t.1 c R d) with heq | ⟨i,hi⟩
  · let old := (smoothCrossingEquiv t.1 c).symm (R.crossingEquiv d).val
    have he : smoothCrossingEquiv t.1 c old = (R.crossingEquiv d).val :=
      (smoothCrossingEquiv t.1 c).apply_symm_apply _
    rw [R.crossingSign_eq,←he,crossingSign_smoothRetained]
    exact heq
  · exact (detachedCrossing_incoming_not_marked c hc R d i hi).elim

/-- Exact signed crossing data and actual old-word port positions for the
constructed crossing equivalence; no matching-data hypothesis is supplied. -/
theorem MarkedParentTrace.detachedCrossingEquiv_data (d : Fin R.diagram.nCrossing) :
    R.diagram.through d = s.1.through (h.detachedCrossingEquiv c hc R d).val ∧
    R.diagram.overBranch d = s.1.overBranch (h.detachedCrossingEquiv c hc R d).val ∧
    crossingSign R.diagram d = crossingSign s.1 (h.detachedCrossingEquiv c hc R d).val ∧
    ∀ i : Fin 2, ∃ j : Fin (detachedOrbitSize t c R-1),
      detachedOldOrbitArc c R j=R.diagram.incoming d i ∧
      h.detachedOriginalArc c hc R j=s.1.incoming (h.detachedCrossingEquiv c hc R d).val i := by
  exact ⟨h.detachedCrossingOrigin_through c R d,
    h.detachedCrossingOrigin_over c hc R d,h.detachedCrossingOrigin_sign c hc R d,
    fun i => h.detachedCrossingOrigin_incoming_position c hc R d i⟩
end DirectGLSSW.HOMFLY
