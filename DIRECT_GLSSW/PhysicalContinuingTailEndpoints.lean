import PhysicalContinuingTailOrigin
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
attribute [local instance] Classical.propDecidable
variable {s t : MarkedParentState}

theorem continuingTrace_origin (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (e : Fin (continuingState t c hc hgood).1.nArc) :
    (continuingTrace h c hc hgood).arcOrigin e =
      ((MarkedParentStep.smoothed t.2.2 c hc hgood (continuingRestriction t c)).arcOrigin e).bind h.arcOrigin := by
  rw [continuingTrace,arcOrigin_append]
  rfl

/-- The continuing state has the old original root, even when it has no remaining crossing. -/
theorem continuingTrace_root_origin (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    (continuingTrace h c hc hgood).arcOrigin
      (markedOrbitRoot (continuingState t c hc hgood) (connector t c)) =
      some (markedOrbitRoot s (s.1.incoming (h.crossingOrigin c) 0)) := by
  rw [continuingTrace_origin]
  have hr : (MarkedParentStep.smoothed t.2.2 c hc hgood (continuingRestriction t c)).arcOrigin
      (markedOrbitRoot (continuingState t c hc hgood) (connector t c)) =
      some (markedOrbitRoot t (t.1.incoming c 0)) :=
    (MarkedParentStep.smoothed t.2.2 c hc hgood (continuingRestriction t c)).arcOrigin_root
      (connector t c) (t.1.incoming c 0)
  rw [hr,Option.some_bind,h.arcOrigin_root c]

/-- The actual connector exits to the old continuation of the OTHER incoming port. -/
theorem connector_successor_origin (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    (continuingTrace h c hc hgood).arcOrigin
      ((continuingState t c hc hgood).1.continuation (connector t c)) =
      some (s.1.continuation (s.1.incoming (h.crossingOrigin c)
        (otherBranch (firstVisitedBranch t.2.1 c)))) := by
  rw [continuingTrace_origin]
  let R := continuingRestriction t c
  have hm := R.continuation_eq (connector t c)
  change (R.arcEquiv (R.diagram.continuation (connector t c))).val =
    (smoothCrossing t.1 c).continuation (R.arcEquiv (connector t c)).val at hm
  have htag : (R.arcEquiv (connector t c)).val =
      smoothArcEquiv t.1 (Sum.inr (firstVisitedBranch t.2.1 c)) :=
    liftConnector_map t.1 t.2.1 c (continuingRestriction t c)
  rw [htag,Gemini.smooth_step_connector] at hm
  change (smoothOldArcOrigin t.1
    (R.arcEquiv (R.diagram.continuation (connector t c))).val).bind h.arcOrigin = _
  rw [hm]
  simp only [smoothOldArcOrigin,Equiv.symm_apply_apply,Option.some_bind]
  rw [t.1.continuation_crossing,h.crossingOrigin_outgoing,h.crossingOrigin_through,
    ← s.1.continuation_crossing]

theorem tailArc_zero_eq_successor (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (hgood : GoodBefore t c) (hpos : 0<tailSize t c hc hgood) :
    tailArc t c hc hgood ⟨0,hpos⟩ =
      (continuingState t c hc hgood).1.continuation (connector t c) := by
  have hh := markedSuffixArc_successor (continuingState t c hc hgood) (connector t c)
    ⟨0,markedSuffixSize_pos _ _⟩ ⟨1,by unfold tailSize at hpos;omega⟩ rfl
  rw [markedSuffixArc_zero] at hh
  exact hh.symm

theorem tailOriginalArc_zero (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (hpos : 0<tailSize t c hc hgood) :
    tailOriginalArc h c hc hgood ⟨0,hpos⟩ =
      s.1.continuation (s.1.incoming (h.crossingOrigin c) (otherBranch (firstVisitedBranch t.2.1 c))) := by
  have hh := tailOriginalArc_spec h c hc hgood ⟨0,hpos⟩
  rw [tailArc_zero_eq_successor c hc hgood hpos,connector_successor_origin] at hh
  exact (Option.some.inj hh).symm

/-- Every actual unprocessed tail ancestor avoids the original stored root. -/
theorem tailOriginalArc_ne_root (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (i : Fin (tailSize t c hc hgood)) :
    tailOriginalArc h c hc hgood i ≠ markedOrbitRoot s (s.1.incoming (h.crossingOrigin c) 0) := by
  intro he
  have hor := continuingTrace_root_origin h c hc hgood
  have hi := tailOriginalArc_spec h c hc hgood i
  rw [he] at hi
  have heq := (continuingTrace h c hc hgood).arcOrigin_some_injective _ _ _ hi hor
  have hp := congrArg (visitPosition (continuingState t c hc hgood).2.1) heq
  unfold tailArc at hp
  rw [markedSuffixArc_visitPosition,markedOrbitRoot_visitPosition] at hp
  change visitPosition (continuingState t c hc hgood).2.1 (connector t c)+(i.val+1)=0 at hp
  omega

/-- The last original tail ancestor returns to the same original stored root. -/
theorem tailOriginalArc_last_continuation (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (hpos : 0<tailSize t c hc hgood) :
    s.1.continuation (tailOriginalArc h c hc hgood
      ⟨tailSize t c hc hgood-1,by omega⟩) =
      markedOrbitRoot s (s.1.incoming (h.crossingOrigin c) 0) := by
  apply (continuingTrace h c hc hgood).arcOrigin_continuation
    (tailArc t c hc hgood ⟨tailSize t c hc hgood-1,by omega⟩)
    (markedOrbitRoot (continuingState t c hc hgood) (connector t c))
  · have he : tailSize t c hc hgood-1+1=
        markedSuffixSize (continuingState t c hc hgood) (connector t c)-1 := by
      unfold tailSize at *;omega
    unfold tailArc
    convert markedSuffixArc_last_continuation (continuingState t c hc hgood) (connector t c) using 1
    congr 2
    exact Fin.ext he
  · exact tailOriginalArc_spec h c hc hgood _
  · exact continuingTrace_root_origin h c hc hgood
end DirectGLSSW.HOMFLY.PhysicalParentHistory
