import ProcessedCrossingOriginTrace
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

def detachedLastOldIndex : Fin (detachedOrbitSize t c R-1) :=
  ⟨detachedOrbitSize t c R-2,by have := detachedOldOrbitSize_pos c R; omega⟩

theorem detachedOldOrbitArc_first :
    detachedOldOrbitArc c R ⟨0,detachedOldOrbitSize_pos c R⟩ =
      R.diagram.continuation (detachedConnector t c R) := by
  rw [detachedOldOrbitArc,detachedOrbitEquiv_apply]
  rfl

theorem detachedOldOrbitArc_last_successor :
    R.diagram.continuation (detachedOldOrbitArc c R (detachedLastOldIndex c R)) =
      detachedConnector t c R := by
  rw [detachedOldOrbitArc,detachedOrbitEquiv_apply]
  rw [← Equiv.Perm.mul_apply,← pow_succ']
  have he : (detachedOldOrbitIndex c R (detachedLastOldIndex c R)).val+1 =
      detachedOrbitSize t c R := by
    change detachedOrbitSize t c R-2+1+1=detachedOrbitSize t c R
    have := detachedOldOrbitSize_pos c R
    omega
  rw [he,detachedOrbitSize_eq_nArc]
  have hp : R.diagram.continuation.IsCycleOn (Finset.univ : Finset (Fin R.diagram.nArc)) := by
    refine ⟨R.diagram.continuation.bijOn (fun _ => by simp),?_⟩
    intro x _ y _
    exact R.continuation_sameCycle x y
  simpa only [Finset.card_univ,Fintype.card_fin] using
    hp.pow_card_apply (Finset.mem_univ (detachedConnector t c R))

theorem detachedOldOrbitCode_first :
    detachedOldOrbitCode c R ⟨0,detachedOldOrbitSize_pos c R⟩ =
      t.1.outgoing c (t.1.through c (firstVisitedBranch t.2.1 c)) := by
  have hm : (R.arcEquiv (detachedOldOrbitArc c R ⟨0,detachedOldOrbitSize_pos c R⟩)).val =
      smoothArcEquiv t.1 (Sum.inl (t.1.outgoing c (t.1.through c (firstVisitedBranch t.2.1 c)))) := by
    rw [detachedOldOrbitArc_first,R.continuation_eq,detachedConnector_map,
      Gemini.smooth_step_connector,otherBranch_involutive,t.1.continuation_crossing]
  have hh := detachedOldOrbitCode_spec c R ⟨0,detachedOldOrbitSize_pos c R⟩
  rw [hm,Equiv.symm_apply_apply] at hh
  exact (Sum.inl.inj hh).symm

theorem detachedOldOrbitCode_last :
    detachedOldOrbitCode c R (detachedLastOldIndex c R) =
      t.1.incoming c (otherBranch (firstVisitedBranch t.2.1 c)) := by
  have hm : (R.arcEquiv (detachedOldOrbitArc c R (detachedLastOldIndex c R))).val =
      smoothArcEquiv t.1 (Sum.inl (t.1.incoming c (otherBranch (firstVisitedBranch t.2.1 c)))) := by
    apply (smoothCrossing t.1 c).continuation.injective
    rw [← R.continuation_eq,detachedOldOrbitArc_last_successor,detachedConnector_map,
      Gemini.smooth_step_incoming]
  have hh := detachedOldOrbitCode_spec c R (detachedLastOldIndex c R)
  rw [hm,Equiv.symm_apply_apply] at hh
  exact (Sum.inl.inj hh).symm

theorem MarkedParentTrace.detachedOriginalArc_first :
    h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩ =
      s.1.outgoing (h.crossingOrigin c)
        (s.1.through (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) := by
  have hh := h.detachedOriginalArc_spec c hc R ⟨0,detachedOldOrbitSize_pos c R⟩
  rw [detachedOldOrbitCode_first,h.crossingOrigin_outgoing,h.crossingOrigin_through] at hh
  exact (Option.some.inj hh).symm

theorem MarkedParentTrace.detachedOriginalArc_last :
    h.detachedOriginalArc c hc R (detachedLastOldIndex c R) =
      s.1.incoming (h.crossingOrigin c) (otherBranch (firstVisitedBranch t.2.1 c)) := by
  have hh := h.detachedOriginalArc_spec c hc R (detachedLastOldIndex c R)
  rw [detachedOldOrbitCode_last,h.crossingOrigin_incoming] at hh
  exact (Option.some.inj hh).symm

/-- The sharp outer corner is the same original crossing point at both ends of
the original arc chain. The two actual bevel cutpoints are not identified. -/
theorem MarkedParentTrace.detachedOriginalArc_outer_points :
    s.1.vertexPoint (s.1.arcSource
      (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) =
        t.1.vertexPoint (t.1.crossingVertex c) ∧
    s.1.vertexPoint (s.1.arcTarget
      (h.detachedOriginalArc c hc R (detachedLastOldIndex c R))) =
        t.1.vertexPoint (t.1.crossingVertex c) := by
  rw [h.detachedOriginalArc_first,h.detachedOriginalArc_last,s.1.outgoing_source,s.1.incoming_target]
  exact ⟨(h.crossingOrigin_point c).symm,(h.crossingOrigin_point c).symm⟩

end DirectGLSSW.HOMFLY
