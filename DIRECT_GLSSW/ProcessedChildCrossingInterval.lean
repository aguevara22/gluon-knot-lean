import ProcessedCrossingCompleteness
import ProcessedChildOuterPorts
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

theorem detachedOldOrbitArc_surjective_of_old (e : Fin R.diagram.nArc)
    (he : ∃ a : Fin t.1.nArc, (smoothArcEquiv t.1).symm (R.arcEquiv e).val = Sum.inl a) :
    ∃ j : Fin (detachedOrbitSize t c R-1), detachedOldOrbitArc c R j=e := by
  have hne := (detached_old_code_iff t c R e).mp he
  let k := (detachedOrbitEquiv t c R).symm e
  have hk : 0 < k.val := by
    by_contra hh
    have hk0 : k = ⟨0,detachedOrbitSize_pos t c R⟩ := by
      apply Fin.ext
      change k.val=0
      omega
    have hmap := (detachedOrbitEquiv t c R).apply_symm_apply e
    change detachedOrbitEquiv t c R k=e at hmap
    rw [hk0,detachedOrbitEquiv_zero] at hmap
    exact hne hmap.symm
  let j : Fin (detachedOrbitSize t c R-1) := ⟨k.val-1,by have := k.isLt; omega⟩
  have hj : detachedOldOrbitIndex c R j=k := by
    apply Fin.ext
    change k.val-1+1=k.val
    omega
  refine ⟨j,?_⟩
  rw [detachedOldOrbitArc,hj]
  exact (detachedOrbitEquiv t c R).apply_symm_apply e

def MarkedParentTrace.detachedCrossingOrigin : Fin R.diagram.nCrossing ↪ Fin s.1.nCrossing :=
  (smoothedRestrictionCrossingOrigin t.1 c R).trans h.crossingOrigin

/-- Each actual child crossing port occupies a proved position of the actual
old word, labelled by the corresponding original incoming port. -/
theorem MarkedParentTrace.detachedCrossingOrigin_incoming_position
    (d : Fin R.diagram.nCrossing) (i : Fin 2) :
    ∃ j : Fin (detachedOrbitSize t c R-1),
      detachedOldOrbitArc c R j=R.diagram.incoming d i ∧
      h.detachedOriginalArc c hc R j=s.1.incoming (h.detachedCrossingOrigin c R d) i := by
  let dc := smoothedRestrictionCrossingOrigin t.1 c R d
  have hsome := smoothedRestrictionCrossingOrigin_incoming t.1 c R d i
  have hmap := (smoothOldArcOrigin_some_iff _ _ _).mp hsome
  have hcode : (smoothArcEquiv t.1).symm (R.arcEquiv (R.diagram.incoming d i)).val =
      Sum.inl (t.1.incoming dc i) := by rw [hmap,Equiv.symm_apply_apply]
  obtain ⟨j,hj⟩ := detachedOldOrbitArc_surjective_of_old c R (R.diagram.incoming d i) ⟨_,hcode⟩
  have hspec := detachedOldOrbitCode_spec c R j
  rw [hj,hcode] at hspec
  have hlabel := (Sum.inl.inj hspec).symm
  have ha := h.detachedOriginalArc_spec c hc R j
  rw [hlabel,h.crossingOrigin_incoming] at ha
  exact ⟨j,hj,(Option.some.inj ha).symm⟩

/-- The intrinsic original crossing-label carrier of this actual interval. -/
def DetachedIntervalCrossing :=
  {d : Fin s.1.nCrossing // ∀ i : Fin 2, ∃ j : Fin (detachedOrbitSize t c R-1),
    h.detachedOriginalArc c hc R j = s.1.incoming d i}

theorem MarkedParentTrace.detachedCrossingOrigin_complete
    (d : Fin s.1.nCrossing)
    (hports : ∀ i : Fin 2, ∃ j : Fin (detachedOrbitSize t c R-1),
      h.detachedOriginalArc c hc R j=s.1.incoming d i) :
    ∃ e : Fin R.diagram.nCrossing, h.detachedCrossingOrigin c R e=d := by
  have hp : ∀ i : Fin 2, ∃ a : Fin t.1.nArc,
      h.arcOrigin a = some (s.1.incoming d i) := by
    intro i
    obtain ⟨j,hj⟩ := hports i
    exact ⟨detachedOldOrbitCode c R j,hj ▸ h.detachedOriginalArc_spec c hc R j⟩
  obtain ⟨dc,hdc⟩ := h.crossingOrigin_complete d hp
  have hcurrent : ∀ i : Fin 2, ∃ e : Fin R.diagram.nArc,
      smoothOldArcOrigin t.1 (R.arcEquiv e).val = some (t.1.incoming dc i) := by
    intro i
    obtain ⟨j,hj⟩ := hports i
    have ha := h.detachedOriginalArc_spec c hc R j
    rw [hj] at ha
    have hb := h.crossingOrigin_incoming dc i
    rw [hdc] at hb
    have heq := h.arcOrigin_some_injective (detachedOldOrbitCode c R j) (t.1.incoming dc i) _ ha hb
    refine ⟨detachedOldOrbitArc c R j,?_⟩
    simp only [smoothOldArcOrigin,detachedOldOrbitCode_spec,heq]
  obtain ⟨e,he⟩ := smoothedRestrictionCrossingOrigin_complete t.1 c (t.2.2.connected _ _) R dc hcurrent
  refine ⟨e,?_⟩
  change h.crossingOrigin (smoothedRestrictionCrossingOrigin t.1 c R e)=d
  rw [he,hdc]

/-- Actual child crossings are exactly original crossings whose BOTH incoming
ports occur in the proved original interval. No completeness premise is used. -/
def MarkedParentTrace.detachedCrossingEquiv :
    Fin R.diagram.nCrossing ≃ DetachedIntervalCrossing h c hc R :=
  Equiv.ofBijective
    (fun d => ⟨h.detachedCrossingOrigin c R d,fun i => by
      obtain ⟨j,_,hj⟩ := h.detachedCrossingOrigin_incoming_position c hc R d i
      exact ⟨j,hj⟩⟩) (by
        constructor
        · intro d e he
          exact (h.detachedCrossingOrigin c R).injective (congrArg Subtype.val he)
        · intro d
          obtain ⟨e,he⟩ := h.detachedCrossingOrigin_complete c hc R d.val d.property
          exact ⟨e,Subtype.ext he⟩)

theorem MarkedParentTrace.detachedCrossingEquiv_val (d : Fin R.diagram.nCrossing) :
    (h.detachedCrossingEquiv c hc R d).val=h.detachedCrossingOrigin c R d := rfl

end DirectGLSSW.HOMFLY
