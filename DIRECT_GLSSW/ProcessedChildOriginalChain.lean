import ProcessedChildOrbitEnumeration
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

/-- Positive orbit positions, with the unique fresh connector deleted. -/
def detachedOldOrbitIndex (i : Fin (detachedOrbitSize t c R-1)) : Fin (detachedOrbitSize t c R) :=
  ⟨i.val+1,by have := i.isLt; omega⟩

def detachedOldOrbitArc (i : Fin (detachedOrbitSize t c R-1)) : Fin R.diagram.nArc :=
  detachedOrbitEquiv t c R (detachedOldOrbitIndex c R i)

/-- The old-code label is chosen only from the proved actual positive-position
old-code theorem; there is no fallback label. -/
def detachedOldOrbitCode (i : Fin (detachedOrbitSize t c R-1)) : Fin t.1.nArc :=
  Classical.choose (detachedOrbitEquiv_old_code t c R (detachedOldOrbitIndex c R i) (Nat.succ_pos _))

theorem detachedOldOrbitCode_spec (i : Fin (detachedOrbitSize t c R-1)) :
    (smoothArcEquiv t.1).symm (R.arcEquiv (detachedOldOrbitArc c R i)).val =
      Sum.inl (detachedOldOrbitCode c R i) :=
  Classical.choose_spec (detachedOrbitEquiv_old_code t c R (detachedOldOrbitIndex c R i) (Nat.succ_pos _))

def MarkedParentTrace.detachedOriginalArc (i : Fin (detachedOrbitSize t c R-1)) : Fin s.1.nArc :=
  Classical.choose (h.detached_old_arc_has_origin c hc R (detachedOldOrbitArc c R i)
    (detachedOldOrbitCode c R i) (detachedOldOrbitCode_spec c R i))

theorem MarkedParentTrace.detachedOriginalArc_spec (i : Fin (detachedOrbitSize t c R-1)) :
    h.arcOrigin (detachedOldOrbitCode c R i) = some (h.detachedOriginalArc c hc R i) :=
  Classical.choose_spec (h.detached_old_arc_has_origin c hc R (detachedOldOrbitArc c R i)
    (detachedOldOrbitCode c R i) (detachedOldOrbitCode_spec c R i))

theorem MarkedParentTrace.detachedOriginalArc_successor
    (i j : Fin (detachedOrbitSize t c R-1)) (hij : j.val = i.val+1) :
    s.1.continuation (h.detachedOriginalArc c hc R i) = h.detachedOriginalArc c hc R j := by
  have hstep : R.diagram.continuation (detachedOldOrbitArc c R i) = detachedOldOrbitArc c R j := by
    apply detachedOrbitEquiv_successor
    change j.val+1 = i.val+1+1
    omega
  obtain ⟨a,b,ha,hb,hab⟩ := h.detached_old_arcs_continuation c hc R
    (detachedOldOrbitArc c R i) (detachedOldOrbitArc c R j)
    (detachedOldOrbitCode c R i) (detachedOldOrbitCode c R j) hstep
    (detachedOldOrbitCode_spec c R i) (detachedOldOrbitCode_spec c R j)
  have ha' : a = h.detachedOriginalArc c hc R i :=
    Option.some.inj (ha.symm.trans (h.detachedOriginalArc_spec c hc R i))
  have hb' : b = h.detachedOriginalArc c hc R j :=
    Option.some.inj (hb.symm.trans (h.detachedOriginalArc_spec c hc R j))
  simpa only [ha',hb'] using hab

theorem MarkedParentTrace.detachedOriginalArc_injective :
    Function.Injective (h.detachedOriginalArc c hc R) := by
  intro i j hij
  have ha : detachedOldOrbitCode c R i = detachedOldOrbitCode c R j :=
    h.arcOrigin_some_injective _ _ _ (h.detachedOriginalArc_spec c hc R i)
      (hij.symm ▸ h.detachedOriginalArc_spec c hc R j)
  have he : detachedOldOrbitArc c R i = detachedOldOrbitArc c R j := by
    apply R.arcEquiv.injective
    apply Subtype.ext
    apply (smoothArcEquiv t.1).symm.injective
    rw [detachedOldOrbitCode_spec,detachedOldOrbitCode_spec,ha]
  have hi := (detachedOrbitEquiv t c R).injective he
  apply Fin.ext
  have hv := congrArg Fin.val hi
  change i.val+1 = j.val+1 at hv
  omega

end DirectGLSSW.HOMFLY
