import RootFreeChainPositions
import ProcessedChildRootExclusion
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

/-- The actual original interval's rooted positions are consecutive, without wrap. -/
theorem MarkedParentTrace.detachedOriginalArc_visitPosition
    (i : Fin (detachedOrbitSize t c R-1)) :
    visitPosition s.2.1 (h.detachedOriginalArc c hc R i) =
      visitPosition s.2.1 (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)+i.val := by
  letI : NeZero (detachedOrbitSize t c R-1) := ⟨Nat.ne_of_gt (detachedOldOrbitSize_pos c R)⟩
  apply rootFreeChain_visitPosition s.1 s.2.1 (h.detachedOriginalArc c hc R)
  · intro j hj
    exact (h.detachedOriginalArc_successor c hc R j ⟨j.val+1,hj⟩ rfl).symm
  · intro j
    have he : componentOf s.1.continuation (h.detachedOriginalArc c hc R j) =
        componentOf s.1.continuation (s.1.incoming (h.crossingOrigin c) 0) :=
      (componentOf_eq_iff _ _ _).mpr (s.2.2.connected _ _)
    rw [he]
    exact h.detachedOriginalArc_ne_baseArc c hc R j

/-- The produced original interval has the same strict rooted visit order as its indices. -/
theorem MarkedParentTrace.detachedOriginalArc_visitPosition_lt_iff
    (i j : Fin (detachedOrbitSize t c R-1)) :
    visitPosition s.2.1 (h.detachedOriginalArc c hc R i) <
      visitPosition s.2.1 (h.detachedOriginalArc c hc R j) ↔ i.val<j.val := by
  rw [h.detachedOriginalArc_visitPosition c hc R i,
    h.detachedOriginalArc_visitPosition c hc R j]
  omega

/-- Every derived position is below the actual original component first-return length. -/
theorem MarkedParentTrace.detachedOriginalArc_visitPosition_bound
    (i : Fin (detachedOrbitSize t c R-1)) :
    visitPosition s.2.1 (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)+i.val <
      Fintype.card (Fibre s.1.continuation
        (componentOf s.1.continuation (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩))) := by
  rw [←h.detachedOriginalArc_visitPosition c hc R i]
  have he : componentOf s.1.continuation (h.detachedOriginalArc c hc R i) =
      componentOf s.1.continuation (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) :=
    (componentOf_eq_iff _ _ _).mpr (s.2.2.connected _ _)
  have hp := ((orbitEnumeration s.1.continuation
    (s.2.1.baseArc (componentOf s.1.continuation (h.detachedOriginalArc c hc R i))).val).symm
      ⟨h.detachedOriginalArc c hc R i,
        (s.2.1.baseArc (componentOf s.1.continuation (h.detachedOriginalArc c hc R i))).property.symm⟩).isLt
  simpa only [visitPosition,
    (s.2.1.baseArc (componentOf s.1.continuation (h.detachedOriginalArc c hc R i))).property,he] using hp

end DirectGLSSW.HOMFLY
