import ProcessedChildRootExclusion
import DirectGLSSW.OrbitWordPrerequisite
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

/-- The first incoming port is outside the detached original old word. -/
theorem MarkedParentTrace.detachedOriginalArc_ne_firstIncoming
    (i : Fin (detachedOrbitSize t c R-1)) :
    h.detachedOriginalArc c hc R i ≠
      s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c) := by
  by_cases hi : i=detachedLastOldIndex c R
  · rw [hi,h.detachedOriginalArc_last]
    exact (rootCut_ports_distinct s.1 (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)).symm
  · have hnext : i.val+1 < detachedOrbitSize t c R-1 := by
      have := i.isLt
      have hine : i.val ≠ detachedOrbitSize t c R-2 := fun hh => hi (Fin.ext hh)
      omega
    let j : Fin (detachedOrbitSize t c R-1) := ⟨i.val+1,hnext⟩
    intro he
    have hs := h.detachedOriginalArc_successor c hc R i j rfl
    rw [he,s.1.continuation_crossing,←h.detachedOriginalArc_first c hc R] at hs
    have hj := h.detachedOriginalArc_injective c hc R hs.symm
    have hval := congrArg Fin.val hj
    change i.val+1=0 at hval
    omega

/-- The original cut permutation closes exactly the produced old-arc word. -/
theorem MarkedParentTrace.detachedOriginalArc_cut_successor
    (i : Fin (detachedOrbitSize t c R-1)) :
    cutContinuation s.1 (h.crossingOrigin c) (h.detachedOriginalArc c hc R i) =
      h.detachedOriginalArc c hc R (cyclicSuccessor i) := by
  rw [←rootCutContinuation_eq s.1 (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)]
  change s.1.continuation (Equiv.swap
    (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))
    (s.1.incoming (h.crossingOrigin c) (otherBranch (firstVisitedBranch t.2.1 c)))
    (h.detachedOriginalArc c hc R i)) = _
  by_cases hi : i=detachedLastOldIndex c R
  · have hz : cyclicSuccessor i=⟨0,detachedOldOrbitSize_pos c R⟩ := by
      apply Fin.ext
      change (i.val+1) % (detachedOrbitSize t c R-1)=0
      have he : i.val+1=detachedOrbitSize t c R-1 := by
        rw [hi];change detachedOrbitSize t c R-2+1=detachedOrbitSize t c R-1
        have := detachedOldOrbitSize_pos c R
        omega
      rw [he,Nat.mod_self]
    rw [hz,hi,h.detachedOriginalArc_last,Equiv.swap_apply_right,s.1.continuation_crossing,
      h.detachedOriginalArc_first]
  · have hnext : i.val+1 < detachedOrbitSize t c R-1 := by
      have := i.isLt
      have hine : i.val ≠ detachedOrbitSize t c R-2 := fun hh => hi (Fin.ext hh)
      omega
    have hne := h.detachedOriginalArc_ne_firstIncoming c hc R i
    have hne' : h.detachedOriginalArc c hc R i ≠
        s.1.incoming (h.crossingOrigin c) (otherBranch (firstVisitedBranch t.2.1 c)) := by
      rw [←h.detachedOriginalArc_last c hc R]
      exact fun hh => hi (h.detachedOriginalArc_injective c hc R hh)
    rw [Equiv.swap_apply_of_ne_of_ne hne hne']
    apply h.detachedOriginalArc_successor c hc R
    change (i.val+1) % (detachedOrbitSize t c R-1)=i.val+1
    exact Nat.mod_eq_of_lt hnext

/-- Exact original singleton-cut orbit, not a supplied cyclic word correspondence. -/
theorem MarkedParentTrace.detachedOriginalCut_orbitWord :
    orbitWord (cutContinuation s.1 (h.crossingOrigin c))
      (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) =
      List.ofFn (h.detachedOriginalArc c hc R) :=
  orbitWord_eq_of_injective_cyclicSuccessor _ (detachedOldOrbitSize_pos c R) _
    (h.detachedOriginalArc_injective c hc R) (h.detachedOriginalArc_cut_successor c hc R)

/-- This actual original singleton-cut orbit is the closed side: it does not
contain the fixed original base arc. -/
theorem MarkedParentTrace.detachedOriginalCut_component_ne_baseArc :
    componentOf (cutContinuation s.1 (h.crossingOrigin c))
      (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) ≠
    componentOf (cutContinuation s.1 (h.crossingOrigin c))
      (s.2.1.baseArc (componentOf s.1.continuation (s.1.incoming (h.crossingOrigin c) 0))).val := by
  intro he
  have hm := (mem_orbitWord_iff _ _ _).mpr ((componentOf_eq_iff _ _ _).mp he)
  rw [h.detachedOriginalCut_orbitWord c hc R] at hm
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  exact h.detachedOriginalArc_ne_baseArc c hc R i hi
end DirectGLSSW.HOMFLY
