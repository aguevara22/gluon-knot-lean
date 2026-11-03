import PhysicalContinuingTailEndpoints
import RootFreeChainPositions
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
attribute [local instance] Classical.propDecidable
variable {s t : MarkedParentState}

/-- Exact original rooted coordinates for every old arc after the continuing connector. -/
theorem tailOriginalArc_visitPosition (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (i : Fin (tailSize t c hc hgood)) :
    visitPosition s.2.1 (tailOriginalArc h c hc hgood i) =
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c)
        (otherBranch (firstVisitedBranch t.2.1 c)))+1+i.val := by
  have hm : 0<tailSize t c hc hgood := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  letI : NeZero (tailSize t c hc hgood) := ⟨ne_of_gt hm⟩
  have H := rootFreeChain_visitPosition_of_common_root s.1 s.2.1
    (tailOriginalArc h c hc hgood) (by
      intro j hj
      exact (tailOriginalArc_successor h c hc hgood j ⟨j.val+1,hj⟩ rfl).symm)
    (by
      intro j
      change tailOriginalArc h c hc hgood j ≠ markedOrbitRoot s _
      rw [markedOrbitRoot_eq s _ (s.1.incoming (h.crossingOrigin c) 0)]
      exact tailOriginalArc_ne_root h c hc hgood j) i
  have hne : s.1.continuation (s.1.incoming (h.crossingOrigin c)
      (otherBranch (firstVisitedBranch t.2.1 c))) ≠
      (s.2.1.baseArc (componentOf s.1.continuation (s.1.incoming (h.crossingOrigin c)
        (otherBranch (firstVisitedBranch t.2.1 c))))).val := by
    rw [← tailOriginalArc_zero h c hc hgood hm]
    change tailOriginalArc h c hc hgood ⟨0,hm⟩ ≠ markedOrbitRoot s _
    rw [markedOrbitRoot_eq s _ (s.1.incoming (h.crossingOrigin c) 0)]
    exact tailOriginalArc_ne_root h c hc hgood _
  have Hz := tailOriginalArc_zero h c hc hgood hm
  change tailOriginalArc h c hc hgood (0 : Fin (tailSize t c hc hgood)) = _ at Hz
  rw [Hz, visitPosition_continuation_of_ne_root s.1 s.2.1 _ hne] at H
  exact H

/-- The complete parent tail has exactly the original number of positions after the second cut visit. -/
theorem tailSize_eq_original_remaining (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    tailSize t c hc hgood =
      markedOrbitSize s (s.1.incoming (h.crossingOrigin c) 0) -
        visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c)
          (otherBranch (firstVisitedBranch t.2.1 c)))-1 := by
  by_cases hp : 0<tailSize t c hc hgood
  · have hl := tailOriginalArc_last_continuation h c hc hgood hp
    have hb := marked_visitPosition_of_continuation_root s
      (s.1.incoming (h.crossingOrigin c) 0) _ hl
    rw [tailOriginalArc_visitPosition] at hb
    change _+1+(tailSize t c hc hgood-1)+1 = _ at hb
    omega
  · have hz : tailSize t c hc hgood=0 := by omega
    have hs : markedSuffixSize (continuingState t c hc hgood) (connector t c)=1 := by
      have := markedSuffixSize_pos (continuingState t c hc hgood) (connector t c)
      unfold tailSize at hz
      omega
    have hlast := markedSuffixArc_last_continuation (continuingState t c hc hgood) (connector t c)
    simp only [hs,Nat.sub_self] at hlast
    rw [markedSuffixArc_zero] at hlast
    have ho := connector_successor_origin h c hc hgood
    rw [hlast,continuingTrace_root_origin] at ho
    have he := (Option.some.inj ho).symm
    have hb := marked_visitPosition_of_continuation_root s
      (s.1.incoming (h.crossingOrigin c) 0) _ he
    omega

/-- Literal old-arc word, with no omitted or extra original tail label. -/
theorem tailOriginalArc_eq_original_orbit (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (i : Fin (tailSize t c hc hgood)) :
    tailOriginalArc h c hc hgood i =
      markedOrbitArc s (s.1.incoming (h.crossingOrigin c) 0)
        ⟨visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c)
          (otherBranch (firstVisitedBranch t.2.1 c)))+1+i.val,by
          have hh := tailSize_eq_original_remaining h c hc hgood
          have := i.isLt;omega⟩ := by
  apply marked_visitPosition_injective s
  rw [tailOriginalArc_visitPosition,markedOrbitArc_visitPosition]

/-- Complete original strict-future range at the second incoming cut port. -/
theorem tailOriginalArc_range (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (e : Fin s.1.nArc) :
    (∃ i,tailOriginalArc h c hc hgood i=e) ↔
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c)
        (otherBranch (firstVisitedBranch t.2.1 c))) < visitPosition s.2.1 e := by
  constructor
  · rintro ⟨i,rfl⟩;rw [tailOriginalArc_visitPosition];omega
  · intro hle
    have hb := visitPosition_lt_markedOrbitSize s e
    rw [markedOrbitSize_eq s e (s.1.incoming (h.crossingOrigin c) 0)] at hb
    let i : Fin (tailSize t c hc hgood) :=
      ⟨visitPosition s.2.1 e - visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c)
        (otherBranch (firstVisitedBranch t.2.1 c)))-1,by
          rw [tailSize_eq_original_remaining h c hc hgood];omega⟩
    refine ⟨i,?_⟩
    apply marked_visitPosition_injective s
    rw [tailOriginalArc_visitPosition]
    dsimp only [i]
    omega

theorem tailOriginalArc_order (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (i j : Fin (tailSize t c hc hgood)) :
    visitPosition s.2.1 (tailOriginalArc h c hc hgood i) <
      visitPosition s.2.1 (tailOriginalArc h c hc hgood j) ↔ i.val<j.val := by
  rw [tailOriginalArc_visitPosition,tailOriginalArc_visitPosition]
  omega
end DirectGLSSW.HOMFLY.PhysicalParentHistory
