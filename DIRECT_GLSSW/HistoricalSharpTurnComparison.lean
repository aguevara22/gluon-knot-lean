import HistoricalSharpTurnCoordinates
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge PrincipalTurning SmoothingCornerGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem oldArc_map (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)))
    (j : Fin (detachedOrbitSize t c R-1)) :
    (R.arcEquiv (detachedOldOrbitArc c R j)).val =
      smoothArcEquiv t.1 (Sum.inl (detachedOldOrbitCode c R j)) := by
  simpa only [Equiv.apply_symm_apply] using congrArg (smoothArcEquiv t.1) (detachedOldOrbitCode_spec c R j)

/-- Both physical bevel turns contract to the exact sharp turn between the two
actual surviving boundary arcs, for the actual detached restriction. -/
theorem detached_boundary_turn (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    turn R.diagram (detachedOldOrbitArc c R (detachedLastOldIndex c R)) +
      turn R.diagram (detachedConnector t c R) =
      Complex.arg (PrincipalTurning.arcVector R.diagram (detachedOldOrbitArc c R ⟨0,detachedOldOrbitSize_pos c R⟩) /
        PrincipalTurning.arcVector R.diagram (detachedOldOrbitArc c R (detachedLastOldIndex c R))) := by
  have hfirst := oldArc_map t c R ⟨0,detachedOldOrbitSize_pos c R⟩
  rw [detachedOldOrbitCode_first] at hfirst
  have hlast := oldArc_map t c R (detachedLastOldIndex c R)
  rw [detachedOldOrbitCode_last] at hlast
  obtain ⟨a,ha,hva⟩ := smoothCrossing_old_arcVector_positive t.1 c
    (t.1.incoming c (otherBranch (firstVisitedBranch t.2.1 c)))
  have hvl : PrincipalTurning.arcVector R.diagram (detachedOldOrbitArc c R (detachedLastOldIndex c R)) =
      (a:ℂ)*crossingVector t.1 c (otherBranch (firstVisitedBranch t.2.1 c)) := by
    rw [arcVector_restriction,hlast,hva,arcVector_incoming]
  obtain ⟨b,hb,hvb⟩ := SmoothingCornerGeometry.outgoing_vector t.1 c (firstVisitedBranch t.2.1 c)
  have hvf : PrincipalTurning.arcVector R.diagram (detachedOldOrbitArc c R ⟨0,detachedOldOrbitSize_pos c R⟩) =
      (b:ℂ)*crossingVector t.1 c (firstVisitedBranch t.2.1 c) := by
    rw [arcVector_restriction,hfirst]
    apply Complex.ext
    · simpa [PrincipalTurning.arcVector,crossingVector,SmoothingCornerGeometry.arcVector] using congrArg Prod.fst hvb
    · simpa [PrincipalTurning.arcVector,crossingVector,SmoothingCornerGeometry.arcVector] using congrArg Prod.snd hvb
  rw [turn_restriction,turn_restriction,hlast,detachedConnector_map,two_smoothing_bends_eq_exchange,
    otherBranch_involutive,hvf,hvl]
  exact (turn_positive_rescale _ _ b a hb ha).symm

private theorem fin_sum_zero_succ {N : ℕ} (hN : 0<N) (f : Fin N → ℝ) :
    (∑ k, f k) = f ⟨0,hN⟩ + ∑ j : Fin (N-1), f ⟨j.val+1,by have := j.isLt;omega⟩ := by
  cases N with
  | zero => omega
  | succ m => simpa using Fin.sum_univ_succ f

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem historical_old_turn (j : Fin (detachedOrbitSize t c R-1))
    (hj : j ≠ detachedLastOldIndex c R) :
    turn R.diagram (detachedOldOrbitArc c R j) = historicalIntervalTurn q hq h c hc R j := by
  have hlt : j.val+1 < detachedOrbitSize t c R-1 := by
    have := j.isLt
    have hne : j.val ≠ detachedOrbitSize t c R-2 := fun he => hj (Fin.ext he)
    omega
  have hsucc : (cyclicSuccessor j).val = j.val+1 := Nat.mod_eq_of_lt hlt
  have hstep : R.diagram.continuation (detachedOldOrbitArc c R j) =
      detachedOldOrbitArc c R (cyclicSuccessor j) := by
    apply detachedOrbitEquiv_successor
    change (cyclicSuccessor j).val+1=j.val+1+1
    rw [hsucc]
  obtain ⟨a,ha,hva⟩ := historical_old_arcVector q hq h c hc R (cyclicSuccessor j)
  obtain ⟨b,hb,hvb⟩ := historical_old_arcVector q hq h c hc R j
  rw [turn,hstep,hva,hvb]
  exact turn_positive_rescale _ _ a b ha hb

theorem historical_boundary_turn :
    turn R.diagram (detachedOldOrbitArc c R (detachedLastOldIndex c R)) +
      turn R.diagram (detachedConnector t c R) =
      historicalIntervalTurn q hq h c hc R (detachedLastOldIndex c R) := by
  have hz : cyclicSuccessor (detachedLastOldIndex c R) = ⟨0,detachedOldOrbitSize_pos c R⟩ := by
    apply Fin.ext
    change (detachedOrbitSize t c R-2+1) % (detachedOrbitSize t c R-1)=0
    have he : detachedOrbitSize t c R-2+1=detachedOrbitSize t c R-1 := by
      have := detachedOldOrbitSize_pos c R;omega
    rw [he,Nat.mod_self]
  obtain ⟨a,ha,hva⟩ := historical_old_arcVector q hq h c hc R ⟨0,detachedOldOrbitSize_pos c R⟩
  obtain ⟨b,hb,hvb⟩ := historical_old_arcVector q hq h c hc R (detachedLastOldIndex c R)
  rw [detached_boundary_turn,historicalIntervalTurn,hz,hva,hvb]
  exact turn_positive_rescale _ _ a b ha hb

/-- Actual detached component and actual historical sharp subdivision have
identical real total principal turn. All direction/order/bevel inputs are derived. -/
theorem historicalSharp_totalTurn_eq :
    totalTurn R.diagram = totalTurn (historicalSharpDiagram q hq h c hc R) := by
  have hsum : totalTurn R.diagram = turn R.diagram (detachedConnector t c R) +
      ∑ j, turn R.diagram (detachedOldOrbitArc c R j) := by
    calc
      totalTurn R.diagram = ∑ k,turn R.diagram (detachedOrbitEquiv t c R k) :=
        (Fintype.sum_equiv (detachedOrbitEquiv t c R) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [fin_sum_zero_succ (detachedOrbitSize_pos t c R),detachedOrbitEquiv_zero]
        rfl
  have hd : (∑ j, (turn R.diagram (detachedOldOrbitArc c R j) - historicalIntervalTurn q hq h c hc R j)) =
      turn R.diagram (detachedOldOrbitArc c R (detachedLastOldIndex c R)) -
        historicalIntervalTurn q hq h c hc R (detachedLastOldIndex c R) := by
    apply Finset.sum_eq_single (detachedLastOldIndex c R)
    · intro j hj hne
      rw [historical_old_turn q hq h c hc R j hne,sub_self]
    · simp
  rw [Finset.sum_sub_distrib] at hd
  rw [historical_sharp_totalTurn]
  have hb := historical_boundary_turn q hq h c hc R
  linarith

/-- Unique integer turning transport, with no supplied rotation equality. -/
theorem historicalSharp_turnInteger_eq :
    turnInteger R.diagram = turnInteger (historicalSharpDiagram q hq h c hc R) := by
  apply turnInteger_unique
  rw [historicalSharp_totalTurn_eq q hq h c hc R]
  exact totalTurn_eq_turnInteger _
end DirectGLSSW.HOMFLY.ProcessedExposedChild
