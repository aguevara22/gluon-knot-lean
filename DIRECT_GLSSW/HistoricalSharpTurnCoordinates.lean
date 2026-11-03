import TwoBendContraction
import ProcessedSharpCrossingComparison
import SharpDaughterTurns
import ComponentTurnRestriction
import ProcessedChildArcSubsegment
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge PrincipalTurning
open SmoothingCornerGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- Every actual old arc has exactly the positive direction of its proved
original ancestor. This uses produced ordered subsegment parameters. -/
theorem historical_old_arcVector (j : Fin (detachedOrbitSize t c R-1)) :
    ∃ a : ℝ, 0<a ∧
      PrincipalTurning.arcVector R.diagram (detachedOldOrbitArc c R j) =
        (a:ℂ)*PrincipalTurning.arcVector (positivePolygonEventDiagram q hq) (h.detachedOriginalArc c hc R j) := by
  obtain ⟨a₀,u,v,ha₀,hu,huv,hv,hs,ht⟩ := h.detached_old_arc_subsegment c hc R
    (detachedOldOrbitArc c R j) (detachedOldOrbitCode c R j) (detachedOldOrbitCode_spec c R j)
  have he : a₀ = h.detachedOriginalArc c hc R j :=
    Option.some.inj (ha₀.symm.trans (h.detachedOriginalArc_spec c hc R j))
  subst a₀
  refine ⟨v-u,sub_pos.mpr huv,?_⟩
  dsimp only [positivePolygonMarkedState] at hs ht
  unfold PrincipalTurning.arcVector
  rw [hs,ht]
  apply Complex.ext <;>
    simp [affinePoint,Complex.mul_re,Complex.mul_im] <;> ring

/-- Actual whole sharp arc fibre, without dropping demoted crossing visits. -/
def sharpIntervalArcEquiv :
    Fin (detachedOrbitSize t c R-1) ≃
      SharpDaughter.Arc q hq (sharpSupport q hq h c) (sharpIntervalComponent q hq h c hc R) :=
  Equiv.ofBijective
    (fun j => ⟨sharpIntervalEvent q hq h c hc R j,
      (sharpInterval_mem_iff q hq h c hc R _).mpr ⟨j,by simp [sharpIntervalEvent]⟩⟩) (by
        constructor
        · intro i j he
          apply h.detachedOriginalArc_injective c hc R
          have hh := congrArg (fun x => eventFin q x.val) he
          simpa only [sharpIntervalEvent,Equiv.apply_symm_apply] using hh
        · intro x
          obtain ⟨j,hj⟩ := (sharpInterval_mem_iff q hq h c hc R x.val).mp x.property
          refine ⟨j,Subtype.ext ?_⟩
          apply (eventFin q).injective
          simpa only [sharpIntervalEvent,Equiv.apply_symm_apply] using hj)

/-- The exact original cyclic interval principal turns. -/
def historicalIntervalTurn (j : Fin (detachedOrbitSize t c R-1)) : ℝ :=
  Complex.arg (PrincipalTurning.arcVector (positivePolygonEventDiagram q hq)
      (h.detachedOriginalArc c hc R (cyclicSuccessor j)) /
    PrincipalTurning.arcVector (positivePolygonEventDiagram q hq) (h.detachedOriginalArc c hc R j))

/-- Reindex the actual sharp diagram's physical total turn by its proved
original interval. No retained-word or sum equality is supplied. -/
theorem historical_sharp_totalTurn :
    totalTurn (historicalSharpDiagram q hq h c hc R) =
      ∑ j, historicalIntervalTurn q hq h c hc R j := by
  let S := sharpSupport q hq h c
  let C := sharpIntervalComponent q hq h c hc R
  let E := (sharpIntervalArcEquiv q hq h c hc R).trans (SharpDaughter.arcEquiv q hq S C).symm
  change (∑ a, turn (historicalSharpDiagram q hq h c hc R) a) = _
  symm
  apply Fintype.sum_equiv E
  intro j
  change _ = Complex.arg (PrincipalTurning.arcVector (historicalSharpDiagram q hq h c hc R)
    ((historicalSharpDiagram q hq h c hc R).continuation (E j)) /
      PrincipalTurning.arcVector (historicalSharpDiagram q hq h c hc R) (E j))
  dsimp only [historicalSharpDiagram]
  rw [SharpDaughterRotation.actual_arcVector,SharpDaughterRotation.actual_arcVector]
  change _ = Complex.arg (PrincipalTurning.arcVector (positivePolygonEventDiagram q hq)
    (SharpDaughter.oldArc q hq S C (SharpDaughter.next q hq S C (E j))) /
      PrincipalTurning.arcVector (positivePolygonEventDiagram q hq) (SharpDaughter.oldArc q hq S C (E j)))
  rw [SharpDaughter.old_next]
  have he : SharpDaughter.arcEquiv q hq S C (E j) = sharpIntervalArcEquiv q hq h c hc R j :=
    (SharpDaughter.arcEquiv q hq S C).apply_symm_apply _
  simp only [SharpDaughter.oldArc]
  rw [he]
  change _ = Complex.arg (PrincipalTurning.arcVector (positivePolygonEventDiagram q hq)
    (eventFin q (SharpDaughter.P q hq S (sharpIntervalEvent q hq h c hc R j))) /
      PrincipalTurning.arcVector (positivePolygonEventDiagram q hq) (eventFin q (sharpIntervalEvent q hq h c hc R j)))
  rw [sharpIntervalEvent_step q hq h c hc R]
  simp only [sharpIntervalEvent,Equiv.apply_symm_apply,historicalIntervalTurn]
end DirectGLSSW.HOMFLY.ProcessedExposedChild
