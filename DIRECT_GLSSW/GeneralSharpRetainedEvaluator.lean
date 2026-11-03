import GeneralSharpRetainedNext
import FirstChildEvaluatorZero
import ActualTerminalFramedValue
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.GeneralSharpRetained
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge DaughterFirstReturn Coefficients
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
  (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
  (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
  (hroot : retainedCorner q S root)
  (hP : CyclicGeneric (daughterVertex q hq.g2 S root))

theorem branch_data (d : PolygonCrossing (daughterVertex q hq.g2 S root)) :
    (∀ i : Fin 2, branchPermutation q hq S root d
      ((sharpDiagram q hq S root hNA).through (crossingIndexEquiv q hq S root hNA hroot d) i) =
      (retainedDiagram q hq S root hP).through (crossingFin _ d)
        (branchPermutation q hq S root d i)) ∧
    branchPermutation q hq S root d
      ((sharpDiagram q hq S root hNA).overBranch (crossingIndexEquiv q hq S root hNA hroot d)) =
      (retainedDiagram q hq S root hP).overBranch (crossingFin _ d) ∧
    crossingSign (sharpDiagram q hq S root hNA) (crossingIndexEquiv q hq S root hNA hroot d) =
      crossingSign (retainedDiagram q hq S root hP) (crossingFin _ d) := by
  refine ⟨fun _ => rfl,?_,?_⟩
  · change branchPermutation q hq S root d ((positivePolygonEventDiagram q hq).overBranch
      (SharpDaughter.oldCrossing q hq S (componentOf (smoothingDartPermutation q hq.g2 S) root)
        (crossingIndexEquiv q hq S root hNA hroot d))) = _
    rw [crossingIndexEquiv_old]
    exact branchPermutation_over q hq S root hNA hroot hP d
  · exact (SharpDaughter.sharpDaughterDiagram_crossingSign q hq S _ hNA _).trans
      (positivePolygonEventDiagram_crossingSign _ hP _).symm

include hroot in
/-- Equality for the actual sharp daughter and actual retained polygon, with
all branch, crossing, and cyclic order data constructed from the original support. -/
theorem evaluator_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H) :
    H (sharpDiagram q hq S root hNA) (SharpDaughter.arc_count_pos q hq S _ hNA) =
    H (retainedDiagram q hq S root hP) (positivePolygonEventDiagram_nArc_pos _ hP) := by
  by_cases hz : (sharpDiagram q hq S root hNA).nCrossing = 0
  · have hzQ : (retainedDiagram q hq S root hP).nCrossing = 0 :=
      (crossing_count q hq S root hNA hroot hP).symm.trans hz
    exact (normalizedEvaluator_eq_one_of_zero_crossings H hH _
      (SharpDaughter.arc_count_pos q hq S _ hNA) hz
      (SharpDaughter.sharpDaughterDiagram_componentCount q hq S _ hNA)).trans
      (normalizedEvaluator_eq_one_of_zero_crossings H hH _
        (positivePolygonEventDiagram_nArc_pos _ hP) hzQ
        (positivePolygonEventDiagram_componentCount _ hP)).symm
  let d : Fin (sharpDiagram q hq S root hNA).nCrossing := ⟨0,Nat.pos_of_ne_zero hz⟩
  letI : Nonempty (PolygonCrossing (daughterVertex q hq.g2 S root)) :=
    ⟨(crossingIndexEquiv q hq S root hNA hroot).symm d⟩
  exact normalizedEvaluator_eq_of_branch_matching_incoming H hH _ _
    (SharpDaughter.arc_count_pos q hq S _ hNA) (positivePolygonEventDiagram_nArc_pos _ hP)
    (crossingIndexEquiv q hq S root hNA hroot) (crossingFin _)
    (branchPermutation q hq S root)
    (SharpDaughter.next_isCycleOn q hq S _) (polygonEventDiagram_isCycleOn _ hP)
    (incoming_next_eq q hq S root hNA hroot hP)
    (fun j => (branch_data q hq S root hNA hroot hP j).1)
    (fun j => (branch_data q hq S root hNA hroot hP j).2.1)
    (fun j => (branch_data q hq S root hNA hroot hP j).2.2)



end DirectGLSSW.HOMFLY.GeneralSharpRetained
