import DaughterInteriorComponent
import DirectGLSSW.ActualLocalSupports

set_option autoImplicit false
namespace DirectGLSSW.DaughterLocalCrossing
open DaughterFirstReturn DaughterParentCrossing DaughterCrossingAvoidance
  DaughterInteriorComponent PolygonNonalternation PermutationOrbits ActualLocalSupports
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

/-- Both visits of the actual lifted crossing lie in the actual daughter component. -/
theorem parentCrossing_visit_component
    (c : PolygonCrossing (daughterVertex P hP.g2 S root)) (b : Bool) :
    componentOf (smoothingDartPermutation P hP.g2 S)
        (Sum.inr (parentCrossing P hP S hS root hroot c,b)) =
      componentOf (smoothingDartPermutation P hP.g2 S) root := by
  have hp : polygonEventPoint P (Sum.inr (parentCrossing P hP S hS root hroot c,b)) =
      crossingPoint (daughterVertex P hP.g2 S root) c :=
    parentCrossing_point P hP S hS root hroot c
  have step (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
      (he : polygonEventEdge P (Sum.inr (parentCrossing P hP S hS root hroot c,b)) =
        daughterCarrier P hP.g2 S root i)
      (hi : edgeInterior (daughterVertex P hP.g2 S root) i
        (crossingPoint (daughterVertex P hP.g2 S root) c)) :
      componentOf (smoothingDartPermutation P hP.g2 S)
          (Sum.inr (parentCrossing P hP S hS root hroot c,b)) =
        componentOf (smoothingDartPermutation P hP.g2 S) root := by
    apply event_in_daughter_edge_component P hP S root hroot i _ he
    rw [hp]
    exact hi
  by_cases h : daughterCarrier P hP.g2 S root c.val.1 <
      daughterCarrier P hP.g2 S root c.val.2
  · cases b
    · apply step c.val.1 _ (crossingPoint_mem_left _ c)
      simp only [polygonEventEdge,crossingVisitEdge,Bool.false_eq_true,ite_false,
        parentCrossing_labels,h,ite_true]
    · apply step c.val.2 _ (crossingPoint_mem_right _ c)
      simp only [polygonEventEdge,crossingVisitEdge,ite_true,parentCrossing_labels,h]
  · cases b
    · apply step c.val.2 _ (crossingPoint_mem_right _ c)
      simp only [polygonEventEdge,crossingVisitEdge,Bool.false_eq_true,ite_false,
        parentCrossing_labels,h]
    · apply step c.val.1 _ (crossingPoint_mem_left _ c)
      simp only [polygonEventEdge,crossingVisitEdge,ite_true,parentCrossing_labels,h,ite_false]

/-- The geometric crossing map lands in the genuine old component's local crossings. -/
def localCrossingEmbedding : PolygonCrossing (daughterVertex P hP.g2 S root) ↪
    LocalCrossing P (smoothingDartPermutation P hP.g2 S) S
      (componentOf (smoothingDartPermutation P hP.g2 S) root) where
  toFun c := ⟨parentCrossing P hP S hS root hroot c,
    parentCrossing_not_mem P hP S hS root hroot c,
    parentCrossing_visit_component P hP S hS root hroot c false,
    parentCrossing_visit_component P hP S hS root hroot c true⟩
  inj' := fun _ _ h => parentCrossing_injective P hP S hS root hroot (congrArg Subtype.val h)



end
end DirectGLSSW.DaughterLocalCrossing
