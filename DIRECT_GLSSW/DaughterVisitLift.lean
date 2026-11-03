import DaughterLocalCrossingEquiv

set_option autoImplicit false
namespace DirectGLSSW.DaughterVisitLift
open DaughterFirstReturn DaughterParentCrossing DaughterLocalCrossing
  DaughterCrossingAvoidance PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

/-- The Boolean visit label reverses exactly when the two parent carriers reverse. -/
def parentSide (c : PolygonCrossing (daughterVertex P hP.g2 S root)) (b : Bool) : Bool :=
  if daughterCarrier P hP.g2 S root c.val.1 < daughterCarrier P hP.g2 S root c.val.2
  then b else !b

def visitLift (v : CrossingVisit (daughterVertex P hP.g2 S root)) : CrossingVisit P :=
  (parentCrossing P hP S hS root hroot v.1,parentSide P hP S root v.1 v.2)

theorem visitLift_crossing (v : CrossingVisit (daughterVertex P hP.g2 S root)) :
    (visitLift P hP S hS root hroot v).1 = parentCrossing P hP S hS root hroot v.1 := rfl

theorem visitLift_point (v : CrossingVisit (daughterVertex P hP.g2 S root)) :
    crossingVisitPoint P (visitLift P hP S hS root hroot v) =
      crossingVisitPoint (daughterVertex P hP.g2 S root) v :=
  parentCrossing_point P hP S hS root hroot v.1

theorem visitLift_carrier (v : CrossingVisit (daughterVertex P hP.g2 S root)) :
    crossingVisitEdge P (visitLift P hP S hS root hroot v) =
      daughterCarrier P hP.g2 S root (crossingVisitEdge (daughterVertex P hP.g2 S root) v) := by
  rcases v with ⟨c,b⟩
  by_cases h : daughterCarrier P hP.g2 S root c.val.1 < daughterCarrier P hP.g2 S root c.val.2
  · cases b <;> simp [visitLift,parentSide,crossingVisitEdge,parentCrossing_labels,h]
  · cases b <;> simp [visitLift,parentSide,crossingVisitEdge,parentCrossing_labels,h]

theorem visitLift_flip (v : CrossingVisit (daughterVertex P hP.g2 S root)) :
    visitLift P hP S hS root hroot (crossingVisitFlip (daughterVertex P hP.g2 S root) v) =
      crossingVisitFlip P (visitLift P hP S hS root hroot v) := by
  rcases v with ⟨c,b⟩
  by_cases h : daughterCarrier P hP.g2 S root c.val.1 < daughterCarrier P hP.g2 S root c.val.2
  · cases b <;> simp [visitLift,parentSide,crossingVisitFlip,h]
  · cases b <;> simp [visitLift,parentSide,crossingVisitFlip,h]

theorem visitLift_injective : Function.Injective (visitLift P hP S hS root hroot) := by
  rintro ⟨c,b⟩ ⟨d,a⟩ h
  have hc : c = d := parentCrossing_injective P hP S hS root hroot (congrArg Prod.fst h)
  subst d
  have hb := congrArg Prod.snd h
  change parentSide P hP S root c b = parentSide P hP S root c a at hb
  unfold parentSide at hb
  split_ifs at hb with hlt
  · exact Prod.ext rfl hb
  · cases b <;> cases a <;> simp_all

theorem visitLift_component (v : CrossingVisit (daughterVertex P hP.g2 S root)) :
    componentOf (smoothingDartPermutation P hP.g2 S)
      (Sum.inr (visitLift P hP S hS root hroot v)) =
      componentOf (smoothingDartPermutation P hP.g2 S) root :=
  parentCrossing_visit_component P hP S hS root hroot v.1 (parentSide P hP S root v.1 v.2)

theorem visitLift_not_retained (v : CrossingVisit (daughterVertex P hP.g2 S root)) :
    ¬ retainedCorner P S (Sum.inr (visitLift P hP S hS root hroot v)) :=
  parentCrossing_not_mem P hP S hS root hroot v.1

/-- Every visit of an actual eligible local crossing is the lift of a daughter visit. -/
theorem exists_visitLift (v : CrossingVisit P) (hv : v.1 ∉ S)
    (hf : componentOf (smoothingDartPermutation P hP.g2 S) (Sum.inr (v.1,false)) =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (ht : componentOf (smoothingDartPermutation P hP.g2 S) (Sum.inr (v.1,true)) =
      componentOf (smoothingDartPermutation P hP.g2 S) root) :
    ∃ w, visitLift P hP S hS root hroot w = v := by
  let c : ActualLocalSupports.LocalCrossing P (smoothingDartPermutation P hP.g2 S) S
      (componentOf (smoothingDartPermutation P hP.g2 S) root) := ⟨v.1,hv,hf,ht⟩
  obtain ⟨d,hd⟩ := DaughterLocalCrossingEquiv.localCrossingEmbedding_surjective P hP S hS root hroot c
  have hd' : parentCrossing P hP S hS root hroot d = v.1 := congrArg Subtype.val hd
  refine ⟨(d,parentSide P hP S root d v.2),?_⟩
  apply Prod.ext
  · exact hd'
  · change parentSide P hP S root d (parentSide P hP S root d v.2) = v.2
    unfold parentSide
    split_ifs <;> simp











end
end DirectGLSSW.DaughterVisitLift
