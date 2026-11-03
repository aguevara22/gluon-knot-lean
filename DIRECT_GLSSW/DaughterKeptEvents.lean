import DaughterEventLift

set_option autoImplicit false
namespace DirectGLSSW.DaughterKeptEvents
open DaughterFirstReturn DaughterVisitLift DaughterEventLift PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

/-- Keep retained corners and actual self-crossing visits in this old component.
Visits at crossings with other components are omitted. -/
def keptEvent (y : PolygonEvent P) : Prop :=
  componentOf (smoothingDartPermutation P hP.g2 S) y =
    componentOf (smoothingDartPermutation P hP.g2 S) root ∧
  (retainedCorner P S y ∨ match y with
    | .inl _ => False
    | .inr v => componentOf (smoothingDartPermutation P hP.g2 S)
        (Sum.inr (crossingVisitFlip P v)) =
      componentOf (smoothingDartPermutation P hP.g2 S) root)

theorem eventLift_kept (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    keptEvent P hP S root (eventLift P hP S hS root hroot x) := by
  refine ⟨eventLift_component P hP S hS root hroot x,?_⟩
  cases x with
  | inl i => exact Or.inl (cornerEnumeration P hP.g2 S root i).property
  | inr v =>
    apply Or.inr
    change componentOf (smoothingDartPermutation P hP.g2 S)
      (Sum.inr (crossingVisitFlip P (visitLift P hP S hS root hroot v))) = _
    rw [← visitLift_flip]
    exact visitLift_component P hP S hS root hroot _

theorem exists_eventLift_iff (y : PolygonEvent P) :
    (∃ x, eventLift P hP S hS root hroot x = y) ↔ keptEvent P hP S root y := by
  constructor
  · rintro ⟨x,rfl⟩
    exact eventLift_kept P hP S hS root hroot x
  · rintro ⟨hcomp,hkept⟩
    by_cases hret : retainedCorner P S y
    · obtain ⟨i,hi⟩ := exists_anchorLift P hP S hS root hroot y hret hcomp
      exact ⟨Sum.inl i,hi⟩
    · have hother := hkept.resolve_left hret
      cases y with
      | inl i => exact hother.elim
      | inr v =>
        have hc : v.1 ∉ S := hret
        have hf : componentOf (smoothingDartPermutation P hP.g2 S) (Sum.inr (v.1,false)) =
            componentOf (smoothingDartPermutation P hP.g2 S) root := by
          rcases v with ⟨c,b⟩
          cases b
          · exact hcomp
          · exact hother
        have ht : componentOf (smoothingDartPermutation P hP.g2 S) (Sum.inr (v.1,true)) =
            componentOf (smoothingDartPermutation P hP.g2 S) root := by
          rcases v with ⟨c,b⟩
          cases b
          · exact hother
          · exact hcomp
        obtain ⟨w,hw⟩ := exists_visitLift P hP S hS root hroot v hc hf ht
        exact ⟨Sum.inr w,congrArg Sum.inr hw⟩

def eventEquivKept : PolygonEvent (daughterVertex P hP.g2 S root) ≃
    {y : PolygonEvent P // keptEvent P hP S root y} :=
  Equiv.ofBijective (fun x => ⟨eventLift P hP S hS root hroot x,eventLift_kept P hP S hS root hroot x⟩)
    ⟨fun _ _ h => eventLift_injective P hP S hS root hroot (congrArg Subtype.val h),by
      intro y
      obtain ⟨x,hx⟩ := (exists_eventLift_iff P hP S hS root hroot y.val).mpr y.property
      exact ⟨x,Subtype.ext hx⟩⟩

theorem eventEquivKept_apply (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    (eventEquivKept P hP S hS root hroot x).val = eventLift P hP S hS root hroot x := rfl






end
end DirectGLSSW.DaughterKeptEvents
