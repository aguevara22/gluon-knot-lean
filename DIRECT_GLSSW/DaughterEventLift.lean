import DaughterVisitLift

set_option autoImplicit false
namespace DirectGLSSW.DaughterEventLift
open DaughterFirstReturn DaughterVisitLift DaughterParentCrossing
  PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

/-- Actual daughter anchors are retained original starts; visits use actual crossings. -/
def eventLift : PolygonEvent (daughterVertex P hP.g2 S root) → PolygonEvent P
  | .inl i => orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val
  | .inr v => Sum.inr (visitLift P hP S hS root hroot v)

theorem eventLift_point (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    polygonEventPoint P (eventLift P hP S hS root hroot x) =
      polygonEventPoint (daughterVertex P hP.g2 S root) x := by
  cases x with
  | inl i => rfl
  | inr v => exact visitLift_point P hP S hS root hroot v

theorem eventLift_carrier (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    polygonEventEdge P (eventLift P hP S hS root hroot x) =
      daughterCarrier P hP.g2 S root (polygonEventEdge (daughterVertex P hP.g2 S root) x) := by
  cases x with
  | inl i => rfl
  | inr v => exact visitLift_carrier P hP S hS root hroot v

theorem eventLift_component (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    componentOf (smoothingDartPermutation P hP.g2 S) (eventLift P hP S hS root hroot x) =
      componentOf (smoothingDartPermutation P hP.g2 S) root := by
  cases x with
  | inl i => exact (orbitEnumeration (DartPerm P hP.g2 S) root
      (cornerEnumeration P hP.g2 S root i).val).property
  | inr v => exact visitLift_component P hP S hS root hroot v

theorem eventLift_retained_iff (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    retainedCorner P S (eventLift P hP S hS root hroot x) ↔ ∃ i, x = Sum.inl i := by
  cases x with
  | inl i => exact ⟨fun _ => ⟨i,rfl⟩,fun _ => (cornerEnumeration P hP.g2 S root i).property⟩
  | inr v =>
    constructor
    · intro h
      exact (visitLift_not_retained P hP S hS root hroot v h).elim
    · rintro ⟨i,h⟩
      cases h

theorem eventLift_injective : Function.Injective (eventLift P hP S hS root hroot) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have he := congrArg (polygonEventEdge P) h
      change daughterCarrier P hP.g2 S root i = daughterCarrier P hP.g2 S root j at he
      exact congrArg Sum.inl (daughterCarrier_injective P hP.g2 S hP.size_ge_three hS root he)
    | inr v =>
      have hr : retainedCorner P S (eventLift P hP S hS root hroot (Sum.inl i)) :=
        (cornerEnumeration P hP.g2 S root i).property
      rw [h] at hr
      exact (visitLift_not_retained P hP S hS root hroot v hr).elim
  | inr v =>
    cases y with
    | inl i =>
      have hr : retainedCorner P S (eventLift P hP S hS root hroot (Sum.inl i)) :=
        (cornerEnumeration P hP.g2 S root i).property
      rw [← h] at hr
      exact (visitLift_not_retained P hP S hS root hroot v hr).elim
    | inr w =>
      exact congrArg Sum.inr (visitLift_injective P hP S hS root hroot (Sum.inr.inj h))

theorem eventLift_zero (hN : 0 < Fintype.card (CornerCoord P hP.g2 S root)) :
    eventLift P hP S hS root hroot (Sum.inl ⟨0,hN⟩) = root := by
  change orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root ⟨0,hN⟩).val = root
  rw [cornerEnumeration_zero_eq_rootcoord P hP.g2 S root hroot hN]
  simp [orbitEventAt]

/-- Every retained event of this component is represented by one daughter anchor. -/
theorem exists_anchorLift (y : PolygonEvent P) (hy : retainedCorner P S y)
    (hcomp : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root) :
    ∃ i, eventLift P hP S hS root hroot (Sum.inl i) = y := by
  let F := orbitEnumeration (DartPerm P hP.g2 S) root
  let r := F.symm ⟨y,hcomp⟩
  have hr : orbitEventAt P hP.g2 S root r = y := congrArg Subtype.val (F.apply_symm_apply ⟨y,hcomp⟩)
  let c : CornerCoord P hP.g2 S root := ⟨r,hr ▸ hy⟩
  refine ⟨(cornerEnumeration P hP.g2 S root).symm c,?_⟩
  change orbitEventAt P hP.g2 S root
    (cornerEnumeration P hP.g2 S root ((cornerEnumeration P hP.g2 S root).symm c)).val = y
  rw [OrderIso.apply_symm_apply]
  exact hr









end
end DirectGLSSW.DaughterEventLift
