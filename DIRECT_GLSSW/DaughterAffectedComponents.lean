import FirstReturnComponents
import DaughterSecondReturn
import DirectGLSSW.IndexedInvariantPartition

set_option autoImplicit false
namespace DirectGLSSW.DaughterAffectedComponents
open DaughterFirstReturn DaughterParentCrossing DaughterLocalCrossing
  DaughterEventLift DaughterKeptEvents DaughterPairingLift DaughterSecondReturn
  DaughterG2Inheritance PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)
variable (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))

abbrev finalDart := smoothingDartPermutation P hP.g2
  (S ∪ liftedSupport P hP S hS root hroot T)
abbrev daughterDart := smoothingDartPermutation (daughterVertex P hP.g2 S root)
  (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T

theorem liftedPairing_preserves_old_component (x : PolygonEvent P) :
    componentOf (smoothingDartPermutation P hP.g2 S)
      (smoothingPairing P (liftedSupport P hP S hS root hroot T) x) =
    componentOf (smoothingDartPermutation P hP.g2 S) x := by
  cases x with
  | inl a => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    by_cases hc : c ∈ liftedSupport P hP S hS root hroot T
    · have h (a : Bool) := (liftedSupport_visit_kept P hP S hS root hroot T (c,a) hc).1
      cases b <;> simp only [smoothingPairing_apply,smoothingPairingMap_visit,
        if_pos hc,crossingVisitFlip,Bool.not_false,Bool.not_true,h]
    · rw [(smoothingPairing_visit_fixed_iff P _ (c,b)).mpr hc]

theorem finalDart_preserves_old_component (x : PolygonEvent P) :
    componentOf (smoothingDartPermutation P hP.g2 S)
      (finalDart P hP S hS root hroot T x) =
    componentOf (smoothingDartPermutation P hP.g2 S) x := by
  rw [finalDart,smoothingDartPermutation_union P hP.g2 S _
    (liftedSupport_disjoint P hP S hS root hroot T),Equiv.Perm.mul_apply,
    liftedPairing_preserves_old_component,componentOf_apply]

def oldComponentOfFinal : Component (finalDart P hP S hS root hroot T) →
    Component (smoothingDartPermutation P hP.g2 S) :=
  Quotient.lift (componentOf (smoothingDartPermutation P hP.g2 S))
    (fun _ _ h => IndexedInvariantPartition.index_eq_of_sameCycle
      (finalDart P hP S hS root hroot T)
      (componentOf (smoothingDartPermutation P hP.g2 S))
      (finalDart_preserves_old_component P hP S hS root hroot T) h)

@[simp] theorem oldComponentOfFinal_componentOf (x : PolygonEvent P) :
    oldComponentOfFinal P hP S hS root hroot T
      (componentOf (finalDart P hP S hS root hroot T) x) =
    componentOf (smoothingDartPermutation P hP.g2 S) x := rfl

def AffectedFinal := {C : Component (finalDart P hP S hS root hroot T) //
  oldComponentOfFinal P hP S hS root hroot T C =
    componentOf (smoothingDartPermutation P hP.g2 S) root}

instance affectedFinalFintype : Fintype (AffectedFinal P hP S hS root hroot T) := by
  unfold AffectedFinal
  infer_instance

theorem sameCycle_eventLift_iff (x y : PolygonEvent (daughterVertex P hP.g2 S root)) :
    (daughterDart P hP S hS root T).SameCycle x y ↔
    (finalDart P hP S hS root hroot T).SameCycle
      (eventLift P hP S hS root hroot x) (eventLift P hP S hS root hroot y) :=
  FirstReturnComponents.sameCycle_iff _ _ _ (eventLift_injective P hP S hS root hroot)
    (keptEvent P hP S root) (eventLift_kept P hP S hS root hroot)
    (secondStage_firstReturn P hP S hS root hroot T) x y

def componentMap : Component (daughterDart P hP S hS root T) →
    Component (finalDart P hP S hS root hroot T) :=
  FirstReturnComponents.componentMap _ _ (eventLift P hP S hS root hroot)
    (keptEvent P hP S root) (secondStage_firstReturn P hP S hS root hroot T)

@[simp] theorem componentMap_componentOf (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    componentMap P hP S hS root hroot T
      (componentOf (daughterDart P hP S hS root T) x) =
    componentOf (finalDart P hP S hS root hroot T) (eventLift P hP S hS root hroot x) := rfl

theorem componentMap_affected (C : Component (daughterDart P hP S hS root T)) :
    oldComponentOfFinal P hP S hS root hroot T (componentMap P hP S hS root hroot T C) =
    componentOf (smoothingDartPermutation P hP.g2 S) root := by
  induction C using Quotient.inductionOn with
  | h x => exact eventLift_component P hP S hS root hroot x

theorem retained_final_kept (y : PolygonEvent P)
    (hy : retainedCorner P (S ∪ liftedSupport P hP S hS root hroot T) y)
    (hcomp : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root) :
    keptEvent P hP S root y := by
  cases y with
  | inl a => exact ⟨hcomp,Or.inl trivial⟩
  | inr v =>
    rcases Finset.mem_union.mp hy with hS' | hT
    · exact ⟨hcomp,Or.inl hS'⟩
    · exact liftedSupport_visit_kept P hP S hS root hroot T v hT

theorem exists_lift_in_affected_component
    (C : AffectedFinal P hP S hS root hroot T) :
    ∃ x : PolygonEvent (daughterVertex P hP.g2 S root),
      componentOf (finalDart P hP S hS root hroot T)
        (eventLift P hP S hS root hroot x) = C.val := by
  obtain ⟨z,hz⟩ := (inferInstance : Nonempty (Fibre (finalDart P hP S hS root hroot T) C.val))
  obtain ⟨y,hycycle,hyret⟩ := everyDartOrbit_hasCorner P hP.g2
    (S ∪ liftedSupport P hP S hS root hroot T) hP.size_ge_three z
  have hy : componentOf (finalDart P hP S hS root hroot T) y = C.val :=
    ((componentOf_eq_iff _ _ _).mpr hycycle).symm.trans hz
  have hcomp : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root := by
    have h := congrArg (oldComponentOfFinal P hP S hS root hroot T) hy
    exact h.trans C.property
  obtain ⟨x,hx⟩ := (exists_eventLift_iff P hP S hS root hroot y).mpr
    (retained_final_kept P hP S hS root hroot T y hyret hcomp)
  exact ⟨x,by rw [hx]; exact hy⟩

def componentEquivAffected : Component (daughterDart P hP S hS root T) ≃
    AffectedFinal P hP S hS root hroot T :=
  Equiv.ofBijective
    (fun C => ⟨componentMap P hP S hS root hroot T C,
      componentMap_affected P hP S hS root hroot T C⟩) ⟨by
      intro C D h
      exact FirstReturnComponents.componentMap_injective _ _ _
        (eventLift_injective P hP S hS root hroot) (keptEvent P hP S root)
        (eventLift_kept P hP S hS root hroot)
        (secondStage_firstReturn P hP S hS root hroot T) (congrArg Subtype.val h),by
      intro C
      obtain ⟨x,hx⟩ := exists_lift_in_affected_component P hP S hS root hroot T C
      exact ⟨componentOf _ x,Subtype.ext hx⟩⟩

@[simp] theorem componentEquivAffected_componentOf
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    (componentEquivAffected P hP S hS root hroot T
      (componentOf (daughterDart P hP S hS root T) x)).val =
    componentOf (finalDart P hP S hS root hroot T) (eventLift P hP S hS root hroot x) := rfl

theorem component_count_eq_affected :
    Fintype.card (Component (daughterDart P hP S hS root T)) =
    Fintype.card (AffectedFinal P hP S hS root hroot T) :=
  Fintype.card_congr (componentEquivAffected P hP S hS root hroot T)
















end
end DirectGLSSW.DaughterAffectedComponents
