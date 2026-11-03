import DaughterAffectedComponents

set_option autoImplicit false
namespace DirectGLSSW.DaughterAffectedProjection
open DaughterFirstReturn DaughterEventLift DaughterPairingLift DaughterAffectedComponents
  DaughterG2Inheritance PermutationOrbits PolygonNonalternation
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)
variable (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)))

theorem oldComponent_finalDart_pow (x : PolygonEvent P) (k : ℕ) :
    componentOf (smoothingDartPermutation P hP.g2 S)
      ((finalDart P hP S hS root hroot T ^ k) x) =
    componentOf (smoothingDartPermutation P hP.g2 S) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,finalDart_preserves_old_component,ih]

theorem oldComponent_unionDart_pow
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) (k : ℕ) :
    componentOf (smoothingDartPermutation P hP.g2 S)
      ((smoothingDartPermutation P hP.g2
        (S ∪ liftedSupport P hP S hS root hroot T) ^ k)
        (eventLift P hP S hS root hroot x)) =
    componentOf (smoothingDartPermutation P hP.g2 S) root :=
  (oldComponent_finalDart_pow P hP S hS root hroot T _ k).trans
    (eventLift_component P hP S hS root hroot x)

variable (f : Component (finalDart P hP S hS root hroot T) →
  Component (smoothingDartPermutation P hP.g2 S))
variable (hf : ∀ x, f (componentOf (finalDart P hP S hS root hroot T) x) =
  componentOf (smoothingDartPermutation P hP.g2 S) x)

include hf in
theorem oldProjection_eq : f = oldComponentOfFinal P hP S hS root hroot T := by
  funext C
  induction C using Quotient.inductionOn with
  | h x => exact hf x

/-- The same actual equivalence with any independently defined old projection
having its actual representative equation, including the spectator partition. -/
def componentEquivAffectedOfProjection :
    Component (daughterDart P hP S hS root T) ≃
    {C : Component (finalDart P hP S hS root hroot T) //
      f C = componentOf (smoothingDartPermutation P hP.g2 S) root} :=
  (componentEquivAffected P hP S hS root hroot T).trans
    ((Equiv.refl _).subtypeEquiv (fun C => by
      change oldComponentOfFinal P hP S hS root hroot T C = _ ↔ f C = _
      rw [oldProjection_eq P hP S hS root hroot T f hf]))

@[simp] theorem componentEquivAffectedOfProjection_componentOf
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    (componentEquivAffectedOfProjection P hP S hS root hroot T f hf
      (componentOf (daughterDart P hP S hS root T) x)).val =
    componentOf (finalDart P hP S hS root hroot T)
      (eventLift P hP S hS root hroot x) := rfl

/-- Incoming daughter classes require pairing their representative before
lifting to the parent's outgoing-dart component. -/
def incomingComponentEquivAffected :
    Component (smoothingIncomingPermutation (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T) ≃
    AffectedFinal P hP S hS root hroot T :=
  (productOrderEquiv
    (polygonEventSuccessor (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root))
    (smoothingPairing (daughterVertex P hP.g2 S root) T)).trans
    (componentEquivAffected P hP S hS root hroot T)

@[simp] theorem incomingComponentEquivAffected_componentOf
    (x : PolygonEvent (daughterVertex P hP.g2 S root)) :
    (incomingComponentEquivAffected P hP S hS root hroot T
      (componentOf (smoothingIncomingPermutation (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T) x)).val =
    componentOf (finalDart P hP S hS root hroot T)
      (eventLift P hP S hS root hroot (smoothingPairing (daughterVertex P hP.g2 S root) T x)) := rfl








end
end DirectGLSSW.DaughterAffectedProjection
