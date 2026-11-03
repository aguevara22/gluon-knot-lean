import SharpDaughterRotationDegree

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughterRotation
open DirectGLSSW PermutationOrbits PrincipalTurning PolygonDrawingBridge SharpDaughter DaughterFirstReturn
open scoped BigOperators
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)

/-- The genuinely unique integer from the independently reviewed full actual
rotation characterization. No fallback or additional domain premise. -/
noncomputable def sharpDaughterRotationInteger : ℤ :=
  Classical.choose (existsUnique_component_actual_rotation_integer q hq S C hNA)

theorem sharpDaughterRotationInteger_spec :
    totalTurn (sharpDaughterDiagram q hq S C hNA) = (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi) ∧
      (∀ root : PolygonEvent q, ∀ hroot : retainedCorner q S root,
        componentOf (P q hq S) root = C →
          SharpDaughterTurning.cornerTotalTurn q hq S root hroot = (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi)) ∧
      (∀ e : Fin (sharpDaughterDiagram q hq S C hNA).nArc, ∀ δ : RoundingFraction, ∀ t : ℝ,
        actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ
          (t + (componentArcLength (sharpDaughterDiagram q hq S C hNA) e : ℝ)) -
        actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ t = (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi)) ∧
      (∀ e : Fin (sharpDaughterDiagram q hq S C hNA).nArc, ∀ δ : RoundingFraction,
        ∀ f : ℝ → ℝ, Continuous f →
          (∀ t, (f t : Real.Angle) =
            ((roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t).arg : Real.Angle)) →
          f (componentArcLength (sharpDaughterDiagram q hq S C hNA) e) - f 0 =
            (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi)) :=
  (Classical.choose_spec (existsUnique_component_actual_rotation_integer q hq S C hNA)).1

theorem sharpDaughterRotationInteger_characterization (r : ℤ) :
    (totalTurn (sharpDaughterDiagram q hq S C hNA) = (r : ℝ) * (2 * Real.pi) ∧
      (∀ root : PolygonEvent q, ∀ hroot : retainedCorner q S root,
        componentOf (P q hq S) root = C →
          SharpDaughterTurning.cornerTotalTurn q hq S root hroot = (r : ℝ) * (2 * Real.pi)) ∧
      (∀ e : Fin (sharpDaughterDiagram q hq S C hNA).nArc, ∀ δ : RoundingFraction, ∀ t : ℝ,
        actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ
          (t + (componentArcLength (sharpDaughterDiagram q hq S C hNA) e : ℝ)) -
        actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ t = (r : ℝ) * (2 * Real.pi)) ∧
      (∀ e : Fin (sharpDaughterDiagram q hq S C hNA).nArc, ∀ δ : RoundingFraction,
        ∀ f : ℝ → ℝ, Continuous f →
          (∀ t, (f t : Real.Angle) =
            ((roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t).arg : Real.Angle)) →
          f (componentArcLength (sharpDaughterDiagram q hq S C hNA) e) - f 0 =
            (r : ℝ) * (2 * Real.pi))) ↔ r = sharpDaughterRotationInteger q hq S C hNA := by
  constructor
  · intro hr
    exact (Classical.choose_spec (existsUnique_component_actual_rotation_integer q hq S C hNA)).2 r hr
  · intro hr
    subst r
    exact sharpDaughterRotationInteger_spec q hq S C hNA

theorem sharpDaughterRotationInteger_eq_turnInteger :
    sharpDaughterRotationInteger q hq S C hNA =
      turnInteger (sharpDaughterDiagram q hq S C hNA) :=
  (turnInteger_unique _ _ (sharpDaughterRotationInteger_spec q hq S C hNA).1).symm

theorem sharpDaughterRotationInteger_unique_iff (r : ℤ) :
    totalTurn (sharpDaughterDiagram q hq S C hNA) = (r : ℝ) * (2 * Real.pi) ↔
      r = sharpDaughterRotationInteger q hq S C hNA := by
  constructor
  · intro hr
    exact (turnInteger_unique _ r hr).symm.trans
      (sharpDaughterRotationInteger_eq_turnInteger q hq S C hNA).symm
  · intro hr
    subst r
    exact (sharpDaughterRotationInteger_spec q hq S C hNA).1

theorem sharpDaughterRotationInteger_cornerTotalTurn (root : PolygonEvent q)
    (hroot : retainedCorner q S root) (hC : componentOf (P q hq S) root = C) :
    SharpDaughterTurning.cornerTotalTurn q hq S root hroot =
      (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi) :=
  (sharpDaughterRotationInteger_spec q hq S C hNA).2.1 root hroot hC

theorem sharpDaughterRotationInteger_actualLift_increment
    (e : Fin (sharpDaughterDiagram q hq S C hNA).nArc) (δ : RoundingFraction) (t : ℝ) :
    actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ
      (t + (componentArcLength (sharpDaughterDiagram q hq S C hNA) e : ℝ)) -
    actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ t =
      (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi) :=
  (sharpDaughterRotationInteger_spec q hq S C hNA).2.2.1 e δ t

theorem sharpDaughterRotationInteger_anyLift_increment
    (e : Fin (sharpDaughterDiagram q hq S C hNA).nArc) (δ : RoundingFraction)
    (f : ℝ → ℝ) (hf : Continuous f)
    (ha : ∀ t, (f t : Real.Angle) =
      ((roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t).arg : Real.Angle)) :
    f (componentArcLength (sharpDaughterDiagram q hq S C hNA) e) - f 0 =
      (sharpDaughterRotationInteger q hq S C hNA : ℝ) * (2 * Real.pi) :=
  (sharpDaughterRotationInteger_spec q hq S C hNA).2.2.2 e δ f hf ha

end DirectGLSSW.HOMFLY.SharpDaughterRotation








