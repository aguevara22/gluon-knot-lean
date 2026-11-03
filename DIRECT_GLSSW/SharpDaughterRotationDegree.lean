import SharpDaughterTurns

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughterRotation
open DirectGLSSW PermutationOrbits PrincipalTurning PolygonDrawingBridge SharpDaughter DaughterFirstReturn
open scoped BigOperators
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)

theorem componentTotalTurn_eq_cornerTotalTurn (root : PolygonEvent q)
    (hroot : retainedCorner q S root) (hC : componentOf (P q hq S) root = C)
    (e : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    componentTotalTurn (sharpDaughterDiagram q hq S C hNA)
      (componentOf (sharpDaughterDiagram q hq S C hNA).continuation e) =
      SharpDaughterTurning.cornerTotalTurn q hq S root hroot := by
  classical
  let D := sharpDaughterDiagram q hq S C hNA
  have hp : D.continuation.IsCycleOn Set.univ := next_isCycleOn q hq S C
  let E : Fibre D.continuation (componentOf D.continuation e) ≃ Fin D.nArc :=
    { toFun := fun x => x.val
      invFun := fun x => ⟨x, (componentOf_eq_iff D.continuation x e).mpr
        (hp.2 (Set.mem_univ x) (Set.mem_univ e))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : componentTotalTurn D (componentOf D.continuation e) = totalTurn D :=
    Fintype.sum_equiv E _ _ (fun _ => rfl)
  exact hs.trans (totalTurn_eq_cornerTotalTurn q hq S C hNA root hroot hC)

theorem actualTangentLift_shift_eq_cornerTotalTurn (root : PolygonEvent q)
    (hroot : retainedCorner q S root) (hC : componentOf (P q hq S) root = C)
    (e : Fin (sharpDaughterDiagram q hq S C hNA).nArc) (δ : RoundingFraction) (t : ℝ) :
    actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ
        (t + (componentArcLength (sharpDaughterDiagram q hq S C hNA) e : ℝ)) -
      actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ t =
        SharpDaughterTurning.cornerTotalTurn q hq S root hroot := by
  rw [actualTangentLift_shift,
    componentTotalTurn_eq_cornerTotalTurn q hq S C hNA root hroot hC]

theorem any_actual_tangent_lift_increment_eq_cornerTotalTurn (root : PolygonEvent q)
    (hroot : retainedCorner q S root) (hC : componentOf (P q hq S) root = C)
    (e : Fin (sharpDaughterDiagram q hq S C hNA).nArc) (δ : RoundingFraction)
    (f : ℝ → ℝ) (hf : Continuous f)
    (ha : ∀ t, (f t : Real.Angle) =
      ((roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t).arg : Real.Angle)) :
    f (componentArcLength (sharpDaughterDiagram q hq S C hNA) e) - f 0 =
      SharpDaughterTurning.cornerTotalTurn q hq S root hroot := by
  rw [any_actual_tangent_lift_increment _ _ _ f hf ha,
    componentTotalTurn_eq_cornerTotalTurn q hq S C hNA root hroot hC]

include hNA in
theorem cornerTotalTurn_root_independent (root root' : PolygonEvent q)
    (hroot : retainedCorner q S root) (hroot' : retainedCorner q S root')
    (hC : componentOf (P q hq S) root = C)
    (hC' : componentOf (P q hq S) root' = C) :
    SharpDaughterTurning.cornerTotalTurn q hq S root hroot =
      SharpDaughterTurning.cornerTotalTurn q hq S root' hroot' :=
  (totalTurn_eq_cornerTotalTurn q hq S C hNA root hroot hC).symm.trans
    (totalTurn_eq_cornerTotalTurn q hq S C hNA root' hroot' hC')

/-- A unique integer simultaneously characterizes the retained source corner
sum and actual continuous tangent degree of every explicit rounding fraction.
No characteristic integer is defined by this theorem. -/
theorem existsUnique_actual_rotation_integer (root : PolygonEvent q)
    (hroot : retainedCorner q S root) (hC : componentOf (P q hq S) root = C) :
    ∃! r : ℤ,
      SharpDaughterTurning.cornerTotalTurn q hq S root hroot = (r : ℝ) * (2 * Real.pi) ∧
      (∀ e : Fin (sharpDaughterDiagram q hq S C hNA).nArc, ∀ δ : RoundingFraction,
        ∃ f : ℝ → ℝ, Continuous f ∧
          (∀ t, (f t : Real.Angle) =
            ((roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t).arg : Real.Angle)) ∧
          (∀ t, f (t + (componentArcLength (sharpDaughterDiagram q hq S C hNA) e : ℝ)) - f t =
            (r : ℝ) * (2 * Real.pi))) ∧
      (∀ e : Fin (sharpDaughterDiagram q hq S C hNA).nArc, ∀ δ : RoundingFraction,
        ∀ f : ℝ → ℝ, Continuous f →
          (∀ t, (f t : Real.Angle) =
            ((roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t).arg : Real.Angle)) →
          f (componentArcLength (sharpDaughterDiagram q hq S C hNA) e) - f 0 =
            (r : ℝ) * (2 * Real.pi)) := by
  obtain ⟨r, hr, hu⟩ := SharpDaughterTurning.existsUnique_cornerTurnInteger q hq S root hroot
  refine ⟨r, ⟨hr, ?_, ?_⟩, ?_⟩
  · intro e δ
    refine ⟨actualTangentLift (sharpDaughterDiagram q hq S C hNA) e δ,
      actualTangentLift_continuous _ _ _, actualTangentLift_coe _ _ _, ?_⟩
    intro t
    rw [actualTangentLift_shift_eq_cornerTotalTurn q hq S C hNA root hroot hC, hr]
  · intro e δ f hf ha
    rw [any_actual_tangent_lift_increment_eq_cornerTotalTurn q hq S C hNA root hroot hC e δ f hf ha, hr]
  · intro s hs
    exact hu s hs.1

theorem actual_rounding_is_short_turn :
    ∀ a : Fin (sharpDaughterDiagram q hq S C hNA).nArc,
      -Real.pi < turn (sharpDaughterDiagram q hq S C hNA) a ∧
        turn (sharpDaughterDiagram q hq S C hNA) a < Real.pi :=
  turn_mem_open_semicircle _

theorem actual_rounding_regular_periodic
    (e : Fin (sharpDaughterDiagram q hq S C hNA).nArc) (δ : RoundingFraction) :
    Function.Periodic (roundedComponentCurve (sharpDaughterDiagram q hq S C hNA) e δ)
      (componentArcLength (sharpDaughterDiagram q hq S C hNA) e : ℝ) ∧
    Continuous (roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ) ∧
    (∀ t : ℝ, HasDerivAt (roundedComponentCurve (sharpDaughterDiagram q hq S C hNA) e δ)
      (roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t) t ∧
      roundedComponentVelocity (sharpDaughterDiagram q hq S C hNA) e δ t ≠ 0) :=
  ⟨roundedComponentCurve_periodic _ _ _, roundedComponentVelocity_continuous _ _ _,
    fun t => ⟨roundedComponentCurve_hasDerivAt _ _ _ t, roundedComponentVelocity_ne_zero _ _ _ t⟩⟩


theorem exists_retained_root :
    ∃ root : PolygonEvent q, retainedCorner q S root ∧ componentOf (P q hq S) root = C := by
  obtain ⟨a⟩ := (inferInstance : Nonempty (Arc q hq S C))
  obtain ⟨root, hcycle, hret⟩ := everyDartOrbit_hasCorner q hq.g2 S hq.size_ge_three a.val
  have hc : componentOf (P q hq S) a.val = componentOf (P q hq S) root :=
    (componentOf_eq_iff _ _ _).mpr hcycle
  exact ⟨root, hret, hc.symm.trans a.property⟩

/-- Root-free full-parent-domain characterization; the actual total turn makes
uniqueness nonvacuous. Every retained root of C has this same actual degree. -/
theorem existsUnique_component_actual_rotation_integer :
    ∃! r : ℤ,
      totalTurn (sharpDaughterDiagram q hq S C hNA) = (r : ℝ) * (2 * Real.pi) ∧
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
            (r : ℝ) * (2 * Real.pi)) := by
  obtain ⟨root, hroot, hC⟩ := exists_retained_root q hq S C
  obtain ⟨r, hr, hu⟩ := existsUnique_turnInteger (sharpDaughterDiagram q hq S C hNA)
  have hsum : SharpDaughterTurning.cornerTotalTurn q hq S root hroot = (r : ℝ) * (2 * Real.pi) :=
    (totalTurn_eq_cornerTotalTurn q hq S C hNA root hroot hC).symm.trans hr
  refine ⟨r, ⟨hr, ?_, ?_, ?_⟩, ?_⟩
  · intro root' hroot' hC'
    exact (totalTurn_eq_cornerTotalTurn q hq S C hNA root' hroot' hC').symm.trans hr
  · intro e δ t
    rw [actualTangentLift_shift_eq_cornerTotalTurn q hq S C hNA root hroot hC, hsum]
  · intro e δ f hf ha
    rw [any_actual_tangent_lift_increment_eq_cornerTotalTurn q hq S C hNA root hroot hC e δ f hf ha, hsum]
  · intro s hs
    exact hu s hs.1

end DirectGLSSW.HOMFLY.SharpDaughterRotation





