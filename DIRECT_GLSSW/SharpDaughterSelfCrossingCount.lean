import SharpDaughterCharacterization

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW PermutationOrbits PolygonDrawingBridge
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)

/-- The individual daughter retains exactly its unselected self crossings.
Selected and mixed crossings contribute no crossing to this count. -/
theorem sharpDaughterDiagram_selfCrossingCount :
    (sharpDaughterDiagram q hq S C hNA).nCrossing =
      Fintype.card {c : PolygonCrossing q // c ∉ S ∧
        ∀ b : Bool, componentOf (P q hq S) (Sum.inr (c,b)) = C} := by
  classical
  let D := sharpDaughterDiagram q hq S C hNA
  let f : Fin D.nCrossing → {c : PolygonCrossing q // c ∉ S ∧
      ∀ b : Bool, componentOf (P q hq S) (Sum.inr (c,b)) = C} := fun d =>
    ⟨(crossingFin q).symm (oldCrossing q hq S C d),
      (actual_crossing_retained_iff q hq S C hNA _).mp
        ⟨d, ((crossingFin q).apply_symm_apply (oldCrossing q hq S C d)).symm⟩⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply oldCrossing_injective q hq S C
    apply (crossingFin q).symm.injective
    exact congrArg Subtype.val hab
  have hs : Function.Surjective f := by
    intro c
    obtain ⟨d, hd⟩ := (actual_crossing_retained_iff q hq S C hNA c.val).mpr c.property
    refine ⟨d, Subtype.ext ?_⟩
    change (crossingFin q).symm (oldCrossing q hq S C d) = c.val
    rw [hd, Equiv.symm_apply_apply]
  simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)

theorem sharpDaughterDiagram_selfCrossingCount_filter :
    (sharpDaughterDiagram q hq S C hNA).nCrossing =
      (Finset.univ.filter (fun c : PolygonCrossing q => c ∉ S ∧
        ∀ b : Bool, componentOf (P q hq S) (Sum.inr (c,b)) = C)).card := by
  classical
  rw [sharpDaughterDiagram_selfCrossingCount q hq S C hNA, Fintype.card_subtype]

end DirectGLSSW.HOMFLY.SharpDaughter


