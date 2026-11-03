import OrderedStarBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

/-- Actual ordered secant, with the first branch's actual component as domain.
The following theorems apply it only when both branch visits lie on that component. -/
noncomputable def basedOrderedCrossingPullback {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i j : Fin 2) (x y : ℝ) : ℂ :=
  Complex.equivRealProd.symm (
    basedUniformPLCurve T (componentOf D.continuation (D.incoming c i))
      (crossingVisitTime T c j + crossingStarCoordinateInverse D c j y) -
    basedUniformPLCurve T (componentOf D.continuation (D.incoming c i))
      (crossingVisitTime T c i + crossingStarCoordinateInverse D c i x))

theorem basedOrderedCrossingPullback01 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1))
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c))
    (hy : y ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c)) :
    basedOrderedCrossingPullback T c 0 1 x y = crossingStarPullback D c x y := by
  apply Complex.equivRealProd.injective
  simp only [basedOrderedCrossingPullback,Equiv.apply_symm_apply]
  exact (basedUniformPLCurve_secant01 T c hC _ _
    (Set.Ioo_subset_Icc_self (crossingStarStrict_inverse_window D c 0 x hx))
    (Set.Ioo_subset_Icc_self (crossingStarStrict_inverse_window D c 1 y hy))).symm

theorem basedOrderedCrossingPullback10 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1))
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c))
    (hy : y ∈ Set.Icc (-crossingStarStrictRadius D c) (2*crossingStarStrictRadius D c)) :
    basedOrderedCrossingPullback T c 1 0 x y = -crossingStarPullback D c y x := by
  apply Complex.equivRealProd.injective
  simp only [basedOrderedCrossingPullback,Equiv.apply_symm_apply]
  rw [← hC]
  exact (basedUniformPLCurve_secant10 T c hC _ _
    (Set.Ioo_subset_Icc_self (crossingStarStrict_inverse_window D c 1 x hx))
    (Set.Ioo_subset_Icc_self (crossingStarStrict_inverse_window D c 0 y hy))).symm

theorem starEightTurn_congr_rectangle (Z W : ℝ → ℝ → ℂ) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ x y, x ∈ Set.Icc (-ε) (2*ε) → y ∈ Set.Icc (-ε) (2*ε) → Z x y = W x y) :
    starEightTurn Z ε = starEightTurn W ε := by
  have hm : -ε ∈ Set.Icc (-ε) (2*ε) := ⟨le_refl _, by linarith⟩
  have hz : (0 : ℝ) ∈ Set.Icc (-ε) (2*ε) := ⟨by linarith,by linarith⟩
  have hp : 2*ε ∈ Set.Icc (-ε) (2*ε) := ⟨by linarith,le_refl _⟩
  simp only [starEightTurn,h _ _ hz hm,h _ _ hm hm,h _ _ hp hm,h _ _ hp hz,
    h _ _ hp hp,h _ _ hz hp,h _ _ hm hp,h _ _ hm hz]

theorem basedOrderedCrossing_boundary01 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1)) :
    starEightTurn (basedOrderedCrossingPullback T c 0 1) (crossingStarStrictRadius D c) =
      if 0 < complexDet (crossingVector D c 0) (crossingVector D c 1)
      then -(2*Real.pi) else 2*Real.pi := by
  rw [starEightTurn_congr_rectangle _ (crossingStarPullback D c) _
    (crossingStarStrictRadius_pos D c) (basedOrderedCrossingPullback01 T c hC)]
  exact actualStar_boundary_breakpoint_balance_at_radius D c _ (crossingStarStrictRadius_pos D c)

theorem basedOrderedCrossing_boundary10 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1)) :
    starEightTurn (basedOrderedCrossingPullback T c 1 0) (crossingStarStrictRadius D c) =
      if 0 < complexDet (crossingVector D c 1) (crossingVector D c 0)
      then -(2*Real.pi) else 2*Real.pi := by
  rw [starEightTurn_congr_rectangle _ (fun x y => -crossingStarPullback D c y x) _
    (crossingStarStrictRadius_pos D c) (basedOrderedCrossingPullback10 T c hC)]
  exact actualStar_boundary_balance10 D c _ (crossingStarStrictRadius_pos D c)

end DirectGLSSW.HOMFLY.PrincipalTurning





