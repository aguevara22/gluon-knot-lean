import ActiveArcCornerClosedAuxiliary

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive RetainedWords PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)

theorem corner_closedWeight_eq (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary q hR) (T : Support (suffix q) (regular_suffix q hR))
    (D : {D : Components (suffix q) (regular_suffix q hR) T //
      D ≠ openComponent (suffix q) (regular_suffix q hR).noTriple T.val}) :
    let C := cornerClosedComponentEquiv q hR hfree T D
    closedWeight (suffix q) (regular_suffix q hR)
      (corner_closedAuxiliary_suffix q hR hfree hAux) T D.val =
    closedWeight q hR hAux (firstEdgeFreeSupportEquiv q hfree hR T) C.val := by
  dsimp only
  have hC : (cornerClosedComponentEquiv q hR hfree T D).val ≠
      openComponent q hR.noTriple (firstEdgeFreeSupportEquiv q hfree hR T).val :=
    (cornerClosedComponentEquiv q hR hfree T D).property
  rw [closedWeight,dif_pos D.property,closedWeight,dif_pos hC]
  exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI
    (corner_closedAuxiliary_suffix q hR hfree hAux T D.val D.property)
    (corner_closed_word_isRotated q hR hfree T D)

/-- All actual closed factors are preserved, with no nonzero or division hypothesis. -/
theorem corner_closedWeight_product_eq (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary q hR) (T : Support (suffix q) (regular_suffix q hR)) :
    (∏ D ∈ Finset.univ.erase (openComponent (suffix q) (regular_suffix q hR).noTriple T.val),
      closedWeight (suffix q) (regular_suffix q hR)
        (corner_closedAuxiliary_suffix q hR hfree hAux) T D) =
    (∏ C ∈ Finset.univ.erase (openComponent q hR.noTriple
        (firstEdgeFreeSupportEquiv q hfree hR T).val),
      closedWeight q hR hAux (firstEdgeFreeSupportEquiv q hfree hR T) C) := by
  rw [Finset.prod_subtype (p := fun D => D ≠ openComponent (suffix q)
    (regular_suffix q hR).noTriple T.val)
    (Finset.univ.erase (openComponent (suffix q) (regular_suffix q hR).noTriple T.val))
    (fun D => by simp)]
  rw [Finset.prod_subtype (p := fun C => C ≠ openComponent q hR.noTriple
    (firstEdgeFreeSupportEquiv q hfree hR T).val)
    (Finset.univ.erase (openComponent q hR.noTriple
      (firstEdgeFreeSupportEquiv q hfree hR T).val)) (fun C => by simp)]
  apply Fintype.prod_equiv (cornerClosedComponentEquiv q hR hfree T)
  intro D
  exact corner_closedWeight_eq q hR hfree hRI hAux T D

end DirectGLSSW.ActiveArc.Split
