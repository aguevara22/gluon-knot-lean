import PolygonRebaseSmoothing
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
open GeometricSmoothingWeights
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

include hρ in
/-- The literal original-corner left-turn count is invariant under cyclic rebasing. -/
theorem leftCount_relabel :
    (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent (q ∘ ρ) i)
        (cyclicTangent (q ∘ ρ) (cyclicSuccessor i)))).card =
    (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent q i)
        (cyclicTangent q (cyclicSuccessor i)))).card := by
  let P : Fin n → Prop := fun i => 0 < planarDet (cyclicTangent q i)
    (cyclicTangent q (cyclicSuccessor i))
  let Q : Fin n → Prop := fun i => 0 < planarDet (cyclicTangent (q ∘ ρ) i)
    (cyclicTangent (q ∘ ρ) (cyclicSuccessor i))
  have hp (i : Fin n) : Q i ↔ P (ρ i) := by
    dsimp [P,Q]
    rw [tangent_relabel q ρ hρ,tangent_relabel q ρ hρ,hρ]
  let E : {i : Fin n // Q i} ≃ {i : Fin n // P i} :=
    { toFun := fun i => ⟨ρ i.val,(hp i.val).mp i.property⟩
      invFun := fun i => ⟨ρ.symm i.val,(hp (ρ.symm i.val)).mpr (by simpa using i.property)⟩
      left_inv := fun i => Subtype.ext (ρ.symm_apply_apply i.val)
      right_inv := fun i => Subtype.ext (ρ.apply_symm_apply i.val) }
  simpa only [Fintype.card_subtype] using Fintype.card_congr E

/-- Source normalization by the literal count of left corners; no duplicate
normalization definition or external package import is needed. -/
theorem normalizedPrimitive_relabel (hq : CyclicGeneric q)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    (-1 : ℚ) ^ (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent (q ∘ ρ) i)
        (cyclicTangent (q ∘ ρ) (cyclicSuccessor i)))).card *
      separatingSmoothingSum (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)
        (auxiliaryGenericity_relabel q hq ρ hρ hAux) =
    (-1 : ℚ) ^ (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent q i)
        (cyclicTangent q (cyclicSuccessor i)))).card *
      separatingSmoothingSum q hq hAux := by
  rw [leftCount_relabel q ρ hρ,separatingSmoothingSum_relabel q hq ρ hρ hRI hAux]

/-- Uniform-left current restart uses the same literal vertex count n on both
sides, so its (-1)^n normalization is preserved directly. -/
theorem vertexParity_normalizedPrimitive_relabel (hq : CyclicGeneric q)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    (-1 : ℚ)^n * separatingSmoothingSum (q ∘ ρ)
      (cyclicGeneric_relabel q ρ hρ hq) (auxiliaryGenericity_relabel q hq ρ hρ hAux) =
    (-1 : ℚ)^n * separatingSmoothingSum q hq hAux := by
  rw [separatingSmoothingSum_relabel q hq ρ hρ hRI hAux]

end DirectGLSSW.PolygonRebase
