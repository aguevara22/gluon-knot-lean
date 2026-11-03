import PolygonRebaseAuxiliary
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace DirectGLSSW.PolygonRebase
open DaughterFirstReturn PermutationOrbits GeometricSmoothingWeights DaughterRootAmplitude
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

theorem smoothingDart_relabel (S' : Finset (PolygonCrossing (q ∘ ρ)))
    (x : PolygonEvent (q ∘ ρ)) :
    eventEquiv q ρ hρ (smoothingDartPermutation (q ∘ ρ)
      (cyclicGeneric_relabel q ρ hρ hq).g2 S' x) =
      smoothingDartPermutation q hq.g2 (S'.map (crossingEquiv q ρ hρ).toEmbedding)
        (eventEquiv q ρ hρ x) := by
  rw [smoothingDartPermutation_apply, smoothingDartPermutation_apply]
  rw [← eventEquiv_successor q hq ρ hρ x]
  exact (eventEquiv_pairing_relabel q hq ρ hρ S'
    (polygonEventSuccessor (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g2 x)).symm

def smoothingComponentEquiv (S' : Finset (PolygonCrossing (q ∘ ρ))) :
    Component (smoothingDartPermutation (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq).g2 S') ≃
      Component (smoothingDartPermutation q hq.g2 (S'.map (crossingEquiv q ρ hρ).toEmbedding)) :=
  componentEquivOfIntertwining (eventEquiv q ρ hρ) _ _ (smoothingDart_relabel q hq ρ hρ S')

def separatingSupportEquiv :
    SeparatingSupport (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq) ≃ SeparatingSupport q hq where
  toFun S := ⟨(crossingEquiv q ρ hρ).finsetCongr S.val,
    (polygonNonalternating_relabel q hq ρ hρ S.val).mp S.property⟩
  invFun T := ⟨(crossingEquiv q ρ hρ).finsetCongr.symm T.val,
    (polygonNonalternating_relabel q hq ρ hρ _).mpr (by
      change PolygonNonalternation.polygonNonalternating q hq.g2
        ((crossingEquiv q ρ hρ).finsetCongr ((crossingEquiv q ρ hρ).finsetCongr.symm T.val))
      simpa only [Equiv.apply_symm_apply] using T.property)⟩
  left_inv S := Subtype.ext ((crossingEquiv q ρ hρ).finsetCongr.symm_apply_apply S.val)
  right_inv T := Subtype.ext ((crossingEquiv q ρ hρ).finsetCongr.apply_symm_apply T.val)

theorem componentAmplitude_relabel (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity q hq)
    (S' : Finset (PolygonCrossing (q ∘ ρ)))
    (hS' : PolygonNonalternation.polygonNonalternating (q ∘ ρ)
      (cyclicGeneric_relabel q ρ hρ hq).g2 S')
    (C : Component (smoothingDartPermutation (q ∘ ρ)
      (cyclicGeneric_relabel q ρ hρ hq).g2 S')) :
    componentAmplitude (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq) S'
      (auxiliaryGenericity_relabel q hq ρ hρ hAux) hS' C =
    componentAmplitude q hq (S'.map (crossingEquiv q ρ hρ).toEmbedding) hAux
      ((polygonNonalternating_relabel q hq ρ hρ S').mp hS')
      (smoothingComponentEquiv q hq ρ hρ S' C) := by
  let hQ := cyclicGeneric_relabel q ρ hρ hq
  let S := S'.map (crossingEquiv q ρ hρ).toEmbedding
  let ra := componentRoot (q ∘ ρ) hQ S' C
  let rb := componentRoot q hq S (smoothingComponentEquiv q hq ρ hρ S' C)
  have hcomp : componentOf (smoothingDartPermutation q hq.g2 S)
      (eventEquiv q ρ hρ ra) = smoothingComponentEquiv q hq ρ hρ S' C := by
    change smoothingComponentEquiv q hq ρ hρ S'
      (componentOf (smoothingDartPermutation (q ∘ ρ) hQ.g2 S') ra) = _
    rw [componentRoot_sameComponent]
  have hcycle : (smoothingDartPermutation q hq.g2 S).SameCycle
      (eventEquiv q ρ hρ ra) rb := by
    apply (componentOf_eq_iff _ _ _).mp
    exact hcomp.trans (componentRoot_sameComponent q hq S _).symm
  have hrot : List.ofFn (componentPolygon (q ∘ ρ) hQ S' C) ~r
      List.ofFn (componentPolygon q hq S (smoothingComponentEquiv q hq ρ hρ S' C)) := by
    change daughterPointList (q ∘ ρ) hQ.g2 S' ra ~r daughterPointList q hq.g2 S rb
    rw [← daughterPointList_relabel q hq ρ hρ S' ra]
    exact DaughterRootRotation.daughterPointList_isRotated_of_sameCycle q hq.g2 S _ _ hcycle
  unfold componentAmplitude
  exact polygonAmplitude_ofFn_isRotated hRI
    ((auxiliaryGenericity_relabel q hq ρ hρ hAux) S' hS' ra) hrot

theorem componentAmplitudeProduct_relabel (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity q hq)
    (S' : SeparatingSupport (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)) :
    componentAmplitudeProduct (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq) S'.val
      (auxiliaryGenericity_relabel q hq ρ hρ hAux) S'.property =
    componentAmplitudeProduct q hq (separatingSupportEquiv q hq ρ hρ S').val hAux
      (separatingSupportEquiv q hq ρ hρ S').property := by
  unfold componentAmplitudeProduct
  exact Fintype.prod_equiv (smoothingComponentEquiv q hq ρ hρ S'.val) _ _
    (fun C => componentAmplitude_relabel q hq ρ hρ hRI hAux S'.val S'.property C)

theorem separatingSmoothingSum_relabel (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity q hq) :
    separatingSmoothingSum (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)
      (auxiliaryGenericity_relabel q hq ρ hρ hAux) = separatingSmoothingSum q hq hAux := by
  unfold separatingSmoothingSum
  apply Fintype.sum_equiv (separatingSupportEquiv q hq ρ hρ)
  intro S
  rw [componentAmplitudeProduct_relabel q hq ρ hρ hRI hAux S]
  have hcard : (separatingSupportEquiv q hq ρ hρ S).val.card = S.val.card :=
    Finset.card_map _
  rw [hcard]

end DirectGLSSW.PolygonRebase
