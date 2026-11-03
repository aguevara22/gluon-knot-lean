import ActiveArcUnselectedClosedProduct
import ActiveArcChildAuxiliary

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW ActiveArc Primitive Cursor Split SingletonWords
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual weighted sum over independent compatible child and parent
supports factors into the child's separating smoothing sum and the parent's
GammaM. Original closed weights are converted termwise by the proved
compatible-component product identity. -/
theorem compatible_pair_weighted_sum_factorization
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR) :
    (∑ S : GeometricSmoothingWeights.SeparatingSupport
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux),
      ∑ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
        let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T);
        let U : Primitive.Support q hR := ⟨V.val,
          (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
            ⟨S.property,T.property⟩⟩;
        (-1 : ℚ)^(S.val.card + T.val.card) *
          (openCurrent (parent q c hcut) (regular_parent q hR c hcut) T *
            (polygonAmplitude
                (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
                  (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
                (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)) *
              ∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val),
                closedWeight q hR hAux U D))) =
      GeometricSmoothingWeights.separatingSmoothingSum
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
        (child_auxiliaryGenericity q hR c hc hcut hAux) *
      Primitive.GammaM (parent q c hcut) (regular_parent q hR c hcut)
        (parent_closedAuxiliary q hR c hc hcut hAux) := by
  classical
  let p := parent q c hcut
  let hp := regular_parent q hR c hcut
  let SType := GeometricSmoothingWeights.SeparatingSupport
    (child q hR c hc.1 hcut)
    (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
  let TType := Primitive.Support p hp
  let A := fun S : SType =>
    GeometricSmoothingWeights.componentAmplitudeProduct
      (child q hR c hc.1 hcut)
      (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S.val
      (child_auxiliaryGenericity q hR c hc hcut hAux) S.property
  let B := fun T : TType =>
    (-1 : ℚ)^T.val.card *
      (openCurrent p hp T *
        ∏ C ∈ Finset.univ.erase (openComponent p hp.noTriple T.val),
          closedWeight p hp (parent_closedAuxiliary q hR c hc hcut hAux) T C)
  have hdouble :
      (∑ S : SType,
        ∑ T : TType,
          let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T);
          let U : Primitive.Support q hR := ⟨V.val,
          (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr
            ⟨S.property,T.property⟩⟩;
          (-1 : ℚ)^(S.val.card + T.val.card) *
            (openCurrent p hp T *
              (polygonAmplitude
                  (DaughterFirstReturn.daughterVertex (child q hR c hc.1 hcut)
                    (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0))
                  (child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)) *
                ∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val),
                  closedWeight q hR hAux U D))) =
      (∑ S : SType, (-1 : ℚ)^S.val.card * A S) * (∑ T : TType, B T) := by
    calc
      _ = ∑ S : SType,
          ∑ T : TType, ((-1 : ℚ)^S.val.card * A S) * B T := by
        apply Finset.sum_congr rfl
        intro S hS
        apply Finset.sum_congr rfl
        intro T hT
        rw [pow_add]
        dsimp only
        have hfac := compatible_unselected_closedWeight_product hRI q hR c hc hcut hAux S T
        dsimp only at hfac
        rw [hfac]
        dsimp only [A, B, p, hp]
        ring
      _ = ∑ S : SType, (((-1 : ℚ)^S.val.card * A S) * ∑ T : TType, B T) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  dsimp only
  rw [hdouble]
  rfl


end DirectGLSSW.ActiveArc.CompatibleWords
