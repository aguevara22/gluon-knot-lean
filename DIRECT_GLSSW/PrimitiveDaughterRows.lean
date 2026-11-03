import DaughterEdgeCompletion
import DaughterNestedWeights
import PrimitiveSpectatorRows
import UncutDaughterTurns
import MixedEdgeDensityRecursion

set_option autoImplicit false
namespace DirectGLSSW.PrimitiveDaughterRows
open PrimitiveEdgeGrouping PrimitiveSpectatorRows DaughterUncutIncidence DaughterEdgeCompletion
  DaughterFirstReturn DaughterPairingLift DaughterNestedWeights GeometricSmoothingWeights
  PolygonNonalternation ChosenEdgeNormalization
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (e : Fin n) (U : OffEdgeSupport P hP e) (hAux : auxiliaryGenericity P hP)

theorem affectedFactor_eq_product_of_val (hRI : GLSSWRootIndependence)
    (T : EdgeCompletion P hP e U)
    (W : Finset (PolygonCrossing (edgeDaughter P hP e U)))
    (hW : polygonNonalternating (edgeDaughter P hP e U) (edgeDaughterG2 P hP e U) W)
    (hval : T.val = liftedSupport P hP U.val U.property.1 (Sum.inl e) (by trivial) W) :
    affectedFactor P hP e hAux U T =
      componentAmplitudeProduct (edgeDaughter P hP e U) (hAux U.val U.property.1 (Sum.inl e)) W
        (daughter_auxiliaryGenericity P hP U.val U.property.1 (Sum.inl e) (by trivial) hAux) hW := by
  rcases T with ⟨T,hOff,hNA⟩
  dsimp only at hval
  subst T
  exact (componentAmplitudeProduct_eq_affected P hP U.val U.property.1 (Sum.inl e)
    (by trivial) hRI hAux W hW).symm

theorem affectedFactor_edgeCompletionEquiv (hRI : GLSSWRootIndependence)
    (W : DaughterEdgeSupport P hP e U) :
    affectedFactor P hP e hAux U (edgeCompletionEquiv P hP e U W) =
      componentAmplitudeProduct (edgeDaughter P hP e U) (hAux U.val U.property.1 (Sum.inl e))
        (W.val.image Subtype.val)
        (daughter_auxiliaryGenericity P hP U.val U.property.1 (Sum.inl e) (by trivial) hAux) W.property :=
  affectedFactor_eq_product_of_val P hP e U hAux hRI _ _ W.property
    (edgeCompletionEquiv_val P hP e U W)

/-- The exact affected primitive row reindexed by actual daughter edge supports,
including the empty support and preserving the original support-cardinality sign. -/
theorem affectedRow_eq_daughterRow (hRI : GLSSWRootIndependence) :
    (∑ T : EdgeCompletion P hP e U, (-1 : ℚ)^T.val.card * affectedFactor P hP e hAux U T) =
    ∑ W : DaughterEdgeSupport P hP e U, (-1 : ℚ)^W.val.card *
      componentAmplitudeProduct (edgeDaughter P hP e U) (hAux U.val U.property.1 (Sum.inl e))
        (W.val.image Subtype.val)
        (daughter_auxiliaryGenericity P hP U.val U.property.1 (Sum.inl e) (by trivial) hAux) W.property := by
  symm
  apply Fintype.sum_equiv (edgeCompletionEquiv P hP e U)
  intro W
  rw [edgeCompletionEquiv_card,affectedFactor_edgeCompletionEquiv P hP e U hAux hRI]

theorem edgeDaughter_opposite_turns
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0) :
    planarDet (cyclicTangent (edgeDaughter P hP e U) (daughterChosenEdge P hP e U))
      (cyclicTangent (edgeDaughter P hP e U) (cyclicSuccessor (daughterChosenEdge P hP e U))) *
    planarDet (cyclicTangent (edgeDaughter P hP e U)
      (cyclicVertexIndex (daughterChosenEdge P hP e U)
        (Fintype.card (CornerCoord P hP.g2 U.val (Sum.inl e))-2)))
      (cyclicTangent (edgeDaughter P hP e U) (daughterChosenEdge P hP e U)) < 0 :=
  UncutDaughterTurns.uncut_endpoint_turn_product_neg P hP U.val (Sum.inl e) (by trivial)
    e U.property.2 (daughterChosenEdge P hP e U) (chosenEdge_start_event P hP e U) hturn

theorem edgeDaughter_mixed_recursion (hRI : GLSSWRootIndependence)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0) :
    polygonAmplitude (edgeDaughter P hP e U) (hAux U.val U.property.1 (Sum.inl e)) =
    chosenEdgeSmoothingSum (edgeDaughter P hP e U) (hAux U.val U.property.1 (Sum.inl e))
      (daughterChosenEdge P hP e U)
      (daughter_auxiliaryGenericity P hP U.val U.property.1 (Sum.inl e) (by trivial) hAux) :=
  MixedEdgeDensityRecursion.mixed_edge_recursion_auxiliary hRI _ _ _
    (edgeDaughter_opposite_turns P hP e U hturn) _






end
end DirectGLSSW.PrimitiveDaughterRows
