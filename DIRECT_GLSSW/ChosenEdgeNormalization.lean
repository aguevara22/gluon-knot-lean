import DirectGLSSW.EdgeNormalizationSmoothing
import DirectGLSSW.MixedEdgeSupportOrder

set_option autoImplicit false
open scoped BigOperators
namespace DirectGLSSW.ChosenEdgeNormalization
open EdgeAffineNormalization PolygonNonalternation GeometricSmoothingWeights
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Source mixed-edge formula: nonempty separating supports on any chosen edge.
No coordinate-choice premise belongs to this finite indexing type. -/
def ChosenEdgeSeparatingSupport (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) :=
  {T : Finset (DirectGLSSW.EdgeChord q e) // T.Nonempty ∧
    polygonNonalternating q hq.g2 (T.image Subtype.val)}

instance chosenEdgeSeparatingSupportFintype (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin n) :
    Fintype (ChosenEdgeSeparatingSupport q hq e) := by
  unfold ChosenEdgeSeparatingSupport
  infer_instance

/-- Exact right side of the source mixed-edge formula, with actual component amplitudes. -/
def chosenEdgeSmoothingSum (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hAux : auxiliaryGenericity q hq) : ℚ :=
  ∑ T : ChosenEdgeSeparatingSupport q hq e,
    (-1 : ℚ)^(T.val.card+1) *
      componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property.2

theorem chosenEdgeSeparatingSupport_eq_horizontal
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) :
    ChosenEdgeSeparatingSupport q hq e =
      MixedEdgeSupportOrder.EdgeSeparatingSupport q hq.g2 e hflat hleft := rfl

/-- Chosen-edge incidence contributes no duplicate crossings to the source support. -/
theorem chosenEdgeSupport_image_card
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (T : ChosenEdgeSeparatingSupport q hq e) :
    (T.val.image Subtype.val).card = T.val.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

/-- Agreement holds for any Fintype instance used for the existing horizontal subtype. -/
theorem chosenEdgeSmoothingSum_eq_horizontal
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    [Fintype (MixedEdgeSupportOrder.EdgeSeparatingSupport q hq.g2 e hflat hleft)]
    (hAux : auxiliaryGenericity q hq) :
    chosenEdgeSmoothingSum q hq e hAux =
      ∑ T : MixedEdgeSupportOrder.EdgeSeparatingSupport q hq.g2 e hflat hleft,
        (-1 : ℚ)^(T.val.card+1) *
          componentAmplitudeProduct q hq (T.val.image Subtype.val) hAux T.property.2 := by
  unfold chosenEdgeSmoothingSum
  apply Finset.sum_congr
  · ext T
    simp
  · intro T _
    rfl

variable (u v : PlanarPoint ℝ) (huv : u ≠ v) (q : Fin n → PlanarPoint ℝ)

/-- Affine normalization restricts to the actual crossings incident to the same edge label. -/
def edgeChordEquiv (e : Fin n) :
    DirectGLSSW.EdgeChord q e ≃ DirectGLSSW.EdgeChord (fun i => normalize u v (q i)) e where
  toFun c := ⟨crossingEquiv u v huv q c.val,c.property⟩
  invFun c := ⟨(crossingEquiv u v huv q).symm c.val,c.property⟩
  left_inv c := Subtype.ext ((crossingEquiv u v huv q).symm_apply_apply c.val)
  right_inv c := Subtype.ext ((crossingEquiv u v huv q).apply_symm_apply c.val)

theorem edgeChordEquiv_val (e : Fin n) (c : DirectGLSSW.EdgeChord q e) :
    (edgeChordEquiv u v huv q e c).val = crossingEquiv u v huv q c.val := rfl

/-- Forgetting the chosen-edge incidence commutes with transport of finite supports. -/
theorem edgeChordSupport_image (e : Fin n) (T : Finset (DirectGLSSW.EdgeChord q e)) :
    (T.map (edgeChordEquiv u v huv q e).toEmbedding).image Subtype.val =
      normalizedSupport u v huv q (T.image Subtype.val) := by
  simp only [normalizedSupport,Finset.map_eq_image,Finset.image_image]
  rfl

variable (hq : CyclicGeneric q)

theorem edgeChordSupport_nonalternating_iff (e : Fin n)
    (T : Finset (DirectGLSSW.EdgeChord q e)) :
    polygonNonalternating q hq.g2 (T.image Subtype.val) ↔
      polygonNonalternating (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq).g2
        ((T.map (edgeChordEquiv u v huv q e).toEmbedding).image Subtype.val) := by
  rw [edgeChordSupport_image]
  exact normalization_nonalternating_iff u v huv q hq (T.image Subtype.val)

/-- The precise nonempty separating-support bijection; no ordered-chain representation is used. -/
def chosenEdgeSupportEquiv (e : Fin n) :
    ChosenEdgeSeparatingSupport q hq e ≃
      ChosenEdgeSeparatingSupport (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq) e :=
  Equiv.subtypeEquiv (edgeChordEquiv u v huv q e).finsetCongr (fun T =>
    and_congr Finset.map_nonempty.symm (edgeChordSupport_nonalternating_iff u v huv q hq e T))

theorem chosenEdgeSupportEquiv_card (e : Fin n)
    (T : ChosenEdgeSeparatingSupport q hq e) :
    (chosenEdgeSupportEquiv u v huv q hq e T).val.card = T.val.card :=
  Finset.card_map _

theorem chosenEdgeSupportEquiv_image (e : Fin n)
    (T : ChosenEdgeSeparatingSupport q hq e) :
    (chosenEdgeSupportEquiv u v huv q hq e T).val.image Subtype.val =
      normalizedSupport u v huv q (T.val.image Subtype.val) :=
  edgeChordSupport_image u v huv q e T.val

/-- The literal source sum is invariant under the positive affine coordinates.
Only original daughter genericity is transported; it is not strengthened. -/
theorem normalization_chosenEdgeSmoothingSum (e : Fin n)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    chosenEdgeSmoothingSum q hq e hAux =
      chosenEdgeSmoothingSum (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq) e
        (normalization_auxiliaryGenericity u v huv q hq hAux) := by
  unfold chosenEdgeSmoothingSum
  apply Fintype.sum_equiv (chosenEdgeSupportEquiv u v huv q hq e)
  intro T
  rw [chosenEdgeSupportEquiv_card]
  apply congrArg (fun x : ℚ => (-1 : ℚ)^(T.val.card+1)*x)
  have himage := chosenEdgeSupportEquiv_image u v huv q hq e T
  simpa only [← himage] using
    normalization_componentAmplitudeProduct u v huv q hq hRI hAux
      (T.val.image Subtype.val) T.property.2

/-- The normalization at the chosen endpoints preserves its exact support sum. -/
theorem normalizedPolygon_chosenEdgeSmoothingSum
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    chosenEdgeSmoothingSum q hq e hAux =
      chosenEdgeSmoothingSum (normalizedPolygon q e) (normalizedPolygon_generic q hq e) e
        (normalization_auxiliaryGenericity (q (cyclicSuccessor e)) (q e)
          (chosen_endpoints_ne q hq e) q hq hAux) :=
  normalization_chosenEdgeSmoothingSum (q (cyclicSuccessor e)) (q e)
    (chosen_endpoints_ne q hq e) q hq e hRI hAux

/-- Any determinant of two actual directed tangents scales by the positive determinant. -/
theorem normalize_tangent_det (u v : PlanarPoint ℝ) (q : Fin n → PlanarPoint ℝ)
    (a b : Fin n) :
    planarDet (cyclicTangent (fun i => normalize u v (q i)) a)
      (cyclicTangent (fun i => normalize u v (q i)) b) =
      normSq u v * planarDet (cyclicTangent q a) (cyclicTangent q b) := by
  dsimp [cyclicTangent,normalize,normSq,planarDet]
  ring

/-- Exact source endpoint-turn product for the closing edge e scales by normSq squared. -/
theorem normalize_endpoint_turn_product (u v : PlanarPoint ℝ)
    (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    planarDet (cyclicTangent (fun i => normalize u v (q i)) e)
        (cyclicTangent (fun i => normalize u v (q i)) (cyclicSuccessor e)) *
      planarDet (cyclicTangent (fun i => normalize u v (q i)) (cyclicVertexIndex e (n-2)))
        (cyclicTangent (fun i => normalize u v (q i)) e) =
    normSq u v ^ 2 * (planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e)) := by
  rw [normalize_tangent_det,normalize_tangent_det]
  ring

theorem normalize_endpoint_turn_product_neg_iff (u v : PlanarPoint ℝ) (huv : u ≠ v)
    (q : Fin n → PlanarPoint ℝ) (e : Fin n) :
    planarDet (cyclicTangent (fun i => normalize u v (q i)) e)
        (cyclicTangent (fun i => normalize u v (q i)) (cyclicSuccessor e)) *
      planarDet (cyclicTangent (fun i => normalize u v (q i)) (cyclicVertexIndex e (n-2)))
        (cyclicTangent (fun i => normalize u v (q i)) e) < 0 ↔
    planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0 := by
  rw [normalize_endpoint_turn_product]
  have hD := sq_pos_of_pos (normSq_pos u v huv)
  constructor
  · intro h
    by_contra hx
    have hn := mul_nonneg hD.le (le_of_not_gt hx)
    linarith
  · exact fun h => mul_neg_of_pos_of_neg hD h

theorem normalizedPolygon_endpoint_turn_product_neg_iff
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n) :
    planarDet (cyclicTangent (normalizedPolygon q e) e)
        (cyclicTangent (normalizedPolygon q e) (cyclicSuccessor e)) *
      planarDet (cyclicTangent (normalizedPolygon q e) (cyclicVertexIndex e (n-2)))
        (cyclicTangent (normalizedPolygon q e) e) < 0 ↔
    planarDet (cyclicTangent q e) (cyclicTangent q (cyclicSuccessor e)) *
      planarDet (cyclicTangent q (cyclicVertexIndex e (n-2))) (cyclicTangent q e) < 0 :=
  normalize_endpoint_turn_product_neg_iff (q (cyclicSuccessor e)) (q e)
    (chosen_endpoints_ne q hq e) q e


/-- Coordinate removal for the mixed-edge equation, separate from proving that equation. -/
theorem normalizedPolygon_mixed_edge_iff
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (e : Fin n)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    (polygonAmplitude q hq = chosenEdgeSmoothingSum q hq e hAux) ↔
    (polygonAmplitude (normalizedPolygon q e) (normalizedPolygon_generic q hq e) =
      chosenEdgeSmoothingSum (normalizedPolygon q e) (normalizedPolygon_generic q hq e) e
        (normalization_auxiliaryGenericity (q (cyclicSuccessor e)) (q e)
          (chosen_endpoints_ne q hq e) q hq hAux)) := by
  rw [← normalizedPolygon_amplitude q hq e,
    ← normalizedPolygon_chosenEdgeSmoothingSum q hq e hRI hAux]


end
end DirectGLSSW.ChosenEdgeNormalization






















