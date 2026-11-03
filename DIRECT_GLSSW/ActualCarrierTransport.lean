import LocalDaughterTransport
import CarrierFamilyDensity
import LocalCarrierContinuity
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActualCarrierTransport
open DaughterFirstReturn AuxiliaryCarrierChart LocalDaughterTransport LocalCrossingTransport
open GeometricSmoothingWeights

variable {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
  (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
  (E : PolygonCrossing q ≃ PolygonCrossing q')
  (hlabels : ∀ c, (E c).val = c.val)
  (S : Finset (PolygonCrossing q))
  (hdart : ∀ x, polygonEventMapEquiv E (smoothingDartPermutation q hq.g2 S x) =
    smoothingDartPermutation q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E x))

include hlabels in
 theorem daughterCarrier_cast_eq (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S root))) :
    daughterCarrier q' hq'.g2 (S.map E.toEmbedding) (polygonEventMapEquiv E root)
      (Fin.cast (daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root) i) =
    daughterCarrier q hq.g2 S root i := by
  have he : ∀ x : PolygonEvent q,
      polygonEventEdge q' (polygonEventMapEquiv E x) = polygonEventEdge q x := by
    intro x
    cases x with
    | inl e => rfl
    | inr v => exact crossingVisit_mapEquiv_edge_eq q q' E hlabels v
  have hw := congrArg (List.map (polygonEventEdge q'))
    (daughterEventWord_map q q' hq.g2 hq'.g2 E S hdart root)
  have hl : List.ofFn (daughterCarrier q' hq'.g2 (S.map E.toEmbedding)
      (polygonEventMapEquiv E root)) = List.ofFn (daughterCarrier q hq.g2 S root) := by
    simpa only [daughterEventWord, List.map_ofFn, List.map_map, Function.comp_def,
      he, daughterCarrier] using hw
  exact ofFn_eq_cast _ _ (daughterCard_eq q q' hq.g2 hq'.g2 E S hdart root) hl i

 theorem lineValue_affine (L : CarrierLine) (a b : PlanarPoint ℝ) (t : ℝ)
    (ha : lineValue L a = 0) (hb : lineValue L b = 0) :
    lineValue L (affinePoint a b t) = 0 := by
  have hid : lineValue L (affinePoint a b t) =
      (1-t)*lineValue L a + t*lineValue L b := by
    simp only [lineValue, planarDet, affinePoint]
    ring
  rw [hid, ha, hb]
  ring

 theorem reconstruct_incidence (L : Fin n → CarrierLine)
    (hden : ∀ e, lineDenominator (L ((cyclicSuccessorPerm n)⁻¹ e)) (L e) ≠ 0)
    (e : Fin n) :
    lineValue (L e) (reconstructPolygon L e) = 0 ∧
      lineValue (L e) (reconstructPolygon L (cyclicSuccessor e)) = 0 := by
  constructor
  · exact lineValue_intersection_right _ _ (hden e)
  · have hp : (cyclicSuccessorPerm n)⁻¹ (cyclicSuccessor e) = e :=
      (cyclicSuccessorPerm n).symm_apply_apply e
    unfold reconstructPolygon
    rw [hp]
    apply lineValue_intersection_left
    simpa only [hp] using hden (cyclicSuccessor e)

 theorem daughter_intersection_of_incidence
    (L : Fin n → CarrierLine)
    (hinc : ∀ e, lineValue (L e) (q' e) = 0 ∧
      lineValue (L e) (q' (cyclicSuccessor e)) = 0)
    (root : PolygonEvent q') (hroot : retainedCorner q' (S.map E.toEmbedding) root)
    (i : Fin (Fintype.card (CornerCoord q' hq'.g2 (S.map E.toEmbedding) root)))
    (hden : lineDenominator
      (L (daughterCarrier q' hq'.g2 (S.map E.toEmbedding) root
        ((cyclicSuccessorPerm _)⁻¹ i)))
      (L (daughterCarrier q' hq'.g2 (S.map E.toEmbedding) root i)) ≠ 0) :
    daughterVertex q' hq'.g2 (S.map E.toEmbedding) root i =
      lineIntersection
      (L (daughterCarrier q' hq'.g2 (S.map E.toEmbedding) root
        ((cyclicSuccessorPerm _)⁻¹ i)))
      (L (daughterCarrier q' hq'.g2 (S.map E.toEmbedding) root i)) := by
  let p := (cyclicSuccessorPerm _)⁻¹ i
  have hp : cyclicSuccessor p = i := (cyclicSuccessorPerm _).apply_symm_apply i
  obtain ⟨s,t,_,_,_,hs,ht⟩ := DaughterClosedContainment.daughterSide_endpoint_parameters
    q' hq'.g2 (S.map E.toEmbedding) hq'.size_ge_three root hroot i
  obtain ⟨u,v,_,_,_,hu,hv⟩ := DaughterClosedContainment.daughterSide_endpoint_parameters
    q' hq'.g2 (S.map E.toEmbedding) hq'.size_ge_three root hroot p
  rw [hp] at hv
  apply lineIntersection_unique _ _ _ hden
  · rw [hv]
    exact lineValue_affine _ _ _ _ (hinc _).1 (hinc _).2
  · rw [hs]
    exact lineValue_affine _ _ _ _ (hinc _).1 (hinc _).2

 theorem auxiliaryGenericity_of_retained
    (h : ∀ (S : Finset (PolygonCrossing q)),
      PolygonNonalternation.polygonNonalternating q hq.g2 S →
      ∀ root, retainedCorner q S root → CyclicGeneric (daughterVertex q hq.g2 S root)) :
    auxiliaryGenericity q hq := by
  intro S hS root
  obtain ⟨r, hr, hret⟩ := everyDartOrbit_hasCorner q hq.g2 S hq.size_ge_three root
  exact DaughterRootAmplitude.daughterCyclicGeneric_of_sameCycle q hq.g2 S r root
    hr.symm (h S hS r hret)





end DirectGLSSW.ActualCarrierTransport
