import SharpDaughterRotationInteger
import LocalSupportConjugacy
import ConfigurationEventLocality

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughterRotationLocality
open PermutationOrbits PrincipalTurning PolygonDrawingBridge SharpDaughter SharpDaughterRotation
open LocalCrossingTransport LocalSupportConjugacy Filter Topology
open scoped BigOperators

private theorem polygonEdgeVector_ne_zero {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (i : Fin n) :
    polygonEdgeVector q i ≠ 0 := by
  intro h
  apply cyclicTangent_ne_zero hq.size_ge_three q hq.g1 i
  apply Prod.ext
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

private theorem continuous_polygonEdgeVector {n : ℕ} (i : Fin n) :
    Continuous (fun r : Fin n → PlanarPoint ℝ => polygonEdgeVector r i) :=
  Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_apply (cyclicSuccessor i)).sub (continuous_apply i))

/-- The finite parent-carrier formula for one actual component is continuous
at the original G1/G2 parent. Short-turn geometry excludes the arg branch cut,
including for daughters with collinear nonadjacent vertices. -/
theorem continuousAt_fixed_event_turn_sum {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S) :
    ContinuousAt (fun r : Fin n → PlanarPoint ℝ =>
      ∑ a : Arc q hq S C,
        Complex.arg (polygonEdgeVector r (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector r (polygonEventEdge q a.val))) q := by
  have hterm (a : Arc q hq S C) : ContinuousAt
      (fun r : Fin n → PlanarPoint ℝ =>
        Complex.arg (polygonEdgeVector r (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector r (polygonEventEdge q a.val))) q := by
    have harg : Complex.arg
        (polygonEdgeVector q (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector q (polygonEventEdge q a.val)) < Real.pi := by
      have h := (actual_rounding_is_short_turn q hq S C hNA
        ((arcEquiv q hq S C).symm a)).2
      rw [actual_turn] at h
      simpa only [Equiv.apply_symm_apply, eventTurn] using h
    have hslit : polygonEdgeVector q (polygonEventEdge q (P q hq S a.val)) /
        polygonEdgeVector q (polygonEventEdge q a.val) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff_arg.mpr ⟨ne_of_lt harg,
        div_ne_zero (polygonEdgeVector_ne_zero q hq _) (polygonEdgeVector_ne_zero q hq _)⟩
    have hr : ContinuousAt (fun r : Fin n → PlanarPoint ℝ =>
        polygonEdgeVector r (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector r (polygonEventEdge q a.val)) q :=
      (continuous_polygonEdgeVector _).continuousAt.div
        (continuous_polygonEdgeVector _).continuousAt (polygonEdgeVector_ne_zero q hq _)
    exact ContinuousAt.comp
      (f := fun r : Fin n → PlanarPoint ℝ =>
        polygonEdgeVector r (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector r (polygonEventEdge q a.val))
      (x := q) (Complex.continuousAt_arg hslit) hr

  have hs (t : Finset (Arc q hq S C)) : ContinuousAt
      (fun r : Fin n → PlanarPoint ℝ => ∑ a ∈ t,
        Complex.arg (polygonEdgeVector r (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector r (polygonEventEdge q a.val))) q := by
    classical
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (continuousAt_const : ContinuousAt (fun _ : Fin n → PlanarPoint ℝ => (0 : ℝ)) q)
    | @insert a t ha ih =>
      simpa only [Finset.sum_insert ha] using (hterm a).add ih
  exact hs Finset.univ

/-- Exact reindexing of an actual nearby component total turn by the old
component's events and their unchanged carrier labels. No turn equality or
orientation assumption is required: the carrier vectors are evaluated at q'. -/
theorem totalTurn_eq_fixed_event_sum {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2; polygonEventMapEquiv E x < polygonEventMapEquiv E y))
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S) :
    totalTurn (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
      (smoothingComponentMapEquiv q q' hq hq' E hlabels horder S C)
      ((polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA)) =
      ∑ a : Arc q hq S C,
        Complex.arg (polygonEdgeVector q' (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector q' (polygonEventEdge q a.val)) := by
  let F := polygonEventMapEquiv E
  let T := S.map E.toEmbedding
  let CE := smoothingComponentMapEquiv q q' hq hq' E hlabels horder S
  let C' := CE C
  let hNA' := (polygonNonalternating_map_iff q q' hq hq' E hlabels horder S).mp hNA
  have hcomp (x : PolygonEvent q) :
      CE (componentOf (P q hq S) x) = componentOf (P q' hq' T) (F x) := rfl
  let A : Arc q hq S C ≃ Arc q' hq' T C' :=
    Equiv.subtypeEquiv F (fun x => by
      constructor
      · intro hx
        exact (hcomp x).symm.trans (congrArg CE hx)
      · intro hx
        apply CE.injective
        exact (hcomp x).trans hx)
  have hedge (x : PolygonEvent q) : polygonEventEdge q' (F x) = polygonEventEdge q x := by
    cases x with
    | inl i => rfl
    | inr v => exact crossingVisit_mapEquiv_edge_eq q q' E hlabels v
  have hP (x : PolygonEvent q) : F (P q hq S x) = P q' hq' T (F x) :=
    smoothingDartPermutation_map q q' hq hq' E hlabels horder S x
  calc
    totalTurn (sharpDaughterDiagram q' hq' T C' hNA') =
        ∑ b : Arc q' hq' T C', eventTurn q' hq' T b.val :=
      Fintype.sum_equiv (arcEquiv q' hq' T C') _ _ (actual_turn q' hq' T C' hNA')
    _ = ∑ a : Arc q hq S C,
        Complex.arg (polygonEdgeVector q' (polygonEventEdge q (P q hq S a.val)) /
          polygonEdgeVector q' (polygonEventEdge q a.val)) := by
      symm
      apply Fintype.sum_equiv A
      intro a
      change _ = Complex.arg (polygonEdgeVector q' (polygonEventEdge q' (P q' hq' T (F a.val))) /
        polygonEdgeVector q' (polygonEventEdge q' (F a.val)))
      rw [← hP, hedge, hedge]



end DirectGLSSW.HOMFLY.SharpDaughterRotationLocality
