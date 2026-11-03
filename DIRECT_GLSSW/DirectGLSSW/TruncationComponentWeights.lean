import DirectGLSSW.TruncationDaughterGenericity
import DirectGLSSW.TruncationWeightedSum

set_option autoImplicit false

namespace DirectGLSSW.TruncationComponentWeights

open DaughterFirstReturn TruncationDirection TruncationEdgeLift TruncationEventOrder
open TruncationDaughterEvents PermutationOrbits GeometricSmoothingWeights PolygonNonalternation
attribute [local instance] Classical.propDecidable

theorem componentAmplitude_eq_at_root
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (hAux : auxiliaryGenericity q hq)
    (hS : polygonNonalternating q hq.g2 S)
    (c : Component (smoothingDartPermutation q hq.g2 S))
    (x : PolygonEvent q)
    (hx : componentOf (smoothingDartPermutation q hq.g2 S) x = c) :
    componentAmplitude q hq S hAux hS c =
      polygonAmplitude (daughterVertex q hq.g2 S x) (hAux S hS x)
 := by
  have hxy : (smoothingDartPermutation q hq.g2 S).SameCycle (componentRoot q hq S c) x :=
    (componentOf_eq_iff _ _ _).mp ((componentRoot_sameComponent q hq S c).trans hx.symm)
  exact DaughterRootAmplitude.daughterPolygonAmplitude_eq_of_sameCycle
    hRI q hq.g2 S (componentRoot q hq S c) x hxy (hAux S hS (componentRoot q hq S c))

theorem componentAmplitude_truncation
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (hAux : auxiliaryGenericity q hq)
    (hAuxQ : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ)
    (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S)
    (hSQ : polygonNonalternating (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding))
    (hAffected : ∃ hB : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
      hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
      polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
        hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hB =
      -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a)) (hAux S hS (Sum.inl a)))
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    componentAmplitude (truncateCyclicCorner q a p scale ε) hQ (S.map E.toEmbedding) hAuxQ hSQ
      (truncationDartComponentEquiv hq.size_ge_three q a p hp scale ε hε hε1 hscale hscale1
        hq hQ E hleft hright hpoint S c) =
      if c = componentOf (smoothingDartPermutation q hq.g2 S) (Sum.inl a)
      then -componentAmplitude q hq S hAux hS c
      else componentAmplitude q hq S hAux hS c
 := by
  classical
  let Q := truncateCyclicCorner q a p scale ε
  let F := truncationDartComponentEquiv hq.size_ge_three q a p hp scale ε
    hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  by_cases hc : c = componentOf (smoothingDartPermutation q hq.g2 S) (Sum.inl a)
  · subst c
    rw [if_pos rfl]
    rw [componentAmplitude_eq_at_root hRI Q hQ (S.map E.toEmbedding) hAuxQ hSQ
      _ (Sum.inl a.castSucc)
      (truncationDartComponentEquiv_extra hq.size_ge_three q a p hp scale ε
        hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S).symm]
    rw [componentAmplitude_eq_at_root hRI q hq S hAux hS _ (Sum.inl a) rfl]
    exact hAffected.choose_spec
  · rw [if_neg hc]
    let x := componentRoot q hq S c
    have hxc : componentOf (smoothingDartPermutation q hq.g2 S) x = c :=
      componentRoot_sameComponent q hq S c
    have hx : ¬ (smoothingDartPermutation q hq.g2 S).SameCycle x (Sum.inl a) := by
      intro h
      apply hc
      exact hxc.symm.trans ((componentOf_eq_iff _ _ _).mpr h)
    obtain ⟨hFx, hamp⟩ := TruncationDaughterAmplitude.unaffected_daughter_truncation_amplitude
      q hq a p hp scale ε hε hε1 hscale hscale1 hQ E hleft hright hpoint S x hx (hAux S hS x)
    have hcomp : componentOf (smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding))
        (truncationPolygonEventMap q a p scale ε E x) = F c := by
      calc
        _ = F (componentOf (smoothingDartPermutation q hq.g2 S) x) :=
          (truncationDartComponentEquiv_componentOf hq.size_ge_three q a p hp scale ε
            hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S x).symm
        _ = F c := congrArg F hxc
    rw [componentAmplitude_eq_at_root hRI Q hQ (S.map E.toEmbedding) hAuxQ hSQ
      _ (truncationPolygonEventMap q a p scale ε E x) hcomp]
    rw [componentAmplitude_eq_at_root hRI q hq S hAux hS c x hxc]
    exact hamp

theorem componentAmplitudeProduct_truncation
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (hAux : auxiliaryGenericity q hq)
    (hAuxQ : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ)
    (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S)
    (hSQ : polygonNonalternating (truncateCyclicCorner q a p scale ε) hQ.g2 (S.map E.toEmbedding))
    (hAffected : ∃ hB : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
      hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)),
      polygonAmplitude (daughterVertex (truncateCyclicCorner q a p scale ε)
        hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc)) hB =
      -polygonAmplitude (daughterVertex q hq.g2 S (Sum.inl a)) (hAux S hS (Sum.inl a)))
    : componentAmplitudeProduct (truncateCyclicCorner q a p scale ε) hQ
        (S.map E.toEmbedding) hAuxQ hSQ =
      -componentAmplitudeProduct q hq S hAux hS
 := by
  classical
  exact TruncationWeightedSum.prod_equiv_single_sign_flip
    (truncationDartComponentEquiv hq.size_ge_three q a p hp scale ε
      hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S)
    (componentOf (smoothingDartPermutation q hq.g2 S) (Sum.inl a))
    (componentAmplitude q hq S hAux hS)
    (componentAmplitude (truncateCyclicCorner q a p scale ε) hQ (S.map E.toEmbedding) hAuxQ hSQ)
    (componentAmplitude_truncation hRI q hq a p hp scale ε hε hε1 hscale hscale1
      hQ E hleft hright hpoint hAux hAuxQ S hS hSQ hAffected)

end DirectGLSSW.TruncationComponentWeights
