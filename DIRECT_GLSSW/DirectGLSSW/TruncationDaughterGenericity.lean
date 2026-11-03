import DirectGLSSW.TruncationDaughterAmplitude
import DirectGLSSW.DaughterRootAmplitude
import DirectGLSSW.GeometricSmoothingWeights

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DirectGLSSW.TruncationDaughterGenericity

open DaughterFirstReturn TruncationDirection TruncationEdgeLift TruncationEventOrder
open TruncationDaughterEvents PermutationOrbits GeometricSmoothingWeights PolygonNonalternation

theorem all_daughter_genericity_transport {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) = crossingPoint q c)
    (S : Finset (PolygonCrossing q))
    (hOld : ∀ x : PolygonEvent q, CyclicGeneric (daughterVertex q hq.g2 S x))
    (hB : CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
      hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc))) :
    ∀ y : PolygonEvent (truncateCyclicCorner q a p scale ε),
      CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
        hQ.g2 (S.map E.toEmbedding) y)
 := by
  classical
  let Q := truncateCyclicCorner q a p scale ε
  let d := smoothingDartPermutation q hq.g2 S
  let dQ := smoothingDartPermutation Q hQ.g2 (S.map E.toEmbedding)
  let F := truncationDartComponentEquiv hq.size_ge_three q a p hp scale ε
    hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hmap := truncationDartComponentEquiv_componentOf hq.size_ge_three q a p hp scale ε
    hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  have hextra := truncationDartComponentEquiv_extra hq.size_ge_three q a p hp scale ε
    hε hε1 hscale hscale1 hq hQ E hleft hright hpoint S
  intro y
  let c : Component d := F.symm (componentOf dQ y)
  let x : PolygonEvent q := Quotient.out c
  have hxc : componentOf d x = c := Quotient.out_eq c
  by_cases hc : c = componentOf d (Sum.inl a)
  · have hBy : componentOf dQ (Sum.inl a.castSucc) = componentOf dQ y := by
      calc
        componentOf dQ (Sum.inl a.castSucc) = F (componentOf d (Sum.inl a)) := hextra.symm
        _ = F c := congrArg F hc.symm
        _ = componentOf dQ y := F.apply_symm_apply _
    exact DaughterRootAmplitude.daughterCyclicGeneric_of_sameCycle Q hQ.g2
      (S.map E.toEmbedding) (Sum.inl a.castSucc) y
      ((componentOf_eq_iff dQ _ _).mp hBy) hB
  · have hx : ¬ d.SameCycle x (Sum.inl a) := by
      intro h
      apply hc
      exact hxc.symm.trans ((componentOf_eq_iff d _ _).mpr h)
    obtain ⟨hFx, _⟩ := TruncationDaughterAmplitude.unaffected_daughter_truncation_amplitude
      q hq a p hp scale ε hε hε1 hscale hscale1 hQ E hleft hright hpoint S x hx (hOld x)
    have hFxy : componentOf dQ (truncationPolygonEventMap q a p scale ε E x) =
        componentOf dQ y := by
      calc
        componentOf dQ (truncationPolygonEventMap q a p scale ε E x) = F (componentOf d x) := (hmap x).symm
        _ = F c := congrArg F hxc
        _ = componentOf dQ y := F.apply_symm_apply _
    exact DaughterRootAmplitude.daughterCyclicGeneric_of_sameCycle Q hQ.g2
      (S.map E.toEmbedding) (truncationPolygonEventMap q a p scale ε E x) y
      ((componentOf_eq_iff dQ _ _).mp hFxy) hFx

theorem auxiliaryGenericity_transport {n : ℕ}
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
    (hB : ∀ (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S),
      CyclicGeneric (daughterVertex (truncateCyclicCorner q a p scale ε)
        hQ.g2 (S.map E.toEmbedding) (Sum.inl a.castSucc))) :
    auxiliaryGenericity (truncateCyclicCorner q a p scale ε) hQ
 := by
  classical
  have hsep := TruncationSmoothingComponents.truncation_polygonNonalternating_iff
    hq.size_ge_three q a p hp scale ε hε hε1 hscale hscale1 hq hQ E hleft hright hpoint
  intro T hT y
  obtain ⟨S, hST⟩ := E.finsetCongr.surjective T
  change S.map E.toEmbedding = T at hST
  subst T
  have hS := (hsep S).mpr hT
  exact all_daughter_genericity_transport q hq a p hp scale ε hε hε1 hscale hscale1
    hQ E hleft hright hpoint S (hAux S hS) (hB S hS) y

end DirectGLSSW.TruncationDaughterGenericity
