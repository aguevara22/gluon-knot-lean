import ScalarSingletonFamily

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open DirectGLSSW.PermutationOrbits DirectGLSSW.ActualLocalSupports
open DirectGLSSW.ScalarInversionBridge DirectGLSSW.LocalCoordinates
open DirectGLSSW.DaughterFirstReturn DirectGLSSW.DaughterPairingLift
open DirectGLSSW.DaughterAffectedComponents
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 20000000 in
theorem scalar_daughterProduct_eq_singletonLocalProduct {R : Type*} [CommRing R]
    (X : CyclicScalar R) {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    let root := rootEvent q hq S A
    let T := daughterSupportForFamily q hq S rootsS family hfamily A
    componentProduct X (daughterVertex q hq.g2 S.1 root)
      (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
        hq.size_ge_three S.2 root) T.val =
    ∏ C : Component (localSmoothing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)),
      singletonFiberScalar X q hq S rootsS family ⟨A, C⟩ := by
  classical
  dsimp only
  let root := rootEvent q hq S A
  let hroot := rootEvent_retained q hq S A
  let T := daughterSupportForFamily q hq S rootsS family hfamily A
  rw [scalar_nested_componentProduct_eq_affected X q hq S.1 S.2 root hroot T.val]
  let eA := affectedFinalEquivOutgoingSingletonFiber q hq S rootsS family hfamily A
  let eO := outgoingComponentFiberEquiv q hq S (singletonFamily q family A) rootsS A
  let eL := singletonLocalComponentEquiv q hq S rootsS family A
  let E := eA.trans (eO.trans eL)
  let refined := S.1 ∪ unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
  have hSupport : liftedSupport q hq S.1 S.2 root hroot T.val =
      unionLocal q (smoothingIncomingPermutation q hq.g2 S.1) S.1
        (singletonFamily q family A) :=
    daughterSupportForFamily_liftedSupport_eq q hq S rootsS family hfamily A
  have hWholeSupport : S.1 ∪ liftedSupport q hq S.1 S.2 root hroot T.val =
      refined := congrArg (fun U => S.1 ∪ U) hSupport
  have hCancel (C : AffectedFinal q hq S.1 S.2 root hroot T.val) :
      eL.symm (E C) = eO (eA C) := by
    dsimp [E]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  refine Fintype.prod_equiv E
    (fun C => X.toFun (componentWord q hq.g2
      (S.1 ∪ liftedSupport q hq S.1 S.2 root hroot T.val) C.val))
    (fun z => singletonFiberScalar X q hq S rootsS family ⟨A, z⟩) ?_
  intro C
  dsimp [singletonFiberScalar]
  have hComp : outgoingComponentOfLocal q hq S (singletonFamily q family A)
      rootsS A (eL.symm (E C)) = (eA C).val := by
    rw [hCancel]
    exact outgoingComponentOfLocal_fiberEquiv q hq S
      (singletonFamily q family A) rootsS A (eA C)
  have hScalar := scalar_component_eq_of_support_eq X q hq.g2 hWholeSupport C.val
  have hTransport :
      (componentEquivOfIntertwining (Equiv.refl _)
        (smoothingDartPermutation q hq.g2
          (S.1 ∪ liftedSupport q hq S.1 S.2 root hroot T.val))
        (smoothingDartPermutation q hq.g2 refined)
        (by
          have hp := congrArg (smoothingDartPermutation q hq.g2) hWholeSupport
          intro x
          exact congrArg (fun f : Equiv.Perm (PolygonEvent q) => f x) hp)) C.val =
        (eA C).val := by
    exact (affectedFinalEquivOutgoingSingletonFiber_val q hq S rootsS family hfamily A C).symm
  exact hScalar.trans
    (congrArg (fun D => X.toFun (componentWord q hq.g2 refined D))
      (hTransport.trans hComp.symm))

set_option maxHeartbeats 20000000 in
theorem scalar_componentProduct_eq_product_daughterProducts {R : Type*} [CommRing R]
    (X : CyclicScalar R) {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family) :
    let full := S.1 ∪ unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    componentProduct X q hq.g2 full =
    ∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      componentProduct X (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A))
        (daughterSupportForFamily q hq S rootsS family hfamily A).val := by
  classical
  dsimp only
  rw [scalar_componentProduct_eq_sigmaSingletonFiber X q hq S rootsS family]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro A hA
  symm
  exact scalar_daughterProduct_eq_singletonLocalProduct X q hq S rootsS family hfamily A

end DirectGLSSW.FullScalarInversion


