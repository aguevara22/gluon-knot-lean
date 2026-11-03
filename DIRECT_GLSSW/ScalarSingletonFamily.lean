import ScalarNestedWords
import DaughterProductSplit10Closed

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open DirectGLSSW.PermutationOrbits DirectGLSSW.ActualLocalSupports
open DirectGLSSW.ScalarInversionBridge DirectGLSSW.LocalCoordinates
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 10000000 in
theorem scalar_component_eq_singleton_at_localComponent {R : Type*}
    (X : CyclicScalar R) {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (C : Component (localSmoothing q (smoothingIncomingPermutation q hq.g2 S.1)
      S.1 A (rootsS A) (family A))) :
    let full := S.1 ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    let refined := S.1 ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S.1)
      S.1 (singletonFamily q family A)
    X.toFun (componentWord q hq.g2 full
      (outgoingComponentOfLocal q hq S family rootsS A C)) =
    X.toFun (componentWord q hq.g2 refined
      (outgoingComponentOfLocal q hq S (singletonFamily q family A) rootsS A
        ((singletonLocalComponentEquiv q hq S rootsS family A).symm C))) := by
  classical
  dsimp only
  let pS := smoothingIncomingPermutation q hq.g2 S.1
  let pLocal := localSmoothing q pS S.1 A (rootsS A) (family A)
  let pSingle := localSmoothing q pS S.1 A (rootsS A)
    (singletonFamily q family A A)
  let eComp := singletonLocalComponentEquiv q hq S rootsS family A
  let Csingle : Component pSingle := eComp.symm C
  let z : Fibre pLocal C := Classical.choice (fibreNonempty pLocal C)
  let i := z.val
  have hi : componentOf pLocal i = C := z.property
  have hCsingle : Csingle = componentOf pSingle i := by
    apply eComp.injective
    calc
      eComp Csingle = C := by simp [Csingle]
      _ = componentOf pLocal i := hi.symm
      _ = eComp (componentOf pSingle i) := by
        symm
        change eComp (componentOf pSingle i) = componentOf pLocal i
        unfold eComp singletonLocalComponentEquiv
        apply componentEquivOfIntertwining_componentOf
  have hfull := outgoingComponentOfLocal_eq_at_index q hq S rootsS family A i
  have hsingle := outgoingComponentOfLocal_eq_at_index q hq S
    rootsS (singletonFamily q family A) A i
  have hxA : componentOf pS (rootedEnumeration pS (rootsS A) i).val = A :=
    (rootedEnumeration pS (rootsS A) i).property
  have hp : smoothingPairing q
      (S.1 ∪ unionLocal q pS S.1 family)
      (rootedEnumeration pS (rootsS A) i).val =
      smoothingPairing q
        (S.1 ∪ unionLocal q pS S.1 (singletonFamily q family A))
        (rootedEnumeration pS (rootsS A) i).val := by
    have hT := unionLocal_eligible q pS S.1 family
    have hT' := unionLocal_eligible q pS S.1 (singletonFamily q family A)
    have hd := disjoint_of_eligible q pS S.1 _ hT
    have hd' := disjoint_of_eligible q pS S.1 _ hT'
    have hpLocal := DirectGLSSW.RefinementFamilyLocality.pairing_families_eq_on_label
      q hq S.1 family (singletonFamily q family A) A (by simp [singletonFamily])
      (rootedEnumeration pS (rootsS A) i).val hxA
    calc
      _ = (smoothingPairing q S.1 * smoothingPairing q (unionLocal q pS S.1 family))
          ((rootedEnumeration pS (rootsS A) i).val) := by
            rw [smoothingPairing_union q S.1 _ hd]
      _ = (smoothingPairing q S.1 * smoothingPairing q
          (unionLocal q pS S.1 (singletonFamily q family A)))
          ((rootedEnumeration pS (rootsS A) i).val) := by
            simp only [Equiv.Perm.mul_apply]
            exact congrArg (smoothingPairing q S.1) hpLocal
      _ = _ := by rw [← smoothingPairing_union q S.1 _ hd']
  have hfullC : outgoingComponentOfLocal q hq S family rootsS A C =
      componentOf (smoothingDartPermutation q hq.g2
        (S.1 ∪ unionLocal q pS S.1 family))
        (smoothingPairing q (S.1 ∪ unionLocal q pS S.1 family)
          (rootedEnumeration pS (rootsS A) i).val) := by
    simpa [hi, pS, pLocal] using hfull
  have hsingleC : outgoingComponentOfLocal q hq S (singletonFamily q family A)
      rootsS A Csingle = componentOf (smoothingDartPermutation q hq.g2
        (S.1 ∪ unionLocal q pS S.1 (singletonFamily q family A)))
        (smoothingPairing q (S.1 ∪ unionLocal q pS S.1 (singletonFamily q family A))
          (rootedEnumeration pS (rootsS A) i).val) := by
    change outgoingComponentOfLocal q hq S (singletonFamily q family A) rootsS A
      Csingle = _
    rw [hCsingle]
    simpa [pS, pLocal, singletonFamily_at] using hsingle
  have hlabel : DirectGLSSW.RefinementFamilyLocality.outgoingOldLabel q hq S.1
      (smoothingPairing q (S.1 ∪ unionLocal q pS S.1 family)
        (rootedEnumeration pS (rootsS A) i).val) = A := by
    rw [outgoingOldLabel_pairing_refinement q hq S family]
    exact hxA
  have heq := scalar_component_eq_of_family_eq X q hq S.1 family
    (singletonFamily q family A) A (by simp [singletonFamily])
    (smoothingPairing q (S.1 ∪ unionLocal q pS S.1 family)
      (rootedEnumeration pS (rootsS A) i).val) hlabel
  rw [hfullC,hsingleC]
  simpa [pS,hp] using heq

noncomputable def singletonFiberScalar {R : Type*} (X : CyclicScalar R)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (z : Σ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      Component (localSmoothing q (smoothingIncomingPermutation q hq.g2 S.1)
        S.1 A (rootsS A) (family A))) : R :=
  let A := z.1
  let refined := S.1 ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S.1)
    S.1 (singletonFamily q family A)
  X.toFun (componentWord q hq.g2 refined
    (outgoingComponentOfLocal q hq S (singletonFamily q family A) rootsS A
      ((singletonLocalComponentEquiv q hq S rootsS family A).symm z.2)))

set_option maxHeartbeats 10000000 in
theorem scalar_componentProduct_eq_sigmaSingletonFiber {R : Type*} [CommRing R]
    (X : CyclicScalar R) {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1) :
    let full := S.1 ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    componentProduct X q hq.g2 full =
      ∏ z : Σ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
        Component (localSmoothing q (smoothingIncomingPermutation q hq.g2 S.1)
          S.1 A (rootsS A) (family A)),
        singletonFiberScalar X q hq S rootsS family z := by
  classical
  let full := S.1 ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  let pIn := smoothingIncomingPermutation q hq.g2 S.1
  let E := (smoothingComponentEquiv q hq.g2 full).symm.trans
    (actualLocalComponentEquiv q hq.g2 S.1 family rootsS)
  let w := fun c : Component (smoothingDartPermutation q hq.g2 full) =>
    X.toFun (componentWord q hq.g2 full c)
  let g := fun z : Σ A : Component pIn,
      Component (localSmoothing q pIn S.1 A (rootsS A) (family A)) =>
    singletonFiberScalar X q hq S rootsS family z
  have hweight : ∀ c, w c = g (E c) := by
    intro c
    have hcomponent : outgoingComponentOfLocal q hq S family rootsS
        (E c).1 (E c).2 = c := by
      change E.symm (E c) = c
      exact Equiv.symm_apply_apply E c
    have hs := scalar_component_eq_singleton_at_localComponent X q hq S rootsS
      family (E c).1 (E c).2
    simpa [w,g,singletonFiberScalar,hcomponent] using hs
  dsimp [componentProduct]
  calc
    (∏ c : Component (smoothingDartPermutation q hq.g2 full), w c) =
        ∏ c, g (E c) := by
          apply Finset.prod_congr rfl
          intro c hc
          exact hweight c
    _ = ∏ z, g z :=
      Fintype.prod_equiv E (fun c => g (E c)) g (by intro c; rfl)
    _ = _ := by rfl

end DirectGLSSW.FullScalarInversion


