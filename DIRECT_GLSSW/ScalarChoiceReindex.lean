import ScalarDaughterProduct
import LiteralInversionFinal

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open scoped BigOperators
open DirectGLSSW.PermutationOrbits DirectGLSSW.ActualLocalSupports
open DirectGLSSW.ScalarInversionBridge DirectGLSSW.LocalCoordinates
open DirectGLSSW.DaughterFirstReturn
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

noncomputable def scalarDaughterChoicesEquiv
    (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1)) :
    (∀ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      SeparatingSupportG2 (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A))) ≃
    {family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family} := by
  classical
  let E : (∀ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      SeparatingSupportG2 (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A))) ≃
      (∀ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
        {L : Finset (LocalCrossing q (smoothingIncomingPermutation q hq.g2 S.1)
          S.1 A) // ChordNonalternation.Nonalternating
            (localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
              S.1 A (rootsS A)) L}) :=
    Equiv.piCongrRight fun A => daughterSupportToLocalFamilyEquiv q hq S rootsS A
  exact E.trans (DirectGLSSW.ScalarInversionFinal.localChoicesToFamily q hq S rootsS)

theorem scalarDaughterChoicesEquiv_symm_apply
    (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : {family : LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family})
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    (scalarDaughterChoicesEquiv q hq S rootsS).symm family A =
      daughterSupportForFamily q hq S rootsS family.1 family.2 A := by
  classical
  unfold scalarDaughterChoicesEquiv
  change (daughterSupportToLocalFamilyEquiv q hq S rootsS A).symm
    ⟨family.1 A, family.2 A⟩ = _
  exact (DirectGLSSW.ScalarInversionFinal.daughterSupportForFamily_eq_equiv_symm
    q hq S rootsS family.1 family.2 A).symm

noncomputable def scalarLocalFamilyFintype
    (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1)) :
    Fintype {family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1)
      S.1 // TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family} := by
  classical
  exact Fintype.ofEquiv _ (scalarDaughterChoicesEquiv q hq S rootsS)

theorem scalar_localFamily_sign {R : Type*} [CommRing R]
    (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : LocalSupports q (smoothingIncomingPermutation q hq.g2 S.1) S.1) :
    (∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      (-1 : R) ^ (family A).card) =
    (-1 : R) ^ ((S.1 ∪ unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family).card - S.1.card) := by
  classical
  let pS := smoothingIncomingPermutation q hq.g2 S.1
  let T := unionLocal q pS S.1 family
  have hEligible := unionLocal_eligible q pS S.1 family
  have hDisjoint := disjoint_of_eligible q pS S.1 T hEligible
  have hLocalCard := unionLocal_card q pS S.1 family
  have hFullCard : (S.1 ∪ T).card - S.1.card = T.card := by
    rw [Finset.card_union_of_disjoint hDisjoint]
    omega
  have hPow : (∏ A : Component pS, (-1 : R) ^ (family A).card) =
      (-1 : R) ^ (∑ A : Component pS, (family A).card) := by
    simpa using Finset.prod_pow_eq_pow_sum (Finset.univ)
      (fun A : Component pS => (family A).card) (-1 : R)
  rw [hPow, ← hLocalCard, ← hFullCard]

end DirectGLSSW.FullScalarInversion


