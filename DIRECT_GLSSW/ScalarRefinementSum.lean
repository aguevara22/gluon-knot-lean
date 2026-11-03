import ScalarChoiceReindex

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open scoped BigOperators
open DirectGLSSW.PermutationOrbits DirectGLSSW.ActualLocalSupports
open DirectGLSSW.ScalarInversionBridge DirectGLSSW.LocalCoordinates
open DirectGLSSW.DaughterFirstReturn
attribute [local instance] Classical.propDecidable

variable {R : Type*} [CommRing R] (X : CyclicScalar R)
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

set_option maxHeartbeats 10000000 in
theorem scalar_product_daughter_primitives_eq_refinement_sum
    (S : Supports q hq)
    (rootsS : ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    [Fintype {family : LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family}] :
    (∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      primitive X (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A))) =
    ∑ family : {family : LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family},
      (-1 : R) ^ ((S.1 ∪ unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family.1).card - S.1.card) *
      componentProduct X q hq.g2 (S.1 ∪ unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family.1) := by
  classical
  let pS := smoothingIncomingPermutation q hq.g2 S.1
  let E := scalarDaughterChoicesEquiv q hq S rootsS
  let w := fun (A : Component pS)
      (T : SeparatingSupportG2 (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A))) =>
      (-1 : R) ^ T.1.card * componentProduct X
        (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A)) T.1
  have hExpand :
      (∏ A : Component pS, primitive X
        (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A))) =
      ∑ choices : ∀ A, SeparatingSupportG2
          (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
          (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
            hq.size_ge_three S.2 (rootEvent q hq S A)),
        ∏ A, w A (choices A) := by
    simp only [primitive]
    exact Fintype.prod_sum w
  rw [hExpand]
  let v := fun (choices : ∀ A, SeparatingSupportG2
      (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
      (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
        hq.size_ge_three S.2 (rootEvent q hq S A))) =>
      ∏ A, w A (choices A)
  let target := fun (family : {family : LocalSupports q pS S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family}) =>
      (-1 : R) ^ ((S.1 ∪ unionLocal q pS S.1 family.1).card - S.1.card) *
        componentProduct X q hq.g2 (S.1 ∪ unionLocal q pS S.1 family.1)
  change (∑ choices, v choices) = ∑ family, target family
  apply Fintype.sum_equiv E v target
  intro choices
  let family := E choices
  change v choices = target family
  have hchoices : ∀ A, choices A =
      daughterSupportForFamily q hq S rootsS family.1 family.2 A := by
    intro A
    calc
      choices A = (E.symm family) A := by rw [Equiv.symm_apply_apply]
      _ = _ := scalarDaughterChoicesEquiv_symm_apply q hq S rootsS family A
  have hweight (A : Component pS) : w A (choices A) =
      (-1 : R) ^ (family.1 A).card *
      componentProduct X
        (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A))
        (daughterSupportForFamily q hq S rootsS family.1 family.2 A).1 := by
    rw [hchoices A]
    simp only [w]
    congr 2
    rw [DirectGLSSW.ScalarInversionFinal.daughterSupportForFamily_eq_equiv_symm
      q hq S rootsS family.1 family.2 A]
    exact DirectGLSSW.ScalarInversionFinal.daughterSupportToLocalFamilyEquiv_symm_card
      q hq S rootsS family.1 family.2 A
  have hsplit := scalar_componentProduct_eq_product_daughterProducts X q hq S rootsS
    family.1 family.2
  change (∏ A, w A (choices A)) = target family
  calc
    (∏ A, w A (choices A)) =
        ∏ A : Component pS, (-1 : R) ^ (family.1 A).card *
          componentProduct X
            (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
            (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
              hq.size_ge_three S.2 (rootEvent q hq S A))
            (daughterSupportForFamily q hq S rootsS family.1 family.2 A).1 := by
      apply Finset.prod_congr rfl
      intro A hA
      exact hweight A
    _ = (∏ A : Component pS, (-1 : R) ^ (family.1 A).card) *
        (∏ A : Component pS,
          componentProduct X
            (daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
            (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
              hq.size_ge_three S.2 (rootEvent q hq S A))
            (daughterSupportForFamily q hq S rootsS family.1 family.2 A).1) := by
      rw [Finset.prod_mul_distrib]
    _ = target family := by
      rw [scalar_localFamily_sign q hq S rootsS family.1]
      exact congrArg ((-1 : R) ^ ((S.1 ∪ unionLocal q pS S.1 family.1).card - S.1.card) * ·)
        hsplit.symm

end DirectGLSSW.FullScalarInversion

