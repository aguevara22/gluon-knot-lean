import DaughterProductSplit10Closed
import DirectGLSSW.BooleanInversion
import DirectGLSSW.GeometricSmoothingWeights
import DirectGLSSW.MixedEdgeRootWeights
import DirectGLSSW.DaughterRootRotation
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
namespace DirectGLSSW.ScalarInversionFinal
open scoped BigOperators
open GeometricSmoothingWeights DaughterFirstReturn DaughterG2Inheritance
open ActualLocalSupports LocalCoordinates PolygonNonalternation PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem product_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → Type*)
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℚ) :
    (∏ i, ∑ a : α i, w i a) =
      ∑ f : ∀ i, α i, ∏ i, w i (f i) := by
  exact Fintype.prod_sum w

theorem product_daughter_primitives_eq_sum_support_choices
    (S : ScalarInversionBridge.Supports q hq)
    (hAux : auxiliaryGenericity q hq) :
    (∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      separatingSmoothingSum
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
        (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
          (ScalarInversionBridge.rootEvent q hq S A)
          (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)) =
    ∑ choices : ∀ A : PermutationOrbits.Component
        (smoothingIncomingPermutation q hq.g2 S.1),
        GeometricSmoothingWeights.SeparatingSupport
          (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
          (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A)),
      ∏ A, (-1 : ℚ) ^ (choices A).1.card *
        componentAmplitudeProduct
          (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
          (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
          (choices A).1
          (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
            (ScalarInversionBridge.rootEvent q hq S A)
            (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)
          (choices A).2 := by
  classical
  simp only [GeometricSmoothingWeights.separatingSmoothingSum]
  exact product_sum_pi _ _

noncomputable def daughterChoicesToLocalChoices
    (S : ScalarInversionBridge.Supports q hq)
    (hAux : auxiliaryGenericity q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1)) :
    (∀ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      GeometricSmoothingWeights.SeparatingSupport
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))) ≃
    (∀ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      {L : Finset (ActualLocalSupports.LocalCrossing q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 A) // ChordNonalternation.Nonalternating
            (LocalCoordinates.localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
              S.1 A (rootsS A)) L}) := by
  classical
  exact Equiv.piCongrRight fun A =>
    ScalarInversionBridge.daughterSupportToLocalFamilyEquiv q hq S rootsS A

noncomputable def localChoicesToFamily
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1)) :
    (∀ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      {L : Finset (ActualLocalSupports.LocalCrossing q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 A) // ChordNonalternation.Nonalternating
            (LocalCoordinates.localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
              S.1 A (rootsS A)) L}) ≃
    {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family} where
  toFun choices := ⟨fun A => (choices A).val, fun A => (choices A).property⟩
  invFun family A := ⟨family.val A, family.property A⟩
  left_inv choices := by
    funext A
    exact Subtype.ext rfl
  right_inv family := by
    apply Subtype.ext
    funext A
    rfl

@[simp] theorem localChoicesToFamily_symm_apply
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family})
    (A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    (localChoicesToFamily q hq S rootsS).symm family A =
      ⟨family.1 A, family.2 A⟩ := rfl

noncomputable def localFamilySubtypeFintype
    (S : ScalarInversionBridge.Supports q hq)
    (hAux : auxiliaryGenericity q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1)) :
    Fintype {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family} := by
  classical
  let e := (daughterChoicesToLocalChoices q hq S hAux rootsS).trans
    (localChoicesToFamily q hq S rootsS)
  letI : Fintype (∀ A : PermutationOrbits.Component
      (smoothingIncomingPermutation q hq.g2 S.1),
      GeometricSmoothingWeights.SeparatingSupport
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))) := by
    classical
    infer_instance
  exact Fintype.ofEquiv _ e

theorem sum_daughterChoices_reindex_localFamilies
    (S : ScalarInversionBridge.Supports q hq)
    (hAux : auxiliaryGenericity q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    [Fintype {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family}]
    (F : (∀ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      GeometricSmoothingWeights.SeparatingSupport
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))) → ℚ) :
    (∑ choices, F choices) =
      ∑ family : {family : ActualLocalSupports.LocalSupports q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
        TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family},
        F ((daughterChoicesToLocalChoices q hq S hAux rootsS).symm
          ((localChoicesToFamily q hq S rootsS).symm family)) := by
  classical
  let E := (daughterChoicesToLocalChoices q hq S hAux rootsS).trans
    (localChoicesToFamily q hq S rootsS)
  apply Fintype.sum_equiv E
  intro choices
  change F choices = F (E.symm (E choices))
  rw [Equiv.symm_apply_apply]

theorem daughterSupportForFamily_eq_equiv_symm
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    ScalarInversionBridge.daughterSupportForFamily q hq S rootsS family hfamily A =
      (ScalarInversionBridge.daughterSupportToLocalFamilyEquiv q hq S rootsS A).symm
        ⟨family A, hfamily A⟩ := by
  let E := ScalarInversionBridge.daughterSupportToLocalFamilyEquiv q hq S rootsS A
  apply E.injective
  rw [Equiv.apply_symm_apply]
  change E (ScalarInversionBridge.daughterSupportForFamily q hq S rootsS family hfamily A) =
    ⟨family A, hfamily A⟩
  simp [E, ScalarInversionBridge.daughterSupportToLocalFamilyEquiv,
    ScalarInversionBridge.daughterSupportForFamily,
    ScalarInversionBridge.daughterSupportForLocalFamily,
    DaughterLocalSupportTransport.localSupportEquiv,
    DaughterLocalSupportTransport.localSupportEquiv_apply,
    Finset.map_map, Equiv.toEmbedding, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply, Function.comp_def] <;>
    (ext c; simp)

theorem daughterSupportToLocalFamilyEquiv_card (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1))
    (T : {T : Finset (PolygonCrossing (daughterVertex q hq.g2 S.1
        (ScalarInversionBridge.rootEvent q hq S A))) //
      PolygonNonalternation.polygonNonalternating (daughterVertex q hq.g2 S.1
        (ScalarInversionBridge.rootEvent q hq S A))
        (daughter_cyclicNoTripleIntersections q hq.g2 S.1 hq.size_ge_three S.2
          (ScalarInversionBridge.rootEvent q hq S A)) T}) :
    (ScalarInversionBridge.daughterSupportToLocalFamilyEquiv q hq S rootsS A T).val.card =
      T.val.card := by
  unfold ScalarInversionBridge.daughterSupportToLocalFamilyEquiv
  simp [DaughterLocalSupportTransport.localSupportEquiv,
    DaughterLocalSupportTransport.localSupportEquiv_apply,
    DaughterLocalSupportTransport.incomingSupport]

@[simp] theorem daughterSupportToLocalFamilyEquiv_symm_card
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    ((ScalarInversionBridge.daughterSupportToLocalFamilyEquiv q hq S rootsS A).symm
      ⟨family A, hfamily A⟩).val.card = (family A).card := by
  simpa only [Equiv.apply_symm_apply] using
    (daughterSupportToLocalFamilyEquiv_card q hq S rootsS A
      ((ScalarInversionBridge.daughterSupportToLocalFamilyEquiv q hq S rootsS A).symm
        ⟨family A, hfamily A⟩)).symm

@[simp] theorem daughterChoicesToLocalChoices_symm_apply
    (S : ScalarInversionBridge.Supports q hq)
    (hAux : auxiliaryGenericity q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (f : ∀ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      {L : Finset (ActualLocalSupports.LocalCrossing q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 A) // ChordNonalternation.Nonalternating
            (LocalCoordinates.localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
              S.1 A (rootsS A)) L})
    (A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    (daughterChoicesToLocalChoices q hq S hAux rootsS).symm f A =
      (ScalarInversionBridge.daughterSupportToLocalFamilyEquiv q hq S rootsS A).symm (f A) := rfl

noncomputable def localFamilyDaughterChoices
    (S : ScalarInversionBridge.Supports q hq)
    (hAux : auxiliaryGenericity q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family) :
    ∀ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      GeometricSmoothingWeights.SeparatingSupport
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A)) :=
  (daughterChoicesToLocalChoices q hq S hAux rootsS).symm
    ((localChoicesToFamily q hq S rootsS).symm ⟨family, hfamily⟩)

theorem componentAmplitudeProduct_eq_of_support_eq
    {Q : Fin n → PlanarPoint ℝ} {hQ : CyclicGeneric Q}
    {U V : Finset (PolygonCrossing Q)}
    (hUV : U = V) (hAuxQ : auxiliaryGenericity Q hQ)
    (hU : PolygonNonalternation.polygonNonalternating Q hQ.g2 U)
    (hV : PolygonNonalternation.polygonNonalternating Q hQ.g2 V) :
    componentAmplitudeProduct Q hQ U hAuxQ hU =
      componentAmplitudeProduct Q hQ V hAuxQ hV := by
  subst V
  rfl

theorem localFamily_sign_product_eq_refinement_sign
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family) :
    (∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      (-1 : ℚ) ^ (family A).card) =
      (-1 : ℚ) ^ ((S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family).card - S.1.card) := by
  classical
  let T := ActualLocalSupports.unionLocal q (smoothingIncomingPermutation q hq.g2 S.1)
    S.1 family
  let full := S.1 ∪ T
  have hEligible := ActualLocalSupports.unionLocal_eligible q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  have hDisjoint := ActualLocalSupports.disjoint_of_eligible q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 T hEligible
  have hLocalCard := ActualLocalSupports.unionLocal_card q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  have hFullCard : full.card - S.1.card = T.card := by
    dsimp [full, T]
    rw [Finset.card_union_of_disjoint hDisjoint]
    rw [hLocalCard]
    omega
  have hPow : (∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      (-1 : ℚ) ^ (family A).card) =
      (-1 : ℚ) ^ (∑ A : PermutationOrbits.Component
        (smoothingIncomingPermutation q hq.g2 S.1), (family A).card) := by
    simpa using Finset.prod_pow_eq_pow_sum (Finset.univ)
      (fun A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1) =>
        (family A).card) (-1 : ℚ)
  rw [hPow, ← hLocalCard, hFullCard]

theorem localFamilyDaughterAmplitudeProduct_eq_parent
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    (∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      componentAmplitudeProduct
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
        (localFamilyDaughterChoices q hq S hAux rootsS family hfamily A).1
        (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
          (ScalarInversionBridge.rootEvent q hq S A)
          (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)
        (localFamilyDaughterChoices q hq S hAux rootsS family hfamily A).2) =
    componentAmplitudeProduct q hq
      (S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)
      hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) := by
  classical
  have hsplit := ScalarInversionBridge.componentAmplitudeProduct_eq_product_daughterProducts
    q hq S rootsS family hfamily hRI hAux
  rw [hsplit]
  apply Finset.prod_congr rfl
  intro A hA
  dsimp [localFamilyDaughterChoices, localChoicesToFamily]
  have hchoice := congrArg Subtype.val
    (daughterSupportForFamily_eq_equiv_symm q hq S rootsS family hfamily A)
  exact (componentAmplitudeProduct_eq_of_support_eq hchoice.symm
    (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
      (ScalarInversionBridge.rootEvent q hq S A)
      (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)
    ((localFamilyDaughterChoices q hq S hAux rootsS family hfamily A).2)
    (ScalarInversionBridge.daughterSupportForFamily q hq S rootsS family hfamily A).property)

theorem localFamilyDaughterContribution_eq_parent_refinement_term
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    (∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      (-1 : ℚ) ^ (family A).card *
        componentAmplitudeProduct
          (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
          (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
          (localFamilyDaughterChoices q hq S hAux rootsS family hfamily A).1
          (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
            (ScalarInversionBridge.rootEvent q hq S A)
            (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)
          (localFamilyDaughterChoices q hq S hAux rootsS family hfamily A).2) =
    (-1 : ℚ) ^ ((S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family).card - S.1.card) *
      componentAmplitudeProduct q hq
        (S.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)
        hAux
        ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
          hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) := by
  classical
  rw [Finset.prod_mul_distrib]
  rw [localFamily_sign_product_eq_refinement_sign q hq S rootsS family hfamily]
  rw [localFamilyDaughterAmplitudeProduct_eq_parent q hq S rootsS family hfamily hRI hAux]

theorem product_daughter_primitives_eq_refinement_family_sum
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    [Fintype {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family}]
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    (∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      separatingSmoothingSum
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
        (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
          (ScalarInversionBridge.rootEvent q hq S A)
          (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)) =
    ∑ family : {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family},
      (-1 : ℚ) ^ ((S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family.1).card - S.1.card) *
        componentAmplitudeProduct q hq
          (S.1 ∪ ActualLocalSupports.unionLocal q
            (smoothingIncomingPermutation q hq.g2 S.1) S.1 family.1)
          hAux
          ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
            hq.size_ge_three S.1 S.2 rootsS family.1).2 family.2) := by
  classical
  rw [product_daughter_primitives_eq_sum_support_choices q hq S hAux]
  rw [sum_daughterChoices_reindex_localFamilies q hq S hAux rootsS]
  apply Fintype.sum_congr
  intro family
  cases family with
  | mk family hfamily =>
    convert (localFamilyDaughterContribution_eq_parent_refinement_term q hq S rootsS
      family hfamily hRI hAux) using 1
    · simp only [localFamilyDaughterChoices, daughterChoicesToLocalChoices_symm_apply,
        localChoicesToFamily_symm_apply, daughterSupportToLocalFamilyEquiv_symm_card]

theorem daughterProduct_sum (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity q hq)
    (S : ScalarInversionBridge.Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    [Fintype {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1
        rootsS family}] :
    (∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
      separatingSmoothingSum
        (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
        (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
        (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
          (ScalarInversionBridge.rootEvent q hq S A)
          (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)) =
    ∑ family : {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1
        rootsS family},
      (-1 : ℚ) ^ ((S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family.1).card - S.1.card) *
        componentAmplitudeProduct q hq
          (S.1 ∪ ActualLocalSupports.unionLocal q
            (smoothingIncomingPermutation q hq.g2 S.1) S.1 family.1)
          hAux
          ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
            hq.size_ge_three S.1 S.2 rootsS family.1).2
            family.2) := by
  classical
  exact product_daughter_primitives_eq_refinement_family_sum q hq S rootsS hRI hAux

theorem empty_daughterPointList_zero_local {n : ℕ} (hn : 0 < n)
    (P : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections P) :
    daughterPointList P hG2 ∅ (Sum.inl (⟨0,hn⟩ : Fin n)) = List.ofFn P := by
  letI : LinearOrder (PolygonEvent P) := polygonEventOrder P hG2
  letI : LinearOrder (Fin n ⊕ CrossingVisit P) := polygonEventOrder P hG2
  let E := increasingEnumeration (PolygonEvent P)
  let z : PolygonEvent P := Sum.inl (⟨0,hn⟩ : Fin n)
  have hN : 0 < Fintype.card (PolygonEvent P) := Fintype.card_pos_iff.mpr ⟨z⟩
  have hzmin (y : PolygonEvent P) : z ≤ y := by
    apply le_of_not_gt
    intro hlt
    rcases (polygonEvent_lt_iff P hG2 y z).mp hlt with h | ⟨_,h⟩
    · change (polygonEventEdge P y).val < 0 at h
      omega
    · exact (not_lt_of_ge (polygonEventParameter_bounds P y).1) h
  have hemin (y : PolygonEvent P) : E ⟨0,hN⟩ ≤ y := by
    rw [← E.apply_symm_apply y]
    exact E.monotone (show (⟨0,hN⟩ : Fin (Fintype.card (PolygonEvent P))) ≤ E.symm y from Nat.zero_le _)
  have hE0 : E (⟨0,hN⟩ : Fin (Fintype.card (PolygonEvent P))) = z :=
    le_antisymm (hemin z) (hzmin _)
  have hstep (i : Fin (Fintype.card (PolygonEvent P))) :
      polygonEventSuccessor P hG2 (E i) = E (cyclicSuccessor i) := by
    change orderedCyclicSuccessor (PolygonEvent P) (E i) = E (cyclicSuccessor i)
    simp only [orderedCyclicSuccessor_apply,E,OrderIso.symm_apply_apply]
  have hw := orbitWord_eq_of_injective_cyclicSuccessor (polygonEventSuccessor P hG2)
    hN E E.injective hstep
  rw [hE0] at hw
  have ha : List.ofFn (fun i : Fin n => (Sum.inl i : PolygonEvent P)) =
      (List.ofFn E).filter (fun y => decide (retainedCorner P ∅ y)) := by
    have hs1 : (List.ofFn (fun i : Fin n => (Sum.inl i : PolygonEvent P))).Sorted (· < ·) := by
      apply List.sorted_lt_ofFn_iff.mpr
      intro i j hij
      exact (polygonEvent_anchor_lt_iff P hG2 i j).mpr hij
    have hs2 : ((List.ofFn E).filter (fun y => decide (retainedCorner P ∅ y))).Sorted (· < ·) :=
      (List.sorted_lt_ofFn_iff.mpr E.strictMono).filter _
    apply List.Sorted.eq_of_mem_iff hs1 hs2
    intro y
    cases y with
    | inl i =>
      constructor
      · intro _
        exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨E.symm (Sum.inl i),E.apply_symm_apply _⟩,by simp [retainedCorner]⟩
      · intro _
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
    | inr v => simp [retainedCorner,List.mem_ofFn]
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    smoothingDartPermutation_empty]
  change ((orbitWord (polygonEventSuccessor P hG2) z).filter _).map _ = _
  rw [hw,← ha,List.map_ofFn]
  rfl

theorem empty_componentAmplitudeProduct_eq_polygonAmplitude
    (hRI : GLSSWRootIndependence) (e : Fin n)
    (hAux : auxiliaryGenericity q hq) :
    componentAmplitudeProduct q hq ∅ hAux (by simp [PolygonNonalternation.polygonNonalternating]) =
      polygonAmplitude q hq := by
  classical
  let T : Finset (EdgeChord q e) := ∅
  have hNA : PolygonNonalternation.polygonNonalternating q hq.g2
      (T.image Subtype.val) := by simp [T, PolygonNonalternation.polygonNonalternating]
  change componentAmplitudeProduct q hq (T.image Subtype.val) hAux hNA = _
  rw [MixedEdgeRootWeights.componentAmplitudeProduct_eq_edgeRootProduct
    hRI q hq e T hAux hNA]
  simp only [T, Finset.image_empty]
  simp [MixedEdgeComponentRoots.EdgeRoot, MixedEdgeComponentRoots.rootEvent]
  let root0 : PolygonEvent q := Sum.inl ⟨0, by have := hq.size_ge_three; omega⟩
  have hcycle : (polygonEventSuccessor q hq.g2).SameCycle (Sum.inl e) root0 :=
    (polygonEventSuccessor_isCycleOn q hq.g2).2 (Set.mem_univ _) (Set.mem_univ _)
  have hcycleDart : (smoothingDartPermutation q hq.g2 ∅).SameCycle (Sum.inl e) root0 := by
    simpa [smoothingDartPermutation_empty] using hcycle
  have hrot := DaughterRootRotation.daughterPointList_isRotated_of_sameCycle
    q hq.g2 ∅ (Sum.inl e) root0 hcycleDart
  have hn : 0 < n := by have := hq.size_ge_three; omega
  have hlist : List.ofFn q ~r
      List.ofFn (fun i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 ∅ (Sum.inl e))) =>
        DaughterFirstReturn.daughterVertex q hq.g2 ∅ (Sum.inl e) i) := by
    rw [empty_daughterPointList_zero_local hn q hq.g2] at hrot
    exact hrot.symm
  have hamp := DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI hq hlist
  exact hamp.symm

theorem subset_refinement_coefficient (U : Finset (PolygonCrossing q)) :
    (∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U},
      (-1 : ℚ) ^ (U.card - S.1.card)) =
      if U = ∅ then 1 else 0 := by
  classical
  let E : {S : Finset (PolygonCrossing q) // S ⊆ U} ≃
      {S : Finset (PolygonCrossing q) // S ∈ U.powerset} :=
    { toFun := fun S => ⟨S.1, Finset.mem_powerset.mpr S.2⟩
      invFun := fun S => ⟨S.1, Finset.mem_powerset.mp S.2⟩
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl }
  have hsum :
      (∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U},
        (-1 : ℚ) ^ (U.card - S.1.card)) =
      ∑ S ∈ U.powerset, (-1 : ℚ) ^ (U.card - S.card) := by
    calc
      _ = ∑ S : {S : Finset (PolygonCrossing q) // S ∈ U.powerset},
          (-1 : ℚ) ^ (U.card - S.1.card) := by
            apply Fintype.sum_equiv E
            intro S
            rfl
      _ = ∑ S ∈ U.powerset, (-1 : ℚ) ^ (U.card - S.card) := by
        simpa using (Finset.sum_attach U.powerset
          (fun S : Finset (PolygonCrossing q) => (-1 : ℚ) ^ (U.card - S.card)))
  rw [hsum]
  simpa [DirectGLSSW.refinementCoefficient] using
    DirectGLSSW.refinementCoefficient_eq (R := ℚ) U

theorem literal_scalar_inversion (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity q hq) :
    polygonAmplitude q hq =
      ∑ S : ScalarInversionBridge.Supports q hq,
        ∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
          separatingSmoothingSum
            (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
            (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
            (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
              (ScalarInversionBridge.rootEvent q hq S A)
              (ScalarInversionBridge.rootEvent_retained q hq S A) hAux) := by
  classical
  let roots : ∀ S : ScalarInversionBridge.Supports q hq,
      LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1) :=
    fun S => ScalarInversionBridge.roots q hq S
  let weighted (U : ScalarInversionBridge.Supports q hq) : ℚ :=
    componentAmplitudeProduct q hq U.1 hAux U.2
  let families := fun S : ScalarInversionBridge.Supports q hq =>
    {family : ActualLocalSupports.LocalSupports q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 //
      TwoStageRefinement.LocalNonalternating q hq.g2 S.1 (roots S) family}
  let Source := Σ S : ScalarInversionBridge.Supports q hq, families S
  let Target := Σ U : ScalarInversionBridge.Supports q hq,
    {S : Finset (PolygonCrossing q) // S ⊆ U.1}
  let sourceWeight : Source → ℚ := fun x =>
    (-1 : ℚ) ^ ((x.1.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 x.1.1) x.1.1 x.2.1).card - x.1.1.card) *
      componentAmplitudeProduct q hq
        (x.1.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 x.1.1) x.1.1 x.2.1)
        hAux
        ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
          hq.size_ge_three x.1.1 x.1.2 (roots x.1) x.2.1).2 x.2.2)
  letI : ∀ S : ScalarInversionBridge.Supports q hq, Fintype (families S) :=
    fun S => localFamilySubtypeFintype q hq S hAux (roots S)
  letI : Fintype Source := inferInstance
  let E := TwoStageRefinement.twoStageSupportEquiv q hq.g2 hq.size_ge_three roots
  have hExpand :
      (∑ S : ScalarInversionBridge.Supports q hq,
        ∏ A : PermutationOrbits.Component (smoothingIncomingPermutation q hq.g2 S.1),
          separatingSmoothingSum
            (daughterVertex q hq.g2 S.1 (ScalarInversionBridge.rootEvent q hq S A))
            (hAux S.1 S.2 (ScalarInversionBridge.rootEvent q hq S A))
            (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
              (ScalarInversionBridge.rootEvent q hq S A)
              (ScalarInversionBridge.rootEvent_retained q hq S A) hAux)) =
      ∑ x : Source, sourceWeight x := by
    rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro S
    exact daughterProduct_sum q hq hRI hAux S (roots S)
  let targetWeight : Target → ℚ := fun y =>
    (-1 : ℚ) ^ (y.1.1.card - y.2.1.card) * weighted y.1
  have hPoint (x : Source) : sourceWeight x = targetWeight (E x) := by
    rcases x with ⟨S, family⟩
    simp [sourceWeight, targetWeight, weighted, E,
      TwoStageRefinement.twoStageSupportEquiv_apply_support,
      TwoStageRefinement.twoStageSupportEquiv_apply_firstStage]
  have hReindex : (∑ x : Source, sourceWeight x) =
      ∑ y : Target, targetWeight y := by
    apply Fintype.sum_equiv E sourceWeight targetWeight
    intro x
    exact hPoint x
  have hTarget : (∑ y : Target, targetWeight y) =
      weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ := by
    rw [Fintype.sum_sigma]
    change (∑ U : ScalarInversionBridge.Supports q hq,
      ∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U.1},
        (-1 : ℚ) ^ (U.1.card - S.1.card) * weighted U) = _
    calc
      _ = ∑ U : ScalarInversionBridge.Supports q hq,
          (∑ S : {S : Finset (PolygonCrossing q) // S ⊆ U.1},
            (-1 : ℚ) ^ (U.1.card - S.1.card)) * weighted U := by
              apply Fintype.sum_congr
              intro U
              rw [← Finset.sum_mul]
      _ = weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ := by
        let U0 : ScalarInversionBridge.Supports q hq :=
          ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩
        rw [Finset.sum_eq_single U0]
        · simp [U0, subset_refinement_coefficient]
        · intro U hU hU0
          have hne : U.1 ≠ ∅ := by
            intro h
            apply hU0
            apply Subtype.ext
            exact h
          simp [subset_refinement_coefficient, hne]
        · intro h
          exact (h (Finset.mem_univ U0)).elim
  have hEmpty := empty_componentAmplitudeProduct_eq_polygonAmplitude q hq hRI
    (⟨0, by have := hq.size_ge_three; omega⟩ : Fin n) hAux
  change weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ =
    polygonAmplitude q hq at hEmpty
  calc
    polygonAmplitude q hq = weighted ⟨∅, by simp [PolygonNonalternation.polygonNonalternating]⟩ :=
      hEmpty.symm
    _ = ∑ y : Target, targetWeight y := hTarget.symm
    _ = ∑ x : Source, sourceWeight x := hReindex.symm
    _ = _ := hExpand.symm

end DirectGLSSW.ScalarInversionFinal




