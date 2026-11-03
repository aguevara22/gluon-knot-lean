import DaughterNestedWeights
import DaughterLocalSupportTransport
import DaughterAffectedProjection
import DirectGLSSW.TwoStageRefinement
import RefinementFamilyLocality

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace DirectGLSSW.ScalarInversionBridge
open GeometricSmoothingWeights PolygonNonalternation PermutationOrbits
open DaughterFirstReturn DaughterLocalSupportTransport
attribute [local instance] Classical.decEq

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

abbrev Supports := {S : Finset (PolygonCrossing q) //
  polygonNonalternating q hq.g2 S}

/-- Choose the same retained root used by geometric component amplitudes, indexed
by the incoming-event component used by two-stage refinement. -/
noncomputable def rootEvent (S : Supports q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) : PolygonEvent q :=
  componentRoot q hq S.1
    (productOrderEquiv (polygonEventSuccessor q hq.g2)
      (smoothingPairing q S.1) A)

theorem rootEvent_retained (S : Supports q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    retainedCorner q S.1 (rootEvent q hq S A) :=
  componentRoot_retainedCorner q hq S.1 _


theorem incoming_component_pair_root (S : Supports q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    componentOf (smoothingIncomingPermutation q hq.g2 S.1)
      (smoothingPairing q S.1 (rootEvent q hq S A)) = A := by
  apply (productOrderEquiv (polygonEventSuccessor q hq.g2)
    (smoothingPairing q S.1)).injective
  change (productOrderEquiv (polygonEventSuccessor q hq.g2)
    (smoothingPairing q S.1))
      (componentOf ((polygonEventSuccessor q hq.g2) * (smoothingPairing q S.1))
        (smoothingPairing q S.1 (rootEvent q hq S A))) = _
  rw [productOrderEquiv_componentOf]
  rw [← Equiv.Perm.mul_apply, smoothingPairing_mul_self]
  exact componentRoot_sameComponent q hq S.1
    (productOrderEquiv (polygonEventSuccessor q hq.g2) (smoothingPairing q S.1) A)

noncomputable def roots (S : Supports q hq) :
    LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1) :=
  fun A => ⟨smoothingPairing q S.1 (rootEvent q hq S A),
    incoming_component_pair_root q hq S A⟩


noncomputable def rootLocalEquiv (S : Supports q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    ActualLocalSupports.LocalCrossing q (smoothingIncomingPermutation q hq.g2 S.1)
        S.1 A ≃ IncomingLocal q hq S.1 (rootEvent q hq S A) := by
  let root := rootEvent q hq S A
  let hA := incoming_component_pair_root q hq S A
  exact
    { toFun := fun c => ⟨c.val, c.property.1,
        c.property.2.1.trans hA.symm, c.property.2.2.trans hA.symm⟩
      invFun := fun c => ⟨c.val, c.property.1,
        c.property.2.1.trans hA, c.property.2.2.trans hA⟩
      left_inv := by intro c; apply Subtype.ext; rfl
      right_inv := by intro c; apply Subtype.ext; rfl }


theorem localNonalternating_transport {m : ℕ} (Q : Fin m → PlanarPoint ℝ)
    (p : Equiv.Perm (PolygonEvent Q)) (U : Finset (PolygonCrossing Q))
    (A B : Component p) (hAB : A = B)
    (e : ActualLocalSupports.LocalCrossing Q p U A ≃
      ActualLocalSupports.LocalCrossing Q p U B)
    (he : ∀ c, (e c).val = c.val)
    (x : Fibre p A) (y : Fibre p B)
    (L : Finset (ActualLocalSupports.LocalCrossing Q p U A)) :
    ChordNonalternation.Nonalternating (LocalCoordinates.localEndpoint Q p U A x) L ↔
      ChordNonalternation.Nonalternating (LocalCoordinates.localEndpoint Q p U B y)
        (Finset.map e.toEmbedding L) := by
  cases hAB
  have heq : e = Equiv.refl _ := by
    apply Equiv.ext
    intro c
    apply Subtype.ext
    exact he c
  subst e
  simpa using DaughterLocalSupportTransport.local_nonalternating_root_iff Q p U A x y L

noncomputable def daughterSupportForLocalFamily (S : Supports q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (familyA : Finset (ActualLocalSupports.LocalCrossing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 A))
    (hLocal : ChordNonalternation.Nonalternating
      (LocalCoordinates.localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
        S.1 (componentOf (smoothingIncomingPermutation q hq.g2 S.1)
          (smoothingPairing q S.1 (rootEvent q hq S A)))
        ⟨smoothingPairing q S.1 (rootEvent q hq S A), rfl⟩)
      (Finset.map (rootLocalEquiv q hq S A).toEmbedding familyA)) :
    {T : Finset (PolygonCrossing (DaughterFirstReturn.daughterVertex q hq.g2 S.1 (rootEvent q hq S A))) //
      PolygonNonalternation.polygonNonalternating
        (DaughterFirstReturn.daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A)) T} := by
  let root := rootEvent q hq S A
  let hroot := rootEvent_retained q hq S A
  exact (localSupportEquiv q hq S.1 S.2 root hroot).symm
    ⟨familyA.map (rootLocalEquiv q hq S A).toEmbedding, hLocal⟩





noncomputable def singletonFamily (q : Fin n → PlanarPoint ℝ) {p : Equiv.Perm (PolygonEvent q)}
    {S : Finset (PolygonCrossing q)}
    (family : ActualLocalSupports.LocalSupports q p S)
    (A : Component p) : ActualLocalSupports.LocalSupports q p S := by
  letI : DecidableEq (Component p) := Classical.decEq _
  exact Function.update (fun _ => ∅) A (family A)

@[simp] theorem singletonFamily_at (q : Fin n → PlanarPoint ℝ) {p : Equiv.Perm (PolygonEvent q)}
    {S : Finset (PolygonCrossing q)}
    (family : ActualLocalSupports.LocalSupports q p S)
    (A : Component p) : singletonFamily q family A A = family A := by
  simp [singletonFamily]

@[simp] theorem singletonFamily_ne (q : Fin n → PlanarPoint ℝ) {p : Equiv.Perm (PolygonEvent q)}
    {S : Finset (PolygonCrossing q)}
    (family : ActualLocalSupports.LocalSupports q p S)
    {A B : Component p} (h : B ≠ A) : singletonFamily q family A B = ∅ := by
  simp [singletonFamily, h]


theorem singletonFamily_localNonalternating (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS
      (singletonFamily q family A) := by
  intro B
  by_cases h : B = A
  · subst B
    simpa [singletonFamily] using hfamily A
  · simp [singletonFamily, h]

theorem singletonFamily_union_nonalternating (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    PolygonNonalternation.polygonNonalternating q hq.g2
      (S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)) := by
  letI : DecidableEq (Component (smoothingIncomingPermutation q hq.g2 S.1)) := Classical.decEq _
  exact (TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2 hq.size_ge_three
    S.1 S.2 rootsS (singletonFamily q family A)).mpr
    (singletonFamily_localNonalternating q hq S rootsS family hfamily A)


noncomputable def sigmaFiberEquiv {I : Type*} (β : I → Type*) (i : I) :
    {z : (Σ j, β j) // z.1 = i} ≃ β i where
  toFun z := z.property ▸ z.val.2
  invFun x := ⟨⟨i, x⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨j, x⟩, rfl⟩
    rfl
  right_inv := by intro x; rfl

/-- The full-U components whose first-stage ancestor is A are exactly the
local smoothing components in A. -/
noncomputable def fullLocalComponentFiberEquiv (S : Supports q hq)
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    {C : Component (smoothingIncomingPermutation q hq.g2
        (S.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)) //
      (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS C).1 = A} ≃
    Component (LocalCoordinates.localSmoothing q (smoothingIncomingPermutation q hq.g2 S.1)
      S.1 A (rootsS A) (family A)) := by
  let E := LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS
  let β := fun B : Component (smoothingIncomingPermutation q hq.g2 S.1) =>
    Component (LocalCoordinates.localSmoothing q (smoothingIncomingPermutation q hq.g2 S.1)
      S.1 B (rootsS B) (family B))
  exact (Equiv.subtypeEquiv (e := E)
      (p := fun C => (E C).1 = A) (q := fun z : Σ B, β B => z.1 = A)
      (by intro C; exact Iff.rfl)).trans (sigmaFiberEquiv β A)

noncomputable def outgoingComponentFiber (S : Supports q hq)
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :=
  {C : Component (smoothingDartPermutation q hq.g2
      (S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)) //
    (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS
      ((smoothingComponentEquiv q hq.g2
        (S.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)).symm C)).1 = A}

noncomputable def outgoingComponentFiberEquiv (S : Supports q hq)
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    outgoingComponentFiber q hq S family rootsS A ≃
      Component (LocalCoordinates.localSmoothing q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)) := by
  let E := smoothingComponentEquiv q hq.g2
    (S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)
  let F := LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS
  let e := Equiv.subtypeEquiv (e := E.symm)
    (p := fun C => (F (E.symm C)).1 = A)
    (q := fun C => (F C).1 = A) (by intro C; exact Iff.rfl)
  exact e.trans (fullLocalComponentFiberEquiv q hq S family rootsS A)


theorem unionLocal_singleton_eq_image {p : Equiv.Perm (PolygonEvent q)}
    {S : Finset (PolygonCrossing q)}
    (family : ActualLocalSupports.LocalSupports q p S)
    (A : Component p) :
    ActualLocalSupports.unionLocal q p S (singletonFamily q family A) =
      (family A).image Subtype.val := by
  classical
  ext c
  simp only [ActualLocalSupports.unionLocal, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨B, hx, hmem⟩
    by_cases hBA : B = A
    · subst B
      exact ⟨hx, by simpa [singletonFamily] using hmem⟩
    · simp [singletonFamily, hBA] at hmem
  · rintro ⟨hx, hmem⟩
    exact ⟨A, hx, by simpa [singletonFamily] using hmem⟩


noncomputable def daughterSupportForFamily (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    {T : Finset (PolygonCrossing
        (DaughterFirstReturn.daughterVertex q hq.g2 S.1 (rootEvent q hq S A))) //
      PolygonNonalternation.polygonNonalternating
        (DaughterFirstReturn.daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A)) T} := by
  let B := componentOf (smoothingIncomingPermutation q hq.g2 S.1)
    (smoothingPairing q S.1 (rootEvent q hq S A))
  let y : Fibre (smoothingIncomingPermutation q hq.g2 S.1) B :=
    ⟨smoothingPairing q S.1 (rootEvent q hq S A), rfl⟩
  have hBA : B = A := incoming_component_pair_root q hq S A
  have hLocal : ChordNonalternation.Nonalternating
      (LocalCoordinates.localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
        S.1 B y)
      (Finset.map (rootLocalEquiv q hq S A).toEmbedding (family A)) :=
    (localNonalternating_transport q (smoothingIncomingPermutation q hq.g2 S.1)
      S.1 A B hBA.symm (rootLocalEquiv q hq S A)
      (fun c => rfl) (rootsS A) y (family A)).mp (hfamily A)
  exact daughterSupportForLocalFamily q hq S A (family A) hLocal


theorem daughterSupportForFamily_liftedSupport_eq (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    DaughterPairingLift.liftedSupport q hq S.1 S.2 (rootEvent q hq S A)
      (rootEvent_retained q hq S A) (daughterSupportForFamily q hq S rootsS family hfamily A).val =
    ActualLocalSupports.unionLocal q (smoothingIncomingPermutation q hq.g2 S.1)
      S.1 (singletonFamily q family A) := by
  let T := daughterSupportForFamily q hq S rootsS family hfamily A
  have hmap := DaughterLocalSupportTransport.localSupportEquiv_apply q hq S.1 S.2
    (rootEvent q hq S A) (rootEvent_retained q hq S A) T
  let e := DaughterLocalSupportTransport.localSupportEquiv q hq S.1 S.2
    (rootEvent q hq S A) (rootEvent_retained q hq S A)
  let z : {L : Finset (ActualLocalSupports.LocalCrossing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1
      (componentOf (smoothingIncomingPermutation q hq.g2 S.1)
        (smoothingPairing q S.1 (rootEvent q hq S A)))) //
      ChordNonalternation.Nonalternating
        (LocalCoordinates.localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
          S.1 (componentOf (smoothingIncomingPermutation q hq.g2 S.1)
            (smoothingPairing q S.1 (rootEvent q hq S A)))
          ⟨smoothingPairing q S.1 (rootEvent q hq S A), rfl⟩) L} :=
    ⟨Finset.map (rootLocalEquiv q hq S A).toEmbedding (family A), by
      exact (localNonalternating_transport q (smoothingIncomingPermutation q hq.g2 S.1)
        S.1 A
        (componentOf (smoothingIncomingPermutation q hq.g2 S.1)
          (smoothingPairing q S.1 (rootEvent q hq S A)))
        (incoming_component_pair_root q hq S A).symm (rootLocalEquiv q hq S A)
        (fun c => rfl) (rootsS A)
        ⟨smoothingPairing q S.1 (rootEvent q hq S A), rfl⟩ (family A)).mp (hfamily A)⟩
  have hback := congrArg Subtype.val (Equiv.apply_symm_apply e z)
  have hincoming : DaughterLocalSupportTransport.incomingSupport q hq S.1 S.2
      (rootEvent q hq S A) (rootEvent_retained q hq S A) T.val =
      Finset.map (rootLocalEquiv q hq S A).toEmbedding (family A) := by
    calc
      _ = (e T).val :=
        (DaughterLocalSupportTransport.localSupportEquiv_apply q hq S.1 S.2
          (rootEvent q hq S A) (rootEvent_retained q hq S A) T).symm
      _ = z.val := by
        dsimp [T, daughterSupportForFamily, daughterSupportForLocalFamily, z]
        exact congrArg Subtype.val (Equiv.apply_symm_apply e z)
  rw [← DaughterLocalSupportTransport.incomingSupport_parent_image q hq S.1 S.2
    (rootEvent q hq S A) (rootEvent_retained q hq S A) T.val]
  rw [hincoming]
  rw [unionLocal_singleton_eq_image (q := q)
    (p := smoothingIncomingPermutation q hq.g2 S.1) (S := S.1) family A]
  apply Finset.ext
  intro c
  simp [rootLocalEquiv, ← PermutationOrbits.componentOf_eq_iff,
    incoming_component_pair_root]

theorem componentAmplitude_eq_singleton_on_A (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    let full := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    let refined := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
    componentAmplitude q hq full hAux (by
      exact (TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
      (componentOf (smoothingDartPermutation q hq.g2 full) (rootEvent q hq S A)) =
    componentAmplitude q hq refined hAux
      (singletonFamily_union_nonalternating q hq S rootsS family hfamily A)
      (componentOf (smoothingDartPermutation q hq.g2 refined) (rootEvent q hq S A)) := by
  dsimp
  exact RefinementFamilyLocality.componentAmplitude_eq_of_family_eq q hq S.1 hRI hAux
    family (singletonFamily q family A)
    ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
      hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
    (singletonFamily_union_nonalternating q hq S rootsS family hfamily A)
    A (by simp [singletonFamily]) (rootEvent q hq S A)
    (by simpa [RefinementFamilyLocality.outgoingOldLabel] using
      incoming_component_pair_root q hq S A)

theorem outgoingOldLabel_pairing_refinement (S : Supports q hq)
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (x : PolygonEvent q) :
    RefinementFamilyLocality.outgoingOldLabel q hq S.1
      (smoothingPairing q
        (S.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 family) x) =
    componentOf (smoothingIncomingPermutation q hq.g2 S.1) x := by
  let T := ActualLocalSupports.unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  have hT := ActualLocalSupports.unionLocal_eligible q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  have hdisj := ActualLocalSupports.disjoint_of_eligible q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 T hT
  have hp : smoothingPairing q S.1
      (smoothingPairing q (S.1 ∪ T) x) = smoothingPairing q T x := by
    rw [smoothingPairing_union q S.1 T hdisj]
    simp only [Equiv.Perm.mul_apply]
    exact smoothingPairingMap_involutive q S.1 (smoothingPairing q T x)
  unfold RefinementFamilyLocality.outgoingOldLabel
  rw [hp]
  exact ActualLocalSupports.pairing_preserves_oldLabel q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 T hT x

theorem outgoingOldLabel_eq_parentIncoming_at_refined_root (S : Supports q hq)
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (x : PolygonEvent q) :
    RefinementFamilyLocality.outgoingOldLabel q hq S.1 x =
      componentOf (smoothingIncomingPermutation q hq.g2 S.1)
        (smoothingPairing q
          (S.1 ∪ ActualLocalSupports.unionLocal q
            (smoothingIncomingPermutation q hq.g2 S.1) S.1 family) x) := by
  let full := S.1 ∪ ActualLocalSupports.unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  have h := outgoingOldLabel_pairing_refinement q hq S family
    (smoothingPairing q full x)
  have hinv : smoothingPairing q full (smoothingPairing q full x) = x := by
    rw [← Equiv.Perm.mul_apply, smoothingPairing_mul_self]
    rfl
  change RefinementFamilyLocality.outgoingOldLabel q hq S.1
      (smoothingPairing q full (smoothingPairing q full x)) =
    componentOf (smoothingIncomingPermutation q hq.g2 S.1)
      (smoothingPairing q full x) at h
  rw [hinv] at h
  exact h

noncomputable def affectedFinalEquivOutgoingSingletonFiber (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    DaughterAffectedComponents.AffectedFinal q hq S.1 S.2 (rootEvent q hq S A)
      (rootEvent_retained q hq S A)
      (daughterSupportForFamily q hq S rootsS family hfamily A).val ≃
    outgoingComponentFiber q hq S (singletonFamily q family A) rootsS A := by
  classical
  let root := rootEvent q hq S A
  let hroot := rootEvent_retained q hq S A
  let T := daughterSupportForFamily q hq S rootsS family hfamily A
  let lifted := DaughterPairingLift.liftedSupport q hq S.1 S.2 root hroot T.val
  let refined := S.1 ∪ ActualLocalSupports.unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
  let pFinal := smoothingDartPermutation q hq.g2 (S.1 ∪ lifted)
  let pSingle := smoothingDartPermutation q hq.g2 refined
  have hSupport : lifted = ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A) :=
    daughterSupportForFamily_liftedSupport_eq q hq S rootsS family hfamily A
  have hPerm : pFinal = pSingle := by
    dsimp [pFinal, pSingle, refined]
    rw [hSupport]
  let e := PermutationOrbits.componentEquivOfIntertwining (Equiv.refl _) pFinal pSingle
    (by intro x; exact congrArg (fun f => f x) hPerm)
  have hpred : ∀ C : Component pFinal,
      DaughterAffectedComponents.oldComponentOfFinal q hq S.1 S.2 root hroot T.val C =
        componentOf (smoothingDartPermutation q hq.g2 S.1) root ↔
      (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1
        (singletonFamily q family A) rootsS
        ((smoothingComponentEquiv q hq.g2 refined).symm (e C))).1 = A := by
    intro C
    refine Quotient.inductionOn C ?_
    intro x
    change (DaughterAffectedComponents.oldComponentOfFinal q hq S.1 S.2 root hroot T.val
        (componentOf pFinal x) = componentOf (smoothingDartPermutation q hq.g2 S.1) root) ↔
      (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 (singletonFamily q family A) rootsS
        ((smoothingComponentEquiv q hq.g2 refined).symm (e (componentOf pFinal x)))).1 = A
    rw [DaughterAffectedComponents.oldComponentOfFinal_componentOf]
    have he : e (componentOf pFinal x) = componentOf pSingle x := by
      dsimp [e]
    have htoIncoming : (smoothingComponentEquiv q hq.g2 refined).symm
        (e (componentOf pFinal x)) =
        componentOf (smoothingIncomingPermutation q hq.g2 refined)
          (smoothingPairing q refined x) := by
      apply (smoothingComponentEquiv q hq.g2 refined).injective
      rw [Equiv.apply_symm_apply, he]
      rw [smoothingComponentEquiv_componentOf]
      have hinv : smoothingPairing q refined (smoothingPairing q refined x) = x := by
        rw [← Equiv.Perm.mul_apply, smoothingPairing_mul_self]
        rfl
      rw [hinv]
    rw [htoIncoming]
    have hfirst := congrArg Sigma.fst
      (LocalCoordinates.actualLocalComponentEquiv_componentOf q hq.g2 S.1
        (singletonFamily q family A) rootsS (smoothingPairing q refined x))
    have hlabel := outgoingOldLabel_eq_parentIncoming_at_refined_root q hq S
      (singletonFamily q family A) x
    have hright :
        ((LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1
          (singletonFamily q family A) rootsS
          (componentOf (smoothingIncomingPermutation q hq.g2 refined)
            (smoothingPairing q refined x))).1 = A) ↔
        RefinementFamilyLocality.outgoingOldLabel q hq S.1 x = A := by
      constructor
      · intro h
        have hf : componentOf (smoothingIncomingPermutation q hq.g2 S.1)
            (smoothingPairing q refined x) = A := hfirst.trans h
        exact hlabel.trans hf
      · intro h
        have hf : componentOf (smoothingIncomingPermutation q hq.g2 S.1)
            (smoothingPairing q refined x) = A := hlabel.symm.trans h
        exact hfirst.symm.trans hf
    have hleft :
        componentOf (smoothingDartPermutation q hq.g2 S.1) x =
          componentOf (smoothingDartPermutation q hq.g2 S.1) root ↔
        RefinementFamilyLocality.outgoingOldLabel q hq S.1 x =
          RefinementFamilyLocality.outgoingOldLabel q hq S.1 root :=
      (RefinementFamilyLocality.outgoingOldLabel_eq_iff q hq S.1 x root).symm
    have hrootLabel : RefinementFamilyLocality.outgoingOldLabel q hq S.1 root = A := by
      simpa [root, rootEvent] using incoming_component_pair_root q hq S A
    have hleft' :
        componentOf (smoothingDartPermutation q hq.g2 S.1) x =
          componentOf (smoothingDartPermutation q hq.g2 S.1) root ↔
        RefinementFamilyLocality.outgoingOldLabel q hq S.1 x = A := by
      constructor
      · intro hx
        exact (hleft.mp hx).trans hrootLabel
      · intro hx
        exact hleft.mpr (hx.trans hrootLabel.symm)
    exact hleft'.trans hright.symm
  exact Equiv.subtypeEquiv (e := e)
    (p := fun C => DaughterAffectedComponents.oldComponentOfFinal q hq S.1 S.2 root hroot T.val C =
      componentOf (smoothingDartPermutation q hq.g2 S.1) root)
    (q := fun C => (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1
      (singletonFamily q family A) rootsS
      ((smoothingComponentEquiv q hq.g2 refined).symm C)).1 = A) hpred

theorem affectedFinalEquivOutgoingSingletonFiber_val (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (C : DaughterAffectedComponents.AffectedFinal q hq S.1 S.2
      (rootEvent q hq S A) (rootEvent_retained q hq S A)
      (daughterSupportForFamily q hq S rootsS family hfamily A).val) :
    (affectedFinalEquivOutgoingSingletonFiber q hq S rootsS family hfamily A C).val =
      (PermutationOrbits.componentEquivOfIntertwining (Equiv.refl _)
        (smoothingDartPermutation q hq.g2
          (S.1 ∪ DaughterPairingLift.liftedSupport q hq S.1 S.2
            (rootEvent q hq S A) (rootEvent_retained q hq S A)
            (daughterSupportForFamily q hq S rootsS family hfamily A).val))
      (smoothingDartPermutation q hq.g2
        (S.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)))
        (by
          have hs := daughterSupportForFamily_liftedSupport_eq q hq S rootsS family hfamily A
          have hp : smoothingDartPermutation q hq.g2
              (S.1 ∪ DaughterPairingLift.liftedSupport q hq S.1 S.2
                (rootEvent q hq S A) (rootEvent_retained q hq S A)
                (daughterSupportForFamily q hq S rootsS family hfamily A).val) =
              smoothingDartPermutation q hq.g2
                (S.1 ∪ ActualLocalSupports.unionLocal q
                  (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)) := by
            rw [hs]
          intro x
          exact congrArg (fun f : Equiv.Perm (PolygonEvent q) => f x) hp)
        C.val) := by
  rfl

theorem componentAmplitude_eq_of_support_eq
    {U V : Finset (PolygonCrossing q)}
    (hU : PolygonNonalternation.polygonNonalternating q hq.g2 U)
    (hV : PolygonNonalternation.polygonNonalternating q hq.g2 V)
    (hUV : U = V) (hAux : auxiliaryGenericity q hq)
    (C : Component (smoothingDartPermutation q hq.g2 U)) :
    componentAmplitude q hq U hAux hU C =
      componentAmplitude q hq V hAux hV
        ((PermutationOrbits.componentEquivOfIntertwining (Equiv.refl _)
          (smoothingDartPermutation q hq.g2 U) (smoothingDartPermutation q hq.g2 V)
          (by cases hUV; intro x; rfl)) C) := by
  subst V
  let e := PermutationOrbits.componentEquivOfIntertwining (Equiv.refl _)
    (smoothingDartPermutation q hq.g2 U) (smoothingDartPermutation q hq.g2 U)
    (by intro x; rfl)
  have he : ∀ C, e C = C := by
    intro C
    refine Quotient.inductionOn C ?_
    intro x
    rfl
  change componentAmplitude q hq U hAux hU C =
    componentAmplitude q hq U hAux hU (e C)
  rw [he C]

noncomputable def daughterSupportToLocalFamilyEquiv (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    {T : Finset (PolygonCrossing (DaughterFirstReturn.daughterVertex q hq.g2 S.1
        (rootEvent q hq S A))) //
      PolygonNonalternation.polygonNonalternating
        (DaughterFirstReturn.daughterVertex q hq.g2 S.1 (rootEvent q hq S A))
        (DaughterG2Inheritance.daughter_cyclicNoTripleIntersections q hq.g2 S.1
          hq.size_ge_three S.2 (rootEvent q hq S A)) T} ≃
    {L : Finset (ActualLocalSupports.LocalCrossing q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 A) //
      ChordNonalternation.Nonalternating
        (LocalCoordinates.localEndpoint q (smoothingIncomingPermutation q hq.g2 S.1)
          S.1 A (rootsS A)) L} := by
  classical
  let root := rootEvent q hq S A
  let hroot := rootEvent_retained q hq S A
  let pS := smoothingIncomingPermutation q hq.g2 S.1
  let B := componentOf pS (smoothingPairing q S.1 root)
  let y : Fibre pS B := ⟨smoothingPairing q S.1 root,rfl⟩
  let e := rootLocalEquiv q hq S A
  let f := e.finsetCongr
  have hBA : B = A := incoming_component_pair_root q hq S A
  have hfwd : ∀ L : Finset (ActualLocalSupports.LocalCrossing q pS S.1 A),
      ChordNonalternation.Nonalternating (LocalCoordinates.localEndpoint q pS S.1 A
        (rootsS A)) L ↔
      ChordNonalternation.Nonalternating (LocalCoordinates.localEndpoint q pS S.1 B y)
        (f L) := by
    intro L
    exact localNonalternating_transport q pS S.1 A B hBA.symm e
      (fun c => rfl) (rootsS A) y L
  let ef := f.subtypeEquiv hfwd
  exact (DaughterLocalSupportTransport.localSupportEquiv q hq S.1 S.2 root hroot).trans ef.symm

theorem componentAmplitude_eq_singleton_at_localIndex (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (i : Fin (Fintype.card (Fibre (smoothingIncomingPermutation q hq.g2 S.1) A))) :
    let full := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    let refined := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
    let x := (LocalCoordinates.rootedEnumeration (smoothingIncomingPermutation q hq.g2 S.1)
      (rootsS A) i).val
    let root := smoothingPairing q full x
    componentAmplitude q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
      (componentOf (smoothingDartPermutation q hq.g2 full) root) =
    componentAmplitude q hq refined hAux
      (singletonFamily_union_nonalternating q hq S rootsS family hfamily A)
      (componentOf (smoothingDartPermutation q hq.g2 refined) root) := by
  dsimp
  let x := (LocalCoordinates.rootedEnumeration (smoothingIncomingPermutation q hq.g2 S.1)
    (rootsS A) i).val
  have hx : componentOf (smoothingIncomingPermutation q hq.g2 S.1) x = A :=
    (LocalCoordinates.rootedEnumeration (smoothingIncomingPermutation q hq.g2 S.1) (rootsS A) i).property
  have hlabel : RefinementFamilyLocality.outgoingOldLabel q hq S.1
      (smoothingPairing q
        (S.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 family) x) = A :=
    (outgoingOldLabel_pairing_refinement q hq S family x).trans hx
  exact RefinementFamilyLocality.componentAmplitude_eq_of_family_eq q hq S.1 hRI hAux
    family (singletonFamily q family A)
    ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
      hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
    (singletonFamily_union_nonalternating q hq S rootsS family hfamily A)
    A (by simp [singletonFamily])
    (smoothingPairing q
      (S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family) x) hlabel

noncomputable def outgoingComponentOfLocal (S : Supports q hq)
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (C : Component (LocalCoordinates.localSmoothing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A))) :
    Component (smoothingDartPermutation q hq.g2
      (S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)) :=
  smoothingComponentEquiv q hq.g2
    (S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)
    ((LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS).symm ⟨A, C⟩)

theorem outgoingComponentOfLocal_eq_at_index (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (i : Fin (Fintype.card (Fibre
      (smoothingIncomingPermutation q hq.g2 S.1) A)))
    : outgoingComponentOfLocal q hq S family rootsS A
        (componentOf (LocalCoordinates.localSmoothing q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)) i) =
      componentOf (smoothingDartPermutation q hq.g2
        (S.1 ∪ ActualLocalSupports.unionLocal q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 family))
        (smoothingPairing q
          (S.1 ∪ ActualLocalSupports.unionLocal q
            (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)
          (LocalCoordinates.rootedEnumeration
            (smoothingIncomingPermutation q hq.g2 S.1) (rootsS A) i).val) := by
  let x := (LocalCoordinates.rootedEnumeration
    (smoothingIncomingPermutation q hq.g2 S.1) (rootsS A) i).val
  have hinc : componentOf (smoothingIncomingPermutation q hq.g2
      (S.1 ∪ ActualLocalSupports.unionLocal q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 family)) x =
      (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS).symm
        ⟨A, componentOf (LocalCoordinates.localSmoothing q
          (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)) i⟩ := by
    exact (LocalCoordinates.actualLocalComponentEquiv_symm_componentOf
      q hq.g2 S.1 family rootsS A i).symm
  dsimp [outgoingComponentOfLocal]
  rw [← hinc]
  rw [smoothingComponentEquiv_componentOf]

noncomputable def singletonLocalComponentEquiv (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    Component (LocalCoordinates.localSmoothing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A)
      (singletonFamily q family A A)) ≃
    Component (LocalCoordinates.localSmoothing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)) := by
  let pS := smoothingIncomingPermutation q hq.g2 S.1
  let pLocal := LocalCoordinates.localSmoothing q pS S.1 A (rootsS A) (family A)
  let pSingle := LocalCoordinates.localSmoothing q pS S.1 A
    (rootsS A) (singletonFamily q family A A)
  have hPerm : pSingle = pLocal := by
    simp [pSingle, pLocal, singletonFamily_at]
  exact PermutationOrbits.componentEquivOfIntertwining (Equiv.refl _) pSingle pLocal
    (by intro j; exact congrArg (fun f => f j) hPerm)


theorem componentAmplitude_eq_singleton_at_localComponent (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (C : Component (LocalCoordinates.localSmoothing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A))) :
    let full := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    let refined := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
    componentAmplitude q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
      (outgoingComponentOfLocal q hq S family rootsS A C) =
    componentAmplitude q hq refined hAux
      (singletonFamily_union_nonalternating q hq S rootsS family hfamily A)
      (outgoingComponentOfLocal q hq S (singletonFamily q family A) rootsS A
        ((singletonLocalComponentEquiv q hq S rootsS family A).symm C)) := by
  classical
  dsimp
  let pS := smoothingIncomingPermutation q hq.g2 S.1
  let pLocal := LocalCoordinates.localSmoothing q pS S.1 A (rootsS A) (family A)
  have hPerm : LocalCoordinates.localSmoothing q pS S.1 A (rootsS A)
      (singletonFamily q family A A) = pLocal := by
    simp [pLocal, singletonFamily_at]
  let pSingle := LocalCoordinates.localSmoothing q pS S.1 A
    (rootsS A) (singletonFamily q family A A)
  let eComp := singletonLocalComponentEquiv q hq S rootsS family A
  let Csingle : Component (LocalCoordinates.localSmoothing q pS S.1 A
      (rootsS A) (singletonFamily q family A A)) := eComp.symm C
  let z : Fibre pLocal C := Classical.choice (PermutationOrbits.fibreNonempty pLocal C)
  let i := z.val
  have hi : componentOf pLocal i = C := z.property
  have hCsingle : Csingle = componentOf
      (LocalCoordinates.localSmoothing q pS S.1 A (rootsS A)
        (singletonFamily q family A A)) i := by
    apply eComp.injective
    calc
      eComp Csingle = C := by simp [Csingle]
      _ = componentOf pLocal i := hi.symm
      _ = eComp (componentOf pSingle i) := by
        symm
        change eComp (componentOf pSingle i) = componentOf pLocal i
        unfold eComp singletonLocalComponentEquiv
        apply PermutationOrbits.componentEquivOfIntertwining_componentOf
  have hfull := outgoingComponentOfLocal_eq_at_index q hq S rootsS family A i
  have hsingle := outgoingComponentOfLocal_eq_at_index q hq S
    rootsS (singletonFamily q family A) A i
  have hxA : componentOf pS
      (LocalCoordinates.rootedEnumeration pS (rootsS A) i).val = A :=
    (LocalCoordinates.rootedEnumeration pS (rootsS A) i).property
  have hp : smoothingPairing q
      (S.1 ∪ ActualLocalSupports.unionLocal q pS S.1 family)
      (LocalCoordinates.rootedEnumeration pS (rootsS A) i).val =
      smoothingPairing q
        (S.1 ∪ ActualLocalSupports.unionLocal q pS S.1 (singletonFamily q family A))
        (LocalCoordinates.rootedEnumeration pS (rootsS A) i).val := by
    have hT := ActualLocalSupports.unionLocal_eligible q pS S.1 family
    have hT' := ActualLocalSupports.unionLocal_eligible q pS S.1 (singletonFamily q family A)
    have hd := ActualLocalSupports.disjoint_of_eligible q pS S.1 _ hT
    have hd' := ActualLocalSupports.disjoint_of_eligible q pS S.1 _ hT'
    have hpLocal := RefinementFamilyLocality.pairing_families_eq_on_label q hq S.1
      family (singletonFamily q family A) A (by simp [singletonFamily])
      (LocalCoordinates.rootedEnumeration pS (rootsS A) i).val hxA
    calc
      _ = (smoothingPairing q S.1 * smoothingPairing q (ActualLocalSupports.unionLocal q pS S.1 family))
          ((LocalCoordinates.rootedEnumeration pS (rootsS A) i).val) := by
            rw [smoothingPairing_union q S.1 _ hd]
      _ = (smoothingPairing q S.1 * smoothingPairing q
          (ActualLocalSupports.unionLocal q pS S.1 (singletonFamily q family A)))
          ((LocalCoordinates.rootedEnumeration pS (rootsS A) i).val) := by
            simp only [Equiv.Perm.mul_apply]
            exact congrArg (smoothingPairing q S.1) hpLocal
      _ = _ := by
            rw [← smoothingPairing_union q S.1 _ hd']
  have hfullC : outgoingComponentOfLocal q hq S family rootsS A C =
      componentOf (smoothingDartPermutation q hq.g2
        (S.1 ∪ ActualLocalSupports.unionLocal q pS S.1 family))
        (smoothingPairing q
          (S.1 ∪ ActualLocalSupports.unionLocal q pS S.1 family)
          (LocalCoordinates.rootedEnumeration pS (rootsS A) i).val) := by
    simpa [hi, pS, pLocal] using hfull
  have hsingleC : outgoingComponentOfLocal q hq S (singletonFamily q family A)
      rootsS A Csingle = componentOf (smoothingDartPermutation q hq.g2
        (S.1 ∪ ActualLocalSupports.unionLocal q pS S.1 (singletonFamily q family A)))
      (smoothingPairing q
          (S.1 ∪ ActualLocalSupports.unionLocal q pS S.1 (singletonFamily q family A))
          (LocalCoordinates.rootedEnumeration pS (rootsS A) i).val) := by
    change outgoingComponentOfLocal q hq S (singletonFamily q family A) rootsS A
      Csingle = _
    rw [hCsingle]
    simpa [pS, pLocal, singletonFamily_at] using hsingle
  have hamp := componentAmplitude_eq_singleton_at_localIndex q hq S rootsS family
    hfamily hRI hAux A i
  rw [hfullC, hsingleC]
  simpa [pS, hp] using hamp

theorem componentAmplitudeFiberProduct_eq_singleton (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    let full := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    let refined := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
    (∏ C : Component (LocalCoordinates.localSmoothing q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)),
      componentAmplitude q hq full hAux
        ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
          hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
        (outgoingComponentOfLocal q hq S family rootsS A C)) =
    (∏ C : Component (LocalCoordinates.localSmoothing q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)),
      componentAmplitude q hq refined hAux
        (singletonFamily_union_nonalternating q hq S rootsS family hfamily A)
        (outgoingComponentOfLocal q hq S (singletonFamily q family A) rootsS A
          ((singletonLocalComponentEquiv q hq S rootsS family A).symm C))) := by
  classical
  dsimp
  apply Finset.prod_congr rfl
  intro C hC
  exact componentAmplitude_eq_singleton_at_localComponent q hq S rootsS family
    hfamily hRI hAux A C

set_option maxHeartbeats 4000000 in
theorem componentAmplitudeProduct_eq_localFiberProduct (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hAux : auxiliaryGenericity q hq) :
    let full := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    componentAmplitudeProduct q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) =
    ∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      ∏ C : Component (LocalCoordinates.localSmoothing q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)),
        componentAmplitude q hq full hAux
          ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
            hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
          (outgoingComponentOfLocal q hq S family rootsS A C) := by
  classical
  dsimp [componentAmplitudeProduct]
  let full := S.1 ∪ ActualLocalSupports.unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  let pIn := smoothingIncomingPermutation q hq.g2 S.1
  let E := (smoothingComponentEquiv q hq.g2 full).symm.trans
    (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS)
  let β := fun A : Component pIn =>
    Component (LocalCoordinates.localSmoothing q pIn S.1 A (rootsS A) (family A))
  let g := fun z : Σ A, β A =>
    componentAmplitude q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily)
      (outgoingComponentOfLocal q hq S family rootsS z.1 z.2)
  let w := fun c : Component (smoothingDartPermutation q hq.g2 full) =>
    componentAmplitude q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) c
  have hweight : ∀ c, w c = g (E c) := by
    intro c
    have hcomponent : outgoingComponentOfLocal q hq S family rootsS
        (E c).1 (E c).2 = c := by
      change E.symm (E c) = c
      exact Equiv.symm_apply_apply E c
    exact congrArg (fun d => componentAmplitude q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) d) hcomponent.symm
  calc
    (∏ c : Component (smoothingDartPermutation q hq.g2 full), w c) =
        ∏ c, g (E c) := by
          apply Finset.prod_congr rfl
          intro c hc
          exact hweight c
    _ = ∏ z, g z :=
      Fintype.prod_equiv E (fun c => g (E c)) g (by intro c; rfl)
    _ = ∏ A, ∏ C, g ⟨A, C⟩ := Fintype.prod_sigma g
    _ = _ := by rfl

noncomputable def singletonFiberAmplitude (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hAux : auxiliaryGenericity q hq)
    (z : Σ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      Component (LocalCoordinates.localSmoothing q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A))) : ℚ := by
  let A := z.1
  let refined := S.1 ∪ ActualLocalSupports.unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
  exact componentAmplitude q hq refined hAux
    (singletonFamily_union_nonalternating q hq S rootsS family hfamily A)
    (outgoingComponentOfLocal q hq S (singletonFamily q family A) rootsS A
      ((singletonLocalComponentEquiv q hq S rootsS family A).symm z.2))

theorem componentAmplitudeProduct_eq_sigmaSingletonFiber (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    let full := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    componentAmplitudeProduct q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) =
    ∏ z : Σ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      Component (LocalCoordinates.localSmoothing q
        (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)),
      singletonFiberAmplitude q hq S rootsS family hfamily hAux z := by
  classical
  let full := S.1 ∪ ActualLocalSupports.unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
  let pIn := smoothingIncomingPermutation q hq.g2 S.1
  let E := (smoothingComponentEquiv q hq.g2 full).symm.trans
    (LocalCoordinates.actualLocalComponentEquiv q hq.g2 S.1 family rootsS)
  let w := fun c : Component (smoothingDartPermutation q hq.g2 full) =>
    componentAmplitude q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) c
  let g := fun z : Σ A : Component pIn,
      Component (LocalCoordinates.localSmoothing q pIn S.1 A (rootsS A) (family A)) =>
    singletonFiberAmplitude q hq S rootsS family hfamily hAux z
  have hweight : ∀ c, w c = g (E c) := by
    intro c
    have hcomponent : outgoingComponentOfLocal q hq S family rootsS
        (E c).1 (E c).2 = c := by
      change E.symm (E c) = c
      exact Equiv.symm_apply_apply E c
    have hamp := componentAmplitude_eq_singleton_at_localComponent q hq S rootsS family
      hfamily hRI hAux (E c).1 (E c).2
    simpa [w, g, singletonFiberAmplitude, hcomponent] using hamp
  dsimp [componentAmplitudeProduct]
  calc
    (∏ c : Component (smoothingDartPermutation q hq.g2 full), w c) =
        ∏ c, g (E c) := by
          apply Finset.prod_congr rfl
          intro c hc
          exact hweight c
    _ = ∏ z, g z :=
      Fintype.prod_equiv E (fun c => g (E c)) g (by intro c; rfl)
    _ = _ := by rfl

set_option maxHeartbeats 20000000 in
theorem outgoingComponentOfLocal_fiberEquiv (S : Supports q hq)
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1))
    (X : outgoingComponentFiber q hq S family rootsS A) :
    outgoingComponentOfLocal q hq S family rootsS A
      (outgoingComponentFiberEquiv q hq S family rootsS A X) = X.val := by
  let eO := outgoingComponentFiberEquiv q hq S family rootsS A
  change (eO.symm (eO X)).val = X.val
  exact congrArg Subtype.val (Equiv.symm_apply_apply eO X)

set_option maxHeartbeats 20000000 in
theorem daughterComponentAmplitudeProduct_eq_singletonLocalProduct (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq)
    (A : Component (smoothingIncomingPermutation q hq.g2 S.1)) :
    let root := rootEvent q hq S A
    let hroot := rootEvent_retained q hq S A
    let T := daughterSupportForFamily q hq S rootsS family hfamily A
    componentAmplitudeProduct (DaughterFirstReturn.daughterVertex q hq.g2 S.1 root)
      (hAux S.1 S.2 root) T.val
      (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2 root hroot hAux)
      T.property =
    ∏ C : Component (LocalCoordinates.localSmoothing q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 A (rootsS A) (family A)),
      singletonFiberAmplitude q hq S rootsS family hfamily hAux ⟨A, C⟩ := by
  classical
  dsimp only
  let root := rootEvent q hq S A
  let hroot := rootEvent_retained q hq S A
  let T := daughterSupportForFamily q hq S rootsS family hfamily A
  let hD := hAux S.1 S.2 root
  have hAuxD : auxiliaryGenericity (DaughterFirstReturn.daughterVertex q hq.g2 S.1 root) hD :=
    DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2 root hroot hAux
  rw [DaughterNestedWeights.componentAmplitudeProduct_eq_affected q hq S.1 S.2
    root hroot hRI hAux T.val T.property]
  let eA := affectedFinalEquivOutgoingSingletonFiber q hq S rootsS family hfamily A
  let eO := outgoingComponentFiberEquiv q hq S (singletonFamily q family A) rootsS A
  let eL := singletonLocalComponentEquiv q hq S rootsS family A
  let E := eA.trans (eO.trans eL)
  let refined := S.1 ∪ ActualLocalSupports.unionLocal q
    (smoothingIncomingPermutation q hq.g2 S.1) S.1 (singletonFamily q family A)
  have hSupport : DaughterPairingLift.liftedSupport q hq S.1 S.2 root hroot T.val =
      ActualLocalSupports.unionLocal q (smoothingIncomingPermutation q hq.g2 S.1)
        S.1 (singletonFamily q family A) :=
    daughterSupportForFamily_liftedSupport_eq q hq S rootsS family hfamily A
  have hParentNA :=
    (DaughterUnionNonalternation.polygonNonalternating_union_liftedSupport_iff q hq
      S.1 S.2 root hroot T.val).mpr T.property
  have hRefinedNA :=
    (TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
      hq.size_ge_three S.1 S.2 rootsS (singletonFamily q family A)).2
      (singletonFamily_localNonalternating q hq S rootsS family hfamily A)
  have hWholeSupport :
      S.1 ∪ DaughterPairingLift.liftedSupport q hq S.1 S.2 root hroot T.val = refined := by
    dsimp [refined]
    exact congrArg (fun U => S.1 ∪ U) hSupport
  have hCancel (C : DaughterAffectedComponents.AffectedFinal q hq S.1 S.2
      root hroot T.val) :
      eL.symm (E C) = eO (eA C) := by
    dsimp [E]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  refine Fintype.prod_equiv E
    (fun C => componentAmplitude q hq
      (S.1 ∪ DaughterPairingLift.liftedSupport q hq S.1 S.2 root hroot T.val)
      hAux hParentNA C.val)
    (fun z => singletonFiberAmplitude q hq S rootsS family hfamily hAux ⟨A, z⟩)
    ?_
  intro C
  dsimp [singletonFiberAmplitude]
  have hComp : outgoingComponentOfLocal q hq S (singletonFamily q family A)
      rootsS A (eL.symm (E C)) = (eA C).val := by
    rw [hCancel]
    exact outgoingComponentOfLocal_fiberEquiv q hq S
      (singletonFamily q family A) rootsS A (eA C)
  have hAmplitude := componentAmplitude_eq_of_support_eq q hq hParentNA
    hRefinedNA hWholeSupport hAux C.val
  have hTransport :
      (PermutationOrbits.componentEquivOfIntertwining (Equiv.refl _)
        (smoothingDartPermutation q hq.g2
          (S.1 ∪ DaughterPairingLift.liftedSupport q hq S.1 S.2 root hroot T.val))
        (smoothingDartPermutation q hq.g2 refined)
        (by
          have hp := congrArg (smoothingDartPermutation q hq.g2) hWholeSupport
          intro x
          exact congrArg (fun f : Equiv.Perm (PolygonEvent q) => f x) hp)) C.val =
        (eA C).val := by
    exact (affectedFinalEquivOutgoingSingletonFiber_val q hq S rootsS family hfamily A C).symm
  have hTransportToLocal := hTransport.trans hComp.symm
  exact hAmplitude.trans
    (congrArg (fun D => componentAmplitude q hq refined hAux hRefinedNA D)
      hTransportToLocal)

set_option maxHeartbeats 20000000 in
theorem componentAmplitudeProduct_eq_product_daughterProducts (S : Supports q hq)
    (rootsS : LocalCoordinates.ComponentRoots (smoothingIncomingPermutation q hq.g2 S.1))
    (family : ActualLocalSupports.LocalSupports q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1)
    (hfamily : TwoStageRefinement.LocalNonalternating q hq.g2 S.1 rootsS family)
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    let full := S.1 ∪ ActualLocalSupports.unionLocal q
      (smoothingIncomingPermutation q hq.g2 S.1) S.1 family
    componentAmplitudeProduct q hq full hAux
      ((TwoStageRefinement.polygonNonalternating_unionLocal_iff q hq.g2
        hq.size_ge_three S.1 S.2 rootsS family).2 hfamily) =
    ∏ A : Component (smoothingIncomingPermutation q hq.g2 S.1),
      componentAmplitudeProduct (DaughterFirstReturn.daughterVertex q hq.g2 S.1
        (rootEvent q hq S A)) (hAux S.1 S.2 (rootEvent q hq S A))
        (daughterSupportForFamily q hq S rootsS family hfamily A).val
        (DaughterNestedWeights.daughter_auxiliaryGenericity q hq S.1 S.2
          (rootEvent q hq S A) (rootEvent_retained q hq S A) hAux)
        (daughterSupportForFamily q hq S rootsS family hfamily A).property := by
  classical
  dsimp only
  rw [componentAmplitudeProduct_eq_sigmaSingletonFiber q hq S rootsS family
    hfamily hRI hAux]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro A hA
  symm
  exact daughterComponentAmplitudeProduct_eq_singletonLocalProduct q hq S rootsS
    family hfamily hRI hAux A





























end DirectGLSSW.ScalarInversionBridge
