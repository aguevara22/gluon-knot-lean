import DirectGLSSW.LocalCoordinates

set_option autoImplicit false

namespace DirectGLSSW.TwoStageRefinement

open ActualLocalSupports LocalCoordinates PolygonNonalternation
open PermutationOrbits

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}
variable (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)

private noncomputable abbrev incoming (S : Finset (PolygonCrossing q)) :=
  smoothingIncomingPermutation q hq S

private abbrev globallyNA (S : Finset (PolygonCrossing q)) :=
  polygonNonalternating q hq S

/-- The strict chord nonalternation predicate on each actual old-component fibre. -/
def LocalNonalternating (S : Finset (PolygonCrossing q))
    (roots : ComponentRoots (incoming q hq S))
    (family : LocalSupports q (incoming q hq S) S) : Prop :=
  ∀ A : Component (incoming q hq S),
    ChordNonalternation.Nonalternating
      (localEndpoint q (incoming q hq S) S A (roots A)) (family A)

theorem localNonalternating_rootSelector_iff
    (S : Finset (PolygonCrossing q))
    (roots₁ roots₂ : ComponentRoots (incoming q hq S))
    (family : LocalSupports q (incoming q hq S) S) :
    LocalNonalternating q hq S roots₁ family ↔
      LocalNonalternating q hq S roots₂ family := by
  constructor
  · intro h A
    exact (local_nonalternating_root_independent q (incoming q hq S) S family A
      (roots₁ A) (roots₂ A)).mp (h A)
  · intro h A
    exact (local_nonalternating_root_independent q (incoming q hq S) S family A
      (roots₁ A) (roots₂ A)).mpr (h A)

theorem polygonNonalternating_unionLocal_iff
    (hn : 3 ≤ n) (S : Finset (PolygonCrossing q))
    (hS : globallyNA q hq S)
    (roots : ComponentRoots (incoming q hq S))
    (family : LocalSupports q (incoming q hq S) S) :
    globallyNA q hq (S ∪ unionLocal q (incoming q hq S) S family) ↔
      LocalNonalternating q hq S roots family := by
  classical
  let pS := incoming q hq S
  let T := unionLocal q pS S family
  have hT : EligibleSupport q pS S T :=
    unionLocal_eligible q pS S family
  have hdisj : Disjoint S T := disjoint_of_eligible q pS S T hT
  have hSCount : componentCount pS = S.card + 1 :=
    (polygonNonalternating_iff_incoming_count q hq hn S).mp hS
  have hsumOnes : (∑ _A : Component pS, (1 : ℕ)) = componentCount pS := by
    simp [componentCount]
  have hcountRhs : (S ∪ T).card + 1 =
      ∑ A : Component pS, ((family A).card + 1) := by
    rw [Finset.card_union_of_disjoint hdisj, unionLocal_card]
    rw [Finset.sum_add_distrib, hsumOnes]
    omega
  have hcount : componentCount (incoming q hq (S ∪ T)) =
      ∑ A : Component pS,
        componentCount (localSmoothing q pS S A (roots A) (family A)) := by
    exact componentCount_actualLocalComponentEquiv q hq S family roots
  change polygonNonalternating q hq (S ∪ T) ↔
    LocalNonalternating q hq S roots family
  rw [polygonNonalternating_iff_incoming_count q hq hn (S ∪ T), hcount, hcountRhs]
  have hbounds : ∀ A : Component pS,
      componentCount (localSmoothing q pS S A (roots A) (family A)) ≤
        (family A).card + 1 := by
    intro A
    exact localSmoothing_componentCount_le q pS S A (roots A) (family A)
  have hsum := Finset.sum_eq_sum_iff_of_le
    (s := (Finset.univ : Finset (Component pS)))
    (f := fun A => componentCount (localSmoothing q pS S A (roots A) (family A)))
    (g := fun A => (family A).card + 1)
    (fun A _ => hbounds A)
  constructor
  · intro h A
    have hAll := hsum.mp h
    exact (local_nonalternating_iff_componentCount q pS S A (roots A)
      (family A)).mpr (hAll A (Finset.mem_univ A))
  · intro h
    apply hsum.mpr
    intro A hA
    exact (local_nonalternating_iff_componentCount q pS S A (roots A)
      (family A)).mp (h A)

theorem eligibleSupport_sdiff
    (S U : Finset (PolygonCrossing q))
    (hU : globallyNA q hq U) (hSU : S ⊆ U) :
    EligibleSupport q (incoming q hq S) S (U \ S) := by
  intro c hc
  rcases Finset.mem_sdiff.mp hc with ⟨hcU, hcS⟩
  have hinsert : insert c S ⊆ U := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hdS
    · exact hcU
    · exact hSU hdS
  have hNA : globallyNA q hq (insert c S) :=
    polygonNonalternating_mono q hq hU hinsert
  have hcycle := incoming_sameCycle_before_insert q hq S c hcS hNA
  exact ⟨hcS, (componentOf_eq_iff (incoming q hq S)
    (Sum.inr (c, false)) (Sum.inr (c, true))).2 hcycle⟩

noncomputable def fixedSupportEquiv
    (hn : 3 ≤ n) (S : Finset (PolygonCrossing q))
    (hS : globallyNA q hq S)
    (roots : ComponentRoots (incoming q hq S)) :
    {family : LocalSupports q (incoming q hq S) S //
      LocalNonalternating q hq S roots family} ≃
    {U : Finset (PolygonCrossing q) // S ⊆ U ∧ globallyNA q hq U} where
  toFun family := by
    let T := unionLocal q (incoming q hq S) S family.val
    have hNA := (polygonNonalternating_unionLocal_iff q hq hn S hS roots
      family.val).mpr family.property
    exact ⟨S ∪ T, ⟨Finset.subset_union_left, hNA⟩⟩
  invFun U := by
    let hEligible := eligibleSupport_sdiff q hq S U U.property.2 U.property.1
    let family := filterByLabel q (incoming q hq S) S (U.val \ S)
    have hUnion : S ∪ unionLocal q (incoming q hq S) S family = U.val := by
      rw [unionLocal_filterByLabel q (incoming q hq S) S (U.val \ S) hEligible]
      exact Finset.union_sdiff_of_subset U.property.1
    have hNA : globallyNA q hq (S ∪ unionLocal q (incoming q hq S) S family) := by
      rw [hUnion]
      exact U.property.2
    have hLocal := (polygonNonalternating_unionLocal_iff q hq hn S hS roots
      family).mp hNA
    exact ⟨family, hLocal⟩
  left_inv := by
    rintro ⟨family, hLocal⟩
    apply Subtype.ext
    funext A
    let hEligible := unionLocal_eligible q (incoming q hq S) S family
    have hDisjoint := disjoint_of_eligible q (incoming q hq S) S
      (unionLocal q (incoming q hq S) S family) hEligible
    change filterByLabel q (incoming q hq S) S
      ((S ∪ unionLocal q (incoming q hq S) S family) \ S) A = family A
    rw [Finset.union_sdiff_cancel_left hDisjoint]
    exact filterByLabel_unionLocal q (incoming q hq S) S family A
  right_inv := by
    rintro ⟨U, hSU, hU⟩
    apply Subtype.ext
    change S ∪ unionLocal q (incoming q hq S) S
      (filterByLabel q (incoming q hq S) S (U \ S)) = U
    rw [unionLocal_filterByLabel q (incoming q hq S) S (U \ S)
      (eligibleSupport_sdiff q hq S U hU hSU)]
    exact Finset.union_sdiff_of_subset hSU

@[simp] theorem fixedSupportEquiv_apply_val
    (hn : 3 ≤ n) (S : Finset (PolygonCrossing q))
    (hS : globallyNA q hq S) (roots : ComponentRoots (incoming q hq S))
    (family : LocalSupports q (incoming q hq S) S)
    (hfamily : LocalNonalternating q hq S roots family) :
    (fixedSupportEquiv q hq hn S hS roots ⟨family, hfamily⟩).val =
      S ∪ unionLocal q (incoming q hq S) S family := rfl

@[simp] theorem fixedSupportEquiv_symm_apply_val
    (hn : 3 ≤ n) (S : Finset (PolygonCrossing q))
    (hS : globallyNA q hq S) (roots : ComponentRoots (incoming q hq S))
    (U : Finset (PolygonCrossing q)) (hSU : S ⊆ U) (hU : globallyNA q hq U) :
    ((fixedSupportEquiv q hq hn S hS roots).symm ⟨U, ⟨hSU, hU⟩⟩).val =
      filterByLabel q (incoming q hq S) S (U \ S) := rfl

theorem fixedSupportEquiv_left_inverse_eval
    (hn : 3 ≤ n) (S : Finset (PolygonCrossing q))
    (hS : globallyNA q hq S) (roots : ComponentRoots (incoming q hq S))
    (family : LocalSupports q (incoming q hq S) S)
    (hfamily : LocalNonalternating q hq S roots family) :
    ((fixedSupportEquiv q hq hn S hS roots).symm
      (fixedSupportEquiv q hq hn S hS roots ⟨family, hfamily⟩)).val = family := by
  exact congrArg Subtype.val
    ((fixedSupportEquiv q hq hn S hS roots).left_inv ⟨family, hfamily⟩)

theorem fixedSupportEquiv_right_inverse_eval
    (hn : 3 ≤ n) (S : Finset (PolygonCrossing q))
    (hS : globallyNA q hq S) (roots : ComponentRoots (incoming q hq S))
    (U : Finset (PolygonCrossing q)) (hSU : S ⊆ U) (hU : globallyNA q hq U) :
    (fixedSupportEquiv q hq hn S hS roots
      ((fixedSupportEquiv q hq hn S hS roots).symm ⟨U, ⟨hSU, hU⟩⟩)).val = U := by
  exact congrArg Subtype.val
    ((fixedSupportEquiv q hq hn S hS roots).right_inv ⟨U, ⟨hSU, hU⟩⟩)

/-- The local size sum counts exactly the support outside the first stage. -/
theorem filteredFamily_card_sum
    (S U : Finset (PolygonCrossing q))
    (hS : globallyNA q hq S) (hU : globallyNA q hq U) (hSU : S ⊆ U) :
    (∑ A : Component (incoming q hq S),
      (filterByLabel q (incoming q hq S) S (U \ S) A).card) = U.card - S.card := by
  classical
  have hEligible := eligibleSupport_sdiff q hq S U hU hSU
  rw [← unionLocal_card q (incoming q hq S) S (filterByLabel q (incoming q hq S) S (U \ S))]
  rw [unionLocal_filterByLabel q (incoming q hq S) S (U \ S) hEligible]
  exact Finset.card_sdiff hSU

private abbrev NonalternatingSupport :=
  {S : Finset (PolygonCrossing q) // globallyNA q hq S}

private abbrev LocalSuperset (s : NonalternatingSupport q hq) :=
  {U : Finset (PolygonCrossing q) // s.val ⊆ U ∧ globallyNA q hq U}

private noncomputable def supportPairEquiv :
    (Σ s : NonalternatingSupport q hq, LocalSuperset q hq s) ≃
      (Σ u : NonalternatingSupport q hq,
        {s : Finset (PolygonCrossing q) // s ⊆ u.val}) where
  toFun x := ⟨⟨x.2.val, x.2.property.2⟩, ⟨x.1.val, x.2.property.1⟩⟩
  invFun y :=
    ⟨⟨y.2.val,
      polygonNonalternating_mono q hq y.1.property y.2.property⟩,
      ⟨y.1.val, ⟨y.2.property, y.1.property⟩⟩⟩
  left_inv := by
    rintro ⟨⟨S, hS⟩, ⟨U, hSU, hU⟩⟩
    dsimp
  right_inv := by
    rintro ⟨⟨U, hU⟩, ⟨S, hSU⟩⟩
    dsimp

private abbrev RootedLocalFamily (roots : ∀ s : NonalternatingSupport q hq,
    ComponentRoots (incoming q hq s.val)) (s : NonalternatingSupport q hq) :=
  {family : LocalSupports q (incoming q hq s.val) s.val //
    LocalNonalternating q hq s.val (roots s) family}

set_option maxHeartbeats 1000000 in
noncomputable def twoStageSupportEquiv
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val)) :
    (Σ s : NonalternatingSupport q hq, RootedLocalFamily q hq roots s) ≃
      (Σ u : NonalternatingSupport q hq,
        {s : Finset (PolygonCrossing q) // s ⊆ u.val}) :=
  let fibers : ∀ s : NonalternatingSupport q hq,
      RootedLocalFamily q hq roots s ≃ LocalSuperset q hq s :=
    fun s => fixedSupportEquiv q hq hn s.val s.property (roots s)
  (Equiv.sigmaCongrRight fibers).trans (supportPairEquiv q hq)

@[simp] theorem twoStageSupportEquiv_apply_support
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (x : Σ s : NonalternatingSupport q hq, RootedLocalFamily q hq roots s) :
    (twoStageSupportEquiv q hq hn roots x).1.val =
      x.1.val ∪ unionLocal q (incoming q hq x.1.val) x.1.val x.2.val := by
  rfl

@[simp] theorem twoStageSupportEquiv_apply_firstStage
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (x : Σ s : NonalternatingSupport q hq, RootedLocalFamily q hq roots s) :
    (twoStageSupportEquiv q hq hn roots x).2.val = x.1.val := by
  rfl

theorem twoStageSupportEquiv_left_inverse
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (x : Σ s : NonalternatingSupport q hq, RootedLocalFamily q hq roots s) :
    (twoStageSupportEquiv q hq hn roots).symm
      (twoStageSupportEquiv q hq hn roots x) = x := by
  exact (twoStageSupportEquiv q hq hn roots).left_inv x

theorem twoStageSupportEquiv_right_inverse
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (y : Σ u : NonalternatingSupport q hq,
      {s : Finset (PolygonCrossing q) // s ⊆ u.val}) :
    twoStageSupportEquiv q hq hn roots
      ((twoStageSupportEquiv q hq hn roots).symm y) = y := by
  exact (twoStageSupportEquiv q hq hn roots).right_inv y

@[simp] theorem twoStageSupportEquiv_symm_firstStage
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (y : Σ u : NonalternatingSupport q hq,
      {s : Finset (PolygonCrossing q) // s ⊆ u.val}) :
    ((twoStageSupportEquiv q hq hn roots).symm y).1.val = y.2.val := by
  rfl

@[simp] theorem twoStageSupportEquiv_symm_family
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (y : Σ u : NonalternatingSupport q hq,
      {s : Finset (PolygonCrossing q) // s ⊆ u.val}) :
    ((twoStageSupportEquiv q hq hn roots).symm y).2.val =
      filterByLabel q (incoming q hq ((twoStageSupportEquiv q hq hn roots).symm y).1.val)
        ((twoStageSupportEquiv q hq hn roots).symm y).1.val
        (y.1.val \ ((twoStageSupportEquiv q hq hn roots).symm y).1.val) := by
  rfl

private noncomputable abbrev secondStageFamily
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val}) :=
  filterByLabel q (incoming q hq s.val) s.val (u.val \ s.val)

/-- The filtered second-stage family reconstructs exactly the final support. -/
theorem secondStage_reconstruct
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val}) :
    s.val ∪ unionLocal q (incoming q hq s.val) s.val
      (secondStageFamily q hq u s) = u.val := by
  have hEligible := eligibleSupport_sdiff q hq s.val u.val u.property s.property
  rw [unionLocal_filterByLabel q (incoming q hq s.val) s.val (u.val \ s.val) hEligible]
  exact Finset.union_sdiff_of_subset s.property

/-- Casting the orbit quotient along an equality of permutations preserves representatives. -/
private theorem castComponentOf_eq
    {α : Type*} (p₁ p₂ : Equiv.Perm α) (h : p₁ = p₂) (x : α) :
    (Equiv.cast (congrArg (fun p : Equiv.Perm α => Component p) h)).symm
        (componentOf p₂ x) = componentOf p₁ x := by
  cases h
  rfl

private theorem castComponentOf_eq_symm
    {α : Type*} (p₁ p₂ : Equiv.Perm α) (h : p₁ = p₂) (x : α) :
    Equiv.cast (congrArg (fun p : Equiv.Perm α => Component p) h)
        (componentOf p₁ x) = componentOf p₂ x := by
  cases h
  rfl

/-- The actual-local component correspondence, expressed on the final support U. -/
noncomputable def finalUSupportComponentEquiv
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val}) :
    Component (incoming q hq u.val) ≃
      Σ A : Component (incoming q hq s.val),
        Component (localSmoothing q (incoming q hq s.val) s.val A
          (roots ⟨s.val,
            polygonNonalternating_mono q hq u.property s.property⟩ A)
          (secondStageFamily q hq u s A)) := by
  classical
  let pS := incoming q hq s.val
  let family := secondStageFamily q hq u s
  have hrec : s.val ∪ unionLocal q pS s.val family = u.val :=
    secondStage_reconstruct q hq u s
  let hperm : incoming q hq (s.val ∪ unionLocal q pS s.val family) =
      incoming q hq u.val := congrArg (incoming q hq) hrec
  let hcomp : Component (incoming q hq (s.val ∪ unionLocal q pS s.val family)) =
      Component (incoming q hq u.val) :=
    congrArg (fun p : Equiv.Perm (PolygonEvent q) => Component p) hperm
  let actual := actualLocalComponentEquiv q hq s.val family
    (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩)
  exact
    { toFun := fun c => actual ((Equiv.cast hcomp).symm c)
      invFun := fun y => Equiv.cast hcomp (actual.symm y)
      left_inv := by
        intro c
        simp
      right_inv := by
        intro y
        simp }

theorem finalUSupportComponentEquiv_apply
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val})
    (x : Component (incoming q hq u.val)) :
    finalUSupportComponentEquiv q hq hn roots u s x =
      actualLocalComponentEquiv q hq s.val (secondStageFamily q hq u s)
        (roots ⟨s.val,
          polygonNonalternating_mono q hq u.property s.property⟩)
        ((Equiv.cast (congrArg
          (fun p : Equiv.Perm (PolygonEvent q) => Component p)
          (congrArg (incoming q hq) (secondStage_reconstruct q hq u s))).symm) x) := by
  rfl

theorem finalUSupportComponentEquiv_symm_apply
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val})
    (x : Σ A : Component (incoming q hq s.val),
      Component (localSmoothing q (incoming q hq s.val) s.val A
        (roots ⟨s.val,
          polygonNonalternating_mono q hq u.property s.property⟩ A)
        (secondStageFamily q hq u s A))) :
    (finalUSupportComponentEquiv q hq hn roots u s).symm x =
      Equiv.cast (congrArg
        (fun p : Equiv.Perm (PolygonEvent q) => Component p)
        (congrArg (incoming q hq) (secondStage_reconstruct q hq u s)))
        ((actualLocalComponentEquiv q hq s.val (secondStageFamily q hq u s)
          (roots ⟨s.val,
            polygonNonalternating_mono q hq u.property s.property⟩)).symm x) := by
  rfl

@[simp] theorem finalUSupportComponentEquiv_componentOf
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val})
    (x : PolygonEvent q) :
    let pS := incoming q hq s.val
    let family := secondStageFamily q hq u s
    let A := componentOf pS x
    let i := (rootedEnumeration pS
      (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩ A)).symm
      ⟨x, rfl⟩
    finalUSupportComponentEquiv q hq hn roots u s
        (componentOf (incoming q hq u.val) x) =
      ⟨A, componentOf (localSmoothing q pS s.val A
        (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩ A)
        (family A)) i⟩ := by
  classical
  let pS := incoming q hq s.val
  let family := secondStageFamily q hq u s
  let pC := incoming q hq (s.val ∪ unionLocal q pS s.val family)
  have hrec : s.val ∪ unionLocal q pS s.val family = u.val :=
    secondStage_reconstruct q hq u s
  have hperm : pC = incoming q hq u.val := congrArg (incoming q hq) hrec
  simp only [finalUSupportComponentEquiv_apply]
  have hcast := castComponentOf_eq pC (incoming q hq u.val) hperm x
  simp only [Equiv.cast_symm] at hcast
  rw [hcast]
  exact actualLocalComponentEquiv_componentOf q hq s.val family
    (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩) x

@[simp] theorem finalUSupportComponentEquiv_symm_componentOf
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val})
    (A : Component (incoming q hq s.val))
    (i : Fin (Fintype.card (Fibre (incoming q hq s.val) A))) :
    (finalUSupportComponentEquiv q hq hn roots u s).symm
      ⟨A, componentOf (localSmoothing q (incoming q hq s.val) s.val A
        (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩ A)
        (secondStageFamily q hq u s A)) i⟩ =
    componentOf (incoming q hq u.val)
      ((rootedEnumeration (incoming q hq s.val)
        (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩ A) i).val) := by
  classical
  let pS := incoming q hq s.val
  let family := secondStageFamily q hq u s
  let pC := incoming q hq (s.val ∪ unionLocal q pS s.val family)
  have hrec : s.val ∪ unionLocal q pS s.val family = u.val :=
    secondStage_reconstruct q hq u s
  have hperm : pC = incoming q hq u.val := congrArg (incoming q hq) hrec
  rw [finalUSupportComponentEquiv_symm_apply]
  rw [actualLocalComponentEquiv_symm_componentOf]
  exact castComponentOf_eq_symm pC (incoming q hq u.val) hperm
    ((rootedEnumeration pS
      (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩ A) i).val)

theorem finalUSupportComponentEquiv_componentCount
    (hn : 3 ≤ n)
    (roots : ∀ s : NonalternatingSupport q hq,
      ComponentRoots (incoming q hq s.val))
    (u : NonalternatingSupport q hq)
    (s : {S : Finset (PolygonCrossing q) // S ⊆ u.val}) :
    componentCount (incoming q hq u.val) =
      ∑ A : Component (incoming q hq s.val),
        componentCount (localSmoothing q (incoming q hq s.val) s.val A
          (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩ A)
          (secondStageFamily q hq u s A)) := by
  have hrec := secondStage_reconstruct q hq u s
  rw [← congrArg (incoming q hq) hrec]
  exact componentCount_actualLocalComponentEquiv q hq s.val
    (secondStageFamily q hq u s)
    (roots ⟨s.val, polygonNonalternating_mono q hq u.property s.property⟩)


end DirectGLSSW.TwoStageRefinement
