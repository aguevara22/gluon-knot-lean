import DirectGLSSW.SmoothingPermutations
import DirectGLSSW.IndexedInvariantPartition

set_option autoImplicit false

namespace DirectGLSSW.ActualLocalSupports

open Equiv PermutationOrbits IndexedInvariantPartition

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}
variable {q : Fin n → PlanarPoint K}

/-- A crossing outside the current support whose two actual visits belong to one old component. -/
def LocalCrossing (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (A : Component p) :=
  {c : PolygonCrossing q // c ∉ S ∧
    componentOf p (Sum.inr (c, false)) = A ∧
    componentOf p (Sum.inr (c, true)) = A}

/-- One finite local support for every actual old component. -/
def LocalSupports (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) :=
  ∀ A : Component p, Finset (LocalCrossing q p S A)

/-- Crossings contributed by all old component fibres. -/
noncomputable def unionLocal (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) : Finset (PolygonCrossing q) := by
  classical
  exact Finset.univ.biUnion fun A => (family A).image Subtype.val

/-- A set can be assigned to old components exactly when each crossing avoids `S`
and its two actual visits have the same old component label. -/
def EligibleSupport (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S T : Finset (PolygonCrossing q)) : Prop :=
  ∀ c ∈ T, c ∉ S ∧
    componentOf p (Sum.inr (c, false)) = componentOf p (Sum.inr (c, true))

/-- Keep the crossings in `T` inside the old-label fibre `A`. -/
noncomputable def filterByLabel (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S T : Finset (PolygonCrossing q))
    (A : Component p) : Finset (LocalCrossing q p S A) := by
  classical
  letI : Fintype (PolygonCrossing q) := polygonCrossingFintype q
  letI : Fintype (PolygonEvent q) := polygonEventFintype q
  letI : Fintype (Component p) := componentFintype p
  letI : Fintype (LocalCrossing q p S A) :=
    Fintype.subtype (Finset.univ.filter fun c : PolygonCrossing q =>
      c ∉ S ∧ componentOf p (Sum.inr (c, false)) = A ∧
        componentOf p (Sum.inr (c, true)) = A) (by intro c; simp)
  exact Finset.univ.filter fun c => c.val ∈ T

theorem unionLocal_eligible (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) : EligibleSupport q p S (unionLocal q p S family) := by
  classical
  intro c hc
  rcases Finset.mem_biUnion.mp hc with ⟨A, -, hA⟩
  rcases Finset.mem_image.mp hA with ⟨x, hx, rfl⟩
  exact ⟨x.property.1, x.property.2.1.trans x.property.2.2.symm⟩

/-- A crossing from a local family has exactly the component in whose fibre it occurs. -/
theorem unionLocal_mem_label (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) (A : Component p) {c : PolygonCrossing q}
    (hc : c ∈ (family A).image Subtype.val) :
    componentOf p (Sum.inr (c, false)) = A ∧
      componentOf p (Sum.inr (c, true)) = A := by
  rcases Finset.mem_image.mp hc with ⟨x, -, rfl⟩
  exact ⟨x.property.2.1, x.property.2.2⟩

/-- The crossing sets contributed by distinct old labels are disjoint. -/
theorem family_image_disjoint (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) (A B : Component p) (hAB : A ≠ B) :
    Disjoint ((family A).image Subtype.val) ((family B).image Subtype.val) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hcA hcB
  rcases Finset.mem_image.mp hcA with ⟨a, ha, hac⟩
  rcases Finset.mem_image.mp hcB with ⟨b, hb, hbc⟩
  have hlabels : componentOf p (Sum.inr (a.val, false)) =
      componentOf p (Sum.inr (b.val, false)) :=
    congrArg (fun z => componentOf p (Sum.inr (z, false))) (hac.trans hbc.symm)
  have hAB' : A = B := a.property.2.1.symm.trans (hlabels.trans b.property.2.1)
  exact hAB hAB'

/-- The underlying crossing cardinality is the sum of the local family sizes. -/
theorem unionLocal_card (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) :
    (unionLocal q p S family).card = ∑ A : Component p, (family A).card := by
  classical
  have hdisj : (Finset.univ : Finset (Component p)).toSet.PairwiseDisjoint
      (fun A => (family A).image Subtype.val) := by
    intro A hA B hB hAB
    exact family_image_disjoint q p S family A B hAB
  calc
    (unionLocal q p S family).card =
        ∑ A ∈ (Finset.univ : Finset (Component p)),
          ((family A).image Subtype.val).card := by
      unfold unionLocal
      exact Finset.card_biUnion hdisj
    _ = ∑ A : Component p, (family A).card := by
      apply Finset.sum_congr rfl
      intro A hA
      exact Finset.card_image_iff.mpr (by
        intro x hx y hy hxy
        exact Subtype.ext hxy)

theorem filterByLabel_unionLocal (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) (A : Component p) :
    filterByLabel q p S (unionLocal q p S family) A = family A := by
  classical
  ext c
  constructor
  · intro hc
    simp only [filterByLabel, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases Finset.mem_biUnion.mp hc with ⟨B, -, hcB⟩
    rcases Finset.mem_image.mp hcB with ⟨d, hd, hdc⟩
    have hBA : B = A := by
      calc
        B = componentOf p (Sum.inr (d.val, false)) := d.property.2.1.symm
        _ = componentOf p (Sum.inr (c.val, false)) :=
          congrArg (fun z => componentOf p (Sum.inr (z, false))) hdc
        _ = A := c.property.2.1
    cases hBA
    have hdc' : d = c := Subtype.ext hdc
    simpa [hdc'] using hd
  · intro hc
    simp only [filterByLabel, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Finset.mem_biUnion.mpr
    refine ⟨A, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨c, hc, rfl⟩

theorem unionLocal_filterByLabel (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q p S T) :
    unionLocal q p S (filterByLabel q p S T) = T := by
  classical
  ext c
  constructor
  · intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨A, -, hcA⟩
    rcases Finset.mem_image.mp hcA with ⟨x, hx, rfl⟩
    simpa [filterByLabel] using hx
  · intro hcT
    rcases hT c hcT with ⟨hcS, hlabels⟩
    let A : Component p := componentOf p (Sum.inr (c, false))
    let x : LocalCrossing q p S A := ⟨c, hcS, rfl, hlabels.symm⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨A, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, rfl⟩
    simpa [filterByLabel] using hcT


/-- The actual local families are in bijection with eligible crossing supports. -/
noncomputable def familySupportEquiv (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q)) :
    LocalSupports q p S ≃ {T : Finset (PolygonCrossing q) // EligibleSupport q p S T} where
  toFun family := ⟨unionLocal q p S family, unionLocal_eligible q p S family⟩
  invFun T := filterByLabel q p S T.val
  left_inv := by
    intro family
    funext A
    exact filterByLabel_unionLocal q p S family A
  right_inv := by
    intro T
    apply Subtype.ext
    exact unionLocal_filterByLabel q p S T.val T.property

@[simp] theorem familySupportEquiv_apply (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) :
    (familySupportEquiv q p S family).val = unionLocal q p S family := rfl

@[simp] theorem familySupportEquiv_symm_apply (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q p S T) (A : Component p) :
    (familySupportEquiv q p S).symm ⟨T, hT⟩ A = filterByLabel q p S T A := rfl

/-- The old component label of an actual event. -/
def oldLabel (p : Perm (PolygonEvent q)) (x : PolygonEvent q) : Component p :=
  componentOf p x

/-- Eligible visit swaps preserve the old component label pointwise. -/
theorem pairing_preserves_oldLabel (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q p S T) (x : PolygonEvent q) :
    oldLabel p (smoothingPairing q T x) = oldLabel p x := by
  classical
  cases x with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨c, b⟩
      by_cases hc : c ∈ T
      · have hlabels := (hT c hc).2
        cases b <;>
          simp [oldLabel, smoothingPairing, smoothingPairingMap, crossingVisitFlip, hc,
            hlabels]
      · simp [oldLabel, smoothingPairing, smoothingPairingMap, hc]

/-- Eligibility makes the new support disjoint from the support already cut. -/
theorem disjoint_of_eligible (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q p S T) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro c hcS hcT
  exact (hT c hcT).1 hcS

/-- The old labels are invariant under the actual incoming permutation after insertion. -/
theorem incoming_preserves_oldLabel (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T)
    (x : PolygonEvent q) :
    oldLabel (smoothingIncomingPermutation q hq S)
      (smoothingIncomingPermutation q hq (S ∪ T) x) =
    oldLabel (smoothingIncomingPermutation q hq S) x := by
  let pS := smoothingIncomingPermutation q hq S
  have hST : Disjoint S T := disjoint_of_eligible q pS S T hT
  rw [smoothingIncomingPermutation_union q hq S T hST]
  simp only [oldLabel, Equiv.Perm.mul_apply, componentOf_apply]
  exact pairing_preserves_oldLabel q pS S T hT x

/-- Pairing restricted to one exact old successor fibre. -/
noncomputable def restrictedPairing (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q p S T) (A : Component p) : Perm (Fibre p A) :=
  PermutationOrbits.restrictPerm (smoothingPairing q T)
    {x : PolygonEvent q | componentOf p x = A}
    (fun x => by
      change oldLabel p x = A ↔ oldLabel p (smoothingPairing q T x) = A
      rw [pairing_preserves_oldLabel q p S T hT x])

/-- Restrict the post-insertion successor to one exact old fibre. -/
noncomputable def restrictedIncoming (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T)
    (A : Component (smoothingIncomingPermutation q hq S)) : Perm (Fibre
      (smoothingIncomingPermutation q hq S) A) :=
  PermutationOrbits.restrictPerm (smoothingIncomingPermutation q hq (S ∪ T))
    {x : PolygonEvent q | componentOf (smoothingIncomingPermutation q hq S) x = A}
    (fun x => by
      change oldLabel (smoothingIncomingPermutation q hq S) x = A ↔
        oldLabel (smoothingIncomingPermutation q hq S)
          (smoothingIncomingPermutation q hq (S ∪ T) x) = A
      rw [incoming_preserves_oldLabel q hq S T hT x])

/-- On each old fibre, the new actual successor is the old successor after
its restricted actual visit pairing. -/
theorem restrictedIncoming_eq (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T)
    (A : Component (smoothingIncomingPermutation q hq S)) :
    restrictedIncoming q hq S T hT A =
      fibrePerm (smoothingIncomingPermutation q hq S) A *
        restrictedPairing q (smoothingIncomingPermutation q hq S) S T hT A := by
  let pS := smoothingIncomingPermutation q hq S
  let pST := smoothingIncomingPermutation q hq (S ∪ T)
  ext x
  apply Subtype.ext
  change smoothingIncomingPermutation q hq (S ∪ T) x.val = pS (smoothingPairing q T x.val)
  rw [smoothingIncomingPermutation_union q hq S T
    (disjoint_of_eligible q pS S T hT)]
  rfl

/-- The accepted indexed quotient decomposition applied to actual old labels. -/
noncomputable def actualPartitionEquiv (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T) :
    Component (smoothingIncomingPermutation q hq (S ∪ T)) ≃
      Σ A : Component (smoothingIncomingPermutation q hq S),
        Component (indexRestrictedPerm
          (smoothingIncomingPermutation q hq (S ∪ T))
          (oldLabel (smoothingIncomingPermutation q hq S))
          (incoming_preserves_oldLabel q hq S T hT) A) :=
  indexedComponentEquiv (smoothingIncomingPermutation q hq (S ∪ T))
    (oldLabel (smoothingIncomingPermutation q hq S))
    (incoming_preserves_oldLabel q hq S T hT)

@[simp] theorem actualPartitionEquiv_componentOf (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T)
    (x : PolygonEvent q) :
    actualPartitionEquiv q hq S T hT
      (componentOf (smoothingIncomingPermutation q hq (S ∪ T)) x) =
      ⟨oldLabel (smoothingIncomingPermutation q hq S) x,
        componentOf (indexRestrictedPerm
          (smoothingIncomingPermutation q hq (S ∪ T))
          (oldLabel (smoothingIncomingPermutation q hq S))
          (incoming_preserves_oldLabel q hq S T hT)
          (oldLabel (smoothingIncomingPermutation q hq S) x))
          ⟨x, rfl⟩⟩ := by
  exact indexedComponentEquiv_componentOf
    (smoothingIncomingPermutation q hq (S ∪ T))
    (oldLabel (smoothingIncomingPermutation q hq S))
    (incoming_preserves_oldLabel q hq S T hT) x

@[simp] theorem actualPartitionEquiv_symm_componentOf (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T)
    (A : Component (smoothingIncomingPermutation q hq S))
    (x : indexFiber (oldLabel (smoothingIncomingPermutation q hq S)) A) :
    (actualPartitionEquiv q hq S T hT).symm
      ⟨A, componentOf
        (indexRestrictedPerm (smoothingIncomingPermutation q hq (S ∪ T))
          (oldLabel (smoothingIncomingPermutation q hq S))
          (incoming_preserves_oldLabel q hq S T hT) A) x⟩ =
      componentOf (smoothingIncomingPermutation q hq (S ∪ T)) x.val := by
  exact indexedComponentEquiv_symm_componentOf
    (smoothingIncomingPermutation q hq (S ∪ T))
    (oldLabel (smoothingIncomingPermutation q hq S))
    (incoming_preserves_oldLabel q hq S T hT) A x

/-- Finite component counts split across exactly all old actual labels. -/
theorem componentCount_actualPartition (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T) :
    componentCount (smoothingIncomingPermutation q hq (S ∪ T)) =
      ∑ A : Component (smoothingIncomingPermutation q hq S),
        componentCount (indexRestrictedPerm
          (smoothingIncomingPermutation q hq (S ∪ T))
          (oldLabel (smoothingIncomingPermutation q hq S))
          (incoming_preserves_oldLabel q hq S T hT) A) := by
  exact componentCount_indexedInvariantPartition
    (smoothingIncomingPermutation q hq (S ∪ T))
    (oldLabel (smoothingIncomingPermutation q hq S))
    (incoming_preserves_oldLabel q hq S T hT)

end DirectGLSSW.ActualLocalSupports
