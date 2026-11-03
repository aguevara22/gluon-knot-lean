import DirectGLSSW.ActualLocalSupports
import DirectGLSSW.PolygonNonalternation
import DirectGLSSW.ChordNonalternation
import DirectGLSSW.OrbitNormalization

set_option autoImplicit false

/-!
# Local cyclic coordinates

Finite-event prerequisites sourced from `reference/direct_glssw_corner_proof.tex`,
`lem:inversion` and the two-stage refinement discussion at lines 744–750.
These prerequisites do not prove the source inversion. The scope covers local
visit swaps, quotient representatives, and the exact finite count bound; it
does not establish daughter geometry, scalar GLSSW root independence, an
inversion identity, or a HOMFLY identity.
-/
namespace DirectGLSSW.LocalCoordinates

open Equiv PermutationOrbits ActualLocalSupports

attribute [local instance] Classical.propDecidable

universe u
variable {α : Type u}

abbrev ComponentRoots {β : Type*} (p : Perm β) :=
  ∀ A : Component p, Fibre p A

/-- Re-root an accepted cycle enumeration at an explicit point of a named fibre. -/
noncomputable def rootedEnumeration [Fintype α] (p : Perm α)
    {A : Component p} (xA : Fibre p A) :
    Fin (Fintype.card (Fibre p A)) ≃ Fibre p A := by
  let hA : componentOf p xA.val = A := xA.property
  let hf : Fibre p (componentOf p xA.val) = Fibre p A := congrArg (Fibre p) hA
  let hc : Fintype.card (Fibre p (componentOf p xA.val)) = Fintype.card (Fibre p A) :=
    Fintype.card_congr (Equiv.cast hf)
  let hcf : Fin (Fintype.card (Fibre p (componentOf p xA.val))) =
      Fin (Fintype.card (Fibre p A)) := congrArg Fin hc
  exact (Equiv.cast hcf).symm.trans (orbitEnumeration p xA.val) |>.trans (Equiv.cast hf)

theorem rootedEnumeration_successor [Fintype α] (p : Perm α)
    {A : Component p} (xA : Fibre p A)
    (i : Fin (Fintype.card (Fibre p A))) :
    rootedEnumeration p xA (cyclicSuccessorPerm (Fintype.card (Fibre p A)) i) =
      fibrePerm p A (rootedEnumeration p xA i) := by
  rcases xA with ⟨x, hx⟩
  subst A
  simpa [rootedEnumeration] using orbitEnumeration_successor p x i

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- Lift a local crossing visit to its exact old component fibre. -/
def localVisitLift (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (A : Component p)
    (c : LocalCrossing q p S A) : Bool → Fibre p A
  | false => ⟨Sum.inr (c.val, false), c.property.2.1⟩
  | true => ⟨Sum.inr (c.val, true), c.property.2.2⟩

/-- Normalize actual local visits with a chosen root of the old fibre. -/
noncomputable def localEndpoint (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (A : Component p) (xA : Fibre p A) :
    LocalCrossing q p S A × Bool → Fin (Fintype.card (Fibre p A)) :=
  fun z => (rootedEnumeration p xA).symm (localVisitLift q p S A z.1 z.2)

theorem localEndpoint_injective (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (A : Component p) (xA : Fibre p A) :
    Function.Injective (localEndpoint q p S A xA) := by
  intro z w h
  rcases z with ⟨c, b⟩
  rcases w with ⟨d, e⟩
  have h' := congrArg (rootedEnumeration p xA) h
  simp only [localEndpoint, Equiv.apply_symm_apply] at h'
  have hsum := congrArg Subtype.val h'
  cases b <;> cases e
  · change Sum.inr (c.val, false) = Sum.inr (d.val, false) at hsum
    have hp := Sum.inr.inj hsum
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) rfl
  · change Sum.inr (c.val, false) = Sum.inr (d.val, true) at hsum
    have hp := Sum.inr.inj hsum
    exact False.elim (Bool.noConfusion (congrArg Prod.snd hp))
  · change Sum.inr (c.val, true) = Sum.inr (d.val, false) at hsum
    have hp := Sum.inr.inj hsum
    exact False.elim (Bool.noConfusion (congrArg Prod.snd hp))
  · change Sum.inr (c.val, true) = Sum.inr (d.val, true) at hsum
    have hp := Sum.inr.inj hsum
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) rfl


theorem rootedEnumeration_swap (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (A : Component p) (xA : Fibre p A)
    (c : LocalCrossing q p S A)
    (i : Fin (Fintype.card (Fibre p A))) :
    (rootedEnumeration p xA
      (Equiv.swap (localEndpoint q p S A xA (c, false))
        (localEndpoint q p S A xA (c, true)) i)).val =
      smoothingPairing q {c.val} (rootedEnumeration p xA i).val := by
  letI : DecidableEq (PolygonEvent q) := by
    unfold PolygonEvent
    infer_instance
  rw [smoothingPairing_singleton]
  have h0 : (rootedEnumeration p xA
      (localEndpoint q p S A xA (c, false))).val = Sum.inr (c.val, false) := by
    simp [localEndpoint, localVisitLift]
  have h1 : (rootedEnumeration p xA
      (localEndpoint q p S A xA (c, true))).val = Sum.inr (c.val, true) := by
    simp [localEndpoint, localVisitLift]
  have he : Function.Injective
      (fun j : Fin (Fintype.card (Fibre p A)) => (rootedEnumeration p xA j).val) :=
    Subtype.val_injective.comp (rootedEnumeration p xA).injective
  have hmap := he.map_swap
    (localEndpoint q p S A xA (c, false))
    (localEndpoint q p S A xA (c, true)) i
  simpa only [h0, h1] using hmap

theorem localSwapProduct_actual_intertwines (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (A : Component p) (xA : Fibre p A)
    (L : Finset (LocalCrossing q p S A))
    (he : Function.Injective (localEndpoint q p S A xA))
    (i : Fin (Fintype.card (Fibre p A))) :
    (rootedEnumeration p xA
      (ChordNonalternation.swapProduct (localEndpoint q p S A xA) he L i)).val =
      smoothingPairing q (L.image Subtype.val) (rootedEnumeration p xA i).val := by
  classical
  letI : DecidableEq (LocalCrossing q p S A) := Classical.decEq _
  induction L using Finset.induction_on with
  | empty => simp [ChordNonalternation.swapProduct_empty, smoothingPairing_empty]
  | @insert c L hc ih =>
      have hc' : c.val ∉ L.image Subtype.val := by
        intro hm
        rcases Finset.mem_image.mp hm with ⟨d, hd, hdc⟩
        exact hc (Subtype.ext hdc ▸ hd)
      rw [ChordNonalternation.swapProduct_insert (localEndpoint q p S A xA) he L c hc,
        Equiv.Perm.mul_apply]
      rw [Finset.image_insert]
      rw [PolygonNonalternation.smoothingPairing_insert q (L.image Subtype.val) c.val hc']
      rw [Equiv.Perm.mul_apply]
      change (rootedEnumeration p xA
        (Equiv.swap (localEndpoint q p S A xA (c, false))
          (localEndpoint q p S A xA (c, true))
          (ChordNonalternation.swapProduct (localEndpoint q p S A xA) he L i))).val = _
      rw [rootedEnumeration_swap q p S A xA c
        (ChordNonalternation.swapProduct (localEndpoint q p S A xA) he L i)]
      rw [ih]


theorem smoothingPairing_unionLocal_eq_localImage_on_fibre
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (family : LocalSupports q p S)
    (A : Component p) (x : Fibre p A) :
    smoothingPairing q (unionLocal q p S family) x.val =
      smoothingPairing q ((family A).image Subtype.val) x.val := by
  classical
  cases hx : x.val with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨c, b⟩
      have hlabel : componentOf p (Sum.inr (c, b)) = A := by
        simpa [hx] using x.property
      have hm : c ∈ unionLocal q p S family ↔
          c ∈ (family A).image Subtype.val := by
        constructor
        · intro hc
          rcases Finset.mem_biUnion.mp hc with ⟨B, -, hB⟩
          have hlabels := unionLocal_mem_label q p S family B hB
          have hBA : B = A := by
            cases b
            · exact hlabels.1.symm.trans hlabel
            · exact hlabels.2.symm.trans hlabel
          subst B
          rcases Finset.mem_image.mp hB with ⟨d, hd, hdc⟩
          exact Finset.mem_image.mpr ⟨d, hd, hdc⟩
        · intro hc
          exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_univ _, hc⟩
      cases b <;> simp [smoothingPairing_apply, smoothingPairingMap, hm]

theorem localSwapProduct_restrictedPairing_intertwines
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (family : LocalSupports q p S) (A : Component p) (xA : Fibre p A)
    (i : Fin (Fintype.card (Fibre p A))) :
    rootedEnumeration p xA
      (ChordNonalternation.swapProduct (localEndpoint q p S A xA)
        (localEndpoint_injective q p S A xA) (family A) i) =
      restrictedPairing q p S (unionLocal q p S family)
        (unionLocal_eligible q p S family) A (rootedEnumeration p xA i) := by
  classical
  apply Subtype.ext
  have hprod := localSwapProduct_actual_intertwines q p S A xA
    (family A) (localEndpoint_injective q p S A xA) i
  have hpair := smoothingPairing_unionLocal_eq_localImage_on_fibre
    q p S family A (rootedEnumeration p xA i)
  change (rootedEnumeration p xA
      (ChordNonalternation.swapProduct (localEndpoint q p S A xA)
        (localEndpoint_injective q p S A xA) (family A) i)).val =
      smoothingPairing q (unionLocal q p S family)
        (rootedEnumeration p xA i).val
  rw [hprod]
  exact hpair.symm


/-- Finite-circle successor after swapping exactly the selected local visits. -/
noncomputable def localSmoothing (q : Fin n → PlanarPoint K)
    (p : Perm (PolygonEvent q)) (S : Finset (PolygonCrossing q))
    (A : Component p) (xA : Fibre p A)
    (L : Finset (LocalCrossing q p S A)) :
    Perm (Fin (Fintype.card (Fibre p A))) :=
  ChordNonalternation.smoothing (localEndpoint q p S A xA)
    (localEndpoint_injective q p S A xA) L

theorem localSmoothing_intertwines
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (family : LocalSupports q p S)
    (A : Component p) (xA : Fibre p A)
    (i : Fin (Fintype.card (Fibre p A))) :
    rootedEnumeration p xA
      (localSmoothing q p S A xA (family A) i) =
    (fibrePerm p A * restrictedPairing q p S (unionLocal q p S family)
      (unionLocal_eligible q p S family) A) (rootedEnumeration p xA i) := by
  change rootedEnumeration p xA
      ((cyclicSuccessorPerm (Fintype.card (Fibre p A)) *
        ChordNonalternation.swapProduct (localEndpoint q p S A xA)
          (localEndpoint_injective q p S A xA) (family A)) i) = _
  rw [Equiv.Perm.mul_apply, rootedEnumeration_successor]
  rw [localSwapProduct_restrictedPairing_intertwines q p S family A xA i]
  rfl

theorem localIncoming_intertwines
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (A : Component (smoothingIncomingPermutation q hq S))
    (xA : Fibre (smoothingIncomingPermutation q hq S) A)
    (i : Fin (Fintype.card
      (Fibre (smoothingIncomingPermutation q hq S) A))) :
    rootedEnumeration (smoothingIncomingPermutation q hq S) xA
      (localSmoothing q (smoothingIncomingPermutation q hq S) S A xA
        (family A) i) =
    restrictedIncoming q hq S
      (unionLocal q (smoothingIncomingPermutation q hq S) S family)
      (unionLocal_eligible q (smoothingIncomingPermutation q hq S) S family)
      A (rootedEnumeration (smoothingIncomingPermutation q hq S) xA i) := by
  rw [restrictedIncoming_eq]
  exact localSmoothing_intertwines q (smoothingIncomingPermutation q hq S)
    S family A xA i


theorem localSmoothing_componentCount_le
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (A : Component p) (xA : Fibre p A)
    (L : Finset (LocalCrossing q p S A)) :
    componentCount (localSmoothing q p S A xA L) ≤ L.card + 1 := by
  letI : NeZero (Fintype.card (Fibre p A)) :=
    ⟨Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨xA⟩)⟩
  exact ChordNonalternation.smoothing_componentCount_le
    (localEndpoint q p S A xA) (localEndpoint_injective q p S A xA) L

theorem local_nonalternating_iff_componentCount
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (A : Component p) (xA : Fibre p A)
    (L : Finset (LocalCrossing q p S A)) :
    ChordNonalternation.Nonalternating (localEndpoint q p S A xA) L ↔
      componentCount (localSmoothing q p S A xA L) = L.card + 1 := by
  letI : NeZero (Fintype.card (Fibre p A)) :=
    ⟨Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨xA⟩)⟩
  exact ChordNonalternation.nonalternating_iff_componentCount
    (localEndpoint q p S A xA) (localEndpoint_injective q p S A xA) L

theorem local_nonalternating_root_independent
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (family : LocalSupports q p S)
    (A : Component p) (xA yA : Fibre p A) :
    ChordNonalternation.Nonalternating (localEndpoint q p S A xA) (family A) ↔
      ChordNonalternation.Nonalternating (localEndpoint q p S A yA) (family A) := by
  let h : Perm (Fibre p A) := fibrePerm p A *
    restrictedPairing q p S (unionLocal q p S family)
      (unionLocal_eligible q p S family) A
  have hx := PermutationOrbits.componentCount_eq_of_intertwining
    (rootedEnumeration p xA) (localSmoothing q p S A xA (family A)) h
    (localSmoothing_intertwines q p S family A xA)
  have hy := PermutationOrbits.componentCount_eq_of_intertwining
    (rootedEnumeration p yA) (localSmoothing q p S A yA (family A)) h
    (localSmoothing_intertwines q p S family A yA)
  rw [local_nonalternating_iff_componentCount q p S A xA (family A),
    local_nonalternating_iff_componentCount q p S A yA (family A), hx, hy]


theorem indexRestrictedPerm_eq_restrictedIncoming
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S T : Finset (PolygonCrossing q))
    (hT : EligibleSupport q (smoothingIncomingPermutation q hq S) S T)
    (A : Component (smoothingIncomingPermutation q hq S)) :
    IndexedInvariantPartition.indexRestrictedPerm
      (smoothingIncomingPermutation q hq (S ∪ T))
      (oldLabel (smoothingIncomingPermutation q hq S))
      (incoming_preserves_oldLabel q hq S T hT) A =
    restrictedIncoming q hq S T hT A := by
  unfold IndexedInvariantPartition.indexRestrictedPerm
    IndexedInvariantPartition.indexFiber restrictedIncoming
    PermutationOrbits.restrictPerm oldLabel
  rfl



/-- Components of a normalized local circle are the components of its actual
restricted successor, via the rooted event coordinate. -/
noncomputable def localComponentEquiv
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (family : LocalSupports q p S)
    (A : Component p) (xA : Fibre p A) :
    Component (localSmoothing q p S A xA (family A)) ≃
      Component (fibrePerm p A * restrictedPairing q p S
        (unionLocal q p S family) (unionLocal_eligible q p S family) A) :=
  PermutationOrbits.componentEquivOfIntertwining (rootedEnumeration p xA)
    (localSmoothing q p S A xA (family A))
    (fibrePerm p A * restrictedPairing q p S
      (unionLocal q p S family) (unionLocal_eligible q p S family) A)
    (localSmoothing_intertwines q p S family A xA)

@[simp] theorem localComponentEquiv_componentOf
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (family : LocalSupports q p S)
    (A : Component p) (xA : Fibre p A)
    (i : Fin (Fintype.card (Fibre p A))) :
    localComponentEquiv q p S family A xA
      (componentOf (localSmoothing q p S A xA (family A)) i) =
    componentOf (fibrePerm p A * restrictedPairing q p S
      (unionLocal q p S family) (unionLocal_eligible q p S family) A)
      (rootedEnumeration p xA i) := by
  exact PermutationOrbits.componentEquivOfIntertwining_componentOf
    (rootedEnumeration p xA) (localSmoothing q p S A xA (family A))
    (fibrePerm p A * restrictedPairing q p S
      (unionLocal q p S family) (unionLocal_eligible q p S family) A)
    (localSmoothing_intertwines q p S family A xA) i

@[simp] theorem localComponentEquiv_symm_componentOf
    (q : Fin n → PlanarPoint K) (p : Perm (PolygonEvent q))
    (S : Finset (PolygonCrossing q)) (family : LocalSupports q p S)
    (A : Component p) (xA : Fibre p A)
    (i : Fin (Fintype.card (Fibre p A))) :
    (localComponentEquiv q p S family A xA).symm
      (componentOf (fibrePerm p A * restrictedPairing q p S
        (unionLocal q p S family) (unionLocal_eligible q p S family) A)
        (rootedEnumeration p xA i)) =
    componentOf (localSmoothing q p S A xA (family A)) i := by
  apply (localComponentEquiv q p S family A xA).injective
  simp [localComponentEquiv,
    PermutationOrbits.componentEquivOfIntertwining_componentOf]

noncomputable def localComponentEquivAt
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (roots : ComponentRoots (smoothingIncomingPermutation q hq S))
    (A : Component (smoothingIncomingPermutation q hq S)) :
    Component (localSmoothing q (smoothingIncomingPermutation q hq S)
      S A (roots A) (family A)) ≃
    Component (IndexedInvariantPartition.indexRestrictedPerm
      (smoothingIncomingPermutation q hq (S ∪ unionLocal q
        (smoothingIncomingPermutation q hq S) S family))
      (oldLabel (smoothingIncomingPermutation q hq S))
      (incoming_preserves_oldLabel q hq S
        (unionLocal q (smoothingIncomingPermutation q hq S) S family)
        (unionLocal_eligible q (smoothingIncomingPermutation q hq S) S family)) A) := by
  let pS := smoothingIncomingPermutation q hq S
  let T := unionLocal q pS S family
  let hT := unionLocal_eligible q pS S family
  let e := PermutationOrbits.componentEquivOfIntertwining
    (rootedEnumeration pS (roots A))
    (localSmoothing q pS S A (roots A) (family A))
    (restrictedIncoming q hq S T hT A)
    (localIncoming_intertwines q hq S family A (roots A))
  let hbridge := indexRestrictedPerm_eq_restrictedIncoming q hq S T hT A
  exact e.trans (Equiv.cast (congrArg Component hbridge)).symm



theorem localComponentEquivAt_symm_componentOf
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (roots : ComponentRoots (smoothingIncomingPermutation q hq S))
    (A : Component (smoothingIncomingPermutation q hq S))
    (i : Fin (Fintype.card
      (Fibre (smoothingIncomingPermutation q hq S) A))) :
    (localComponentEquivAt q hq S family roots A).symm
      (componentOf
        (IndexedInvariantPartition.indexRestrictedPerm
          (smoothingIncomingPermutation q hq (S ∪ unionLocal q
            (smoothingIncomingPermutation q hq S) S family))
          (oldLabel (smoothingIncomingPermutation q hq S))
          (incoming_preserves_oldLabel q hq S
            (unionLocal q (smoothingIncomingPermutation q hq S) S family)
            (unionLocal_eligible q (smoothingIncomingPermutation q hq S) S family)) A)
        ⟨(rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).val,
          by
            change componentOf (smoothingIncomingPermutation q hq S)
              (rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).val = A
            exact (rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).property⟩) =
      componentOf (localSmoothing q (smoothingIncomingPermutation q hq S)
        S A (roots A) (family A)) i := by
  let pS := smoothingIncomingPermutation q hq S
  let T := unionLocal q pS S family
  let hT := unionLocal_eligible q pS S family
  let hbridge := indexRestrictedPerm_eq_restrictedIncoming q hq S T hT A
  let e := PermutationOrbits.componentEquivOfIntertwining
    (rootedEnumeration pS (roots A))
    (localSmoothing q pS S A (roots A) (family A))
    (restrictedIncoming q hq S T hT A)
    (localIncoming_intertwines q hq S family A (roots A))
  cases hbridge
  change e.symm
      (componentOf (restrictedIncoming q hq S T hT A)
        (rootedEnumeration pS (roots A) i)) =
    componentOf (localSmoothing q pS S A (roots A) (family A)) i
  apply e.injective
  simp [e, PermutationOrbits.componentEquivOfIntertwining_componentOf]


theorem localComponentEquivAt_componentOf
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (roots : ComponentRoots (smoothingIncomingPermutation q hq S))
    (A : Component (smoothingIncomingPermutation q hq S))
    (i : Fin (Fintype.card
      (Fibre (smoothingIncomingPermutation q hq S) A))) :
    localComponentEquivAt q hq S family roots A
      (componentOf (localSmoothing q (smoothingIncomingPermutation q hq S)
        S A (roots A) (family A)) i) =
    componentOf
      (IndexedInvariantPartition.indexRestrictedPerm
        (smoothingIncomingPermutation q hq (S ∪ unionLocal q
          (smoothingIncomingPermutation q hq S) S family))
        (oldLabel (smoothingIncomingPermutation q hq S))
        (incoming_preserves_oldLabel q hq S
          (unionLocal q (smoothingIncomingPermutation q hq S) S family)
          (unionLocal_eligible q (smoothingIncomingPermutation q hq S) S family)) A)
      ⟨(rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).val,
        by
          change componentOf (smoothingIncomingPermutation q hq S)
            (rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).val = A
          exact (rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).property⟩ := by
  let pS := smoothingIncomingPermutation q hq S
  let T := unionLocal q pS S family
  let hT := unionLocal_eligible q pS S family
  let hbridge := indexRestrictedPerm_eq_restrictedIncoming q hq S T hT A
  let e := PermutationOrbits.componentEquivOfIntertwining
    (rootedEnumeration pS (roots A))
    (localSmoothing q pS S A (roots A) (family A))
    (restrictedIncoming q hq S T hT A)
    (localIncoming_intertwines q hq S family A (roots A))
  unfold localComponentEquivAt
  cases hbridge
  change e (componentOf (localSmoothing q pS S A (roots A) (family A)) i) =
    componentOf (restrictedIncoming q hq S T hT A)
      (rootedEnumeration pS (roots A) i)
  simp [e, PermutationOrbits.componentEquivOfIntertwining_componentOf]

noncomputable def actualLocalComponentEquiv
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (roots : ComponentRoots (smoothingIncomingPermutation q hq S)) :
    Component (smoothingIncomingPermutation q hq
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq S) S family)) ≃
    Σ A : Component (smoothingIncomingPermutation q hq S),
      Component (localSmoothing q (smoothingIncomingPermutation q hq S)
        S A (roots A) (family A)) := by
  let pS := smoothingIncomingPermutation q hq S
  let T := unionLocal q pS S family
  let hT := unionLocal_eligible q pS S family
  let pU := smoothingIncomingPermutation q hq (S ∪ T)
  let eA := fun A => localComponentEquivAt q hq S family roots A
  refine (ActualLocalSupports.actualPartitionEquiv q hq S T hT).trans ?_
  refine {
    toFun := fun z => ⟨z.1, (eA z.1).symm z.2⟩
    invFun := fun z => ⟨z.1, eA z.1 z.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨A, c⟩
    simp [eA]
  · rintro ⟨A, c⟩
    simp [eA]



theorem componentCount_actualLocalComponentEquiv
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (roots : ComponentRoots (smoothingIncomingPermutation q hq S)) :
    componentCount (smoothingIncomingPermutation q hq
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq S) S family)) =
    ∑ A : Component (smoothingIncomingPermutation q hq S),
      componentCount (localSmoothing q (smoothingIncomingPermutation q hq S)
        S A (roots A) (family A)) := by
  classical
  have hcard := Fintype.card_congr (actualLocalComponentEquiv q hq S family roots)
  simpa [componentCount, Fintype.card_sigma] using hcard

@[simp] theorem actualLocalComponentEquiv_componentOf
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (roots : ComponentRoots (smoothingIncomingPermutation q hq S))
    (x : PolygonEvent q) :
    let pS := smoothingIncomingPermutation q hq S
    let T := unionLocal q pS S family
    let pU := smoothingIncomingPermutation q hq (S ∪ T)
    let A := componentOf pS x
    let i := (rootedEnumeration pS (roots A)).symm ⟨x, rfl⟩
    actualLocalComponentEquiv q hq S family roots (componentOf pU x) =
      ⟨A, componentOf (localSmoothing q pS S A (roots A) (family A)) i⟩ := by
  classical
  dsimp [actualLocalComponentEquiv]
  apply Sigma.ext
  · rfl
  · dsimp only
    let pS := smoothingIncomingPermutation q hq S
    let A := componentOf pS x
    let i := (rootedEnumeration pS (roots A)).symm ⟨x, rfl⟩
    have hi : rootedEnumeration pS (roots A) i = ⟨x, rfl⟩ := by
      simp [i]
    apply heq_of_eq
    change (localComponentEquivAt q hq S family roots A).symm
        (componentOf
          (IndexedInvariantPartition.indexRestrictedPerm
            (smoothingIncomingPermutation q hq (S ∪ unionLocal q pS S family))
            (oldLabel pS)
            (incoming_preserves_oldLabel q hq S (unionLocal q pS S family)
              (unionLocal_eligible q pS S family)) A)
          ⟨x, rfl⟩) =
      componentOf (localSmoothing q pS S A (roots A) (family A)) i
    rw [← hi]
    exact localComponentEquivAt_symm_componentOf q hq S family roots A i


@[simp] theorem actualLocalComponentEquiv_symm_componentOf
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (family : LocalSupports q (smoothingIncomingPermutation q hq S) S)
    (roots : ComponentRoots (smoothingIncomingPermutation q hq S))
    (A : Component (smoothingIncomingPermutation q hq S))
    (i : Fin (Fintype.card
      (Fibre (smoothingIncomingPermutation q hq S) A))) :
    (actualLocalComponentEquiv q hq S family roots).symm
      ⟨A, componentOf (localSmoothing q (smoothingIncomingPermutation q hq S)
        S A (roots A) (family A)) i⟩ =
      componentOf (smoothingIncomingPermutation q hq
        (S ∪ unionLocal q (smoothingIncomingPermutation q hq S) S family))
        ((rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).val) := by
  classical
  dsimp [actualLocalComponentEquiv]
  change (ActualLocalSupports.actualPartitionEquiv q hq S
      (unionLocal q (smoothingIncomingPermutation q hq S) S family)
      (unionLocal_eligible q (smoothingIncomingPermutation q hq S) S family)).symm
      ⟨A, localComponentEquivAt q hq S family roots A
        (componentOf (localSmoothing q (smoothingIncomingPermutation q hq S)
          S A (roots A) (family A)) i)⟩ = _
  rw [localComponentEquivAt_componentOf]
  exact ActualLocalSupports.actualPartitionEquiv_symm_componentOf q hq S
    (unionLocal q (smoothingIncomingPermutation q hq S) S family)
    (unionLocal_eligible q (smoothingIncomingPermutation q hq S) S family)
    A ⟨(rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).val,
      by
        change componentOf (smoothingIncomingPermutation q hq S)
          (rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).val = A
        exact (rootedEnumeration (smoothingIncomingPermutation q hq S) (roots A) i).property⟩

end DirectGLSSW.LocalCoordinates
