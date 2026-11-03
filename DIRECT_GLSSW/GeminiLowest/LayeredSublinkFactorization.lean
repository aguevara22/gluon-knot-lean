import GeminiLowest.SublinkSmoothingAndTraversal

set_option autoImplicit false
noncomputable section

namespace GeminiLowest

open DirectGLSSW
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.LowestRowContract
open scoped BigOperators

attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  PermutationOrbits.componentFintype D.continuation

/-! ### Part 1: `SublinkPartition`, `blockIndex`, and Component Count Laws -/

structure SublinkPartition (D : PLLinkDiagram) (J : Type*) where
  block : J → Sublink D
  unique : ∀ C : diagramComponent D, ∃! j, C ∈ (block j).components

section SublinkPartitionBasics
variable {D : PLLinkDiagram} {J : Type*} (P : SublinkPartition D J)

theorem partition_disjoint (i j : J) (hij : i ≠ j) :
    Disjoint (P.block i).components (P.block j).components := by
  apply Set.disjoint_left.mpr
  intro C hi hj
  obtain ⟨k, _, hu⟩ := P.unique C
  exact hij ((hu i hi).trans (hu j hj).symm)

def blockIndex (C : diagramComponent D) : J :=
  Classical.choose (P.unique C)

theorem blockIndex_mem (C : diagramComponent D) :
    C ∈ (P.block (blockIndex P C)).components :=
  (Classical.choose_spec (P.unique C)).1

theorem blockIndex_eq_of_mem (C : diagramComponent D) (j : J)
    (hj : C ∈ (P.block j).components) :
    blockIndex P C = j :=
  ((Classical.choose_spec (P.unique C)).2 j hj).symm

theorem mem_block_iff_blockIndex_eq (C : diagramComponent D) (j : J) :
    C ∈ (P.block j).components ↔ blockIndex P C = j :=
  ⟨blockIndex_eq_of_mem P C j, fun h => h ▸ blockIndex_mem P C⟩

def partitionComponentMap
    (x : Σ j, diagramComponent (restrictSublink D (P.block j))) : diagramComponent D :=
  (sublinkComponentEquiv D (P.block x.1) x.2).val

theorem partitionComponentMap_bijective :
    Function.Bijective (partitionComponentMap P) := by
  constructor
  · rintro ⟨i, C⟩ ⟨j, E⟩ h
    change (sublinkComponentEquiv D (P.block i) C).val =
      (sublinkComponentEquiv D (P.block j) E).val at h
    obtain ⟨k, _, hu⟩ := P.unique (sublinkComponentEquiv D (P.block i) C).val
    have hi := hu i (sublinkComponentEquiv D (P.block i) C).property
    have hj := hu j (h ▸ (sublinkComponentEquiv D (P.block j) E).property)
    have hij : i = j := hi.trans hj.symm
    cases hij
    have hCE : C = E := (sublinkComponentEquiv D (P.block i)).injective (Subtype.ext h)
    exact congrArg (fun x => Sigma.mk i x) hCE
  · intro C
    obtain ⟨j, hj, _⟩ := P.unique C
    refine ⟨⟨j, (sublinkComponentEquiv D (P.block j)).symm ⟨C, hj⟩⟩, ?_⟩
    change (sublinkComponentEquiv D (P.block j)
      ((sublinkComponentEquiv D (P.block j)).symm ⟨C, hj⟩)).val = C
    rw [Equiv.apply_symm_apply]

def partitionComponentEquiv :
    (Σ j, diagramComponent (restrictSublink D (P.block j))) ≃ diagramComponent D :=
  Equiv.ofBijective (partitionComponentMap P) (partitionComponentMap_bijective P)

theorem partition_component_count [Fintype J] :
    diagramComponentCount D =
      ∑ j, diagramComponentCount (restrictSublink D (P.block j)) := by
  letI : ∀ j, Fintype (diagramComponent (restrictSublink D (P.block j))) :=
    fun j => componentFintype (restrictSublink D (P.block j)).continuation
  have h := Fintype.card_congr (partitionComponentEquiv P)
  change Fintype.card (diagramComponent D) =
    ∑ j, Fintype.card (diagramComponent (restrictSublink D (P.block j)))
  simpa only [Fintype.card_sigma] using h.symm

theorem partition_unlink_exponent [Fintype J] [Nonempty J] :
    (Fintype.card J - 1) +
      (∑ j, (diagramComponentCount (restrictSublink D (P.block j)) - 1)) =
      diagramComponentCount D - 1 := by
  classical
  have hsum : (∑ j, diagramComponentCount (restrictSublink D (P.block j))) =
      (∑ j, (diagramComponentCount (restrictSublink D (P.block j)) - 1)) + Fintype.card J := by
    calc
      _ = ∑ j, ((diagramComponentCount (restrictSublink D (P.block j)) - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro j _
        have hp := sublink_component_count_pos D (P.block j)
        omega
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_one]
  have hcount := partition_component_count P
  have hpos : 0 < Fintype.card J := Fintype.card_pos
  omega

include P in
theorem partition_parent_arc_pos [Nonempty J] : 0 < D.nArc := by
  let j : J := Classical.choice inferInstance
  obtain ⟨a⟩ := (inferInstance : Nonempty (SublinkArc D (P.block j)))
  exact Nat.zero_lt_of_lt a.val.isLt

include P in
theorem partition_empty_no_arc [IsEmpty J] : D.nArc = 0 := by
  by_contra h
  have hp : 0 < D.nArc := Nat.pos_of_ne_zero h
  obtain ⟨j, _, _⟩ := P.unique (componentOf D.continuation ⟨0, hp⟩)
  exact isEmptyElim j

theorem partition_unlink_value [Fintype J] :
    descendingUnlinkValue D = unlinkFactor ^ (Fintype.card J - 1) *
      ∏ j, descendingUnlinkValue (restrictSublink D (P.block j)) := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h =>
    letI := h
    have hz := partition_empty_no_arc P
    simp [descendingUnlinkValue, hz]
  | inr h =>
    letI := h
    rw [descendingUnlinkValue, if_neg (Nat.ne_of_gt (partition_parent_arc_pos P))]
    have hv : ∀ j, descendingUnlinkValue (restrictSublink D (P.block j)) =
        unlinkFactor ^ (diagramComponentCount (restrictSublink D (P.block j)) - 1) := by
      intro j
      rw [descendingUnlinkValue,
        if_neg (Nat.ne_of_gt (sublink_arc_count_pos D (P.block j)))]
    simp only [hv]
    rw [Finset.prod_pow_eq_pow_sum, ← pow_add, partition_unlink_exponent P]

theorem descendingEvaluator_partition_terminal [Fintype J] (T : BasedTraversal D)
    (hbad : badCrossings T = ∅) :
    descendingLaurentEvaluator D T = unlinkFactor ^ (Fintype.card J - 1) *
      ∏ j, descendingLaurentEvaluator (restrictSublink D (P.block j))
        (inducedSublinkTraversal (P.block j) T) := by
  classical
  rw [descendingLaurentEvaluator_terminal D T (by simp [hbad])]
  have hv : ∀ j, descendingLaurentEvaluator (restrictSublink D (P.block j))
      (inducedSublinkTraversal (P.block j) T) =
      descendingUnlinkValue (restrictSublink D (P.block j)) := by
    intro j
    apply descendingLaurentEvaluator_terminal
    have hj : badCrossings (inducedSublinkTraversal (P.block j) T) = ∅ := by
      ext d
      rw [badCrossings_inducedSublink_mem_iff]
      simp [hbad]
    simp [hj]
  simp only [hv]
  exact partition_unlink_value P

end SublinkPartitionBasics

/-! ### Part 2: Switched and Smoothed `SublinkPartition` and Intra-Block Pivot Step -/

section SublinkPartitionStep
variable {D : PLLinkDiagram} {J : Type*}

def basedSublinkProduct [Fintype J] (P : SublinkPartition D J) (T : BasedTraversal D) :
    HOMFLYCoeff :=
  unlinkFactor ^ (Fintype.card J - 1) *
    ∏ j, descendingLaurentEvaluator (restrictSublink D (P.block j))
      (inducedSublinkTraversal (P.block j) T)

def switchSublinkPartition (P : SublinkPartition D J) (c : Fin D.nCrossing) :
    SublinkPartition (switchCrossing D c) J where
  block j := switchSublink D (P.block j) c
  unique := P.unique

@[simp] theorem blockIndex_switchSublinkPartition (P : SublinkPartition D J)
    (c : Fin D.nCrossing) (C : diagramComponent D) :
    blockIndex (switchSublinkPartition P c) C = blockIndex P C := rfl

theorem other_sublink_untouched (P : SublinkPartition D J)
    (j : J) (cB : Fin (restrictSublink D (P.block j)).nCrossing) (k : J) (hkj : k ≠ j) :
    ∀ i : Fin 2,
      componentOf D.continuation (D.outgoing (sublinkOldCrossing D (P.block j) cB) i) ∉
        (P.block k).components := by
  intro i hk
  exact Set.disjoint_left.mp (partition_disjoint P k j hkj)
    hk ((sublinkCrossingEquiv D (P.block j) cB).property i)

theorem partition_pivotMonochrome (P : SublinkPartition D J)
    (j : J) (cB : Fin (restrictSublink D (P.block j)).nCrossing) (k : J) :
    PivotMonochrome D (P.block k) (sublinkOldCrossing D (P.block j) cB) := by
  by_cases hkj : k = j
  · subst hkj
    exact pivotMonochrome_of_sublinkOldCrossing D (P.block k) cB
  · exact pivotMonochrome_of_untouched D (P.block k)
      (sublinkOldCrossing D (P.block j) cB) (other_sublink_untouched P j cB k hkj)

def smoothSublinkPartition (P : SublinkPartition D J)
    (j : J) (cB : Fin (restrictSublink D (P.block j)).nCrossing) :
    SublinkPartition (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)) J where
  block k := smoothSublink D (P.block k) (sublinkOldCrossing D (P.block j) cB)
    (partition_pivotMonochrome P j cB k)
  unique C := by
    refine Quotient.inductionOn C ?_
    intro a
    obtain ⟨x, rfl⟩ := (smoothArcEquiv D).surjective a
    cases x with
    | inl a =>
      change ∃! k,
        componentOf (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)).continuation
          (smoothArcEquiv D (Sum.inl a)) ∈
          (smoothSublink D (P.block k) (sublinkOldCrossing D (P.block j) cB)
            (partition_pivotMonochrome P j cB k)).components
      simp only [mem_smoothSublink_old]
      exact P.unique (componentOf D.continuation a)
    | inr i =>
      change ∃! k,
        componentOf (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)).continuation
          (smoothArcEquiv D (Sum.inr i)) ∈
          (smoothSublink D (P.block k) (sublinkOldCrossing D (P.block j) cB)
            (partition_pivotMonochrome P j cB k)).components
      simp only [mem_smoothSublink_connector, sublinkPivotSelected]
      exact P.unique
        (componentOf D.continuation (D.outgoing (sublinkOldCrossing D (P.block j) cB) 0))

@[simp] theorem blockIndex_smoothSublinkPartition_old (P : SublinkPartition D J)
    (j : J) (cB : Fin (restrictSublink D (P.block j)).nCrossing) (a : Fin D.nArc) :
    blockIndex (smoothSublinkPartition P j cB)
      (componentOf (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)).continuation
        (smoothArcEquiv D (Sum.inl a))) =
      blockIndex P (componentOf D.continuation a) := by
  apply blockIndex_eq_of_mem
  change componentOf (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)).continuation
    (smoothArcEquiv D (Sum.inl a)) ∈
    (smoothSublink D (P.block (blockIndex P (componentOf D.continuation a)))
      (sublinkOldCrossing D (P.block j) cB) _).components
  rw [mem_smoothSublink_old]
  exact blockIndex_mem P (componentOf D.continuation a)

theorem descendingEvaluator_signedIso {D₁ D₂ : PLLinkDiagram} (I : SignedDiagramIso D₁ D₂)
    (T₁ : BasedTraversal D₁) (T₂ : BasedTraversal D₂) :
    descendingLaurentEvaluator D₁ T₁ = descendingLaurentEvaluator D₂ T₂ :=
  (all_lowerCrossingEvaluatorSkeinIH (D₁.nCrossing + 1)).1 I (Nat.lt_succ_self _) T₁ T₂

theorem descendingEvaluator_traversal_irrel (D₁ : PLLinkDiagram)
    (T₁ T₂ : BasedTraversal D₁) :
    descendingLaurentEvaluator D₁ T₁ = descendingLaurentEvaluator D₁ T₂ :=
  descendingEvaluator_signedIso (SignedDiagramIso.refl D₁) T₁ T₂

theorem basedSublinkProduct_traversal_irrel [Fintype J] (P : SublinkPartition D J)
    (T₁ T₂ : BasedTraversal D) :
    basedSublinkProduct P T₁ = basedSublinkProduct P T₂ := by
  unfold basedSublinkProduct
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact descendingEvaluator_traversal_irrel _ _ _

theorem sublink_switch_factor_selected (B : Sublink D) (T : BasedTraversal D)
    (cB : Fin (restrictSublink D B).nCrossing) :
    descendingLaurentEvaluator
      (restrictSublink (switchCrossing D (sublinkOldCrossing D B cB))
        (switchSublink D B (sublinkOldCrossing D B cB)))
      (inducedSublinkTraversal (switchSublink D B (sublinkOldCrossing D B cB))
        (switchTraversal T (sublinkOldCrossing D B cB))) =
    descendingLaurentEvaluator (switchCrossing (restrictSublink D B) cB)
      (switchTraversal (inducedSublinkTraversal B T) cB) :=
  descendingEvaluator_signedIso (sublinkSwitchRestrictionSignedIso D B cB) _ _

theorem sublink_switch_factor_untouched (B : Sublink D) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : ¬ sublinkPivotSelected D B c) :
    descendingLaurentEvaluator
      (restrictSublink (switchCrossing D c) (switchSublink D B c))
      (inducedSublinkTraversal (switchSublink D B c) (switchTraversal T c)) =
    descendingLaurentEvaluator (restrictSublink D B) (inducedSublinkTraversal B T) :=
  descendingEvaluator_signedIso (sublinkUntouchedSwitchRestrictionSignedIso D B c hc) _ _

theorem sublink_smooth_factor_selected (P : SublinkPartition D J)
    (j : J) (cB : Fin (restrictSublink D (P.block j)).nCrossing)
    (U : BasedTraversal (smoothCrossing D (sublinkOldCrossing D (P.block j) cB))) :
    descendingLaurentEvaluator
      (restrictSublink (smoothCrossing D (sublinkOldCrossing D (P.block j) cB))
        ((smoothSublinkPartition P j cB).block j))
      (inducedSublinkTraversal ((smoothSublinkPartition P j cB).block j) U) =
    descendingLaurentEvaluator (smoothCrossing (restrictSublink D (P.block j)) cB)
      (smoothChildBasedTraversal (restrictSublink D (P.block j)) cB) :=
  descendingEvaluator_signedIso (sublinkSmoothRestrictionSignedIso D (P.block j) cB) _ _

theorem sublink_smooth_factor_untouched (P : SublinkPartition D J) (T : BasedTraversal D)
    (j : J) (cB : Fin (restrictSublink D (P.block j)).nCrossing)
    (k : J) (hkj : k ≠ j)
    (U : BasedTraversal (smoothCrossing D (sublinkOldCrossing D (P.block j) cB))) :
    descendingLaurentEvaluator
      (restrictSublink (smoothCrossing D (sublinkOldCrossing D (P.block j) cB))
        ((smoothSublinkPartition P j cB).block k))
      (inducedSublinkTraversal ((smoothSublinkPartition P j cB).block k) U) =
    descendingLaurentEvaluator (restrictSublink D (P.block k))
      (inducedSublinkTraversal (P.block k) T) :=
  descendingEvaluator_signedIso
    (sublinkUntouchedRestrictionSignedIso D (P.block k)
      (sublinkOldCrossing D (P.block j) cB) (other_sublink_untouched P j cB k hkj)) _ _

theorem sublink_restricted_pivot_factors (B : Sublink D)
    (cB : Fin (restrictSublink D B).nCrossing) :
    pivotSwitchFactor D (sublinkOldCrossing D B cB) =
      pivotSwitchFactor (restrictSublink D B) cB ∧
    pivotSmoothFactor D (sublinkOldCrossing D B cB) =
      pivotSmoothFactor (restrictSublink D B) cB := by
  simp only [pivotSwitchFactor, pivotSmoothFactor, sublink_crossing_sign_preserved, and_self]

theorem sublink_partition_pivot_step [Fintype J]
    (P : SublinkPartition D J) (T : BasedTraversal D) (j : J)
    (cB : Fin (restrictSublink D (P.block j)).nCrossing)
    (hc : badAt T (sublinkOldCrossing D (P.block j) cB))
    (hSwitch : descendingLaurentEvaluator
        (switchCrossing D (sublinkOldCrossing D (P.block j) cB))
        (switchTraversal T (sublinkOldCrossing D (P.block j) cB)) =
      basedSublinkProduct (switchSublinkPartition P (sublinkOldCrossing D (P.block j) cB))
        (switchTraversal T (sublinkOldCrossing D (P.block j) cB)))
    (hSmooth : descendingLaurentEvaluator
        (smoothCrossing D (sublinkOldCrossing D (P.block j) cB))
        (smoothChildBasedTraversal D (sublinkOldCrossing D (P.block j) cB)) =
      basedSublinkProduct (smoothSublinkPartition P j cB)
        (smoothChildBasedTraversal D (sublinkOldCrossing D (P.block j) cB))) :
    descendingLaurentEvaluator D T = basedSublinkProduct P T := by
  classical
  let c := sublinkOldCrossing D (P.block j) cB
  let R := restrictSublink D (P.block j)
  let TR := inducedSublinkTraversal (P.block j) T
  let S := descendingLaurentEvaluator (switchCrossing R cB) (switchTraversal TR cB)
  let M := descendingLaurentEvaluator (smoothCrossing R cB) (smoothChildBasedTraversal R cB)
  let U := smoothChildBasedTraversal D c
  let v : J → HOMFLYCoeff := fun k =>
    descendingLaurentEvaluator (restrictSublink D (P.block k))
      (inducedSublinkTraversal (P.block k) T)
  let vs : J → HOMFLYCoeff := fun k =>
    descendingLaurentEvaluator
      (restrictSublink (switchCrossing D c) (switchSublink D (P.block k) c))
      (inducedSublinkTraversal (switchSublink D (P.block k) c) (switchTraversal T c))
  let vm : J → HOMFLYCoeff := fun k =>
    descendingLaurentEvaluator
      (restrictSublink (smoothCrossing D c) ((smoothSublinkPartition P j cB).block k))
      (inducedSublinkTraversal ((smoothSublinkPartition P j cB).block k) U)
  let F := unlinkFactor ^ (Fintype.card J - 1)
  let rest := ∏ k ∈ Finset.univ.erase j, v k
  have product_replace (f : J → HOMFLYCoeff) (w : HOMFLYCoeff)
      (hf : f j = w) (ho : ∀ k, k ≠ j → f k = v k) : (∏ k, f k) = w * rest := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j), hf]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    exact ho k (Finset.mem_erase.mp hk).1
  have hsp : (∏ k, vs k) = S * rest := by
    apply product_replace
    · exact sublink_switch_factor_selected (P.block j) T cB
    · intro k hkj
      exact sublink_switch_factor_untouched (P.block k) T c
        (other_sublink_untouched P j cB k hkj 0)
  have hmp : (∏ k, vm k) = M * rest := by
    apply product_replace
    · exact sublink_smooth_factor_selected P j cB U
    · intro k hkj
      exact sublink_smooth_factor_untouched P T j cB k hkj U
  have hlocal : badAt TR cB := (badAt_inducedSublink_iff (P.block j) T cB).mpr hc
  have hrec := descendingEvaluator_eq_any_bad_pivot
    (all_lowerCrossingEvaluatorSkeinIH R.nCrossing) R rfl TR cB hlocal
  change v j = pivotSwitchFactor R cB * S + pivotSmoothFactor R cB * M at hrec
  have hg := descendingEvaluator_eq_any_bad_pivot
    (all_lowerCrossingEvaluatorSkeinIH D.nCrossing) D rfl T c hc
  rw [descendingEvaluatorPivotBranch, hSwitch, hSmooth] at hg
  change descendingLaurentEvaluator D T =
    pivotSwitchFactor D c * (F * ∏ k, vs k) +
      pivotSmoothFactor D c * (F * ∏ k, vm k) at hg
  rw [hsp, hmp] at hg
  have hcoef := sublink_restricted_pivot_factors (P.block j) cB
  change descendingLaurentEvaluator D T = F * ∏ k, v k
  calc
    _ = pivotSwitchFactor D c * (F * (S * rest)) +
        pivotSmoothFactor D c * (F * (M * rest)) := hg
    _ = F * ((pivotSwitchFactor R cB * S + pivotSmoothFactor R cB * M) * rest) := by
      rw [hcoef.1, hcoef.2]
      ring
    _ = F * (v j * rest) := by rw [← hrec]
    _ = F * ∏ k, v k := by rw [Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]

end SublinkPartitionStep

/-! ### Part 3: `IsLayeredPartition`, `IsCompatibleTraversal`, and `layeredBasedTraversal` -/

theorem outgoing_mem_sublink_iff_incoming (D : PLLinkDiagram) (B : Sublink D)
    (c : Fin D.nCrossing) :
    (∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∈ B.components) ↔
    (∀ i : Fin 2, componentOf D.continuation (D.incoming c i) ∈ B.components) := by
  constructor
  · intro ho i
    have h := ho (D.through c i)
    rwa [← D.continuation_crossing c i, componentOf_apply] at h
  · intro hi j
    have hth_ne : D.through c 0 ≠ D.through c 1 := by
      intro heq
      have h1 := D.continuation_crossing c 0
      have h2 := D.continuation_crossing c 1
      rw [heq] at h1
      have h01 : D.incoming c 0 = D.incoming c 1 :=
        D.continuation.injective (h1.trans h2.symm)
      exact (D.four_ports_distinct c).1 h01
    have hj_ex : ∃ i : Fin 2, D.through c i = j := by
      by_cases h0 : D.through c 0 = j
      · exact ⟨0, h0⟩
      · refine ⟨1, ?_⟩
        have h1 : D.through c 1 = otherBranch (D.through c 0) :=
          eq_otherBranch_of_ne (D.through c 1) (D.through c 0) hth_ne.symm
        have hj : j = otherBranch (D.through c 0) :=
          eq_otherBranch_of_ne j (D.through c 0) (Ne.symm h0)
        exact h1.trans hj.symm
    obtain ⟨i, rfl⟩ := hj_ex
    rw [← D.continuation_crossing c i, componentOf_apply]
    exact hi i

def IsLayeredPartition {D : PLLinkDiagram} {m : ℕ} (P : SublinkPartition D (Fin m)) : Prop :=
  ∀ c : Fin D.nCrossing,
    blockIndex P (componentOf D.continuation (D.incoming c (D.overBranch c))) ≤
      blockIndex P (componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c))))

def IsCompatibleTraversal {D : PLLinkDiagram} {m : ℕ}
    (P : SublinkPartition D (Fin m)) (T : BasedTraversal D) : Prop :=
  ∀ C E : diagramComponent D,
    blockIndex P C < blockIndex P E → T.componentIndex C < T.componentIndex E

theorem not_badAt_of_componentIndex_lt {D : PLLinkDiagram} (T : BasedTraversal D)
    {c : Fin D.nCrossing}
    (hlt : T.componentIndex (componentOf D.continuation (D.incoming c (D.overBranch c))) <
      T.componentIndex (componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c))))) :
    ¬ badAt T c := by
  intro hbad
  unfold badAt at hbad
  have hfb : firstVisitedBranch T c = otherBranch (D.overBranch c) :=
    eq_otherBranch_of_ne (firstVisitedBranch T c) (D.overBranch c) hbad
  have hfirst := firstVisitedBranch_is_first T c
  rw [hfb, otherBranch_involutive] at hfirst
  unfold rankBefore visitRank at hfirst
  rcases hfirst with hlt' | ⟨heq, _⟩
  · exact not_lt_of_gt hlt hlt'
  · exact ne_of_lt hlt heq.symm

theorem intra_block_of_badAt_layered {D : PLLinkDiagram} {m : ℕ}
    (P : SublinkPartition D (Fin m)) (T : BasedTraversal D)
    (hLayer : IsLayeredPartition P) (hComp : IsCompatibleTraversal P T)
    {c : Fin D.nCrossing} (hc : c ∈ badCrossings T) :
    ∃ (j : Fin m) (cB : Fin (restrictSublink D (P.block j)).nCrossing),
      sublinkOldCrossing D (P.block j) cB = c := by
  have hbad : badAt T c := by simpa [badCrossings] using hc
  let C_over := componentOf D.continuation (D.incoming c (D.overBranch c))
  let C_under := componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c)))
  have hle : blockIndex P C_over ≤ blockIndex P C_under := hLayer c
  have hnot_lt : ¬ blockIndex P C_over < blockIndex P C_under := by
    intro hlt
    exact not_badAt_of_componentIndex_lt T (hComp C_over C_under hlt) hbad
  have heq : blockIndex P C_over = blockIndex P C_under :=
    le_antisymm hle (not_lt.mp hnot_lt)
  let j := blockIndex P C_over
  have hover_mem : C_over ∈ (P.block j).components := blockIndex_mem P C_over
  have hunder_mem : C_under ∈ (P.block j).components := by
    rw [mem_block_iff_blockIndex_eq]
    exact heq.symm
  have hin : ∀ i : Fin 2, componentOf D.continuation (D.incoming c i) ∈ (P.block j).components := by
    intro i
    by_cases hi : i = D.overBranch c
    · rw [hi]; exact hover_mem
    · rw [eq_otherBranch_of_ne i (D.overBranch c) hi]; exact hunder_mem
  have hout : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∈ (P.block j).components :=
    (outgoing_mem_sublink_iff_incoming D (P.block j) c).mpr hin
  refine ⟨j, (sublinkCrossingEquiv D (P.block j)).symm ⟨c, hout⟩, ?_⟩
  simp only [sublinkOldCrossing, Equiv.apply_symm_apply]

theorem isLayeredPartition_switchSublinkPartition {D : PLLinkDiagram} {m : ℕ}
    (P : SublinkPartition D (Fin m)) (j : Fin m)
    (cB : Fin (restrictSublink D (P.block j)).nCrossing)
    (hLayer : IsLayeredPartition P) :
    IsLayeredPartition (switchSublinkPartition P (sublinkOldCrossing D (P.block j) cB)) := by
  intro d
  let c := sublinkOldCrossing D (P.block j) cB
  by_cases hdc : d = c
  · subst d
    have hout : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∈ (P.block j).components :=
      (sublinkCrossingEquiv D (P.block j) cB).property
    have hin : ∀ i : Fin 2, componentOf D.continuation (D.incoming c i) ∈ (P.block j).components :=
      (outgoing_mem_sublink_iff_incoming D (P.block j) c).mp hout
    have h1 : blockIndex P
        (componentOf D.continuation (D.incoming c ((switchCrossing D c).overBranch c))) = j :=
      blockIndex_eq_of_mem P _ j (hin _)
    have h2 : blockIndex P
        (componentOf D.continuation
          (D.incoming c (otherBranch ((switchCrossing D c).overBranch c)))) = j :=
      blockIndex_eq_of_mem P _ j (hin _)
    change blockIndex P
        (componentOf D.continuation (D.incoming c ((switchCrossing D c).overBranch c))) ≤
      blockIndex P
        (componentOf D.continuation
          (D.incoming c (otherBranch ((switchCrossing D c).overBranch c))))
    rw [h1, h2]
  · have hover : (switchCrossing D c).overBranch d = D.overBranch d := by
      simp [switchCrossing, hdc]
    change blockIndex P
        (componentOf D.continuation (D.incoming d ((switchCrossing D c).overBranch d))) ≤
      blockIndex P
        (componentOf D.continuation
          (D.incoming d (otherBranch ((switchCrossing D c).overBranch d))))
    rw [hover]
    exact hLayer d

theorem isCompatibleTraversal_switchSublinkPartition {D : PLLinkDiagram} {m : ℕ}
    (P : SublinkPartition D (Fin m)) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (hComp : IsCompatibleTraversal P T) :
    IsCompatibleTraversal (switchSublinkPartition P c) (switchTraversal T c) :=
  hComp

theorem isLayeredPartition_smoothSublinkPartition {D : PLLinkDiagram} {m : ℕ}
    (P : SublinkPartition D (Fin m)) (j : Fin m)
    (cB : Fin (restrictSublink D (P.block j)).nCrossing)
    (hLayer : IsLayeredPartition P) :
    IsLayeredPartition (smoothSublinkPartition P j cB) := by
  intro d
  let c := sublinkOldCrossing D (P.block j) cB
  let d_old := ((smoothCrossingEquiv D c).symm d).val
  change blockIndex (smoothSublinkPartition P j cB)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inl (D.incoming d_old (D.overBranch d_old))))) ≤
    blockIndex (smoothSublinkPartition P j cB)
      (componentOf (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inl (D.incoming d_old (otherBranch (D.overBranch d_old))))))
  rw [blockIndex_smoothSublinkPartition_old, blockIndex_smoothSublinkPartition_old]
  exact hLayer d_old

section LayeredTraversalConstruction
variable {D : PLLinkDiagram} {m : ℕ} (P : SublinkPartition D (Fin m))

def partitionKeyNat (C : diagramComponent D) : ℕ :=
  (blockIndex P C).val * (diagramComponentCount D + 1) +
    (Fintype.equivFin (diagramComponent D) C).val

private theorem partitionKeyNat_step {x y : ℕ} (hxy : x < y) :
    x * (diagramComponentCount D + 1) + (diagramComponentCount D + 1) ≤
      y * (diagramComponentCount D + 1) := by
  rw [← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ hxy

theorem partitionKeyNat_lt_of_blockIndex_lt {C E : diagramComponent D}
    (hlt : blockIndex P C < blockIndex P E) :
    partitionKeyNat P C < partitionKeyNat P E := by
  unfold partitionKeyNat
  have hstep := partitionKeyNat_step (D := D) hlt
  have hiC : (Fintype.equivFin (diagramComponent D) C).val < diagramComponentCount D :=
    (Fintype.equivFin (diagramComponent D) C).isLt
  omega

theorem partitionKeyNat_injective : Function.Injective (partitionKeyNat P) := by
  intro C E heq
  unfold partitionKeyNat at heq
  have hiC : (Fintype.equivFin (diagramComponent D) C).val < diagramComponentCount D :=
    (Fintype.equivFin (diagramComponent D) C).isLt
  have hiE : (Fintype.equivFin (diagramComponent D) E).val < diagramComponentCount D :=
    (Fintype.equivFin (diagramComponent D) E).isLt
  rcases lt_trichotomy (blockIndex P C).val (blockIndex P E).val with hlt | hEq | hgt
  · have hstep := partitionKeyNat_step (D := D) hlt
    omega
  · rw [hEq] at heq
    have hi : (Fintype.equivFin (diagramComponent D) C).val =
        (Fintype.equivFin (diagramComponent D) E).val := by omega
    exact (Fintype.equivFin (diagramComponent D)).injective (Fin.ext hi)
  · have hstep := partitionKeyNat_step (D := D) hgt
    omega

private noncomputable def partitionKeyFinset : Finset ℕ := by
  classical
  exact Finset.univ.image (partitionKeyNat P)

private theorem partitionKeyFinset_card :
    (partitionKeyFinset P).card = diagramComponentCount D := by
  classical
  unfold partitionKeyFinset
  rw [Finset.card_image_of_injective _ (partitionKeyNat_injective P), Finset.card_univ]
  rfl

private noncomputable def partitionKeyEquiv :
    diagramComponent D ≃ {k : ℕ // k ∈ partitionKeyFinset P} := by
  classical
  refine Equiv.ofBijective
    (fun C => ⟨partitionKeyNat P C, by
      simp only [partitionKeyFinset, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨C, rfl⟩⟩)
    ⟨?_, ?_⟩
  · intro C E h
    exact partitionKeyNat_injective P (congrArg Subtype.val h)
  · rintro ⟨k, hk⟩
    simp only [partitionKeyFinset, Finset.mem_image, Finset.mem_univ, true_and] at hk
    obtain ⟨C, rfl⟩ := hk
    exact ⟨C, rfl⟩

@[simp] private theorem partitionKeyEquiv_val (C : diagramComponent D) :
    (partitionKeyEquiv P C).val = partitionKeyNat P C := rfl

noncomputable def layeredBasedTraversal : BasedTraversal D where
  componentIndex :=
    (partitionKeyEquiv P).trans
      (((partitionKeyFinset P).orderIsoOfFin (partitionKeyFinset_card P)).symm.toEquiv)
  baseArc C := Classical.choice (fibreNonempty D.continuation C)

theorem isCompatibleTraversal_layeredBasedTraversal :
    IsCompatibleTraversal P (layeredBasedTraversal P) := by
  intro C E hlt
  let ord := ((partitionKeyFinset P).orderIsoOfFin (partitionKeyFinset_card P)).symm
  let u := partitionKeyEquiv P C
  let v := partitionKeyEquiv P E
  change ord u < ord v
  have hordLe (x y : {k : ℕ // k ∈ partitionKeyFinset P}) : ord x ≤ ord y ↔ x ≤ y :=
    ord.map_rel_iff
  have hord : ord u < ord v ↔ u < v := by
    rw [lt_iff_le_not_le, hordLe, hordLe, lt_iff_le_not_le]
  rw [hord]
  change (partitionKeyEquiv P C).val < (partitionKeyEquiv P E).val
  rw [partitionKeyEquiv_val, partitionKeyEquiv_val]
  exact partitionKeyNat_lt_of_blockIndex_lt P hlt

end LayeredTraversalConstruction

/-! ### Part 4: Layered Sublink Factorization and Singleton Lowest-Row Evaluation -/

theorem descendingEvaluator_layeredPartition_aux {m : ℕ} :
    ∀ n : ℕ, ∀ (D : PLLinkDiagram), D.nCrossing = n →
      ∀ (P : SublinkPartition D (Fin m)) (T : BasedTraversal D),
        IsLayeredPartition P → IsCompatibleTraversal P T →
          descendingLaurentEvaluator D T = basedSublinkProduct P T := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have inner : ∀ k : ℕ, ∀ (D : PLLinkDiagram), D.nCrossing = n →
        ∀ (P : SublinkPartition D (Fin m)) (T : BasedTraversal D),
          IsLayeredPartition P → IsCompatibleTraversal P T →
            (badCrossings T).card = k →
              descendingLaurentEvaluator D T = basedSublinkProduct P T := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ik =>
        intro D hD P T hLayer hComp hk
        by_cases hz : badCrossings T = ∅
        · exact descendingEvaluator_partition_terminal P T hz
        · have hn : (badCrossings T).Nonempty := Finset.nonempty_iff_ne_empty.mpr hz
          obtain ⟨c, hc⟩ := hn
          obtain ⟨j, cB, hcB⟩ := intra_block_of_badAt_layered P T hLayer hComp hc
          subst c
          have hcAt : badAt T (sublinkOldCrossing D (P.block j) cB) := by
            simpa [badCrossings] using hc
          apply sublink_partition_pivot_step P T j cB hcAt
          · have hlt : (badCrossings
                (switchTraversal T (sublinkOldCrossing D (P.block j) cB))).card < k := by
              have hd := badCrossings_switch_card T (sublinkOldCrossing D (P.block j) cB) hc
              omega
            exact ik _ hlt (switchCrossing D (sublinkOldCrossing D (P.block j) cB)) hD
              (switchSublinkPartition P (sublinkOldCrossing D (P.block j) cB))
              (switchTraversal T (sublinkOldCrossing D (P.block j) cB))
              (isLayeredPartition_switchSublinkPartition P j cB hLayer)
              (isCompatibleTraversal_switchSublinkPartition P T _ hComp) rfl
          · have hlt :
                (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)).nCrossing < n := by
              have hd := smoothCrossing_crossing_count_drop D
                (sublinkOldCrossing D (P.block j) cB)
              omega
            let P' := smoothSublinkPartition P j cB
            let U' := layeredBasedTraversal P'
            have hLayer' : IsLayeredPartition P' :=
              isLayeredPartition_smoothSublinkPartition P j cB hLayer
            have hComp' : IsCompatibleTraversal P' U' :=
              isCompatibleTraversal_layeredBasedTraversal P'
            have hih := ih _ hlt
              (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)) rfl
              P' U' hLayer' hComp'
            calc
              descendingLaurentEvaluator
                  (smoothCrossing D (sublinkOldCrossing D (P.block j) cB))
                  (smoothChildBasedTraversal D (sublinkOldCrossing D (P.block j) cB)) =
                descendingLaurentEvaluator
                  (smoothCrossing D (sublinkOldCrossing D (P.block j) cB)) U' :=
                descendingEvaluator_traversal_irrel _ _ _
              _ = basedSublinkProduct P' U' := hih
              _ = basedSublinkProduct P'
                  (smoothChildBasedTraversal D (sublinkOldCrossing D (P.block j) cB)) :=
                basedSublinkProduct_traversal_irrel P' _ _
    intro D hD P T hLayer hComp
    exact inner _ D hD P T hLayer hComp rfl

theorem candidateEvaluator_layeredPartition {D : PLLinkDiagram} (hD : 0 < D.nArc) {m : ℕ}
    (P : SublinkPartition D (Fin m)) (hLayer : IsLayeredPartition P) :
    candidateEvaluator D hD =
      unlinkFactor ^ (m - 1) *
        ∏ j : Fin m,
          candidateEvaluator (restrictSublink D (P.block j))
            (sublink_arc_count_pos D (P.block j)) := by
  let T := layeredBasedTraversal P
  have hComp : IsCompatibleTraversal P T := isCompatibleTraversal_layeredBasedTraversal P
  rw [candidateEvaluator_eq_traversal all_lowerCrossingEvaluatorSkeinIH D hD T]
  rw [descendingEvaluator_layeredPartition_aux D.nCrossing D rfl P T hLayer hComp]
  unfold basedSublinkProduct
  rw [Fintype.card_fin]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact (candidateEvaluator_eq_traversal all_lowerCrossingEvaluatorSkeinIH
    (restrictSublink D (P.block j)) (sublink_arc_count_pos D (P.block j))
    (inducedSublinkTraversal (P.block j) T)).symm

def singletonLayeredPartition (D : PLLinkDiagram) (T : BasedTraversal D) :
    SublinkPartition D (Fin (diagramComponentCount D)) where
  block j := singletonSublink D (T.componentIndex.symm j)
  unique C := by
    refine ⟨T.componentIndex C, ?_, ?_⟩
    · change C ∈ ({T.componentIndex.symm (T.componentIndex C)} : Set (diagramComponent D))
      rw [Set.mem_singleton_iff, Equiv.symm_apply_apply]
    · intro j hj
      change C ∈ ({T.componentIndex.symm j} : Set (diagramComponent D)) at hj
      rw [Set.mem_singleton_iff] at hj
      rw [hj, Equiv.apply_symm_apply]

@[simp] theorem blockIndex_singletonLayeredPartition (D : PLLinkDiagram)
    (T : BasedTraversal D) (C : diagramComponent D) :
    blockIndex (singletonLayeredPartition D T) C = T.componentIndex C := by
  apply blockIndex_eq_of_mem
  change C ∈ ({T.componentIndex.symm (T.componentIndex C)} : Set (diagramComponent D))
  rw [Set.mem_singleton_iff, Equiv.symm_apply_apply]

theorem isLayeredPartition_singleton_of_no_mixed_bad (D : PLLinkDiagram)
    (T : BasedTraversal D) (hno : ∀ c ∈ badCrossings T, ¬ IsMixed D c) :
    IsLayeredPartition (singletonLayeredPartition D T) := by
  intro c
  rw [blockIndex_singletonLayeredPartition, blockIndex_singletonLayeredPartition]
  let C_over := componentOf D.continuation (D.incoming c (D.overBranch c))
  let C_under := componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c)))
  by_contra hnot_le
  have hlt : T.componentIndex C_under < T.componentIndex C_over := not_le.mp hnot_le
  have hne : C_over ≠ C_under := fun h => ne_of_lt hlt (congrArg T.componentIndex h.symm)
  have hpair : isOverPairCrossing D C_over C_under c := ⟨hne, rfl, rfl⟩
  have hbad : badAt T c := badAt_of_isOverPairCrossing_of_lt T hlt hpair
  have hc_bad : c ∈ badCrossings T := by simpa [badCrossings] using hbad
  have hmixed : IsMixed D c := (isMixed_iff_overUnder_ne D c).mpr hne
  exact hno c hc_bad hmixed

theorem candidateEvaluator_of_no_mixed_bad (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (T : BasedTraversal D) (hno : ∀ c ∈ badCrossings T, ¬ IsMixed D c) :
    candidateEvaluator D hD =
      unlinkFactor ^ (diagramComponentCount D - 1) *
        ∏ C : diagramComponent D,
          candidateEvaluator (canonicalComponentRestriction D C).diagram
            (canonicalComponentRestriction D C).nonempty := by
  have hLayer := isLayeredPartition_singleton_of_no_mixed_bad D T hno
  rw [candidateEvaluator_layeredPartition hD (singletonLayeredPartition D T) hLayer]
  congr 1
  have hbij := Equiv.prod_comp T.componentIndex.symm
    (fun C : diagramComponent D =>
      candidateEvaluator (canonicalComponentRestriction D C).diagram
        (canonicalComponentRestriction D C).nonempty)
  exact hbij

theorem zRow_candidateEvaluator_of_no_mixed_bad (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (T : BasedTraversal D) (hno : ∀ c ∈ badCrossings T, ¬ IsMixed D c) :
    zRow (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
      (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) *
        componentRowProduct candidateEvaluator D (canonicalComponentRestriction D) := by
  rw [candidateEvaluator_of_no_mixed_bad D hD T hno]
  have hf1 : zFloor (unlinkFactor ^ (diagramComponentCount D - 1))
      (1 - (diagramComponentCount D : ℤ)) := by
    have heq : (1 - (diagramComponentCount D : ℤ)) =
        -((diagramComponentCount D - 1 : ℕ) : ℤ) := by
      have hpos : 0 < diagramComponentCount D := diagramComponentCount_pos_of_nArc_pos D hD
      omega
    rw [heq]
    exact zFloor_unlinkFactor_pow (diagramComponentCount D - 1)
  have hf_each : ∀ C ∈ (Finset.univ : Finset (diagramComponent D)),
      zFloor (candidateEvaluator (canonicalComponentRestriction D C).diagram
        (canonicalComponentRestriction D C).nonempty) 0 := by
    intro C _
    have h1 := lowest_z_floor (canonicalComponentRestriction D C).diagram
      (canonicalComponentRestriction D C).nonempty
    rw [componentRestriction_componentCount_eq_one (canonicalComponentRestriction D C)] at h1
    simpa using h1
  have hf2 : zFloor
      (∏ C : diagramComponent D,
        candidateEvaluator (canonicalComponentRestriction D C).diagram
          (canonicalComponentRestriction D C).nonempty) 0 :=
    zFloor_prod_zero Finset.univ _ hf_each
  have hdeg : (1 - (diagramComponentCount D : ℤ)) =
      (1 - (diagramComponentCount D : ℤ)) + 0 := by ring
  conv_lhs => rw [hdeg]
  rw [zRow_mul_of_zFloor hf1 hf2]
  have hrow1 : zRow (unlinkFactor ^ (diagramComponentCount D - 1))
      (1 - (diagramComponentCount D : ℤ)) =
      (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) := by
    have heq : (1 - (diagramComponentCount D : ℤ)) =
        -((diagramComponentCount D - 1 : ℕ) : ℤ) := by
      have hpos : 0 < diagramComponentCount D := diagramComponentCount_pos_of_nArc_pos D hD
      omega
    rw [heq]
    exact zRow_unlinkFactor_pow (diagramComponentCount D - 1)
  rw [hrow1]
  congr 1
  rw [zRow_prod_zero Finset.univ _ hf_each]
  rfl

end GeminiLowest
