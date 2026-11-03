import GeminiLowest.LinkingIntegrality

set_option autoImplicit false
noncomputable section

namespace GeminiLowest

open DirectGLSSW
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.LowestRowContract

/-! ### Part 1: Component Enumeration on `restrictSublink D B` -/

section SublinkComponents
variable (D : PLLinkDiagram) (B : Sublink D)

def SublinkSelectedComponent := {c : diagramComponent D // c ∈ B.components}

instance : Fintype (SublinkSelectedComponent D B) := by
  classical
  letI : Fintype (diagramComponent D) := componentFintype D.continuation
  unfold SublinkSelectedComponent
  infer_instance

instance : Nonempty (SublinkSelectedComponent D B) := by
  obtain ⟨c, hc⟩ := B.nonempty
  exact ⟨⟨c, hc⟩⟩

theorem sublink_sameCycle_iff (a b : Fin (restrictSublink D B).nArc) :
    (restrictSublink D B).continuation.SameCycle a b ↔
      D.continuation.SameCycle (sublinkOldArc D B a) (sublinkOldArc D B b) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, ← sublink_old_continuation_pow, hn]
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply sublinkOldArc_injective D B
    rw [sublink_old_continuation_pow, hn]

def sublinkComponentMap :
    diagramComponent (restrictSublink D B) → SublinkSelectedComponent D B :=
  Quotient.lift
    (fun a => ⟨componentOf D.continuation (sublinkOldArc D B a), (sublinkArcEquiv D B a).property⟩)
    (fun a b h =>
      Subtype.ext ((componentOf_eq_iff _ _ _).mpr ((sublink_sameCycle_iff D B a b).mp h)))

@[simp] theorem sublinkComponentMap_componentOf (a : Fin (restrictSublink D B).nArc) :
    sublinkComponentMap D B (componentOf (restrictSublink D B).continuation a) =
      ⟨componentOf D.continuation (sublinkOldArc D B a), (sublinkArcEquiv D B a).property⟩ := rfl

theorem sublinkComponentMap_injective : Function.Injective (sublinkComponentMap D B) := by
  intro c d
  induction c using Quotient.inductionOn with | h a =>
    induction d using Quotient.inductionOn with | h b =>
      intro h
      apply (componentOf_eq_iff _ _ _).mpr
      apply (sublink_sameCycle_iff D B a b).mpr
      apply (componentOf_eq_iff _ _ _).mp
      exact congrArg Subtype.val h

theorem sublinkComponentMap_surjective : Function.Surjective (sublinkComponentMap D B) := by
  intro c
  obtain ⟨a⟩ := fibreNonempty D.continuation c.val
  let x : SublinkArc D B := ⟨a.val, by simpa only [a.property] using c.property⟩
  refine ⟨componentOf (restrictSublink D B).continuation ((sublinkArcEquiv D B).symm x), ?_⟩
  apply Subtype.ext
  change componentOf D.continuation (sublinkOldArc D B ((sublinkArcEquiv D B).symm x)) = c.val
  simpa only [sublinkOldArc, Equiv.apply_symm_apply] using a.property

def sublinkComponentEquiv :
    diagramComponent (restrictSublink D B) ≃ SublinkSelectedComponent D B :=
  Equiv.ofBijective (sublinkComponentMap D B)
    ⟨sublinkComponentMap_injective D B, sublinkComponentMap_surjective D B⟩

@[simp] theorem sublinkComponentEquiv_componentOf (a : Fin (restrictSublink D B).nArc) :
    sublinkComponentEquiv D B (componentOf (restrictSublink D B).continuation a) =
      ⟨componentOf D.continuation (sublinkOldArc D B a), (sublinkArcEquiv D B a).property⟩ := rfl

theorem sublink_component_count :
    diagramComponentCount (restrictSublink D B) = Fintype.card (SublinkSelectedComponent D B) := by
  letI : Fintype (diagramComponent (restrictSublink D B)) :=
    componentFintype (restrictSublink D B).continuation
  exact Fintype.card_congr (sublinkComponentEquiv D B)

theorem sublink_component_count_pos : 0 < diagramComponentCount (restrictSublink D B) := by
  rw [sublink_component_count]
  exact Fintype.card_pos

theorem sublink_restrict_incoming (c : Fin (restrictSublink D B).nCrossing) (i : Fin 2) :
    sublinkOldArc D B ((restrictSublink D B).incoming c i) =
      D.incoming (sublinkOldCrossing D B c) i :=
  sublink_old_incoming D B c i

theorem sublink_restrict_outgoing (c : Fin (restrictSublink D B).nCrossing) (i : Fin 2) :
    sublinkOldArc D B ((restrictSublink D B).outgoing c i) =
      D.outgoing (sublinkOldCrossing D B c) i :=
  sublink_old_outgoing D B c i

theorem sublink_restrict_next (a : Fin (restrictSublink D B).nArc) :
    sublinkOldArc D B ((restrictSublink D B).continuation a) =
      D.continuation (sublinkOldArc D B a) :=
  sublink_old_next D B a

theorem sublink_crossing_data_preserved (c : Fin (restrictSublink D B).nCrossing) :
    (restrictSublink D B).through c = D.through (sublinkOldCrossing D B c) ∧
    (restrictSublink D B).overBranch c = D.overBranch (sublinkOldCrossing D B c) ∧
    (∀ i, sublinkOldArc D B ((restrictSublink D B).incoming c i) =
      D.incoming (sublinkOldCrossing D B c) i) ∧
    (∀ i, sublinkOldArc D B ((restrictSublink D B).outgoing c i) =
      D.outgoing (sublinkOldCrossing D B c) i) :=
  ⟨rfl, rfl, sublink_restrict_incoming D B c, sublink_restrict_outgoing D B c⟩

end SublinkComponents

/-! ### Part 2: Induced `BasedTraversal` on `restrictSublink D B` -/

section SublinkBasedTraversal
variable {D : PLLinkDiagram} (B : Sublink D) (T : BasedTraversal D)

private noncomputable def sublinkSelectedIndices
    (B : Sublink D) (T : BasedTraversal D) : Finset (Fin (diagramComponentCount D)) := by
  classical
  exact Finset.univ.filter (fun i => T.componentIndex.symm i ∈ B.components)

private noncomputable def sublinkSelectedComponentIndexEquiv
    (B : Sublink D) (T : BasedTraversal D) : SublinkSelectedComponent D B ≃
    {i : Fin (diagramComponentCount D) // i ∈ sublinkSelectedIndices B T} where
  toFun C := by
    refine ⟨T.componentIndex C.1, ?_⟩
    simp only [sublinkSelectedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [C.2]
  invFun i := by
    refine ⟨T.componentIndex.symm i.1, ?_⟩
    have hi := i.2
    simp only [sublinkSelectedIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  left_inv C := by
    apply Subtype.ext
    exact T.componentIndex.symm_apply_apply C.1
  right_inv i := by
    apply Subtype.ext
    exact T.componentIndex.apply_symm_apply i.1

private theorem sublink_restricted_component_count
    (B : Sublink D) (T : BasedTraversal D) :
    diagramComponentCount (restrictSublink D B) = (sublinkSelectedIndices B T).card := by
  rw [sublink_component_count]
  simpa using Fintype.card_congr (sublinkSelectedComponentIndexEquiv B T)

private noncomputable def sublinkSelectedIndexOrderIso (B : Sublink D) (T : BasedTraversal D) :
    {i : Fin (diagramComponentCount D) // i ∈ sublinkSelectedIndices B T} ≃o
      Fin (sublinkSelectedIndices B T).card :=
  ((sublinkSelectedIndices B T).orderIsoOfFin rfl).symm

noncomputable def inducedSublinkTraversal :
    BasedTraversal (restrictSublink D B) where
  componentIndex := by
    let s := sublinkSelectedIndices B T
    let ord := sublinkSelectedIndexOrderIso B T
    let hcard : diagramComponentCount (restrictSublink D B) = s.card :=
      sublink_restricted_component_count B T
    exact Equiv.trans (sublinkComponentEquiv D B) <| Equiv.trans
      (sublinkSelectedComponentIndexEquiv B T) <| Equiv.trans
      ord.toEquiv (Fin.castOrderIso hcard.symm).toEquiv
  baseArc := by
    intro C'
    let Csel := sublinkComponentEquiv D B C'
    let C := Csel.1
    let r := T.baseArc C
    have hr : componentOf D.continuation r.val ∈ B.components := by
      rw [r.property]
      exact Csel.2
    let a : SublinkArc D B := ⟨r.val, hr⟩
    refine ⟨(sublinkArcEquiv D B).symm a, ?_⟩
    apply (sublinkComponentEquiv D B).injective
    rw [sublinkComponentEquiv_componentOf]
    apply Subtype.ext
    change componentOf D.continuation
      (sublinkOldArc D B ((sublinkArcEquiv D B).symm a)) = C
    change componentOf D.continuation
      ((sublinkArcEquiv D B ((sublinkArcEquiv D B).symm a)).val) = C
    rw [Equiv.apply_symm_apply]
    exact r.property

private theorem inducedSublink_componentIndex_lt_iff
    (C₁ C₂ : diagramComponent (restrictSublink D B)) :
    (inducedSublinkTraversal B T).componentIndex C₁ <
        (inducedSublinkTraversal B T).componentIndex C₂ ↔
      T.componentIndex ((sublinkComponentEquiv D B C₁).1) <
        T.componentIndex ((sublinkComponentEquiv D B C₂).1) := by
  let u := sublinkSelectedComponentIndexEquiv B T (sublinkComponentEquiv D B C₁)
  let v := sublinkSelectedComponentIndexEquiv B T (sublinkComponentEquiv D B C₂)
  let ord := sublinkSelectedIndexOrderIso B T
  let castFin := (Fin.castOrderIso (sublink_restricted_component_count B T).symm).toEquiv
  have hordLe (x y : {i : Fin (diagramComponentCount D) //
      i ∈ sublinkSelectedIndices B T}) : ord x ≤ ord y ↔ x ≤ y := ord.map_rel_iff
  have hord : ord u < ord v ↔ u < v := by
    rw [lt_iff_le_not_le, hordLe, hordLe, lt_iff_le_not_le]
  have hidx₁ : (inducedSublinkTraversal B T).componentIndex C₁ =
      castFin (ord u) := by
    dsimp only [inducedSublinkTraversal]
    simp only [Equiv.trans_apply]
    rfl
  have hidx₂ : (inducedSublinkTraversal B T).componentIndex C₂ =
      castFin (ord v) := by
    dsimp only [inducedSublinkTraversal]
    simp only [Equiv.trans_apply]
    rfl
  rw [hidx₁, hidx₂]
  have castFin_eq (i : Fin (sublinkSelectedIndices B T).card) :
      castFin i = Fin.cast (sublink_restricted_component_count B T).symm i := rfl
  have hcast : castFin (ord u) < castFin (ord v) ↔ ord u < ord v := by
    rw [castFin_eq, castFin_eq, Fin.cast_lt_cast]
  rw [hcast, hord]
  change (T.componentIndex ((sublinkComponentEquiv D B C₁).1)).val <
      (T.componentIndex ((sublinkComponentEquiv D B C₂).1)).val ↔ _
  rfl

private theorem inducedSublink_componentIndex_eq_iff
    (C₁ C₂ : diagramComponent (restrictSublink D B)) :
    (inducedSublinkTraversal B T).componentIndex C₁ =
        (inducedSublinkTraversal B T).componentIndex C₂ ↔
      T.componentIndex ((sublinkComponentEquiv D B C₁).1) =
        T.componentIndex ((sublinkComponentEquiv D B C₂).1) := by
  constructor
  · intro h
    have hC : C₁ = C₂ := (inducedSublinkTraversal B T).componentIndex.injective h
    subst C₂
    rfl
  · intro h
    have hsel : (sublinkComponentEquiv D B C₁).1 = (sublinkComponentEquiv D B C₂).1 :=
      T.componentIndex.injective h
    have hC : C₁ = C₂ := (sublinkComponentEquiv D B).injective (Subtype.ext hsel)
    subst C₂
    rfl

theorem inducedSublink_baseArc_old (C' : diagramComponent (restrictSublink D B)) :
    sublinkOldArc D B ((inducedSublinkTraversal B T).baseArc C').val =
      (T.baseArc (sublinkComponentEquiv D B C').1).val := by
  simp [inducedSublinkTraversal, sublinkOldArc]

private noncomputable def sublinkRestrictedFibreEquiv
    (C' : diagramComponent (restrictSublink D B)) :
    Fibre (restrictSublink D B).continuation C' ≃
      Fibre D.continuation (sublinkComponentEquiv D B C').1 where
  toFun x := ⟨sublinkOldArc D B x.val, by
    have hx := congrArg Subtype.val (sublinkComponentEquiv_componentOf D B x.val)
    rw [x.property] at hx
    exact hx.symm⟩
  invFun y := by
    let Csel := sublinkComponentEquiv D B C'
    have hy : componentOf D.continuation y.val ∈ B.components := by
      rw [y.property]
      exact Csel.2
    let a : SublinkArc D B := ⟨y.val, hy⟩
    refine ⟨(sublinkArcEquiv D B).symm a, ?_⟩
    apply (sublinkComponentEquiv D B).injective
    rw [sublinkComponentEquiv_componentOf]
    apply Subtype.ext
    change componentOf D.continuation
      (sublinkOldArc D B ((sublinkArcEquiv D B).symm a)) = Csel.1
    simp only [sublinkOldArc, Equiv.apply_symm_apply]
    exact y.property
  left_inv x := by
    apply Subtype.ext
    apply (sublinkArcEquiv D B).injective
    apply Subtype.ext
    simp [sublinkOldArc, Equiv.apply_symm_apply]
  right_inv y := by
    apply Subtype.ext
    simp [sublinkOldArc, Equiv.apply_symm_apply]

private def fibreEquivOfEq {α : Type} (p : Equiv.Perm α) {c d : Component p}
    (h : c = d) : Fibre p c ≃ Fibre p d where
  toFun x := ⟨x.val, by rw [← h]; exact x.property⟩
  invFun x := ⟨x.val, by rw [h]; exact x.property⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl

@[simp] private theorem fibreEquivOfEq_val {α : Type} (p : Equiv.Perm α)
    {c d : Component p} (h : c = d) (x : Fibre p c) :
    (fibreEquivOfEq p h x).val = x.val := rfl

@[simp] private theorem fibreEquivOfEq_symm_val {α : Type} (p : Equiv.Perm α)
    {c d : Component p} (h : c = d) (x : Fibre p d) :
    ((fibreEquivOfEq p h).symm x).val = x.val := rfl

@[simp] private theorem sublinkRestrictedFibreEquiv_val
    (C' : diagramComponent (restrictSublink D B))
    (x : Fibre (restrictSublink D B).continuation C') :
    (sublinkRestrictedFibreEquiv B C' x).val = sublinkOldArc D B x.val := rfl

theorem visitPosition_inducedSublink_eq (a : Fin (restrictSublink D B).nArc) :
    visitPosition (inducedSublinkTraversal B T) a =
      visitPosition T (sublinkOldArc D B a) := by
  let C' := componentOf (restrictSublink D B).continuation a
  let Csel := sublinkComponentEquiv D B C'
  let C := componentOf D.continuation (sublinkOldArc D B a)
  have hcomp : componentOf D.continuation (sublinkOldArc D B a) = C := rfl
  have hC : Csel.1 = C := by
    have hx := congrArg Subtype.val (sublinkComponentEquiv_componentOf D B a)
    simpa only [C', C] using hx.symm
  let x : Fibre (restrictSublink D B).continuation C' := ⟨a, rfl⟩
  let e := sublinkRestrictedFibreEquiv B C'
  let eAll := e.trans (fibreEquivOfEq D.continuation
    (show Csel.1 = componentOf D.continuation (T.baseArc Csel.1).val from
      (T.baseArc Csel.1).property.symm))
  let rootR := (inducedSublinkTraversal B T).baseArc C'
  let rootP := T.baseArc Csel.1
  have hrootR : componentOf (restrictSublink D B).continuation rootR.val = C' :=
    rootR.property
  have hroot : componentOf D.continuation rootP.val = Csel.1 := rootP.property
  let eRootR : Fibre (restrictSublink D B).continuation C' ≃
      Fibre (restrictSublink D B).continuation
        (componentOf (restrictSublink D B).continuation rootR.val) :=
    fibreEquivOfEq (restrictSublink D B).continuation hrootR.symm
  let eCombined := eRootR.symm.trans eAll
  let xR := eRootR x
  let yP : Fibre D.continuation (componentOf D.continuation rootP.val) :=
    ⟨sublinkOldArc D B a, (hcomp.trans hC.symm).trans hroot.symm⟩
  have he : eCombined xR = yP := by
    calc
      eCombined xR = eAll (eRootR.symm (eRootR x)) := rfl
      _ = eAll x := congrArg eAll (eRootR.symm_apply_apply x)
      _ = yP := rfl
  let enumR := orbitEnumeration (restrictSublink D B).continuation rootR.val
  let enumP := orbitEnumeration D.continuation rootP.val
  have hcard : Fintype.card
      (Fibre (restrictSublink D B).continuation
        (componentOf (restrictSublink D B).continuation rootR.val)) =
      Fintype.card (Fibre D.continuation (componentOf D.continuation rootP.val)) :=
    Fintype.card_congr eCombined
  have heval (z : Fibre (restrictSublink D B).continuation
      (componentOf (restrictSublink D B).continuation rootR.val)) :
      (eCombined z).val = sublinkOldArc D B z.val := by
    simp [eCombined, eRootR, eAll, e]
  have hOrbit (i : Fin (Fintype.card
      (Fibre (restrictSublink D B).continuation
        (componentOf (restrictSublink D B).continuation rootR.val)))) :
      eCombined (enumR i) = enumP (Fin.cast hcard i) := by
    apply Subtype.ext
    rw [heval]
    rw [orbitEnumeration_apply_val, orbitEnumeration_apply_val,
      sublink_old_continuation_pow, inducedSublink_baseArc_old]
    simp [rootP, Csel]
  let iR := enumR.symm xR
  let iP := enumP.symm yP
  have hidx : Fin.cast hcard iR = iP := by
    apply enumP.injective
    calc
      enumP (Fin.cast hcard iR) = eCombined (enumR iR) := (hOrbit iR).symm
      _ = eCombined xR := congrArg eCombined (enumR.apply_symm_apply xR)
      _ = yP := he
      _ = enumP iP := (enumP.apply_symm_apply yP).symm
  let xRactual : Fibre (restrictSublink D B).continuation
      (componentOf (restrictSublink D B).continuation rootR.val) :=
    ⟨a, rfl.trans hrootR.symm⟩
  have hxR : xRactual = xR := by apply Subtype.ext; rfl
  let yPactual : Fibre D.continuation (componentOf D.continuation rootP.val) :=
    ⟨sublinkOldArc D B a, (hcomp.trans hC.symm).trans hroot.symm⟩
  have hyP : yP = yPactual := by apply Subtype.ext; rfl
  have hposR : visitPosition (inducedSublinkTraversal B T) a = iR.val := by
    unfold visitPosition
    change (enumR.symm xRactual).val = iR.val
    rw [hxR]
  have hposP : visitPosition T (sublinkOldArc D B a) = iP.val := by
    unfold visitPosition
    change (enumP.symm yPactual).val = iP.val
    rw [← hyP]
  rw [hposR, hposP]
  have hv := congrArg Fin.val hidx
  simpa [iR, iP] using hv

theorem rankBefore_inducedSublink_iff (a b : Fin (restrictSublink D B).nArc) :
    rankBefore (visitRank (inducedSublinkTraversal B T) a)
      (visitRank (inducedSublinkTraversal B T) b) ↔
    rankBefore (visitRank T (sublinkOldArc D B a)) (visitRank T (sublinkOldArc D B b)) := by
  have hidx := inducedSublink_componentIndex_lt_iff B T
    (componentOf (restrictSublink D B).continuation a)
    (componentOf (restrictSublink D B).continuation b)
  have hidx' :
      (inducedSublinkTraversal B T).componentIndex
          (componentOf (restrictSublink D B).continuation a) <
        (inducedSublinkTraversal B T).componentIndex
          (componentOf (restrictSublink D B).continuation b) ↔
      T.componentIndex (componentOf D.continuation (sublinkOldArc D B a)) <
        T.componentIndex (componentOf D.continuation (sublinkOldArc D B b)) := by
    simpa only [sublinkComponentEquiv_componentOf] using hidx
  have heq := inducedSublink_componentIndex_eq_iff B T
    (componentOf (restrictSublink D B).continuation a)
    (componentOf (restrictSublink D B).continuation b)
  have heq' :
      (inducedSublinkTraversal B T).componentIndex
          (componentOf (restrictSublink D B).continuation a) =
        (inducedSublinkTraversal B T).componentIndex
          (componentOf (restrictSublink D B).continuation b) ↔
      T.componentIndex (componentOf D.continuation (sublinkOldArc D B a)) =
        T.componentIndex (componentOf D.continuation (sublinkOldArc D B b)) := by
    simpa only [sublinkComponentEquiv_componentOf] using heq
  unfold rankBefore visitRank
  rw [visitPosition_inducedSublink_eq B T a, visitPosition_inducedSublink_eq B T b]
  simp only [Prod.fst, Prod.snd, hidx', heq']

theorem badAt_inducedSublink_iff (d : Fin (restrictSublink D B).nCrossing) :
    badAt (inducedSublinkTraversal B T) d ↔
      badAt T (sublinkOldCrossing D B d) := by
  classical
  let c := sublinkOldCrossing D B d
  rcases sublink_crossing_data_preserved D B d with ⟨_, hover, hincoming, _⟩
  have hfirst : firstVisitedBranch (inducedSublinkTraversal B T) d =
      firstVisitedBranch T c := by
    unfold firstVisitedBranch
    have hrank := rankBefore_inducedSublink_iff B T
      ((restrictSublink D B).incoming d 0) ((restrictSublink D B).incoming d 1)
    simpa [c, hincoming] using (if_congr hrank rfl rfl)
  simp [badAt, c, hfirst, hover]

theorem badCrossings_inducedSublink_mem_iff (d : Fin (restrictSublink D B).nCrossing) :
    d ∈ badCrossings (inducedSublinkTraversal B T) ↔
      sublinkOldCrossing D B d ∈ badCrossings T := by
  simp only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and]
  exact badAt_inducedSublink_iff B T d

end SublinkBasedTraversal

/-! ### Part 3: Sublink Smoothing Transport under Monochrome Pivot -/

section SublinkSmoothing
variable (D : PLLinkDiagram) (B : Sublink D) (c : Fin D.nCrossing)

def sublinkPivotSelected : Prop :=
  componentOf D.continuation (D.outgoing c 0) ∈ B.components

def PivotMonochrome : Prop :=
  ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∈ B.components ↔
    sublinkPivotSelected D B c

theorem pivotMonochrome_of_sublinkOldCrossing
    (cB : Fin (restrictSublink D B).nCrossing) :
    PivotMonochrome D B (sublinkOldCrossing D B cB) := by
  intro i
  have hi := (sublinkCrossingEquiv D B cB).property i
  have h0 := (sublinkCrossingEquiv D B cB).property 0
  exact ⟨fun _ => h0, fun _ => hi⟩

theorem pivotMonochrome_of_untouched
    (hc : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∉ B.components) :
    PivotMonochrome D B c := by
  intro i
  exact ⟨fun h => False.elim (hc i h), fun h => False.elim (hc 0 h)⟩

theorem sublink_incoming_selected_iff (hm : PivotMonochrome D B c) (i : Fin 2) :
    componentOf D.continuation (D.incoming c i) ∈ B.components ↔
      sublinkPivotSelected D B c := by
  have h := hm (D.through c i)
  rwa [← D.continuation_crossing c i, componentOf_apply] at h

def sublinkSmoothCodeSelected : SmoothArcCode D → Prop
  | Sum.inl a => componentOf D.continuation a ∈ B.components
  | Sum.inr _ => sublinkPivotSelected D B c

theorem sublinkSmoothCodeSelected_continuation (hm : PivotMonochrome D B c)
    (x : SmoothArcCode D) :
    sublinkSmoothCodeSelected D B c (smoothContinuationGeometryCode D c x) ↔
      sublinkSmoothCodeSelected D B c x := by
  cases x with
  | inl a =>
    by_cases h0 : a = D.incoming c 0
    · subst a
      rw [smoothContinuationGeometryCode_incoming_zero]
      exact (sublink_incoming_selected_iff D B c hm 0).symm
    · by_cases h1 : a = D.incoming c 1
      · subst a
        rw [smoothContinuationGeometryCode_incoming_one]
        exact (sublink_incoming_selected_iff D B c hm 1).symm
      · have ha : ∀ i, a ≠ D.incoming c i := by
          intro i; fin_cases i
          · exact h0
          · exact h1
        rw [smoothContinuationGeometryCode_other_arc D c a ha]
        simp only [sublinkSmoothCodeSelected, componentOf_apply]
  | inr i =>
    rw [smoothContinuationGeometryCode_connector]
    exact hm _

def sublinkSmoothArcSelected (a : Fin (smoothCrossing D c).nArc) : Prop :=
  sublinkSmoothCodeSelected D B c ((smoothArcEquiv D).symm a)

theorem sublinkSmoothArcSelected_continuation (hm : PivotMonochrome D B c)
    (a : Fin (smoothCrossing D c).nArc) :
    sublinkSmoothArcSelected D B c ((smoothCrossing D c).continuation a) ↔
      sublinkSmoothArcSelected D B c a := by
  simpa only [sublinkSmoothArcSelected, smoothCrossing, smoothContinuation, Equiv.trans_apply,
    Equiv.symm_apply_apply] using
    sublinkSmoothCodeSelected_continuation D B c hm ((smoothArcEquiv D).symm a)

theorem sublinkSmoothArcSelected_pow (hm : PivotMonochrome D B c)
    (n : ℕ) (a : Fin (smoothCrossing D c).nArc) :
    sublinkSmoothArcSelected D B c (((smoothCrossing D c).continuation ^ n) a) ↔
      sublinkSmoothArcSelected D B c a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply,
      sublinkSmoothArcSelected_continuation D B c hm, ih]

theorem sublinkSmoothArcSelected_sameCycle (hm : PivotMonochrome D B c)
    (a b : Fin (smoothCrossing D c).nArc)
    (h : (smoothCrossing D c).continuation.SameCycle a b) :
    sublinkSmoothArcSelected D B c a ↔ sublinkSmoothArcSelected D B c b := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact (sublinkSmoothArcSelected_pow D B c hm n a).symm

def sublinkSmoothComponentSelected (hm : PivotMonochrome D B c) :
    diagramComponent (smoothCrossing D c) → Prop :=
  Quotient.lift (sublinkSmoothArcSelected D B c)
    (fun a b h => propext (sublinkSmoothArcSelected_sameCycle D B c hm a b h))

@[simp] theorem sublinkSmoothComponentSelected_componentOf (hm : PivotMonochrome D B c)
    (a : Fin (smoothCrossing D c).nArc) :
    sublinkSmoothComponentSelected D B c hm (componentOf (smoothCrossing D c).continuation a) ↔
      sublinkSmoothArcSelected D B c a := Iff.rfl

def smoothSublink (hm : PivotMonochrome D B c) : Sublink (smoothCrossing D c) where
  components := {C | sublinkSmoothComponentSelected D B c hm C}
  nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty (SublinkArc D B))
    refine ⟨componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a.val)), ?_⟩
    change sublinkSmoothCodeSelected D B c ((smoothArcEquiv D).symm (smoothArcEquiv D (Sum.inl a.val)))
    simpa only [Equiv.symm_apply_apply, sublinkSmoothCodeSelected] using a.property

@[simp] theorem mem_smoothSublink_componentOf (hm : PivotMonochrome D B c)
    (a : Fin (smoothCrossing D c).nArc) :
    componentOf (smoothCrossing D c).continuation a ∈ (smoothSublink D B c hm).components ↔
      sublinkSmoothArcSelected D B c a := Iff.rfl

@[simp] theorem mem_smoothSublink_old (hm : PivotMonochrome D B c) (a : Fin D.nArc) :
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a)) ∈
      (smoothSublink D B c hm).components ↔ componentOf D.continuation a ∈ B.components := by
  simp only [mem_smoothSublink_componentOf, sublinkSmoothArcSelected,
    Equiv.symm_apply_apply, sublinkSmoothCodeSelected]

@[simp] theorem mem_smoothSublink_connector (hm : PivotMonochrome D B c) (i : Fin 2) :
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inr i)) ∈
      (smoothSublink D B c hm).components ↔ sublinkPivotSelected D B c := by
  simp only [mem_smoothSublink_componentOf, sublinkSmoothArcSelected,
    Equiv.symm_apply_apply, sublinkSmoothCodeSelected]

def sublinkSmoothSelectedArcCodeEquiv (hm : PivotMonochrome D B c) :
    SublinkArc (smoothCrossing D c) (smoothSublink D B c hm) ≃
      {x : SmoothArcCode D // sublinkSmoothCodeSelected D B c x} where
  toFun a := ⟨(smoothArcEquiv D).symm a.val, a.property⟩
  invFun x := ⟨smoothArcEquiv D x.val, by
    change sublinkSmoothCodeSelected D B c ((smoothArcEquiv D).symm (smoothArcEquiv D x.val))
    simpa only [Equiv.symm_apply_apply] using x.property⟩
  left_inv a := by apply Subtype.ext; exact (smoothArcEquiv D).apply_symm_apply a.val
  right_inv x := by apply Subtype.ext; exact (smoothArcEquiv D).symm_apply_apply x.val

theorem sublink_selected_restricted_crossing (cB : Fin (restrictSublink D B).nCrossing) :
    sublinkPivotSelected D B (sublinkOldCrossing D B cB) :=
  (sublinkCrossingEquiv D B cB).property 0

def sublinkSelectedSmoothCodeEquiv (cB : Fin (restrictSublink D B).nCrossing) :
    {x : SmoothArcCode D // sublinkSmoothCodeSelected D B (sublinkOldCrossing D B cB) x} ≃
      SmoothArcCode (restrictSublink D B) where
  toFun x := match x with
    | ⟨Sum.inl a, ha⟩ => Sum.inl ((sublinkArcEquiv D B).symm ⟨a, ha⟩)
    | ⟨Sum.inr i, _⟩ => Sum.inr i
  invFun x := match x with
    | Sum.inl a => ⟨Sum.inl (sublinkOldArc D B a), (sublinkArcEquiv D B a).property⟩
    | Sum.inr i => ⟨Sum.inr i, sublink_selected_restricted_crossing D B cB⟩
  left_inv := by
    rintro ⟨x, hx⟩
    cases x with
    | inl a =>
      apply Subtype.ext
      simp only [sublinkOldArc, Equiv.apply_symm_apply]
    | inr i => rfl
  right_inv := by
    intro x
    cases x with
    | inl a =>
      change Sum.inl ((sublinkArcEquiv D B).symm (sublinkArcEquiv D B a)) = Sum.inl a
      exact congrArg Sum.inl ((sublinkArcEquiv D B).symm_apply_apply a)
    | inr i => rfl

def sublinkSmoothRestrictionArcEquiv (cB : Fin (restrictSublink D B).nCrossing) :
    Fin (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))).nArc ≃
    Fin (smoothCrossing (restrictSublink D B) cB).nArc :=
  (sublinkArcEquiv _ _).trans
    ((sublinkSmoothSelectedArcCodeEquiv D B (sublinkOldCrossing D B cB)
      (pivotMonochrome_of_sublinkOldCrossing D B cB)).trans
      ((sublinkSelectedSmoothCodeEquiv D B cB).trans
        (smoothArcEquiv (restrictSublink D B))))

def sublinkSmoothCodeEmbedding : SmoothArcCode (restrictSublink D B) → SmoothArcCode D :=
  Sum.map (sublinkOldArc D B) id

@[simp] theorem sublinkSelectedSmoothCodeEquiv_inverse_val
    (cB : Fin (restrictSublink D B).nCrossing) (x : SmoothArcCode (restrictSublink D B)) :
    ((sublinkSelectedSmoothCodeEquiv D B cB).symm x).val = sublinkSmoothCodeEmbedding D B x := by
  cases x <;> rfl

theorem sublinkSmoothCodeEmbedding_continuation (cB : Fin (restrictSublink D B).nCrossing)
    (x : SmoothArcCode (restrictSublink D B)) :
    sublinkSmoothCodeEmbedding D B
        (smoothContinuationGeometryCode (restrictSublink D B) cB x) =
      smoothContinuationGeometryCode D (sublinkOldCrossing D B cB)
        (sublinkSmoothCodeEmbedding D B x) := by
  cases x with
  | inl a =>
    by_cases h0 : a = (restrictSublink D B).incoming cB 0
    · subst a
      rw [smoothContinuationGeometryCode_incoming_zero]
      have hh : sublinkOldArc D B ((restrictSublink D B).incoming cB 0) =
          D.incoming (sublinkOldCrossing D B cB) 0 := sublink_old_incoming D B cB 0
      simpa only [sublinkSmoothCodeEmbedding, Sum.map_inl, Sum.map_inr, id_eq, hh] using
        (smoothContinuationGeometryCode_incoming_zero D (sublinkOldCrossing D B cB)).symm
    · by_cases h1 : a = (restrictSublink D B).incoming cB 1
      · subst a
        rw [smoothContinuationGeometryCode_incoming_one]
        have hh : sublinkOldArc D B ((restrictSublink D B).incoming cB 1) =
            D.incoming (sublinkOldCrossing D B cB) 1 := sublink_old_incoming D B cB 1
        simpa only [sublinkSmoothCodeEmbedding, Sum.map_inl, Sum.map_inr, id_eq, hh] using
          (smoothContinuationGeometryCode_incoming_one D (sublinkOldCrossing D B cB)).symm
      · have ha : ∀ i, a ≠ (restrictSublink D B).incoming cB i := by
          intro i; fin_cases i
          · exact h0
          · exact h1
        have ho : ∀ i, sublinkOldArc D B a ≠ D.incoming (sublinkOldCrossing D B cB) i := by
          intro i hi
          apply ha i
          apply sublinkOldArc_injective D B
          exact hi.trans (sublink_old_incoming D B cB i).symm
        rw [smoothContinuationGeometryCode_other_arc _ cB a ha]
        simp only [sublinkSmoothCodeEmbedding, Sum.map_inl]
        rw [smoothContinuationGeometryCode_other_arc D
          (sublinkOldCrossing D B cB) (sublinkOldArc D B a) ho]
        congr 1
        exact sublink_old_next D B a
  | inr i =>
    change sublinkSmoothCodeEmbedding D B
        (smoothContinuationGeometryCode (restrictSublink D B) cB (Sum.inr i)) =
      smoothContinuationGeometryCode D (sublinkOldCrossing D B cB) (Sum.inr i)
    rw [smoothContinuationGeometryCode_connector, smoothContinuationGeometryCode_connector]
    simp only [sublinkSmoothCodeEmbedding, Sum.map_inl]
    congr 1
    exact sublink_old_outgoing D B cB _

def sublinkUntouchedSmoothCodeEquiv (hc : ¬ sublinkPivotSelected D B c) :
    {x : SmoothArcCode D // sublinkSmoothCodeSelected D B c x} ≃ SublinkArc D B where
  toFun x := match x with
    | ⟨Sum.inl a, ha⟩ => ⟨a, ha⟩
    | ⟨Sum.inr _, hi⟩ => False.elim (hc hi)
  invFun a := ⟨Sum.inl a.val, a.property⟩
  left_inv := by
    rintro ⟨x, hx⟩
    cases x with
    | inl a => rfl
    | inr i => exact False.elim (hc hx)
  right_inv _ := rfl

def sublinkUntouchedRestrictionArcEquiv
    (hc : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∉ B.components) :
    Fin (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))).nArc ≃
    Fin (restrictSublink D B).nArc :=
  (sublinkArcEquiv _ _).trans
    ((sublinkSmoothSelectedArcCodeEquiv D B c (pivotMonochrome_of_untouched D B c hc)).trans
      ((sublinkUntouchedSmoothCodeEquiv D B c (hc 0)).trans (sublinkArcEquiv D B).symm))

theorem sublink_selected_arc_not_incoming_of_untouched
    (hc : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∉ B.components)
    (a : SublinkArc D B) (i : Fin 2) :
    a.val ≠ D.incoming c i := by
  intro heq
  apply hc 0
  exact (sublink_incoming_selected_iff D B c
    (pivotMonochrome_of_untouched D B c hc) i).mp (heq ▸ a.property)

def SublinkSelectedRetainedCrossing :=
  {d : Fin D.nCrossing // d ≠ c ∧
    ∀ i, componentOf D.continuation (D.outgoing d i) ∈ B.components}

theorem sublinkSmoothCrossing_selected_iff (hm : PivotMonochrome D B c)
    (d : Fin (smoothCrossing D c).nCrossing) :
    (∀ i, componentOf (smoothCrossing D c).continuation ((smoothCrossing D c).outgoing d i) ∈
      (smoothSublink D B c hm).components) ↔
    ∀ i, componentOf D.continuation (D.outgoing ((smoothCrossingEquiv D c).symm d).val i) ∈
      B.components := by
  apply forall_congr'
  intro i
  change componentOf (smoothCrossing D c).continuation
    (smoothArcEquiv D (Sum.inl (D.outgoing ((smoothCrossingEquiv D c).symm d).val i))) ∈
      (smoothSublink D B c hm).components ↔ _
  exact mem_smoothSublink_old D B c hm _

def sublinkSmoothSelectedCrossingCodeEquiv (hm : PivotMonochrome D B c) :
    SublinkCrossing (smoothCrossing D c) (smoothSublink D B c hm) ≃
      SublinkSelectedRetainedCrossing D B c where
  toFun d := ⟨((smoothCrossingEquiv D c).symm d.val).val,
    ((smoothCrossingEquiv D c).symm d.val).property,
    (sublinkSmoothCrossing_selected_iff D B c hm d.val).mp d.property⟩
  invFun d := ⟨smoothCrossingEquiv D c ⟨d.val, d.property.1⟩,
    (sublinkSmoothCrossing_selected_iff D B c hm _).mpr (by
      simpa only [Equiv.symm_apply_apply] using d.property.2)⟩
  left_inv d := by
    apply Subtype.ext
    exact (smoothCrossingEquiv D c).apply_symm_apply d.val
  right_inv d := by
    apply Subtype.ext
    change ((smoothCrossingEquiv D c).symm
      (smoothCrossingEquiv D c ⟨d.val, d.property.1⟩)).val = d.val
    exact congrArg Subtype.val ((smoothCrossingEquiv D c).symm_apply_apply ⟨d.val, d.property.1⟩)

def sublinkSelectedDeletedCrossingEquiv (cB : Fin (restrictSublink D B).nCrossing) :
    SublinkSelectedRetainedCrossing D B (sublinkOldCrossing D B cB) ≃
      {d : Fin (restrictSublink D B).nCrossing // d ≠ cB} where
  toFun d := ⟨(sublinkCrossingEquiv D B).symm ⟨d.val, d.property.2⟩, by
    intro h
    apply d.property.1
    simpa only [sublinkOldCrossing, Equiv.apply_symm_apply] using
      congrArg (sublinkOldCrossing D B) h⟩
  invFun d := ⟨sublinkOldCrossing D B d.val,
    fun h => d.property (sublinkOldCrossing_injective D B h),
    (sublinkCrossingEquiv D B d.val).property⟩
  left_inv d := by
    apply Subtype.ext
    simp only [sublinkOldCrossing, Equiv.apply_symm_apply]
  right_inv d := by
    apply Subtype.ext
    exact (sublinkCrossingEquiv D B).symm_apply_apply d.val

def sublinkSmoothRestrictionCrossingEquiv (cB : Fin (restrictSublink D B).nCrossing) :
    Fin (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))).nCrossing ≃
    Fin (smoothCrossing (restrictSublink D B) cB).nCrossing :=
  (sublinkCrossingEquiv _ _).trans
    ((sublinkSmoothSelectedCrossingCodeEquiv D B (sublinkOldCrossing D B cB)
      (pivotMonochrome_of_sublinkOldCrossing D B cB)).trans
      ((sublinkSelectedDeletedCrossingEquiv D B cB).trans
        (smoothCrossingEquiv (restrictSublink D B) cB)))

def sublinkUntouchedSelectedCrossingEquiv (hc : ¬ sublinkPivotSelected D B c) :
    SublinkSelectedRetainedCrossing D B c ≃ SublinkCrossing D B where
  toFun d := ⟨d.val, d.property.2⟩
  invFun d := ⟨d.val, fun h => hc (h ▸ d.property 0), d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sublinkUntouchedRestrictionCrossingEquiv
    (hc : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∉ B.components) :
    Fin (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))).nCrossing ≃
    Fin (restrictSublink D B).nCrossing :=
  (sublinkCrossingEquiv _ _).trans
    ((sublinkSmoothSelectedCrossingCodeEquiv D B c (pivotMonochrome_of_untouched D B c hc)).trans
      ((sublinkUntouchedSelectedCrossingEquiv D B c (hc 0)).trans
        (sublinkCrossingEquiv D B).symm))

end SublinkSmoothing

/-! ### Part 4: Signed Diagram Isomorphisms for Smoothed and Switched Sublink Restrictions -/

section SublinkSignedIsos
variable (D : PLLinkDiagram) (B : Sublink D)

theorem sublink_selected_arc_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (a : Fin (smoothCrossing (restrictSublink D B) cB).nArc) :
    sublinkOldArc (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))
      ((sublinkSmoothRestrictionArcEquiv D B cB).symm a) =
    smoothArcEquiv D
      (sublinkSmoothCodeEmbedding D B ((smoothArcEquiv (restrictSublink D B)).symm a)) := by
  change (sublinkArcEquiv _ _ ((sublinkArcEquiv _ _).symm
    ((sublinkSmoothSelectedArcCodeEquiv D B (sublinkOldCrossing D B cB) _).symm
      ((sublinkSelectedSmoothCodeEquiv D B cB).symm
        ((smoothArcEquiv (restrictSublink D B)).symm a))))).val = _
  rw [Equiv.apply_symm_apply]
  change smoothArcEquiv D (((sublinkSelectedSmoothCodeEquiv D B cB).symm
    ((smoothArcEquiv (restrictSublink D B)).symm a)).val) = _
  rw [sublinkSelectedSmoothCodeEquiv_inverse_val]

theorem sublink_selected_crossing_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (d : Fin (smoothCrossing (restrictSublink D B) cB).nCrossing) :
    ((smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm
      (sublinkOldCrossing (smoothCrossing D (sublinkOldCrossing D B cB))
        (smoothSublink D B (sublinkOldCrossing D B cB)
          (pivotMonochrome_of_sublinkOldCrossing D B cB))
        ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d))).val =
      sublinkOldCrossing D B ((smoothCrossingEquiv (restrictSublink D B) cB).symm d).val := by
  let D' := smoothCrossing D (sublinkOldCrossing D B cB)
  let B' := smoothSublink D B (sublinkOldCrossing D B cB)
    (pivotMonochrome_of_sublinkOldCrossing D B cB)
  change ((smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm
    ((sublinkCrossingEquiv D' B' ((sublinkCrossingEquiv D' B').symm _)).val)).val = _
  rw [Equiv.apply_symm_apply]
  change ((smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm
    (smoothCrossingEquiv D (sublinkOldCrossing D B cB) _)).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem sublink_selected_incoming_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (d : Fin (smoothCrossing (restrictSublink D B) cB).nCrossing) (i : Fin 2) :
    (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))).incoming
      ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d) i =
    (sublinkSmoothRestrictionArcEquiv D B cB).symm
      ((smoothCrossing (restrictSublink D B) cB).incoming d i) := by
  let D' := smoothCrossing D (sublinkOldCrossing D B cB)
  let B' := smoothSublink D B (sublinkOldCrossing D B cB)
    (pivotMonochrome_of_sublinkOldCrossing D B cB)
  apply sublinkOldArc_injective D' B'
  have hp := sublink_restrict_incoming D' B'
    ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d) i
  rw [hp, sublink_selected_arc_inverse]
  change smoothArcEquiv D (Sum.inl (D.incoming
    (((smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm
      (sublinkOldCrossing D' B'
        ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d))).val) i)) = _
  rw [sublink_selected_crossing_inverse]
  simp only [smoothCrossing, smoothIncoming, Equiv.symm_apply_apply,
    sublinkSmoothCodeEmbedding, Sum.map_inl]
  congr 2
  exact (sublink_restrict_incoming D B _ i).symm

theorem sublink_selected_outgoing_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (d : Fin (smoothCrossing (restrictSublink D B) cB).nCrossing) (i : Fin 2) :
    (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))).outgoing
      ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d) i =
    (sublinkSmoothRestrictionArcEquiv D B cB).symm
      ((smoothCrossing (restrictSublink D B) cB).outgoing d i) := by
  let D' := smoothCrossing D (sublinkOldCrossing D B cB)
  let B' := smoothSublink D B (sublinkOldCrossing D B cB)
    (pivotMonochrome_of_sublinkOldCrossing D B cB)
  apply sublinkOldArc_injective D' B'
  have hp := sublink_restrict_outgoing D' B'
    ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d) i
  rw [hp, sublink_selected_arc_inverse]
  change smoothArcEquiv D (Sum.inl (D.outgoing
    (((smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm
      (sublinkOldCrossing D' B'
        ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d))).val) i)) = _
  rw [sublink_selected_crossing_inverse]
  simp only [smoothCrossing, smoothOutgoing, Equiv.symm_apply_apply,
    sublinkSmoothCodeEmbedding, Sum.map_inl]
  congr 2
  exact (sublink_restrict_outgoing D B _ i).symm

theorem sublink_selected_continuation_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (a : Fin (smoothCrossing (restrictSublink D B) cB).nArc) :
    (sublinkSmoothRestrictionArcEquiv D B cB).symm
      ((smoothCrossing (restrictSublink D B) cB).continuation a) =
    (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))).continuation
      ((sublinkSmoothRestrictionArcEquiv D B cB).symm a) := by
  let D' := smoothCrossing D (sublinkOldCrossing D B cB)
  let B' := smoothSublink D B (sublinkOldCrossing D B cB)
    (pivotMonochrome_of_sublinkOldCrossing D B cB)
  apply sublinkOldArc_injective D' B'
  have hn := sublink_restrict_next D' B' ((sublinkSmoothRestrictionArcEquiv D B cB).symm a)
  rw [sublink_selected_arc_inverse, hn, sublink_selected_arc_inverse]
  simp only [D', smoothCrossing, smoothContinuation, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact congrArg (smoothArcEquiv D)
    (sublinkSmoothCodeEmbedding_continuation D B cB ((smoothArcEquiv (restrictSublink D B)).symm a))

theorem sublink_selected_through_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (d : Fin (smoothCrossing (restrictSublink D B) cB).nCrossing) :
    (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))).through
      ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d) =
    (smoothCrossing (restrictSublink D B) cB).through d := by
  let D' := smoothCrossing D (sublinkOldCrossing D B cB)
  let B' := smoothSublink D B (sublinkOldCrossing D B cB)
    (pivotMonochrome_of_sublinkOldCrossing D B cB)
  change D.through (((smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm
    (sublinkOldCrossing D' B' ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d))).val) = _
  rw [sublink_selected_crossing_inverse]
  rfl

theorem sublink_selected_over_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (d : Fin (smoothCrossing (restrictSublink D B) cB).nCrossing) :
    (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB))).overBranch
      ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d) =
    (smoothCrossing (restrictSublink D B) cB).overBranch d := by
  let D' := smoothCrossing D (sublinkOldCrossing D B cB)
  let B' := smoothSublink D B (sublinkOldCrossing D B cB)
    (pivotMonochrome_of_sublinkOldCrossing D B cB)
  change D.overBranch (((smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm
    (sublinkOldCrossing D' B' ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d))).val) = _
  rw [sublink_selected_crossing_inverse]
  rfl

theorem sublink_selected_sign_inverse (cB : Fin (restrictSublink D B).nCrossing)
    (d : Fin (smoothCrossing (restrictSublink D B) cB).nCrossing) :
    crossingSign (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
      (smoothSublink D B (sublinkOldCrossing D B cB)
        (pivotMonochrome_of_sublinkOldCrossing D B cB)))
      ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d) =
    crossingSign (smoothCrossing (restrictSublink D B) cB) d := by
  rw [sublink_crossing_sign_preserved]
  let k := sublinkOldCrossing (smoothCrossing D (sublinkOldCrossing D B cB))
    (smoothSublink D B (sublinkOldCrossing D B cB)
      (pivotMonochrome_of_sublinkOldCrossing D B cB))
    ((sublinkSmoothRestrictionCrossingEquiv D B cB).symm d)
  let a := (smoothCrossingEquiv D (sublinkOldCrossing D B cB)).symm k
  let b := (smoothCrossingEquiv (restrictSublink D B) cB).symm d
  have ha := crossingSign_smoothRetained D (sublinkOldCrossing D B cB) a.val a.property
  have hb := crossingSign_smoothRetained (restrictSublink D B) cB b.val b.property
  have he : a.val = sublinkOldCrossing D B b.val :=
    sublink_selected_crossing_inverse D B cB d
  calc
    crossingSign (smoothCrossing D (sublinkOldCrossing D B cB)) k = crossingSign D a.val := by
      change crossingSign (smoothCrossing D (sublinkOldCrossing D B cB))
        (smoothCrossingEquiv D (sublinkOldCrossing D B cB) a) = crossingSign D a.val at ha
      have hk : smoothCrossingEquiv D (sublinkOldCrossing D B cB) a = k :=
        (smoothCrossingEquiv D (sublinkOldCrossing D B cB)).apply_symm_apply k
      exact hk ▸ ha
    _ = crossingSign D (sublinkOldCrossing D B b.val) := congrArg (crossingSign D) he
    _ = crossingSign (restrictSublink D B) b.val :=
      (sublink_crossing_sign_preserved D B b.val).symm
    _ = crossingSign (smoothCrossing (restrictSublink D B) cB) d := by
      change crossingSign (smoothCrossing (restrictSublink D B) cB)
        (smoothCrossingEquiv (restrictSublink D B) cB b) =
        crossingSign (restrictSublink D B) b.val at hb
      have hd : smoothCrossingEquiv (restrictSublink D B) cB b = d :=
        (smoothCrossingEquiv (restrictSublink D B) cB).apply_symm_apply d
      exact (hd ▸ hb).symm

def sublinkSmoothRestrictionSignedIso (cB : Fin (restrictSublink D B).nCrossing) :
    SignedDiagramIso
      (restrictSublink (smoothCrossing D (sublinkOldCrossing D B cB))
        (smoothSublink D B (sublinkOldCrossing D B cB)
          (pivotMonochrome_of_sublinkOldCrossing D B cB)))
      (smoothCrossing (restrictSublink D B) cB) where
  arcEquiv := sublinkSmoothRestrictionArcEquiv D B cB
  crossingEquiv := sublinkSmoothRestrictionCrossingEquiv D B cB
  incoming_map d i := by
    apply (sublinkSmoothRestrictionArcEquiv D B cB).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      sublink_selected_incoming_inverse D B cB
        (sublinkSmoothRestrictionCrossingEquiv D B cB d) i
  outgoing_map d i := by
    apply (sublinkSmoothRestrictionArcEquiv D B cB).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      sublink_selected_outgoing_inverse D B cB
        (sublinkSmoothRestrictionCrossingEquiv D B cB d) i
  continuation_map a := by
    apply (sublinkSmoothRestrictionArcEquiv D B cB).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      (sublink_selected_continuation_inverse D B cB
        (sublinkSmoothRestrictionArcEquiv D B cB a)).symm
  through_map d := by
    simpa only [Equiv.symm_apply_apply] using
      sublink_selected_through_inverse D B cB
        (sublinkSmoothRestrictionCrossingEquiv D B cB d)
  overBranch_map d := by
    simpa only [Equiv.symm_apply_apply] using
      sublink_selected_over_inverse D B cB
        (sublinkSmoothRestrictionCrossingEquiv D B cB d)
  crossingSign_map d := by
    simpa only [Equiv.symm_apply_apply] using
      sublink_selected_sign_inverse D B cB
        (sublinkSmoothRestrictionCrossingEquiv D B cB d)

variable (c : Fin D.nCrossing)
  (hc : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∉ B.components)

theorem sublink_untouched_arc_inverse (a : Fin (restrictSublink D B).nArc) :
    sublinkOldArc (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))
      ((sublinkUntouchedRestrictionArcEquiv D B c hc).symm a) =
    smoothArcEquiv D (Sum.inl (sublinkOldArc D B a)) := by
  change (sublinkArcEquiv _ _ ((sublinkArcEquiv _ _).symm
    ((sublinkSmoothSelectedArcCodeEquiv D B c _).symm
      ((sublinkUntouchedSmoothCodeEquiv D B c (hc 0)).symm
        (sublinkArcEquiv D B a))))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem sublink_untouched_crossing_inverse (d : Fin (restrictSublink D B).nCrossing) :
    ((smoothCrossingEquiv D c).symm
      (sublinkOldCrossing (smoothCrossing D c)
        (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))
        ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d))).val =
      sublinkOldCrossing D B d := by
  let D' := smoothCrossing D c
  let B' := smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)
  change ((smoothCrossingEquiv D c).symm
    ((sublinkCrossingEquiv D' B' ((sublinkCrossingEquiv D' B').symm _)).val)).val = _
  rw [Equiv.apply_symm_apply]
  change ((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c _)).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem sublink_untouched_incoming_inverse (d : Fin (restrictSublink D B).nCrossing)
    (i : Fin 2) :
    (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))).incoming
      ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d) i =
    (sublinkUntouchedRestrictionArcEquiv D B c hc).symm
      ((restrictSublink D B).incoming d i) := by
  let D' := smoothCrossing D c
  let B' := smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)
  apply sublinkOldArc_injective D' B'
  have hp := sublink_restrict_incoming D' B'
    ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d) i
  rw [hp, sublink_untouched_arc_inverse]
  change smoothArcEquiv D (Sum.inl (D.incoming
    (((smoothCrossingEquiv D c).symm
      (sublinkOldCrossing D' B'
        ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d))).val) i)) = _
  have hs := sublink_restrict_incoming D B d i
  rw [sublink_untouched_crossing_inverse, hs]

theorem sublink_untouched_outgoing_inverse (d : Fin (restrictSublink D B).nCrossing)
    (i : Fin 2) :
    (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))).outgoing
      ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d) i =
    (sublinkUntouchedRestrictionArcEquiv D B c hc).symm
      ((restrictSublink D B).outgoing d i) := by
  let D' := smoothCrossing D c
  let B' := smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)
  apply sublinkOldArc_injective D' B'
  have hp := sublink_restrict_outgoing D' B'
    ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d) i
  rw [hp, sublink_untouched_arc_inverse]
  change smoothArcEquiv D (Sum.inl (D.outgoing
    (((smoothCrossingEquiv D c).symm
      (sublinkOldCrossing D' B'
        ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d))).val) i)) = _
  have hs := sublink_restrict_outgoing D B d i
  rw [sublink_untouched_crossing_inverse, hs]

theorem sublink_untouched_continuation_inverse (a : Fin (restrictSublink D B).nArc) :
    (sublinkUntouchedRestrictionArcEquiv D B c hc).symm
      ((restrictSublink D B).continuation a) =
    (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))).continuation
      ((sublinkUntouchedRestrictionArcEquiv D B c hc).symm a) := by
  let D' := smoothCrossing D c
  let B' := smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)
  apply sublinkOldArc_injective D' B'
  have hn := sublink_restrict_next D' B' ((sublinkUntouchedRestrictionArcEquiv D B c hc).symm a)
  rw [sublink_untouched_arc_inverse, hn, sublink_untouched_arc_inverse]
  have ha : ∀ i, sublinkOldArc D B a ≠ D.incoming c i :=
    sublink_selected_arc_not_incoming_of_untouched D B c hc (sublinkArcEquiv D B a)
  simp only [D', smoothCrossing, smoothContinuation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [smoothContinuationGeometryCode_other_arc D c (sublinkOldArc D B a) ha]
  exact congrArg (fun x => smoothArcEquiv D (Sum.inl x)) (sublink_restrict_next D B a)

theorem sublink_untouched_through_inverse (d : Fin (restrictSublink D B).nCrossing) :
    (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))).through
      ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d) =
    (restrictSublink D B).through d := by
  let D' := smoothCrossing D c
  let B' := smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)
  change D.through (((smoothCrossingEquiv D c).symm
    (sublinkOldCrossing D' B' ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d))).val) = _
  rw [sublink_untouched_crossing_inverse]
  rfl

theorem sublink_untouched_over_inverse (d : Fin (restrictSublink D B).nCrossing) :
    (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))).overBranch
      ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d) =
    (restrictSublink D B).overBranch d := by
  let D' := smoothCrossing D c
  let B' := smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)
  change D.overBranch (((smoothCrossingEquiv D c).symm
    (sublinkOldCrossing D' B' ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d))).val) = _
  rw [sublink_untouched_crossing_inverse]
  rfl

theorem sublink_untouched_sign_inverse (d : Fin (restrictSublink D B).nCrossing) :
    crossingSign (restrictSublink (smoothCrossing D c)
      (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)))
      ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d) =
    crossingSign (restrictSublink D B) d := by
  rw [sublink_crossing_sign_preserved]
  let k := sublinkOldCrossing (smoothCrossing D c)
    (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc))
    ((sublinkUntouchedRestrictionCrossingEquiv D B c hc).symm d)
  let a := (smoothCrossingEquiv D c).symm k
  have ha := crossingSign_smoothRetained D c a.val a.property
  have he : a.val = sublinkOldCrossing D B d :=
    sublink_untouched_crossing_inverse D B c hc d
  calc
    crossingSign (smoothCrossing D c) k = crossingSign D a.val := by
      change crossingSign (smoothCrossing D c) (smoothCrossingEquiv D c a) =
        crossingSign D a.val at ha
      have hk : smoothCrossingEquiv D c a = k :=
        (smoothCrossingEquiv D c).apply_symm_apply k
      exact hk ▸ ha
    _ = crossingSign D (sublinkOldCrossing D B d) := congrArg (crossingSign D) he
    _ = crossingSign (restrictSublink D B) d :=
      (sublink_crossing_sign_preserved D B d).symm

def sublinkUntouchedRestrictionSignedIso :
    SignedDiagramIso
      (restrictSublink (smoothCrossing D c)
        (smoothSublink D B c (pivotMonochrome_of_untouched D B c hc)))
      (restrictSublink D B) where
  arcEquiv := sublinkUntouchedRestrictionArcEquiv D B c hc
  crossingEquiv := sublinkUntouchedRestrictionCrossingEquiv D B c hc
  incoming_map d i := by
    apply (sublinkUntouchedRestrictionArcEquiv D B c hc).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      sublink_untouched_incoming_inverse D B c hc
        (sublinkUntouchedRestrictionCrossingEquiv D B c hc d) i
  outgoing_map d i := by
    apply (sublinkUntouchedRestrictionArcEquiv D B c hc).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      sublink_untouched_outgoing_inverse D B c hc
        (sublinkUntouchedRestrictionCrossingEquiv D B c hc d) i
  continuation_map a := by
    apply (sublinkUntouchedRestrictionArcEquiv D B c hc).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      (sublink_untouched_continuation_inverse D B c hc
        (sublinkUntouchedRestrictionArcEquiv D B c hc a)).symm
  through_map d := by
    simpa only [Equiv.symm_apply_apply] using
      sublink_untouched_through_inverse D B c hc
        (sublinkUntouchedRestrictionCrossingEquiv D B c hc d)
  overBranch_map d := by
    simpa only [Equiv.symm_apply_apply] using
      sublink_untouched_over_inverse D B c hc
        (sublinkUntouchedRestrictionCrossingEquiv D B c hc d)
  crossingSign_map d := by
    simpa only [Equiv.symm_apply_apply] using
      sublink_untouched_sign_inverse D B c hc
        (sublinkUntouchedRestrictionCrossingEquiv D B c hc d)

/-! ### Part 5: Switched Sublink Restrictions -/

def switchSublink (c : Fin D.nCrossing) : Sublink (switchCrossing D c) where
  components := B.components
  nonempty := B.nonempty

@[simp] theorem sublinkOldCrossing_switchSublink (c : Fin D.nCrossing)
    (d : Fin (restrictSublink (switchCrossing D c) (switchSublink D B c)).nCrossing) :
    sublinkOldCrossing (switchCrossing D c) (switchSublink D B c) d =
      sublinkOldCrossing D B d := rfl

@[simp] theorem sublinkOldArc_switchSublink (c : Fin D.nCrossing)
    (a : Fin (restrictSublink (switchCrossing D c) (switchSublink D B c)).nArc) :
    sublinkOldArc (switchCrossing D c) (switchSublink D B c) a =
      sublinkOldArc D B a := rfl

def sublinkSwitchRestrictionSignedIso (cB : Fin (restrictSublink D B).nCrossing) :
    SignedDiagramIso
      (restrictSublink (switchCrossing D (sublinkOldCrossing D B cB))
        (switchSublink D B (sublinkOldCrossing D B cB)))
      (switchCrossing (restrictSublink D B) cB) where
  arcEquiv := Equiv.refl _
  crossingEquiv := Equiv.refl _
  incoming_map _ _ := rfl
  outgoing_map _ _ := rfl
  continuation_map _ := rfl
  through_map _ := rfl
  overBranch_map d := by
    change (switchCrossing D (sublinkOldCrossing D B cB)).overBranch
        (sublinkOldCrossing (switchCrossing D (sublinkOldCrossing D B cB))
          (switchSublink D B (sublinkOldCrossing D B cB)) d) =
      (switchCrossing (restrictSublink D B) cB).overBranch d
    rw [sublinkOldCrossing_switchSublink]
    by_cases hd : d = cB
    · subst d
      simp [switchCrossing, restrictSublink]
    · have hdc : sublinkOldCrossing D B d ≠ sublinkOldCrossing D B cB :=
        fun h => hd (sublinkOldCrossing_injective D B h)
      simp [switchCrossing, restrictSublink, hd, hdc]
  crossingSign_map d := by
    rw [sublink_crossing_sign_preserved (switchCrossing D (sublinkOldCrossing D B cB))
      (switchSublink D B (sublinkOldCrossing D B cB)) d]
    by_cases hd : d = cB
    · subst d
      change crossingSign (switchCrossing D (sublinkOldCrossing D B cB))
          (sublinkOldCrossing D B cB) =
        crossingSign (switchCrossing (restrictSublink D B) cB) cB
      calc
        _ = (crossingSign D (sublinkOldCrossing D B cB)).reverse :=
          crossingSign_switchCrossing D (sublinkOldCrossing D B cB)
        _ = (crossingSign (restrictSublink D B) cB).reverse :=
          congrArg Sign.reverse (sublink_crossing_sign_preserved D B cB).symm
        _ = crossingSign (switchCrossing (restrictSublink D B) cB) cB :=
          (crossingSign_switchCrossing (restrictSublink D B) cB).symm
    · have hdc : sublinkOldCrossing D B d ≠ sublinkOldCrossing D B cB :=
        fun h => hd (sublinkOldCrossing_injective D B h)
      change crossingSign (switchCrossing D (sublinkOldCrossing D B cB))
          (sublinkOldCrossing D B d) =
        crossingSign (switchCrossing (restrictSublink D B) cB) d
      calc
        _ = crossingSign D (sublinkOldCrossing D B d) :=
          crossingSign_switchCrossing_of_ne D (sublinkOldCrossing D B cB)
            (sublinkOldCrossing D B d) hdc
        _ = crossingSign (restrictSublink D B) d :=
          (sublink_crossing_sign_preserved D B d).symm
        _ = crossingSign (switchCrossing (restrictSublink D B) cB) d :=
          (crossingSign_switchCrossing_of_ne (restrictSublink D B) cB d hd).symm

def sublinkUntouchedSwitchRestrictionSignedIso (c : Fin D.nCrossing)
    (hc : ¬ sublinkPivotSelected D B c) :
    SignedDiagramIso
      (restrictSublink (switchCrossing D c) (switchSublink D B c))
      (restrictSublink D B) where
  arcEquiv := Equiv.refl _
  crossingEquiv := Equiv.refl _
  incoming_map _ _ := rfl
  outgoing_map _ _ := rfl
  continuation_map _ := rfl
  through_map _ := rfl
  overBranch_map d := by
    have hdc : sublinkOldCrossing D B d ≠ c := by
      intro heq
      exact hc (heq ▸ (sublinkCrossingEquiv D B d).property 0)
    change (switchCrossing D c).overBranch
      (sublinkOldCrossing (switchCrossing D c) (switchSublink D B c) d) =
      D.overBranch (sublinkOldCrossing D B d)
    rw [sublinkOldCrossing_switchSublink]
    simp [switchCrossing, hdc]
  crossingSign_map d := by
    have hdc : sublinkOldCrossing D B d ≠ c := by
      intro heq
      exact hc (heq ▸ (sublinkCrossingEquiv D B d).property 0)
    rw [sublink_crossing_sign_preserved (switchCrossing D c) (switchSublink D B c) d,
      sublinkOldCrossing_switchSublink]
    calc
      crossingSign (switchCrossing D c) (sublinkOldCrossing D B d) =
          crossingSign D (sublinkOldCrossing D B d) :=
        crossingSign_switchCrossing_of_ne D c (sublinkOldCrossing D B d) hdc
      _ = crossingSign (restrictSublink D B) d :=
        (sublink_crossing_sign_preserved D B d).symm

end SublinkSignedIsos

end GeminiLowest
