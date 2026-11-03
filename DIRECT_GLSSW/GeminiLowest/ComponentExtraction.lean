import GeminiLowest.ZFloorAndRowAlgebra

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

/-! ### Part 1: Arbitrary Nonempty Sublink Restriction (`Sublink` without `crossing_closed`) -/

structure Sublink (D : PLLinkDiagram) where
  components : Set (diagramComponent D)
  nonempty : components.Nonempty

variable (D : PLLinkDiagram) (B : Sublink D)

def SublinkArc := {a : Fin D.nArc // componentOf D.continuation a ∈ B.components}

instance : Fintype (SublinkArc D B) := by
  classical
  unfold SublinkArc
  infer_instance

instance : Nonempty (SublinkArc D B) := by
  obtain ⟨c, hc⟩ := B.nonempty
  obtain ⟨a⟩ := fibreNonempty D.continuation c
  exact ⟨⟨a.val, by simpa only [a.property] using hc⟩⟩

def sublinkPerm : Equiv.Perm (SublinkArc D B) :=
  D.continuation.subtypePerm (fun _ => by simp)

@[simp] theorem sublinkPerm_apply_val (a : SublinkArc D B) :
    (sublinkPerm D B a).val = D.continuation a.val := rfl

def SublinkVertex := {v : Fin D.nVertex // ∃ a : SublinkArc D B, D.arcSource a.val = v}

def SublinkCrossing :=
  {c : Fin D.nCrossing // ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∈ B.components}

instance : Fintype (SublinkVertex D B) := by
  classical
  unfold SublinkVertex
  infer_instance

instance : Fintype (SublinkCrossing D B) := by
  classical
  unfold SublinkCrossing
  infer_instance

def sublinkSource (a : SublinkArc D B) : SublinkVertex D B :=
  ⟨D.arcSource a.val, a, rfl⟩

def sublinkTarget (a : SublinkArc D B) : SublinkVertex D B :=
  ⟨D.arcTarget a.val, sublinkPerm D B a, (D.continuation_incidence a.val).symm⟩

def sublinkOut (c : SublinkCrossing D B) (i : Fin 2) : SublinkArc D B :=
  ⟨D.outgoing c.val i, c.property i⟩

def sublinkInc (c : SublinkCrossing D B) (i : Fin 2) : SublinkArc D B :=
  ⟨D.incoming c.val i, by
    have h := c.property (D.through c.val i)
    rw [← D.continuation_crossing c.val i, componentOf_apply] at h
    exact h⟩

def sublinkVertex (c : SublinkCrossing D B) : SublinkVertex D B :=
  ⟨D.crossingVertex c.val, sublinkOut D B c 0, D.outgoing_source c.val 0⟩

@[simp] theorem sublinkSource_val (a : SublinkArc D B) :
    (sublinkSource D B a).val = D.arcSource a.val := rfl
@[simp] theorem sublinkTarget_val (a : SublinkArc D B) :
    (sublinkTarget D B a).val = D.arcTarget a.val := rfl
@[simp] theorem sublinkOut_val (c : SublinkCrossing D B) (i : Fin 2) :
    (sublinkOut D B c i).val = D.outgoing c.val i := rfl
@[simp] theorem sublinkInc_val (c : SublinkCrossing D B) (i : Fin 2) :
    (sublinkInc D B c i).val = D.incoming c.val i := rfl
@[simp] theorem sublinkVertex_val (c : SublinkCrossing D B) :
    (sublinkVertex D B c).val = D.crossingVertex c.val := rfl

@[simp] theorem sublinkTarget_eq_source_next (a : SublinkArc D B) :
    sublinkTarget D B a = sublinkSource D B (sublinkPerm D B a) :=
  Subtype.ext (D.continuation_incidence a.val)

theorem sublink_source_crossing_iff (c : Fin D.nCrossing) (e : Fin D.nArc) :
    D.arcSource e = D.crossingVertex c ↔ e = D.outgoing c 0 ∨ e = D.outgoing c 1 := by
  constructor
  · intro h
    rcases (D.crossing_incidence_complete c e).mp (Or.inl h) with h0 | h1 | h0 | h1
    · exact False.elim (D.arc_endpoints_distinct e (h.trans (h0 ▸ D.incoming_target c 0).symm))
    · exact False.elim (D.arc_endpoints_distinct e (h.trans (h1 ▸ D.incoming_target c 1).symm))
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (rfl | rfl) <;> exact D.outgoing_source _ _

theorem sublink_regular_source_unique (v : SublinkVertex D B)
    (hv : ∀ c : SublinkCrossing D B, sublinkVertex D B c ≠ v)
    (a b : SublinkArc D B) (ha : sublinkSource D B a = v) (hb : sublinkSource D B b = v) :
    a = b := by
  classical
  apply Subtype.ext
  have ha' : D.arcSource a.val = v.val := congrArg Subtype.val ha
  have hb' : D.arcSource b.val = v.val := congrArg Subtype.val hb
  by_cases hcross : ∃ c, D.crossingVertex c = v.val
  · obtain ⟨c, hc⟩ := hcross
    have hA := (sublink_source_crossing_iff D c a.val).mp (ha'.trans hc.symm)
    have hB := (sublink_source_crossing_iff D c b.val).mp (hb'.trans hc.symm)
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hA.trans hB.symm
    · exfalso
      have hm : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∈ B.components := by
        intro i; fin_cases i
        · exact hA ▸ a.property
        · exact hB ▸ b.property
      exact hv ⟨c, hm⟩ (Subtype.ext hc)
    · exfalso
      have hm : ∀ i : Fin 2, componentOf D.continuation (D.outgoing c i) ∈ B.components := by
        intro i; fin_cases i
        · exact hB ▸ b.property
        · exact hA ▸ a.property
      exact hv ⟨c, hm⟩ (Subtype.ext hc)
    · exact hA.trans hB.symm
  · have hd := (D.regular_degree_one v.val (by simpa using hcross)).2
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hd
    have hma : a.val ∈ outgoingArcs D.arcSource v.val := by simp [outgoingArcs, ha']
    have hmb : b.val ∈ outgoingArcs D.arcSource v.val := by simp [outgoingArcs, hb']
    rw [he, Finset.mem_singleton] at hma hmb
    exact hma.trans hmb.symm

theorem sublink_regular_existsUnique_source (v : SublinkVertex D B)
    (hv : ∀ c : SublinkCrossing D B, sublinkVertex D B c ≠ v) :
    ∃! a, sublinkSource D B a = v := by
  obtain ⟨a, ha⟩ := v.property
  refine ⟨a, Subtype.ext ha, ?_⟩
  intro b hb
  exact sublink_regular_source_unique D B v hv b a hb (Subtype.ext ha)

theorem sublink_regular_existsUnique_target (v : SublinkVertex D B)
    (hv : ∀ c : SublinkCrossing D B, sublinkVertex D B c ≠ v) :
    ∃! a, sublinkTarget D B a = v := by
  obtain ⟨a, ha, hu⟩ := sublink_regular_existsUnique_source D B v hv
  refine ⟨(sublinkPerm D B).symm a, ?_, ?_⟩
  · simpa only [sublinkTarget_eq_source_next, Equiv.apply_symm_apply] using ha
  · intro b hb
    apply (sublinkPerm D B).injective
    simpa using hu (sublinkPerm D B b) (by simpa only [← sublinkTarget_eq_source_next] using hb)

def sublinkArcEquiv : Fin (Fintype.card (SublinkArc D B)) ≃ SublinkArc D B :=
  (Fintype.equivFin _).symm
def sublinkVertexEquiv : Fin (Fintype.card (SublinkVertex D B)) ≃ SublinkVertex D B :=
  (Fintype.equivFin _).symm
def sublinkCrossingEquiv : Fin (Fintype.card (SublinkCrossing D B)) ≃ SublinkCrossing D B :=
  (Fintype.equivFin _).symm

abbrev sublinkOldArc (a : Fin (Fintype.card (SublinkArc D B))) := (sublinkArcEquiv D B a).val
abbrev sublinkOldVertex (v : Fin (Fintype.card (SublinkVertex D B))) := (sublinkVertexEquiv D B v).val
abbrev sublinkOldCrossing (c : Fin (Fintype.card (SublinkCrossing D B))) := (sublinkCrossingEquiv D B c).val

def sublinkSourceIndex (a : Fin (Fintype.card (SublinkArc D B))) :=
  (sublinkVertexEquiv D B).symm (sublinkSource D B (sublinkArcEquiv D B a))
def sublinkTargetIndex (a : Fin (Fintype.card (SublinkArc D B))) :=
  (sublinkVertexEquiv D B).symm (sublinkTarget D B (sublinkArcEquiv D B a))
def sublinkCrossingIndex (c : Fin (Fintype.card (SublinkCrossing D B))) :=
  (sublinkVertexEquiv D B).symm (sublinkVertex D B (sublinkCrossingEquiv D B c))
def sublinkIncomingIndex (c : Fin (Fintype.card (SublinkCrossing D B))) (i : Fin 2) :=
  (sublinkArcEquiv D B).symm (sublinkInc D B (sublinkCrossingEquiv D B c) i)
def sublinkOutgoingIndex (c : Fin (Fintype.card (SublinkCrossing D B))) (i : Fin 2) :=
  (sublinkArcEquiv D B).symm (sublinkOut D B (sublinkCrossingEquiv D B c) i)
def sublinkNext : Equiv.Perm (Fin (Fintype.card (SublinkArc D B))) :=
  (sublinkArcEquiv D B).trans ((sublinkPerm D B).trans (sublinkArcEquiv D B).symm)

@[simp] theorem sublink_old_source (a) :
    sublinkOldVertex D B (sublinkSourceIndex D B a) = D.arcSource (sublinkOldArc D B a) := by
  simp only [sublinkOldVertex, sublinkOldArc, sublinkSourceIndex, Equiv.apply_symm_apply, sublinkSource_val]
@[simp] theorem sublink_old_target (a) :
    sublinkOldVertex D B (sublinkTargetIndex D B a) = D.arcTarget (sublinkOldArc D B a) := by
  simp only [sublinkOldVertex, sublinkOldArc, sublinkTargetIndex, Equiv.apply_symm_apply, sublinkTarget_val]
@[simp] theorem sublink_old_crossing (c) :
    sublinkOldVertex D B (sublinkCrossingIndex D B c) = D.crossingVertex (sublinkOldCrossing D B c) := by
  simp only [sublinkOldVertex, sublinkOldCrossing, sublinkCrossingIndex, Equiv.apply_symm_apply, sublinkVertex_val]
@[simp] theorem sublink_old_incoming (c) (i) :
    sublinkOldArc D B (sublinkIncomingIndex D B c i) = D.incoming (sublinkOldCrossing D B c) i := by
  simp only [sublinkOldArc, sublinkOldCrossing, sublinkIncomingIndex, Equiv.apply_symm_apply, sublinkInc_val]
@[simp] theorem sublink_old_outgoing (c) (i) :
    sublinkOldArc D B (sublinkOutgoingIndex D B c i) = D.outgoing (sublinkOldCrossing D B c) i := by
  simp only [sublinkOldArc, sublinkOldCrossing, sublinkOutgoingIndex, Equiv.apply_symm_apply, sublinkOut_val]
@[simp] theorem sublink_old_next (a) :
    sublinkOldArc D B (sublinkNext D B a) = D.continuation (sublinkOldArc D B a) := by
  simp only [sublinkOldArc, sublinkNext, Equiv.trans_apply, Equiv.apply_symm_apply, sublinkPerm_apply_val]

theorem sublinkOldArc_injective : Function.Injective (sublinkOldArc D B) :=
  Subtype.val_injective.comp (sublinkArcEquiv D B).injective
theorem sublinkOldVertex_injective : Function.Injective (sublinkOldVertex D B) :=
  Subtype.val_injective.comp (sublinkVertexEquiv D B).injective
theorem sublinkOldCrossing_injective : Function.Injective (sublinkOldCrossing D B) :=
  Subtype.val_injective.comp (sublinkCrossingEquiv D B).injective

theorem sublink_regular_index_degree (v : Fin (Fintype.card (SublinkVertex D B)))
    (hv : ∀ c, sublinkCrossingIndex D B c ≠ v) :
    (incomingArcs (sublinkTargetIndex D B) v).card = 1 ∧
      (outgoingArcs (sublinkSourceIndex D B) v).card = 1 := by
  classical
  have hv' : ∀ c, sublinkVertex D B c ≠ sublinkVertexEquiv D B v := by
    intro c h
    apply hv ((sublinkCrossingEquiv D B).symm c)
    simpa [sublinkCrossingIndex] using congrArg (sublinkVertexEquiv D B).symm h
  have hs := sublink_regular_existsUnique_source D B (sublinkVertexEquiv D B v) hv'
  have ht := sublink_regular_existsUnique_target D B (sublinkVertexEquiv D B v) hv'
  constructor
  · obtain ⟨a, ha, hu⟩ := ht
    apply Finset.card_eq_one.mpr
    refine ⟨(sublinkArcEquiv D B).symm a, ?_⟩
    ext b
    simp only [incomingArcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply (sublinkArcEquiv D B).injective
      simpa using hu (sublinkArcEquiv D B b) (by simpa [sublinkTargetIndex] using congrArg (sublinkVertexEquiv D B) h)
    · rintro rfl
      simpa [sublinkTargetIndex] using congrArg (sublinkVertexEquiv D B).symm ha
  · obtain ⟨a, ha, hu⟩ := hs
    apply Finset.card_eq_one.mpr
    refine ⟨(sublinkArcEquiv D B).symm a, ?_⟩
    ext b
    simp only [outgoingArcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply (sublinkArcEquiv D B).injective
      simpa using hu (sublinkArcEquiv D B b) (by simpa [sublinkSourceIndex] using congrArg (sublinkVertexEquiv D B) h)
    · rintro rfl
      simpa [sublinkSourceIndex] using congrArg (sublinkVertexEquiv D B).symm ha

def restrictSublink : PLLinkDiagram where
  nVertex := Fintype.card (SublinkVertex D B)
  nArc := Fintype.card (SublinkArc D B)
  nCrossing := Fintype.card (SublinkCrossing D B)
  vertexPoint := fun v => D.vertexPoint (sublinkOldVertex D B v)
  arcSource := sublinkSourceIndex D B
  arcTarget := sublinkTargetIndex D B
  crossingVertex := sublinkCrossingIndex D B
  crossingVertex_injective := by
    intro c d h
    apply sublinkOldCrossing_injective D B
    apply D.crossingVertex_injective
    simpa using congrArg (sublinkOldVertex D B) h
  incoming := sublinkIncomingIndex D B
  outgoing := sublinkOutgoingIndex D B
  incoming_target := by
    intro c i; apply sublinkOldVertex_injective D B
    simpa using D.incoming_target (sublinkOldCrossing D B c) i
  outgoing_source := by
    intro c i; apply sublinkOldVertex_injective D B
    simpa using D.outgoing_source (sublinkOldCrossing D B c) i
  four_ports_distinct := by
    intro c
    obtain ⟨hi, ho, hm⟩ := D.four_ports_distinct (sublinkOldCrossing D B c)
    refine ⟨?_, ?_, ?_⟩
    · intro h; apply hi; simpa using congrArg (sublinkOldArc D B) h
    · intro h; apply ho; simpa using congrArg (sublinkOldArc D B) h
    · intro i j h; apply hm i j; simpa using congrArg (sublinkOldArc D B) h
  crossing_incidence_complete := by
    intro c a
    have heq : ∀ a b, sublinkOldArc D B a = sublinkOldArc D B b ↔ a = b :=
      fun _ _ => (sublinkOldArc_injective D B).eq_iff
    have hveq : ∀ a b, sublinkOldVertex D B a = sublinkOldVertex D B b ↔ a = b :=
      fun _ _ => (sublinkOldVertex_injective D B).eq_iff
    simpa only [← heq, ← hveq, sublink_old_source, sublink_old_target, sublink_old_crossing,
      sublink_old_incoming, sublink_old_outgoing]
      using D.crossing_incidence_complete (sublinkOldCrossing D B c) (sublinkOldArc D B a)
  regular_degree_one := sublink_regular_index_degree D B
  through := fun c => D.through (sublinkOldCrossing D B c)
  continuation := sublinkNext D B
  continuation_incidence := by
    intro a; apply sublinkOldVertex_injective D B
    simpa using D.continuation_incidence (sublinkOldArc D B a)
  continuation_crossing := by
    intro c i; apply sublinkOldArc_injective D B
    simpa using D.continuation_crossing (sublinkOldCrossing D B c) i
  overBranch := fun c => D.overBranch (sublinkOldCrossing D B c)
  vertexPoint_injective := D.vertexPoint_injective.comp (sublinkOldVertex_injective D B)
  arc_endpoints_distinct := by
    intro a h
    apply D.arc_endpoints_distinct (sublinkOldArc D B a)
    simpa using congrArg (sublinkOldVertex D B) h
  arc_interiors_disjoint := by
    intro a b hab s t hs hs' ht ht'
    simpa only [sublink_old_source, sublink_old_target] using
      D.arc_interiors_disjoint (sublinkOldArc D B a) (sublinkOldArc D B b)
        (fun h => hab (sublinkOldArc_injective D B h)) s t hs hs' ht ht'
  vertices_avoid_arc_interiors := by
    intro v a t ht ht'
    simpa only [sublink_old_source, sublink_old_target] using
      D.vertices_avoid_arc_interiors (sublinkOldVertex D B v) (sublinkOldArc D B a) t ht ht'
  through_tangents_positive_collinear := by
    intro c i
    simpa only [sublink_old_crossing, sublink_old_source, sublink_old_target,
      sublink_old_incoming, sublink_old_outgoing]
      using D.through_tangents_positive_collinear (sublinkOldCrossing D B c) i
  crossing_transverse := by
    intro c
    simpa only [sublink_old_crossing, sublink_old_source, sublink_old_incoming]
      using D.crossing_transverse (sublinkOldCrossing D B c)

theorem sublink_arc_count_pos : 0 < (restrictSublink D B).nArc := by
  change 0 < Fintype.card (SublinkArc D B)
  exact Fintype.card_pos

theorem sublink_old_continuation_pow (n : ℕ) (a : Fin (restrictSublink D B).nArc) :
    sublinkOldArc D B (((restrictSublink D B).continuation ^ n) a) =
      (D.continuation ^ n) (sublinkOldArc D B a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    change sublinkOldArc D B (sublinkNext D B (((restrictSublink D B).continuation ^ n) a)) = _
    rw [sublink_old_next, ih]

theorem sublink_strand_tangent_preserved (c : Fin (restrictSublink D B).nCrossing) (i : Fin 2) :
    strandTangent (restrictSublink D B) c i = strandTangent D (sublinkOldCrossing D B c) i := by
  simp only [strandTangent, restrictSublink, sublink_old_crossing, sublink_old_source, sublink_old_incoming]

theorem sublink_crossing_det_preserved (c : Fin (restrictSublink D B).nCrossing) :
    crossingDet (restrictSublink D B) c = crossingDet D (sublinkOldCrossing D B c) := by
  unfold crossingDet
  rw [sublink_strand_tangent_preserved, sublink_strand_tangent_preserved]
  rfl

theorem sublink_crossing_sign_preserved (c : Fin (restrictSublink D B).nCrossing) :
    crossingSign (restrictSublink D B) c = crossingSign D (sublinkOldCrossing D B c) := by
  unfold crossingSign nonzeroScalarSign
  simp only [sublink_crossing_det_preserved]

/-! ### Part 2: Canonical `ComponentRestriction` and Single-Component Count -/

def singletonSublink (D : PLLinkDiagram) (C : diagramComponent D) : Sublink D where
  components := {C}
  nonempty := Set.singleton_nonempty C

def singletonArcEquiv (D : PLLinkDiagram) (C : diagramComponent D) :
    SublinkArc D (singletonSublink D C) ≃ ComponentArc D C where
  toFun a := ⟨a.val, a.property⟩
  invFun a := ⟨a.val, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def singletonVertexEquiv (D : PLLinkDiagram) (C : diagramComponent D) :
    SublinkVertex D (singletonSublink D C) ≃ ComponentVertex D C where
  toFun v := ⟨v.val, by
    obtain ⟨a, ha⟩ := v.property
    exact ⟨⟨a.val, a.property⟩, ha⟩⟩
  invFun v := ⟨v.val, by
    obtain ⟨a, ha⟩ := v.property
    exact ⟨⟨a.val, a.property⟩, ha⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def singletonCrossingEquiv (D : PLLinkDiagram) (C : diagramComponent D) :
    SublinkCrossing D (singletonSublink D C) ≃ ComponentCrossing D C where
  toFun c := ⟨c.val, by
    intro i
    have h := c.property (D.through c.val i)
    rw [← D.continuation_crossing c.val i, componentOf_apply] at h
    exact h⟩
  invFun c := ⟨c.val, by
    intro i
    have h := c.property ((D.through c.val).symm i)
    rw [← componentOf_apply D.continuation (D.incoming c.val ((D.through c.val).symm i)),
      D.continuation_crossing, Equiv.apply_symm_apply] at h
    exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl

def canonicalComponentRestriction (D : PLLinkDiagram) (C : diagramComponent D) :
    ComponentRestriction D C where
  diagram := restrictSublink D (singletonSublink D C)
  nonempty := sublink_arc_count_pos D (singletonSublink D C)
  arcEquiv := (sublinkArcEquiv D (singletonSublink D C)).trans (singletonArcEquiv D C)
  vertexEquiv := (sublinkVertexEquiv D (singletonSublink D C)).trans (singletonVertexEquiv D C)
  crossingEquiv := (sublinkCrossingEquiv D (singletonSublink D C)).trans (singletonCrossingEquiv D C)
  vertexPoint_eq := fun _ => rfl
  source_eq := fun a => sublink_old_source D (singletonSublink D C) a
  target_eq := fun a => sublink_old_target D (singletonSublink D C) a
  crossingVertex_eq := fun c => sublink_old_crossing D (singletonSublink D C) c
  incoming_eq := fun c i => sublink_old_incoming D (singletonSublink D C) c i
  outgoing_eq := fun c i => sublink_old_outgoing D (singletonSublink D C) c i
  continuation_eq := fun a => sublink_old_next D (singletonSublink D C) a
  through_eq := fun _ => rfl
  overBranch_eq := fun _ => rfl

/-! ### Part 3: Properties of Arbitrary `ComponentRestriction` and Evaluator Independence -/

theorem componentRestriction_arcEquiv_val_injective {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) :
    Function.Injective (fun a : Fin R.diagram.nArc => (R.arcEquiv a).val) :=
  Subtype.val_injective.comp R.arcEquiv.injective

theorem componentRestriction_crossingEquiv_val_injective {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) :
    Function.Injective (fun c : Fin R.diagram.nCrossing => (R.crossingEquiv c).val) :=
  Subtype.val_injective.comp R.crossingEquiv.injective

theorem componentRestriction_pow {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) (n : ℕ) (a : Fin R.diagram.nArc) :
    (R.arcEquiv ((R.diagram.continuation ^ n) a)).val =
      (D.continuation ^ n) (R.arcEquiv a).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    rw [R.continuation_eq, ih]

theorem componentRestriction_subsingleton_components {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) :
    Subsingleton (diagramComponent R.diagram) := by
  refine ⟨fun x y => ?_⟩
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  apply (componentOf_eq_iff R.diagram.continuation a b).mpr
  have ha : componentOf D.continuation (R.arcEquiv a).val = C := (R.arcEquiv a).property
  have hb : componentOf D.continuation (R.arcEquiv b).val = C := (R.arcEquiv b).property
  have hsc : D.continuation.SameCycle (R.arcEquiv a).val (R.arcEquiv b).val :=
    (componentOf_eq_iff D.continuation _ _).mp (ha.trans hb.symm)
  obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  apply componentRestriction_arcEquiv_val_injective R
  dsimp only
  rw [componentRestriction_pow R n a, hn]

theorem componentRestriction_componentCount_eq_one {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) :
    diagramComponentCount R.diagram = 1 := by
  letI : Fintype (diagramComponent R.diagram) := componentFintype R.diagram.continuation
  haveI : Subsingleton (diagramComponent R.diagram) :=
    componentRestriction_subsingleton_components R
  let c0 : diagramComponent R.diagram := componentOf R.diagram.continuation ⟨0, R.nonempty⟩
  exact Fintype.card_eq_one_iff.mpr ⟨c0, fun y => Subsingleton.elim y c0⟩

theorem componentRestriction_strandTangent {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) (c : Fin R.diagram.nCrossing) (i : Fin 2) :
    strandTangent R.diagram c i = strandTangent D (R.crossingEquiv c).val i := by
  unfold strandTangent
  rw [R.vertexPoint_eq, R.vertexPoint_eq, R.crossingVertex_eq, R.source_eq, R.incoming_eq]

theorem componentRestriction_crossingDet {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) (c : Fin R.diagram.nCrossing) :
    crossingDet R.diagram c = crossingDet D (R.crossingEquiv c).val := by
  unfold crossingDet
  rw [componentRestriction_strandTangent, componentRestriction_strandTangent, R.overBranch_eq]

theorem componentRestriction_crossingSign {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) (c : Fin R.diagram.nCrossing) :
    crossingSign R.diagram c = crossingSign D (R.crossingEquiv c).val := by
  unfold crossingSign nonzeroScalarSign
  simp only [componentRestriction_crossingDet]

def componentRestrictionSignedIso {D : PLLinkDiagram} {C : diagramComponent D}
    (R S : ComponentRestriction D C) :
    SignedDiagramIso R.diagram S.diagram where
  arcEquiv := R.arcEquiv.trans S.arcEquiv.symm
  crossingEquiv := R.crossingEquiv.trans S.crossingEquiv.symm
  incoming_map := by
    intro c i
    apply componentRestriction_arcEquiv_val_injective S
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [S.incoming_eq]
    simp only [Equiv.apply_symm_apply]
    exact R.incoming_eq c i
  outgoing_map := by
    intro c i
    apply componentRestriction_arcEquiv_val_injective S
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [S.outgoing_eq]
    simp only [Equiv.apply_symm_apply]
    exact R.outgoing_eq c i
  continuation_map := by
    intro a
    apply componentRestriction_arcEquiv_val_injective S
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [R.continuation_eq, S.continuation_eq]
    simp only [Equiv.apply_symm_apply]
  through_map := by
    intro c
    simp only [Equiv.trans_apply]
    rw [R.through_eq, S.through_eq]
    simp only [Equiv.apply_symm_apply]
  overBranch_map := by
    intro c
    simp only [Equiv.trans_apply]
    rw [R.overBranch_eq, S.overBranch_eq]
    simp only [Equiv.apply_symm_apply]
  crossingSign_map := by
    intro c
    simp only [Equiv.trans_apply]
    rw [componentRestriction_crossingSign R c, componentRestriction_crossingSign S]
    simp only [Equiv.apply_symm_apply]

theorem component_evaluator_independent :
    ∀ (D : PLLinkDiagram) (C : diagramComponent D) (R S : ComponentRestriction D C),
      candidateEvaluator R.diagram R.nonempty = candidateEvaluator S.diagram S.nonempty := by
  intro D C R S
  exact candidateEvaluator_signedDiagramIso all_lowerCrossingEvaluatorSkeinIH
    R.diagram S.diagram R.nonempty S.nonempty (componentRestrictionSignedIso R S)

end GeminiLowest
