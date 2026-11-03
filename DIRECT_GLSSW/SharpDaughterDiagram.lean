import SharpDaughterGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW PermutationOrbits
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
open PolygonDrawingBridge
def arcEquiv : Fin (Fintype.card (Arc q hq S C)) ≃ Arc q hq S C := (Fintype.equivFin _).symm
def vertexEquiv : Fin (Fintype.card (Vertex q hq S C)) ≃ Vertex q hq S C := (Fintype.equivFin _).symm
def crossingEquiv : Fin (Fintype.card (Crossing q hq S C)) ≃ Crossing q hq S C := (Fintype.equivFin _).symm
abbrev oldArc (a : Fin (Fintype.card (Arc q hq S C))) := eventFin q (arcEquiv q hq S C a).val
abbrev oldVertex (v : Fin (Fintype.card (Vertex q hq S C))) := (vertexEquiv q hq S C v).val
abbrev oldCrossing (c : Fin (Fintype.card (Crossing q hq S C))) := (crossingEquiv q hq S C c).val

def sourceIndex (a : Fin (Fintype.card (Arc q hq S C))) := (vertexEquiv q hq S C).symm (source q hq S C (arcEquiv q hq S C a))
def targetIndex (a : Fin (Fintype.card (Arc q hq S C))) := (vertexEquiv q hq S C).symm (target q hq S C (arcEquiv q hq S C a))
def crossingIndex (c : Fin (Fintype.card (Crossing q hq S C))) := (vertexEquiv q hq S C).symm (vertex q hq S C (crossingEquiv q hq S C c))
def incomingIndex (c : Fin (Fintype.card (Crossing q hq S C))) (i : Fin 2) := (arcEquiv q hq S C).symm (inc q hq S C (crossingEquiv q hq S C c) i)
def outgoingIndex (c : Fin (Fintype.card (Crossing q hq S C))) (i : Fin 2) := (arcEquiv q hq S C).symm (out q hq S C (crossingEquiv q hq S C c) i)
def next : Equiv.Perm (Fin (Fintype.card (Arc q hq S C))) :=
  (arcEquiv q hq S C).trans ((fibrePerm (P q hq S) C).trans (arcEquiv q hq S C).symm)

@[simp] theorem old_source (a) : oldVertex q hq S C (sourceIndex q hq S C a) = (Parent q hq).arcSource (oldArc q hq S C a) := by simp only [oldVertex, oldArc, sourceIndex, Equiv.apply_symm_apply, source_val]
@[simp] theorem old_target (a) : oldVertex q hq S C (targetIndex q hq S C a) = (Parent q hq).arcTarget (oldArc q hq S C a) := by simp only [oldVertex, oldArc, targetIndex, Equiv.apply_symm_apply, target_val]
@[simp] theorem old_crossing (c) : oldVertex q hq S C (crossingIndex q hq S C c) = (Parent q hq).crossingVertex (oldCrossing q hq S C c) := by simp only [oldVertex, oldCrossing, crossingIndex, Equiv.apply_symm_apply, vertex_val]
@[simp] theorem old_incoming (c) (i) : oldArc q hq S C (incomingIndex q hq S C c i) = (Parent q hq).incoming (oldCrossing q hq S C c) i := by simp only [oldArc, oldCrossing, incomingIndex, Equiv.apply_symm_apply, inc_old]
@[simp] theorem old_outgoing (c) (i) : oldArc q hq S C (outgoingIndex q hq S C c i) = (Parent q hq).outgoing (oldCrossing q hq S C c) i := by simp only [oldArc, oldCrossing, outgoingIndex, Equiv.apply_symm_apply, out_old]
@[simp] theorem old_next (a) : oldArc q hq S C (next q hq S C a) =
    eventFin q (P q hq S (arcEquiv q hq S C a).val) := by simp only [oldArc, next, Equiv.trans_apply, Equiv.apply_symm_apply, fibrePerm_apply_val]
theorem oldArc_injective : Function.Injective (oldArc q hq S C) := (eventFin q).injective.comp (Subtype.val_injective.comp (arcEquiv q hq S C).injective)
theorem oldVertex_injective : Function.Injective (oldVertex q hq S C) := Subtype.val_injective.comp (vertexEquiv q hq S C).injective
theorem oldCrossing_injective : Function.Injective (oldCrossing q hq S C) := Subtype.val_injective.comp (crossingEquiv q hq S C).injective

variable (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)

include hNA in
theorem regular_index_degree (v : Fin (Fintype.card (Vertex q hq S C)))
    (hv : ∀ c, crossingIndex q hq S C c ≠ v) :
    (incomingArcs (targetIndex q hq S C) v).card = 1 ∧ (outgoingArcs (sourceIndex q hq S C) v).card = 1 := by
  classical
  have hv' : ∀ c, vertex q hq S C c ≠ vertexEquiv q hq S C v := by
    intro c h
    apply hv ((crossingEquiv q hq S C).symm c)
    simpa [crossingIndex] using congrArg (vertexEquiv q hq S C).symm h
  have hs := regular_existsUnique_source q hq S C hNA (vertexEquiv q hq S C v) hv'
  have ht := regular_existsUnique_target q hq S C hNA (vertexEquiv q hq S C v) hv'
  constructor
  · obtain ⟨a, ha, hu⟩ := ht
    apply Finset.card_eq_one.mpr
    refine ⟨(arcEquiv q hq S C).symm a, ?_⟩
    ext b
    simp only [incomingArcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply (arcEquiv q hq S C).injective
      simpa using hu (arcEquiv q hq S C b) (by simpa [targetIndex] using congrArg (vertexEquiv q hq S C) h)
    · rintro rfl
      simpa [targetIndex] using congrArg (vertexEquiv q hq S C).symm ha
  · obtain ⟨a, ha, hu⟩ := hs
    apply Finset.card_eq_one.mpr
    refine ⟨(arcEquiv q hq S C).symm a, ?_⟩
    ext b
    simp only [outgoingArcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply (arcEquiv q hq S C).injective
      simpa using hu (arcEquiv q hq S C b) (by simpa [sourceIndex] using congrArg (vertexEquiv q hq S C) h)
    · rintro rfl
      simpa [sourceIndex] using congrArg (vertexEquiv q hq S C).symm ha

def sharpDaughterDiagram : PLLinkDiagram where
  nVertex := Fintype.card (Vertex q hq S C)
  nArc := Fintype.card (Arc q hq S C)
  nCrossing := Fintype.card (Crossing q hq S C)
  vertexPoint := fun v => (Parent q hq).vertexPoint (oldVertex q hq S C v)
  arcSource := sourceIndex q hq S C
  arcTarget := targetIndex q hq S C
  crossingVertex := crossingIndex q hq S C
  crossingVertex_injective := by
    intro c d h
    apply oldCrossing_injective q hq S C
    apply (Parent q hq).crossingVertex_injective
    simpa using congrArg (oldVertex q hq S C) h
  incoming := incomingIndex q hq S C
  outgoing := outgoingIndex q hq S C
  incoming_target := by
    intro c i; apply oldVertex_injective q hq S C
    simpa using (Parent q hq).incoming_target (oldCrossing q hq S C c) i
  outgoing_source := by
    intro c i; apply oldVertex_injective q hq S C
    simpa using (Parent q hq).outgoing_source (oldCrossing q hq S C c) i
  four_ports_distinct := by
    intro c
    obtain ⟨hi, ho, hm⟩ := (Parent q hq).four_ports_distinct (oldCrossing q hq S C c)
    refine ⟨?_, ?_, ?_⟩
    · intro h; apply hi; simpa using congrArg (oldArc q hq S C) h
    · intro h; apply ho; simpa using congrArg (oldArc q hq S C) h
    · intro i j h; apply hm i j; simpa using congrArg (oldArc q hq S C) h
  crossing_incidence_complete := by
    intro c a
    have heq : ∀ a b, oldArc q hq S C a = oldArc q hq S C b ↔ a = b := fun _ _ => (oldArc_injective q hq S C).eq_iff
    have hveq : ∀ a b, oldVertex q hq S C a = oldVertex q hq S C b ↔ a = b := fun _ _ => (oldVertex_injective q hq S C).eq_iff
    simpa only [← heq, ← hveq, old_source, old_target, old_crossing, old_incoming, old_outgoing]
      using (Parent q hq).crossing_incidence_complete (oldCrossing q hq S C c) (oldArc q hq S C a)
  regular_degree_one := regular_index_degree q hq S C hNA
  through := fun c => (Parent q hq).through (oldCrossing q hq S C c)
  continuation := next q hq S C
  continuation_incidence := by
    intro a; apply oldVertex_injective q hq S C
    simpa using parent_next_incidence q hq S (arcEquiv q hq S C a).val
  continuation_crossing := by
    intro c i; apply oldArc_injective q hq S C
    simp only [old_next, incomingIndex, Equiv.apply_symm_apply, inc,
      p_incoming q hq S _ (crossingEquiv q hq S C c).property.1,
      Equiv.apply_symm_apply, old_outgoing]
  overBranch := fun c => (Parent q hq).overBranch (oldCrossing q hq S C c)
  vertexPoint_injective := (Parent q hq).vertexPoint_injective.comp (oldVertex_injective q hq S C)
  arc_endpoints_distinct := by
    intro a h
    apply (Parent q hq).arc_endpoints_distinct (oldArc q hq S C a)
    simpa using congrArg (oldVertex q hq S C) h
  arc_interiors_disjoint := by
    intro a b hab s t hs hs' ht ht'
    simpa only [old_source, old_target] using (Parent q hq).arc_interiors_disjoint (oldArc q hq S C a) (oldArc q hq S C b)
      (fun h => hab (oldArc_injective q hq S C h)) s t hs hs' ht ht'
  vertices_avoid_arc_interiors := by
    intro v a t ht ht'
    simpa only [old_source, old_target] using (Parent q hq).vertices_avoid_arc_interiors (oldVertex q hq S C v) (oldArc q hq S C a) t ht ht'
  through_tangents_positive_collinear := by
    intro c i
    simpa only [old_crossing, old_source, old_target, old_incoming, old_outgoing]
      using (Parent q hq).through_tangents_positive_collinear (oldCrossing q hq S C c) i
  crossing_transverse := by
    intro c
    simpa only [old_crossing, old_source, old_incoming]
      using (Parent q hq).crossing_transverse (oldCrossing q hq S C c)

theorem arcEquiv_next (a : Fin (Fintype.card (Arc q hq S C))) :
    arcEquiv q hq S C (next q hq S C a) =
      fibrePerm (P q hq S) C (arcEquiv q hq S C a) := by
  simp only [next, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem arcEquiv_next_pow (k : ℕ) (a : Fin (Fintype.card (Arc q hq S C))) :
    arcEquiv q hq S C ((next q hq S C ^ k) a) =
      (fibrePerm (P q hq S) C ^ k) (arcEquiv q hq S C a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [arcEquiv_next, ih]

theorem next_isCycleOn : (next q hq S C).IsCycleOn Set.univ := by
  refine ⟨(next q hq S C).bijective.bijOn_univ, ?_⟩
  intro a ha b hb
  have hsame := (fibrePerm_isCycleOn (P q hq S) C).2
    (x := arcEquiv q hq S C a) (by trivial)
    (y := arcEquiv q hq S C b) (by trivial)
  obtain ⟨k, hk⟩ := hsame.exists_nat_pow_eq
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  apply (arcEquiv q hq S C).injective
  rw [arcEquiv_next_pow, hk]

theorem sharpDaughterDiagram_nonempty :
    Nonempty (Fin (sharpDaughterDiagram q hq S C hNA).nArc) := by
  obtain ⟨a⟩ := (inferInstance : Nonempty (Arc q hq S C))
  exact ⟨(arcEquiv q hq S C).symm a⟩

theorem sharpDaughterDiagram_componentCount :
    diagramComponentCount (sharpDaughterDiagram q hq S C hNA) = 1 := by
  letI := sharpDaughterDiagram_nonempty q hq S C hNA
  exact componentCount_eq_one _ (next_isCycleOn q hq S C)

theorem sharpDaughterDiagram_crossingSign
    (c : Fin (sharpDaughterDiagram q hq S C hNA).nCrossing) :
    crossingSign (sharpDaughterDiagram q hq S C hNA) c = Sign.pos := by
  have h := positivePolygonEventDiagram_crossingSign q hq (oldCrossing q hq S C c)
  simpa only [crossingSign, crossingDet, strandTangent, sharpDaughterDiagram,
    old_crossing, old_source, old_incoming, oldCrossing] using h

end DirectGLSSW.HOMFLY.SharpDaughter





