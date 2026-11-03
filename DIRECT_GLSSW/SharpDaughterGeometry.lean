import PolygonPositiveDiagram
import DirectGLSSW.DaughterInjectivity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW PermutationOrbits PolygonDrawingBridge
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
abbrev Parent := positivePolygonEventDiagram q hq
abbrev P := smoothingDartPermutation q hq.g2 S
variable (C : Component (P q hq S))
abbrev Arc := Fibre (P q hq S) C
def Vertex := {v : Fin (Parent q hq).nVertex //
  ∃ a : Arc q hq S C, (Parent q hq).arcSource (eventFin q a.val) = v}
def Crossing := {c : Fin (Parent q hq).nCrossing //
  ((crossingFin q).symm c) ∉ S ∧
  ∀ i : Fin 2, componentOf (P q hq S)
    ((eventFin q).symm ((Parent q hq).outgoing c i)) = C}
instance : Fintype (Vertex q hq S C) := by
  classical
  unfold Vertex
  infer_instance
instance : Fintype (Crossing q hq S C) := by
  classical
  unfold Crossing
  infer_instance

theorem source_point (x : PolygonEvent q) :
    (Parent q hq).vertexPoint ((Parent q hq).arcSource (eventFin q x)) =
      polygonEventPoint q x := by
  change PolygonDrawing.vertexPoint q
    ((vertexFin q).symm (sourceIndex q (eventFin q x))) = _
  simp only [sourceIndex, Equiv.symm_apply_apply]
  exact PolygonDrawing.vertexPoint_eventVertex q x

theorem target_point (x : PolygonEvent q) :
    (Parent q hq).vertexPoint ((Parent q hq).arcTarget (eventFin q x)) =
      polygonEventPoint q (polygonEventSuccessor q hq.g2 x) := by
  change PolygonDrawing.vertexPoint q
    ((vertexFin q).symm (targetIndex q hq (eventFin q x))) = _
  simp only [targetIndex, Equiv.symm_apply_apply]
  exact PolygonDrawing.vertexPoint_eventVertex q _

theorem parent_next_incidence (x : PolygonEvent q) :
    (Parent q hq).arcTarget (eventFin q x) =
      (Parent q hq).arcSource (eventFin q (P q hq S x)) := by
  apply (Parent q hq).vertexPoint_injective
  rw [source_point, target_point]
  exact (smoothingDartPermutation_endpoint q hq.g2 S x).symm

def source (a : Arc q hq S C) : Vertex q hq S C :=
  ⟨(Parent q hq).arcSource (eventFin q a.val), a, rfl⟩
def target (a : Arc q hq S C) : Vertex q hq S C :=
  ⟨(Parent q hq).arcTarget (eventFin q a.val), fibrePerm (P q hq S) C a,
    (parent_next_incidence q hq S a.val).symm⟩

theorem outgoing_event (c : Fin (Parent q hq).nCrossing) (i : Fin 2) :
    (eventFin q).symm ((Parent q hq).outgoing c i) =
      PolygonDrawing.visit q ((crossingFin q).symm c) i := by
  change (eventFin q).symm (eventFin q _) = _
  exact (eventFin q).symm_apply_apply _

theorem p_incoming (c : Fin (Parent q hq).nCrossing)
    (hc : ((crossingFin q).symm c) ∉ S) (i : Fin 2) :
    P q hq S ((eventFin q).symm ((Parent q hq).incoming c i)) =
      (eventFin q).symm ((Parent q hq).outgoing c ((Parent q hq).through c i)) := by
  change smoothingPairing q S
    (polygonEventSuccessor q hq.g2
      ((eventFin q).symm (eventFin q (PolygonDrawing.incoming q hq ((crossingFin q).symm c) i)))) =
    (eventFin q).symm (eventFin q (PolygonDrawing.visit q ((crossingFin q).symm c) i))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, PolygonDrawing.incoming_successor]
  fin_cases i <;> exact (smoothingPairing_visit_fixed_iff q S _).mpr hc

def out (c : Crossing q hq S C) (i : Fin 2) : Arc q hq S C :=
  ⟨(eventFin q).symm ((Parent q hq).outgoing c.val i), c.property.2 i⟩
def inc (c : Crossing q hq S C) (i : Fin 2) : Arc q hq S C :=
  ⟨(eventFin q).symm ((Parent q hq).incoming c.val i), by
    have h := c.property.2 ((Parent q hq).through c.val i)
    rw [← p_incoming q hq S c.val c.property.1 i, componentOf_apply] at h
    exact h⟩
def vertex (c : Crossing q hq S C) : Vertex q hq S C :=
  ⟨(Parent q hq).crossingVertex c.val, out q hq S C c 0, by
    change (Parent q hq).arcSource (eventFin q ((eventFin q).symm _)) = _
    rw [Equiv.apply_symm_apply]
    exact (Parent q hq).outgoing_source c.val 0⟩

@[simp] theorem source_val (a : Arc q hq S C) :
    (source q hq S C a).val = (Parent q hq).arcSource (eventFin q a.val) := rfl
@[simp] theorem target_val (a : Arc q hq S C) :
    (target q hq S C a).val = (Parent q hq).arcTarget (eventFin q a.val) := rfl
@[simp] theorem out_old (c : Crossing q hq S C) (i : Fin 2) :
    eventFin q (out q hq S C c i).val = (Parent q hq).outgoing c.val i :=
  (eventFin q).apply_symm_apply _
@[simp] theorem inc_old (c : Crossing q hq S C) (i : Fin 2) :
    eventFin q (inc q hq S C c i).val = (Parent q hq).incoming c.val i :=
  (eventFin q).apply_symm_apply _
@[simp] theorem vertex_val (c : Crossing q hq S C) :
    (vertex q hq S C c).val = (Parent q hq).crossingVertex c.val := rfl
@[simp] theorem target_eq_source_next (a : Arc q hq S C) :
    target q hq S C a = source q hq S C (fibrePerm (P q hq S) C a) :=
  Subtype.ext (parent_next_incidence q hq S a.val)
@[simp] theorem source_out (c : Crossing q hq S C) (i : Fin 2) :
    source q hq S C (out q hq S C c i) = vertex q hq S C c := by
  apply Subtype.ext; simp only [source_val, out_old, vertex_val]
  exact (Parent q hq).outgoing_source c.val i
@[simp] theorem target_inc (c : Crossing q hq S C) (i : Fin 2) :
    target q hq S C (inc q hq S C c i) = vertex q hq S C c := by
  apply Subtype.ext; simp only [target_val, inc_old, vertex_val]
  exact (Parent q hq).incoming_target c.val i

theorem source_crossing_iff (c : Fin (Parent q hq).nCrossing)
    (e : Fin (Parent q hq).nArc) :
    (Parent q hq).arcSource e = (Parent q hq).crossingVertex c ↔
      e = (Parent q hq).outgoing c 0 ∨ e = (Parent q hq).outgoing c 1 := by
  constructor
  · intro h
    rcases ((Parent q hq).crossing_incidence_complete c e).mp (Or.inl h) with h0 | h1 | h0 | h1
    · exact False.elim ((Parent q hq).arc_endpoints_distinct e
        (h.trans (h0 ▸ (Parent q hq).incoming_target c 0).symm))
    · exact False.elim ((Parent q hq).arc_endpoints_distinct e
        (h.trans (h1 ▸ (Parent q hq).incoming_target c 1).symm))
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (rfl | rfl) <;> exact (Parent q hq).outgoing_source _ _

variable (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
include hNA
theorem both_visits_not_selected (c : Fin (Parent q hq).nCrossing)
    (hm : ∀ i : Fin 2, componentOf (P q hq S)
      ((eventFin q).symm ((Parent q hq).outgoing c i)) = C) :
    ((crossingFin q).symm c) ∉ S := by
  intro hc
  have hd := DaughterInjectivity.selectedVisits_differentDartOrbits q hq.g2 S
    hq.size_ge_three hNA hc
  apply hd
  have h0 := hm 0
  have h1 := hm 1
  rw [outgoing_event] at h0 h1
  exact h0.trans h1.symm

theorem regular_source_unique (v : Vertex q hq S C)
    (hv : ∀ c : Crossing q hq S C, vertex q hq S C c ≠ v)
    (a b : Arc q hq S C) (ha : source q hq S C a = v)
    (hb : source q hq S C b = v) : a = b := by
  classical
  apply Subtype.ext
  apply (eventFin q).injective
  have ha' : (Parent q hq).arcSource (eventFin q a.val) = v.val := congrArg Subtype.val ha
  have hb' : (Parent q hq).arcSource (eventFin q b.val) = v.val := congrArg Subtype.val hb
  by_cases hcross : ∃ c, (Parent q hq).crossingVertex c = v.val
  · obtain ⟨c, hc⟩ := hcross
    have hA := (source_crossing_iff q hq c (eventFin q a.val)).mp (ha'.trans hc.symm)
    have hB := (source_crossing_iff q hq c (eventFin q b.val)).mp (hb'.trans hc.symm)
    have hmemA : componentOf (P q hq S) ((eventFin q).symm (eventFin q a.val)) = C := by
      simpa only [Equiv.symm_apply_apply] using a.property
    have hmemB : componentOf (P q hq S) ((eventFin q).symm (eventFin q b.val)) = C := by
      simpa only [Equiv.symm_apply_apply] using b.property
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hA.trans hB.symm
    · exfalso
      have hm : ∀ i : Fin 2, componentOf (P q hq S)
          ((eventFin q).symm ((Parent q hq).outgoing c i)) = C := by
        intro i; fin_cases i
        · exact hA ▸ hmemA
        · exact hB ▸ hmemB
      exact hv ⟨c, both_visits_not_selected q hq S C hNA c hm, hm⟩ (Subtype.ext hc)
    · exfalso
      have hm : ∀ i : Fin 2, componentOf (P q hq S)
          ((eventFin q).symm ((Parent q hq).outgoing c i)) = C := by
        intro i; fin_cases i
        · exact hB ▸ hmemB
        · exact hA ▸ hmemA
      exact hv ⟨c, both_visits_not_selected q hq S C hNA c hm, hm⟩ (Subtype.ext hc)
    · exact hA.trans hB.symm
  · have hd := ((Parent q hq).regular_degree_one v.val (by simpa using hcross)).2
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hd
    have hma : eventFin q a.val ∈ outgoingArcs (Parent q hq).arcSource v.val := by
      simp only [outgoingArcs, Finset.mem_filter, Finset.mem_univ, true_and, ha']
    have hmb : eventFin q b.val ∈ outgoingArcs (Parent q hq).arcSource v.val := by
      simp only [outgoingArcs, Finset.mem_filter, Finset.mem_univ, true_and, hb']
    rw [he, Finset.mem_singleton] at hma hmb
    exact hma.trans hmb.symm

theorem regular_existsUnique_source (v : Vertex q hq S C)
    (hv : ∀ c : Crossing q hq S C, vertex q hq S C c ≠ v) :
    ∃! a : Arc q hq S C, source q hq S C a = v := by
  obtain ⟨a, ha⟩ := v.property
  refine ⟨a, Subtype.ext ha, ?_⟩
  intro b hb
  exact regular_source_unique q hq S C hNA v hv b a hb (Subtype.ext ha)

theorem regular_existsUnique_target (v : Vertex q hq S C)
    (hv : ∀ c : Crossing q hq S C, vertex q hq S C c ≠ v) :
    ∃! a : Arc q hq S C, target q hq S C a = v := by
  obtain ⟨a, ha, hu⟩ := regular_existsUnique_source q hq S C hNA v hv
  refine ⟨(fibrePerm (P q hq S) C).symm a, ?_, ?_⟩
  · simpa only [target_eq_source_next, Equiv.apply_symm_apply] using ha
  · intro b hb
    apply (fibrePerm (P q hq S) C).injective
    simpa using hu (fibrePerm (P q hq S) C b)
      (by simpa only [← target_eq_source_next] using hb)
end DirectGLSSW.HOMFLY.SharpDaughter


