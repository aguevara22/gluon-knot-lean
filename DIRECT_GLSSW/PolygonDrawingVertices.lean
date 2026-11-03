import DirectGLSSW.EventSegmentGeometry
import DirectGLSSW.HOMFLY.PLDiagrams

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PolygonDrawing

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

/-- Actual drawing vertices: original polygon vertices and actual crossings,
with the two visits to a crossing merged into one vertex. -/
abbrev Vertex := Fin n ⊕ PolygonCrossing q

noncomputable def vertexPoint : Vertex q → PlanarPoint ℝ
  | .inl i => q i
  | .inr c => crossingPoint q c

def eventVertex : PolygonEvent q → Vertex q
  | .inl i => .inl i
  | .inr v => .inr v.1

theorem vertexPoint_eventVertex (x : PolygonEvent q) :
    vertexPoint q (eventVertex q x) = polygonEventPoint q x := by
  cases x <;> rfl

include hq in
theorem vertex_not_in_edge (e i : Fin n) : ¬ edgeInterior q e (q i) := by
  have hinj := cyclicNoncollinear_injective hq.size_ge_three q hq.g1
  have hab : q e ≠ q (cyclicSuccessor e) := by
    intro h
    exact cyclicSuccessor_ne_self (by have := hq.size_ge_three; omega) e (hinj h).symm
  by_cases hie : i = e
  · subst i
    intro h
    exact onOpenSegment_ne_left hab h rfl
  by_cases his : i = cyclicSuccessor e
  · subst i
    intro h
    exact onOpenSegment_ne_right hab h rfl
  exact cyclic_vertex_not_in_nonincident_edge hq.size_ge_three q hq.g1 e i hie his

include hq in
theorem vertexPoint_injective : Function.Injective (vertexPoint q) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      exact congrArg Sum.inl (cyclicNoncollinear_injective hq.size_ge_three q hq.g1 h)
    | inr c =>
      have hmem : edgeInterior q c.val.1 (q i) := by
        change q i = crossingPoint q c at h
        rw [h]
        exact crossingPoint_mem_left q c
      exact False.elim (vertex_not_in_edge q hq c.val.1 i hmem)
  | inr c =>
    cases y with
    | inl i =>
      have hmem : edgeInterior q c.val.1 (q i) := by
        change crossingPoint q c = q i at h
        rw [← h]
        exact crossingPoint_mem_left q c
      exact False.elim (vertex_not_in_edge q hq c.val.1 i hmem)
    | inr d =>
      exact congrArg Sum.inr (crossingPoint_injective q hq.g2 h)

theorem eventVertex_eq_anchor_iff (x : PolygonEvent q) (i : Fin n) :
    eventVertex q x = Sum.inl i ↔ x = Sum.inl i := by
  cases x <;> simp [eventVertex, PolygonEvent, CrossingVisit]

theorem eventVertex_eq_crossing_iff (x : PolygonEvent q) (c : PolygonCrossing q) :
    eventVertex q x = Sum.inr c ↔
      x = Sum.inr (c, false) ∨ x = Sum.inr (c, true) := by
  cases x with
  | inl i => simp [eventVertex, PolygonEvent, CrossingVisit]
  | inr v =>
    rcases v with ⟨d,b⟩
    cases b <;> simp [eventVertex, PolygonEvent, CrossingVisit]

def arcSource (x : PolygonEvent q) : Vertex q := eventVertex q x

noncomputable def arcTarget (x : PolygonEvent q) : Vertex q :=
  eventVertex q (polygonEventSuccessor q hq.g2 x)

theorem arc_endpoints_distinct (x : PolygonEvent q) :
    arcSource q x ≠ arcTarget q hq x := by
  intro h
  have hp := congrArg (vertexPoint q) h
  change vertexPoint q (eventVertex q x) =
    vertexPoint q (eventVertex q (polygonEventSuccessor q hq.g2 x)) at hp
  rw [vertexPoint_eventVertex,vertexPoint_eventVertex] at hp
  exact EventSegmentGeometry.polygonEventSuccessor_step_ne_zero q hq.g2
    hq.size_ge_three hq.g1 x (sub_eq_zero.mpr hp.symm)

theorem continuation_incidence (x : PolygonEvent q) :
    arcTarget q hq x = arcSource q (polygonEventSuccessor q hq.g2 x) := rfl

end DirectGLSSW.HOMFLY.PolygonDrawing






