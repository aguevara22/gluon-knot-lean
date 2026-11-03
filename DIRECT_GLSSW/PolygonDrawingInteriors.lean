import PolygonDrawingVertices

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PolygonDrawing

open EventSegmentGeometry

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

noncomputable def subarcParameter (x : PolygonEvent q) (t : ℝ) : ℝ :=
  polygonEventParameter q x + t *
    (polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x -
      polygonEventParameter q x)

theorem subarcParameter_bounds (x : PolygonEvent q) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    polygonEventParameter q x < subarcParameter q hq x t ∧
    subarcParameter q hq x t <
      polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x ∧
    0 < subarcParameter q hq x t ∧ subarcParameter q hq x t < 1 := by
  have hstep := polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three x
  have hstart := polygonEventParameter_bounds q x
  dsimp [subarcParameter]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem subarcPoint_eq (x : PolygonEvent q) (t : ℝ) :
    affinePoint (vertexPoint q (arcSource q x)) (vertexPoint q (arcTarget q hq x)) t =
      affinePoint (q (polygonEventEdge q x))
        (q (cyclicSuccessor (polygonEventEdge q x))) (subarcParameter q hq x t) := by
  change affinePoint (vertexPoint q (eventVertex q x))
      (vertexPoint q (eventVertex q (polygonEventSuccessor q hq.g2 x))) t = _
  rw [vertexPoint_eventVertex, vertexPoint_eventVertex]
  have hstep := polygonEventSuccessor_positive_elementary_step q hq.g2 hq.size_ge_three x
  rw [hstep.2.2.2.1, polygonEventPoint_eq_affine q x]
  ext <;> simp only [affinePoint, subarcParameter] <;> ring

theorem no_event_in_subarc (x z : PolygonEvent q)
    (he : polygonEventEdge q z = polygonEventEdge q x)
    (hlo : polygonEventParameter q x < polygonEventParameter q z) :
    ¬ polygonEventParameter q z <
      polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three x := by
  classical
  letI : LinearOrder (Fin n ⊕ CrossingVisit q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent q) := by
    change LinearOrder (Fin n ⊕ CrossingVisit q)
    exact polygonEventOrder q hq.g2
  intro hhi
  rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three x with
    ⟨hey, hxy, hleast⟩ | ⟨hy, hmax⟩
  · have hyz := hleast z he hlo
    have hu := (polygonEventSuccessorTerminalParameter_spec q hq.g2 hq.size_ge_three x).1 hey
    rw [hu] at hhi
    have hzy := (polygonEvent_sameEdge_lt_iff q hq.g2 z
      (polygonEventSuccessor q hq.g2 x) (he.trans hey.symm)).2 hhi
    exact not_lt_of_ge hyz hzy
  · exact not_lt_of_ge (hmax z he) hlo

include hq in
theorem crossing_visit_on_edge (c : PolygonCrossing q) (e : Fin n)
    (h : edgeInterior q e (crossingPoint q c)) :
    ∃ b : Bool, crossingVisitEdge q (c,b) = e := by
  by_cases hl : e = c.val.1
  · exact ⟨false, by simpa [crossingVisitEdge] using hl.symm⟩
  by_cases hr : e = c.val.2
  · exact ⟨true, by simpa [crossingVisitEdge] using hr.symm⟩
  exact False.elim (hq.g2 c.val.1 c.val.2 e (crossingPoint q c)
    (crossing_edges_ne q c) (Ne.symm hr) (Ne.symm hl)
    ⟨crossingPoint_mem_left q c, crossingPoint_mem_right q c, h⟩)

include hq in
theorem original_edge_endpoints_ne (e : Fin n) : q e ≠ q (cyclicSuccessor e) := by
  intro h
  have hinj := cyclicNoncollinear_injective hq.size_ge_three q hq.g1
  exact cyclicSuccessor_ne_self (by have := hq.size_ge_three; omega) e (hinj h).symm

theorem vertices_avoid_arc_interiors (v : Vertex q) (x : PolygonEvent q) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    vertexPoint q v ≠
      affinePoint (vertexPoint q (arcSource q x)) (vertexPoint q (arcTarget q hq x)) t := by
  intro h
  rw [subarcPoint_eq] at h
  have hb := subarcParameter_bounds q hq x t ht0 ht1
  have hmem : edgeInterior q (polygonEventEdge q x) (vertexPoint q v) :=
    ⟨subarcParameter q hq x t, hb.2.2.1, hb.2.2.2, h⟩
  cases v with
  | inl i => exact vertex_not_in_edge q hq _ i hmem
  | inr c =>
    obtain ⟨b, he⟩ := crossing_visit_on_edge q hq c _ hmem
    let z : PolygonEvent q := Sum.inr (c,b)
    have hze : polygonEventEdge q z = polygonEventEdge q x := he
    have hpoint := polygonEventPoint_eq_affine q z
    have hp : polygonEventParameter q z = subarcParameter q hq x t := by
      apply affinePoint_injective _ _ (original_edge_endpoints_ne q hq _)
      rw [hze] at hpoint
      exact hpoint.symm.trans h
    exact no_event_in_subarc q hq x z hze (hp.symm ▸ hb.1) (hp.symm ▸ hb.2.1)

theorem arc_interiors_disjoint (x y : PolygonEvent q) (hxy : x ≠ y) (s t : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    affinePoint (vertexPoint q (arcSource q x)) (vertexPoint q (arcTarget q hq x)) s ≠
      affinePoint (vertexPoint q (arcSource q y)) (vertexPoint q (arcTarget q hq y)) t := by
  intro h
  have hx := subarcParameter_bounds q hq x s hs0 hs1
  have hy := subarcParameter_bounds q hq y t ht0 ht1
  have h' := h
  rw [subarcPoint_eq, subarcPoint_eq] at h'
  by_cases he : polygonEventEdge q x = polygonEventEdge q y
  · have hpar : subarcParameter q hq x s = subarcParameter q hq y t := by
      apply affinePoint_injective _ _ (original_edge_endpoints_ne q hq _)
      simpa only [he] using h'
    have hne : polygonEventParameter q x ≠ polygonEventParameter q y := by
      intro hp
      apply hxy
      apply polygonEventKey_injective q hq.g2
      exact Prod.ext he hp
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply no_event_in_subarc q hq x y he.symm hlt
      exact lt_trans (by simpa only [hpar] using hy.1) hx.2.1
    · apply no_event_in_subarc q hq y x he hgt
      exact lt_trans (by simpa only [← hpar] using hx.1) hy.2.1
  · let p := affinePoint (vertexPoint q (arcSource q x))
      (vertexPoint q (arcTarget q hq x)) s
    have hmx : edgeInterior q (polygonEventEdge q x) p :=
      ⟨subarcParameter q hq x s, hx.2.2.1, hx.2.2.2, subarcPoint_eq q hq x s⟩
    have hmy : edgeInterior q (polygonEventEdge q y) p :=
      ⟨subarcParameter q hq y t, hy.2.2.1, hy.2.2.2, h.trans (subarcPoint_eq q hq y t)⟩
    obtain ⟨c, hc⟩ := (isCrossingPoint_iff_exists hq.size_ge_three q hq.g1 p).1
      ⟨polygonEventEdge q x, polygonEventEdge q y, he, hmx, hmy⟩
    exact vertices_avoid_arc_interiors q hq (.inr c) x s hs0 hs1 hc

end DirectGLSSW.HOMFLY.PolygonDrawing







