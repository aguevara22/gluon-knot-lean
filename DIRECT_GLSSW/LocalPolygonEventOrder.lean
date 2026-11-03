import LocalCrossingVisitOrder

namespace DirectGLSSW.LocalCrossingTransport
open DirectGLSSW
open DirectGLSSW.TruncationDirection

theorem crossingVisit_mapEquiv_edge_eq {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val) (v : CrossingVisit q) :
    crossingVisitEdge q' (crossingVisit_mapEquiv E v) = crossingVisitEdge q v := by
  rcases v with ⟨c, b⟩
  cases b
  · exact congrArg Prod.fst (hlabels c)
  · exact congrArg Prod.snd (hlabels c)

/-- Original vertex anchors remain fixed, while each crossing's two sides are retained. -/
noncomputable def polygonEventMapEquiv {n : ℕ}
    {q q' : Fin n → PlanarPoint ℝ}
    (E : PolygonCrossing q ≃ PolygonCrossing q') : PolygonEvent q ≃ PolygonEvent q' :=
  Equiv.sumCongr (Equiv.refl (Fin n)) (crossingVisit_mapEquiv E)

theorem polygonEventMapEquiv_order_iff {n : ℕ}
    (q q' : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ v w : CrossingVisit q,
      crossingVisitEdge q v = crossingVisitEdge q w →
      (crossingVisitParameter q v < crossingVisitParameter q w ↔
        crossingVisitParameter q' (crossingVisit_mapEquiv E v) <
        crossingVisitParameter q' (crossingVisit_mapEquiv E w)))
    (x y : PolygonEvent q) :
    (letI := polygonEventOrder q hq.g2; x < y) ↔
      (letI := polygonEventOrder q' hq'.g2;
        polygonEventMapEquiv E x < polygonEventMapEquiv E y) := by
  rw [polygonEvent_lt_iff q hq.g2, polygonEvent_lt_iff q' hq'.g2]
  cases x with
  | inl e =>
    cases y with
    | inl f => rfl
    | inr v =>
      change (e < crossingVisitEdge q v ∨ e = crossingVisitEdge q v ∧
        0 < crossingVisitParameter q v) ↔
        (e < crossingVisitEdge q' (crossingVisit_mapEquiv E v) ∨
          e = crossingVisitEdge q' (crossingVisit_mapEquiv E v) ∧
          0 < crossingVisitParameter q' (crossingVisit_mapEquiv E v))
      rw [crossingVisit_mapEquiv_edge_eq q q' E hlabels v]
      simp only [(crossingVisitParameter_spec q v).1,
        (crossingVisitParameter_spec q' (crossingVisit_mapEquiv E v)).1, and_true]
  | inr v =>
    cases y with
    | inl e =>
      change (crossingVisitEdge q v < e ∨ crossingVisitEdge q v = e ∧
        crossingVisitParameter q v < 0) ↔
        (crossingVisitEdge q' (crossingVisit_mapEquiv E v) < e ∨
          crossingVisitEdge q' (crossingVisit_mapEquiv E v) = e ∧
          crossingVisitParameter q' (crossingVisit_mapEquiv E v) < 0)
      rw [crossingVisit_mapEquiv_edge_eq q q' E hlabels v]
      simp only [not_lt_of_ge (crossingVisitParameter_spec q v).1.le,
        not_lt_of_ge (crossingVisitParameter_spec q' (crossingVisit_mapEquiv E v)).1.le,
        and_false, or_false]
    | inr w =>
      change (crossingVisitEdge q v < crossingVisitEdge q w ∨
        crossingVisitEdge q v = crossingVisitEdge q w ∧
        crossingVisitParameter q v < crossingVisitParameter q w) ↔
        (crossingVisitEdge q' (crossingVisit_mapEquiv E v) <
          crossingVisitEdge q' (crossingVisit_mapEquiv E w) ∨
          crossingVisitEdge q' (crossingVisit_mapEquiv E v) =
          crossingVisitEdge q' (crossingVisit_mapEquiv E w) ∧
          crossingVisitParameter q' (crossingVisit_mapEquiv E v) <
          crossingVisitParameter q' (crossingVisit_mapEquiv E w))
      rw [crossingVisit_mapEquiv_edge_eq q q' E hlabels v,
        crossingVisit_mapEquiv_edge_eq q q' E hlabels w]
      by_cases he : crossingVisitEdge q v = crossingVisitEdge q w
      · simp only [he, true_and, horder v w he]
      · simp only [he, false_and, or_false]

/-- The full finite traversal order of actual anchors and visits is locally preserved. -/
theorem exists_local_polygonEvent_order_equiv {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v, Continuous (fun t => Q t v)) (h0 : CyclicGeneric (Q 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, |t| < δ →
      ∃ ht : CyclicGeneric (Q t),
      ∃ E : PolygonCrossing (Q 0) ≃ PolygonCrossing (Q t),
        (∀ c, (E c).val = c.val) ∧
        ∀ x y : PolygonEvent (Q 0),
          ((polygonEventOrder (Q 0) h0.g2).lt x y ↔
            (polygonEventOrder (Q t) ht.g2).lt
              (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)) := by
  obtain ⟨δ, hδ, hg⟩ := exists_local_crossing_equiv_visit_order Q hQ h0
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  obtain ⟨hgt, E, hlabels, horder⟩ := hg t ht
  exact ⟨hgt, E, hlabels, polygonEventMapEquiv_order_iff (Q 0) (Q t) h0 hgt E hlabels horder⟩




end DirectGLSSW.LocalCrossingTransport
