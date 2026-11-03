import DirectGLSSW.PrimitiveEdgeGrouping
import DirectGLSSW.DaughterAnchorScales

set_option autoImplicit false
namespace DirectGLSSW.UncutDaughterEdge
open PrimitiveEdgeGrouping DaughterFirstReturn EventSegmentGeometry
noncomputable section

/-- On an uncut original edge the only retained event is its initial anchor. -/
theorem retained_event_on_uncut_edge {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (e : Fin n) (S : Finset (PolygonCrossing P))
    (hOff : ∀ c ∈ S, ¬ Incident P e c) (x : PolygonEvent P)
    (hx : retainedCorner P S x) (he : polygonEventEdge P x = e) : x = Sum.inl e := by
  cases x with
  | inl a =>
    have ha : a = e := he
    exact congrArg Sum.inl ha
  | inr v =>
    rcases v with ⟨c,b⟩
    have hc : c ∈ S := hx
    have hi : Incident P e c := by
      cases b
      · exact Or.inl he
      · exact Or.inr he
    exact (hOff c hc hi).elim

/-- The first retained event after an anchor on an uncut edge is derived from
the actual dart first-return construction and is precisely the next original anchor. -/
theorem uncut_anchor_successor_event {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (hn : 3 ≤ n)
    (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
    (hroot : retainedCorner P S root) (e : Fin n)
    (hOff : ∀ c ∈ S, ¬ Incident P e c)
    (i : Fin (Fintype.card (CornerCoord P hG2 S root)))
    (hhere : orbitEventAt P hG2 S root (cornerEnumeration P hG2 S root i).val = Sum.inl e) :
    orbitEventAt P hG2 S root
      (cornerEnumeration P hG2 S root (cyclicSuccessor i)).val = Sum.inl (cyclicSuccessor e) := by
  let c := cornerEnumeration P hG2 S root i
  let d := cornerGap P hG2 S root c.val (cornerSuccessor P hG2 S root c).val
  let z := lastDartStart P hG2 S root c
  obtain ⟨hd,hnext,hpair,_,hret,_⟩ := cornerSuccessor_is_firstReturn P hG2 S hn root hroot c
  have hlast : d - 1 < d := Nat.sub_lt (by exact hd) (by omega)
  have hpref := orbitPrefix_edge_parameter P hG2 S hn root hroot c (d-1) hlast
  have hzedge : polygonEventEdge P z = e := by
    have hh : orbitEventAt P hG2 S root c.val = Sum.inl e := hhere
    simpa only [lastDartStart,z,d,hh,polygonEventEdge] using hpref.1
  have hterminal : terminalEvent P hG2 z = Sum.inl (cyclicSuccessor e) := by
    rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor P hG2 hn z with hs | ha
    · have he : polygonEventEdge P (terminalEvent P hG2 z) = e := hs.1.trans hzedge
      have hx := retained_event_on_uncut_edge P e S hOff (terminalEvent P hG2 z) hret he
      have hlt := hs.2.1
      change polygonEventParameter P z < polygonEventParameter P (terminalEvent P hG2 z) at hlt
      rw [hx] at hlt
      exact ((not_lt_of_ge (polygonEventParameter_bounds P z).1) hlt).elim
    · simpa only [terminalEvent,hzedge] using ha.1
  rw [cornerEnumeration_successor]
  change orbitEventAt P hG2 S root (cornerSuccessor P hG2 S root c).val = _
  rw [← hnext,hpair,hterminal]
  rfl

theorem uncut_anchor_vertices {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (hn : 3 ≤ n)
    (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
    (hroot : retainedCorner P S root) (e : Fin n)
    (hOff : ∀ c ∈ S, ¬ Incident P e c)
    (i : Fin (Fintype.card (CornerCoord P hG2 S root)))
    (hhere : orbitEventAt P hG2 S root (cornerEnumeration P hG2 S root i).val = Sum.inl e) :
    daughterVertex P hG2 S root i = P e ∧
    daughterVertex P hG2 S root (cyclicSuccessor i) = P (cyclicSuccessor e) := by
  constructor
  · unfold daughterVertex
    rw [hhere]
    rfl
  · unfold daughterVertex
    rw [uncut_anchor_successor_event P hG2 hn S root hroot e hOff i hhere]
    rfl

/-- The daughter contains the entire original oriented uncut edge, with scale one. -/
theorem uncut_anchor_tangent {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (hn : 3 ≤ n)
    (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
    (hroot : retainedCorner P S root) (e : Fin n)
    (hOff : ∀ c ∈ S, ¬ Incident P e c)
    (i : Fin (Fintype.card (CornerCoord P hG2 S root)))
    (hhere : orbitEventAt P hG2 S root (cornerEnumeration P hG2 S root i).val = Sum.inl e) :
    cyclicTangent (daughterVertex P hG2 S root) i = cyclicTangent P e := by
  obtain ⟨ha,hb⟩ := uncut_anchor_vertices P hG2 hn S root hroot e hOff i hhere
  unfold cyclicTangent
  rw [ha,hb]

end
end DirectGLSSW.UncutDaughterEdge
