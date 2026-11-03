import UncutDaughterEdge
import NormalizedEdgeTurns

set_option autoImplicit false
namespace DirectGLSSW.UncutDaughterTurns
open DaughterFirstReturn UncutDaughterEdge PrimitiveEdgeGrouping
noncomputable section

/-- At an original anchor, the daughter turn is a positive multiple of the
original turn; both incident scales are derived from the actual first return. -/
theorem anchor_turn_positive_multiple {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (hn : 3 ≤ n)
    (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)
    (hroot : retainedCorner P S root)
    (i : Fin (Fintype.card (CornerCoord P hG2 S root)))
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hhere : orbitEventAt P hG2 S root (cornerEnumeration P hG2 S root i).val = Sum.inl a) :
    ∃ t : ℝ, 0 < t ∧
      planarDet (cyclicTangent (daughterVertex P hG2 S root)
        ((cyclicSuccessorPerm (Fintype.card (CornerCoord P hG2 S root)))⁻¹ i))
        (cyclicTangent (daughterVertex P hG2 S root) i) =
      t * planarDet (cyclicTangent P p) (cyclicTangent P a) := by
  obtain ⟨α,hα,β,hβ,hv,hl,hr⟩ :=
    DaughterAnchorScales.exists_daughter_anchor_incident_scales P hG2 S hn root hroot i a p hp hhere
  have hs : cyclicSuccessor
      ((cyclicSuccessorPerm (Fintype.card (CornerCoord P hG2 S root)))⁻¹ i) = i :=
    Equiv.apply_symm_apply (cyclicSuccessorPerm _) i
  refine ⟨α*β,mul_pos hα hβ,?_⟩
  simp only [cyclicTangent,hs,hv,hl,hr,hp]
  dsimp [planarDet]
  ring

/-- The source endpoint-turn product along the whole uncut edge is preserved
up to a strictly positive factor in its actual retained daughter. -/
theorem uncut_endpoint_turn_product {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (S : Finset (PolygonCrossing P))
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (e : Fin n) (hOff : ∀ c ∈ S, ¬ Incident P e c)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (hhere : orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val = Sum.inl e) :
    ∃ t : ℝ, 0 < t ∧
      planarDet (cyclicTangent (daughterVertex P hP.g2 S root) i)
        (cyclicTangent (daughterVertex P hP.g2 S root) (cyclicSuccessor i)) *
      planarDet (cyclicTangent (daughterVertex P hP.g2 S root)
        (cyclicVertexIndex i (Fintype.card (CornerCoord P hP.g2 S root)-2)))
        (cyclicTangent (daughterVertex P hP.g2 S root) i) =
      t * (planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
        planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e)) := by
  have hn := hP.size_ge_three
  have hm := DaughterTurns.daughterVertexCount_ge_three P hP.g2 S hn hP.g1 root hroot
  have hp := NormalizedEdgeTurns.penultimate_precedes_edge hn e
  obtain ⟨a,ha,hleft⟩ := anchor_turn_positive_multiple P hP.g2 hn S root hroot i e
    (cyclicVertexIndex e (n-2)) hp hhere
  have hnext := uncut_anchor_successor_event P hP.g2 hn S root hroot e hOff i hhere
  obtain ⟨b,hb,hright⟩ := anchor_turn_positive_multiple P hP.g2 hn S root hroot
    (cyclicSuccessor i) (cyclicSuccessor e) e rfl hnext
  have hpred : (cyclicSuccessorPerm (Fintype.card (CornerCoord P hP.g2 S root)))⁻¹ i =
      cyclicVertexIndex i (Fintype.card (CornerCoord P hP.g2 S root)-2) := by
    apply (cyclicSuccessorPerm _).injective
    exact (Equiv.apply_symm_apply (cyclicSuccessorPerm _) i).trans
      (NormalizedEdgeTurns.penultimate_precedes_edge hm i).symm
  have hprednext : (cyclicSuccessorPerm (Fintype.card (CornerCoord P hP.g2 S root)))⁻¹
      (cyclicSuccessor i) = i := Equiv.symm_apply_apply (cyclicSuccessorPerm _) i
  rw [hpred] at hleft
  rw [hprednext] at hright
  refine ⟨b*a,mul_pos hb ha,?_⟩
  rw [hleft,hright]
  ring

theorem uncut_endpoint_turn_product_neg {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (S : Finset (PolygonCrossing P))
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (e : Fin n) (hOff : ∀ c ∈ S, ¬ Incident P e c)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (hhere : orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val = Sum.inl e)
    (hturn : planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0) :
    planarDet (cyclicTangent (daughterVertex P hP.g2 S root) i)
      (cyclicTangent (daughterVertex P hP.g2 S root) (cyclicSuccessor i)) *
    planarDet (cyclicTangent (daughterVertex P hP.g2 S root)
      (cyclicVertexIndex i (Fintype.card (CornerCoord P hP.g2 S root)-2)))
      (cyclicTangent (daughterVertex P hP.g2 S root) i) < 0 := by
  obtain ⟨t,ht,heq⟩ := uncut_endpoint_turn_product P hP S root hroot e hOff i hhere
  rw [heq]
  exact mul_neg_of_pos_of_neg ht hturn




end
end DirectGLSSW.UncutDaughterTurns
