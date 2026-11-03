import DirectGLSSW.DaughterTurns
import DirectGLSSW.RealPolygons
import Mathlib.Algebra.Module.Prod

set_option autoImplicit false

namespace DirectGLSSW.DaughterAnchorScales

open DaughterFirstReturn DaughterTurns

theorem exists_daughter_anchor_incident_scales {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root)))
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hhere : orbitEventAt q hG2 S root
      (cornerEnumeration q hG2 S root i).val = Sum.inl a) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧
      daughterVertex q hG2 S root i = q a ∧
      daughterVertex q hG2 S root
          ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root)))⁻¹ i) =
        q a + α • (q p - q a) ∧
      daughterVertex q hG2 S root (cyclicSuccessor i) =
        q a + β • (q (cyclicSuccessor a) - q a)
 := by
  classical
  let m := Fintype.card (CornerCoord q hG2 S root)
  let prev : Fin m := (cyclicSuccessorPerm m)⁻¹ i
  have hprev : cyclicSuccessor prev = i :=
    Equiv.apply_symm_apply (cyclicSuccessorPerm m) i
  have hparentPrev : (cyclicSuccessorPerm n)⁻¹ a = p := by
    rw [← hp]
    exact Equiv.symm_apply_apply (cyclicSuccessorPerm n) p
  have hvalue : daughterVertex q hG2 S root i = q a := by
    unfold daughterVertex
    rw [hhere]
    rfl
  let α := daughterSideScale q hG2 S root (cornerEnumeration q hG2 S root prev)
  let β := daughterSideScale q hG2 S root (cornerEnumeration q hG2 S root i)
  obtain ⟨hα, hleft⟩ := daughterSide_positive_multiple q hG2 S hn root hroot prev
  obtain ⟨hβ, hright⟩ := daughterSide_positive_multiple q hG2 S hn root hroot i
  have hcarrier := daughterTurn_anchor_incomingCarrier q hG2 S hn root hroot i a hhere
  rw [hparentPrev] at hcarrier
  change polygonEventEdge q
    (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root prev).val) = p at hcarrier
  have hleft' : q a - daughterVertex q hG2 S root prev = α • (q a - q p) := by
    simpa only [daughterSideVector, hprev, hvalue, hcarrier, cyclicTangent, hp] using hleft
  have hright' : daughterVertex q hG2 S root (cyclicSuccessor i) - q a =
      β • (q (cyclicSuccessor a) - q a) := by
    simpa only [daughterSideVector, hvalue, hhere, polygonEventEdge, cyclicTangent] using hright
  refine ⟨α, hα, β, hβ, hvalue, ?_, ?_⟩
  · change daughterVertex q hG2 S root prev = _
    have hneg : daughterVertex q hG2 S root prev - q a = α • (q p - q a) := by
      calc
        daughterVertex q hG2 S root prev - q a =
            -(q a - daughterVertex q hG2 S root prev) := (neg_sub _ _).symm
        _ = -(α • (q a - q p)) := congrArg Neg.neg hleft'
        _ = α • (-(q a - q p)) := (smul_neg α (q a - q p)).symm
        _ = α • (q p - q a) := congrArg (fun v : PlanarPoint ℝ => α • v) (neg_sub _ _)
    exact sub_eq_iff_eq_add'.mp hneg
  · exact sub_eq_iff_eq_add'.mp hright'

end DirectGLSSW.DaughterAnchorScales
