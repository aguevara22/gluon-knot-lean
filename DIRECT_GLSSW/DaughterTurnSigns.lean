import DirectGLSSW.DaughterTurns
import DirectGLSSW.GeometricSmoothingWeights

set_option autoImplicit false
namespace DirectGLSSW.SmoothingTurnCount
open DaughterFirstReturn DaughterTurns GeometricSmoothingWeights PermutationOrbits
open scoped BigOperators
noncomputable section

/-- Source left-turn determinant, incoming tangent followed by outgoing tangent. -/
def turnValue {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) : ℝ :=
  planarDet (cyclicTangent q ((cyclicSuccessorPerm n).symm i)) (cyclicTangent q i)

/-- Number of strictly left-turning vertices of the actual cyclic polygon. -/
def leftTurnCount {n : ℕ} (q : Fin n → PlanarPoint ℝ) : ℕ :=
  ∑ i, if 0 < turnValue q i then 1 else 0

/-- Incoming original carrier after smoothing at a retained event. -/
def incomingCarrier {n : ℕ} (q : Fin n → PlanarPoint ℝ) : PolygonEvent q → Fin n
  | .inl i => (cyclicSuccessorPerm n).symm i
  | .inr v => crossingVisitEdge q (crossingVisitFlip q v)

/-- The determinant of original carrier tangents at a retained event. -/
def eventTurnValue {n : ℕ} (q : Fin n → PlanarPoint ℝ) (x : PolygonEvent q) : ℝ :=
  planarDet (cyclicTangent q (incomingCarrier q x)) (cyclicTangent q (polygonEventEdge q x))

theorem eventTurnValue_anchor {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    eventTurnValue q (.inl i) = turnValue q i := rfl

theorem daughter_incomingCarrier {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (hn : 3 ≤ n) (root : PolygonEvent q) (hr : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    polygonEventEdge q (orbitEventAt q hG2 S root
      (cornerEnumeration q hG2 S root ((cyclicSuccessorPerm _).symm i)).val) =
    incomingCarrier q (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val) := by
  classical
  cases hx : orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val with
  | inl a => exact daughterTurn_anchor_incomingCarrier q hG2 S hn root hr i a hx
  | inr v =>
    have hv : v.1 ∈ S := by
      have h := (cornerEnumeration q hG2 S root i).property
      simpa only [hx, retainedCorner] using h
    have h := daughterTurn_selectedVisit_incomingCarrier q hG2 S hn root hr i v hx hv
    simpa [incomingCarrier, smoothingPairing, smoothingPairingMap, hv, polygonEventEdge] using h

theorem daughter_leftTurn_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (hn : 3 ≤ n) (root : PolygonEvent q) (hr : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    0 < turnValue (daughterVertex q hG2 S root) i ↔
    0 < eventTurnValue q (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val) := by
  let prev := (cyclicSuccessorPerm (Fintype.card (CornerCoord q hG2 S root))).symm i
  obtain ⟨ha, hin⟩ := daughterSide_positive_multiple q hG2 S hn root hr prev
  obtain ⟨hb, hout⟩ := daughterSide_positive_multiple q hG2 S hn root hr i
  have hcarrier := daughter_incomingCarrier q hG2 S hn root hr i
  change 0 < planarDet (daughterSideVector q hG2 S root prev)
    (daughterSideVector q hG2 S root i) ↔ _
  rw [hin, hout]
  have hdet (a b : ℝ) (u v : PlanarPoint ℝ) :
      planarDet (a • u) (b • v) = (a*b)*planarDet u v := by
    simp [planarDet, smul_eq_mul]; ring
  rw [hdet, mul_pos_iff_of_pos_left (mul_pos ha hb)]
  change 0 < planarDet
    (cyclicTangent q (polygonEventEdge q (orbitEventAt q hG2 S root
      (cornerEnumeration q hG2 S root prev).val))) _ ↔ _
  rw [hcarrier]
  rfl

theorem crossing_leftTurn_sum {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (c : PolygonCrossing q) :
    (∑ b : Bool, if 0 < eventTurnValue q (.inr (c,b)) then 1 else 0) = (1 : ℕ) := by
  classical
  have h := crossing_transverse hq.size_ge_three q hq.g1 c
  simp only [Fintype.sum_bool, eventTurnValue, incomingCarrier, polygonEventEdge,
    crossingVisitFlip, crossingVisitEdge, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    if_false, if_true]
  rw [planarDet_swap (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)]
  rcases lt_or_gt_of_ne h with hneg | hpos
  · simp [hneg,not_lt_of_gt hneg]
  · simp [hpos,not_lt_of_gt hpos]









end
end DirectGLSSW.SmoothingTurnCount
