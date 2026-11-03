import DirectGLSSW.DaughterTurns
import LocalSupportConjugacy
import ConfigurationEventLocality

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniformDaughterSupportLocality
open TruncationDirection DaughterFirstReturn PermutationOrbits LocalCrossingTransport LocalSupportConjugacy Filter Topology

/-- The source's actual consecutive-side determinant at a retained daughter corner. -/
def daughterCornerDet {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S root))) : ℝ :=
  planarDet (daughterSideVector q hq.g2 S root
    ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹ i))
    (daughterSideVector q hq.g2 S root i)

/-- Literal root-level uniformity, preserving the disjunction of universal signs. -/
def daughterUniform {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q) : Prop :=
  (∀ i, 0 < daughterCornerDet q hq S root i) ∨
  (∀ i, daughterCornerDet q hq S root i < 0)

/-- Exactly the support predicate of the final frozen statement, with no chosen roots. -/
def uniformDaughterSupport {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) : Prop :=
  PolygonNonalternation.polygonNonalternating q hq.g2 S ∧
    ∀ C : Component (smoothingDartPermutation q hq.g2 S),
      ∃ root : PolygonEvent q, retainedCorner q S root ∧
        componentOf (smoothingDartPermutation q hq.g2 S) root = C ∧
        daughterUniform q hq S root

/-- Incoming parent carrier of a retained anchor or selected crossing visit.
Unselected visits are never used as corners. -/
def incomingCarrier {n : ℕ} (q : Fin n → PlanarPoint ℝ) (x : PolygonEvent q) : Fin n :=
  match x with
  | .inl e => (cyclicSuccessorPerm n)⁻¹ e
  | .inr v => crossingVisitEdge q (crossingVisitFlip q v)

def carrierCornerDet {n : ℕ} (q : Fin n → PlanarPoint ℝ) (x : PolygonEvent q) : ℝ :=
  planarDet (cyclicTangent q (incomingCarrier q x))
    (cyclicTangent q (polygonEventEdge q x))

theorem daughterCornerDet_signs {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q))
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S root))) :
    let x := orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val
    (0 < daughterCornerDet q hq S root i ↔ 0 < carrierCornerDet q x) ∧
    (daughterCornerDet q hq S root i < 0 ↔ carrierCornerDet q x < 0) := by
  classical
  let prev := (cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹ i
  let x := orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val
  have hin : polygonEventEdge q
      (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root prev).val) =
      incomingCarrier q x := by
    cases hx : x with
    | inl e =>
      exact DaughterTurns.daughterTurn_anchor_incomingCarrier q hq.g2 S
        hq.size_ge_three root hroot i e hx
    | inr v =>
      have hv : v.1 ∈ S := by
        have h := (cornerEnumeration q hq.g2 S root i).property
        change retainedCorner q S x at h
        simpa only [hx, retainedCorner] using h
      have h := DaughterTurns.daughterTurn_selectedVisit_incomingCarrier q hq.g2 S
        hq.size_ge_three root hroot i v hx hv
      rw [h]
      cases v with
      | mk c b => cases b <;>
        simp [incomingCarrier, hx, smoothingPairing, smoothingPairingMap,
          crossingVisitFlip, polygonEventEdge, hv]
  obtain ⟨ha, hprev⟩ := daughterSide_positive_multiple q hq.g2 S
    hq.size_ge_three root hroot prev
  obtain ⟨hb, hhere⟩ := daughterSide_positive_multiple q hq.g2 S
    hq.size_ge_three root hroot i
  let a := daughterSideScale q hq.g2 S root (cornerEnumeration q hq.g2 S root prev)
  let b := daughterSideScale q hq.g2 S root (cornerEnumeration q hq.g2 S root i)
  have hab : 0 < a * b := mul_pos ha hb
  have hformula : daughterCornerDet q hq S root i = (a * b) * carrierCornerDet q x := by
    unfold daughterCornerDet
    rw [hprev, hhere, hin]
    simp [carrierCornerDet, x, a, b, planarDet, smul_eq_mul]
    ring
  dsimp only
  rw [hformula]
  refine ⟨mul_pos_iff_of_pos_left hab, ?_⟩
  simpa only [mul_zero] using
    (mul_lt_mul_left hab : (a * b) * carrierCornerDet q x < (a * b) * 0 ↔
      carrierCornerDet q x < 0)

/-- The finite corner enumeration covers precisely all retained events in its root's orbit. -/
theorem retained_event_enumerated {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q))
    (root x : PolygonEvent q) (hx : retainedCorner q S x)
    (hc : componentOf (smoothingDartPermutation q hq.g2 S) x =
      componentOf (smoothingDartPermutation q hq.g2 S) root) :
    ∃ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
      orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val = x := by
  let y : Fibre (DartPerm q hq.g2 S) (componentOf (DartPerm q hq.g2 S) root) := ⟨x, hc⟩
  obtain ⟨j, hj⟩ := (orbitEnumeration (DartPerm q hq.g2 S) root).surjective y
  have hjx : orbitEventAt q hq.g2 S root j = x := congrArg Subtype.val hj
  let c : CornerCoord q hq.g2 S root := ⟨j, by rw [hjx]; exact hx⟩
  obtain ⟨i, hi⟩ := (cornerEnumeration q hq.g2 S root).surjective c
  refine ⟨i, ?_⟩
  rw [hi]
  exact hjx

theorem daughterUniform_iff_carrier {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (S : Finset (PolygonCrossing q))
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    daughterUniform q hq S root ↔
      ((∀ x : PolygonEvent q, retainedCorner q S x →
          componentOf (smoothingDartPermutation q hq.g2 S) x =
            componentOf (smoothingDartPermutation q hq.g2 S) root →
          0 < carrierCornerDet q x) ∨
       (∀ x : PolygonEvent q, retainedCorner q S x →
          componentOf (smoothingDartPermutation q hq.g2 S) x =
            componentOf (smoothingDartPermutation q hq.g2 S) root →
          carrierCornerDet q x < 0)) := by
  constructor
  · rintro (hpos | hneg)
    · left
      intro x hx hc
      obtain ⟨i, hi⟩ := retained_event_enumerated q hq S root x hx hc
      have hs := (daughterCornerDet_signs q hq S root hroot i).1.mp (hpos i)
      simpa only [hi] using hs
    · right
      intro x hx hc
      obtain ⟨i, hi⟩ := retained_event_enumerated q hq S root x hx hc
      have hs := (daughterCornerDet_signs q hq S root hroot i).2.mp (hneg i)
      simpa only [hi] using hs
  · rintro (hpos | hneg)
    · left
      intro i
      apply (daughterCornerDet_signs q hq S root hroot i).1.mpr
      exact hpos _ (cornerEnumeration q hq.g2 S root i).property
        (orbitEnumeration (DartPerm q hq.g2 S) root
          (cornerEnumeration q hq.g2 S root i).val).property
    · right
      intro i
      apply (daughterCornerDet_signs q hq S root hroot i).2.mpr
      exact hneg _ (cornerEnumeration q hq.g2 S root i).property
        (orbitEnumeration (DartPerm q hq.g2 S) root
          (cornerEnumeration q hq.g2 S root i).val).property

end DirectGLSSW.UniformDaughterSupportLocality
