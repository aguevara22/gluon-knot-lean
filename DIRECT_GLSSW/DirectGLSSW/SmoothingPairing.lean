import DirectGLSSW.PolygonEvents
import Mathlib.Algebra.Group.End

/-!
# Pairing selected actual crossing visits

Source: frozen note lines 131–139. This exchanges the outgoing branches
at exactly the selected crossing visits, retaining original vertex anchors.
It is the local pairing operator used with the original traversal successor;
no component-count or geometric smoothing equivalence is asserted here.
-/

namespace DirectGLSSW

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- Fix anchors and unselected visits; exchange the two visits at each cut. -/
noncomputable def smoothingPairingMap (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) : PolygonEvent q → PolygonEvent q := by
  classical
  exact fun x => match x with
    | .inl e => .inl e
    | .inr v => if v.1 ∈ S then .inr (crossingVisitFlip q v) else .inr v

theorem smoothingPairingMap_anchor (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) (e : Fin n) :
    smoothingPairingMap q S (.inl e) = .inl e := rfl

theorem smoothingPairingMap_visit (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) (v : CrossingVisit q) :
    smoothingPairingMap q S (.inr v) =
      if v.1 ∈ S then .inr (crossingVisitFlip q v) else .inr v := by
  classical
  rfl

/-- Each selected pair is exchanged twice; every other event is fixed. -/
theorem smoothingPairingMap_involutive (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) :
    Function.Involutive (smoothingPairingMap q S) := by
  classical
  intro x
  cases x with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨c, b⟩
      by_cases h : c ∈ S <;> cases b <;>
        simp [smoothingPairingMap, crossingVisitFlip, h]

/-- The selected crossing pairing is an actual permutation, equal to its inverse. -/
noncomputable def smoothingPairing (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) : Equiv.Perm (PolygonEvent q) where
  toFun := smoothingPairingMap q S
  invFun := smoothingPairingMap q S
  left_inv := smoothingPairingMap_involutive q S
  right_inv := smoothingPairingMap_involutive q S

theorem smoothingPairing_apply (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingPairing q S x = smoothingPairingMap q S x := rfl

theorem smoothingPairing_inv (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) :
    (smoothingPairing q S)⁻¹ = smoothingPairing q S := rfl

/-- The paired event is at the same actual plane point, not a new location. -/
theorem smoothingPairing_point (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    polygonEventPoint q (smoothingPairing q S x) = polygonEventPoint q x := by
  classical
  cases x with
  | inl e => rfl
  | inr v =>
      change polygonEventPoint q (if v.1 ∈ S then Sum.inr (crossingVisitFlip q v)
        else Sum.inr v) = _
      split_ifs <;> rfl

/-- Exactly selected crossing visits move; all anchors and other visits remain fixed. -/
theorem smoothingPairing_visit_fixed_iff (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) (v : CrossingVisit q) :
    smoothingPairing q S (.inr v) = .inr v ↔ v.1 ∉ S := by
  classical
  change (if v.1 ∈ S then Sum.inr (crossingVisitFlip q v) else Sum.inr v) = Sum.inr v ↔ _
  by_cases h : v.1 ∈ S
  · simp [h, crossingVisitFlip_ne_self q v]
  · simp [h]

/-- No cut means the identity pairing. -/
theorem smoothingPairing_empty (q : Fin n → PlanarPoint K) :
    smoothingPairing q ∅ = 1 := by
  classical
  ext x
  cases x with
  | inl e => rfl
  | inr v => simp [smoothingPairing, smoothingPairingMap]

/-- Pairings commute because every crossing has its own two visits. -/
theorem smoothingPairing_commute (q : Fin n → PlanarPoint K)
    (S T : Finset (PolygonCrossing q)) :
    smoothingPairing q S * smoothingPairing q T =
      smoothingPairing q T * smoothingPairing q S := by
  classical
  ext x
  cases x with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨c, b⟩
      by_cases hs : c ∈ S <;> by_cases ht : c ∈ T <;> cases b <;>
        simp [Equiv.Perm.mul_apply, smoothingPairing, smoothingPairingMap,
          crossingVisitFlip, hs, ht]

/-- Applying disjoint supports in two stages is exactly the union pairing. -/
theorem smoothingPairing_union (q : Fin n → PlanarPoint K)
    (S T : Finset (PolygonCrossing q)) (h : Disjoint S T) :
    smoothingPairing q (S ∪ T) = smoothingPairing q S * smoothingPairing q T := by
  classical
  ext x
  cases x with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨c, b⟩
      have hd : ¬ (c ∈ S ∧ c ∈ T) := fun hc => Finset.disjoint_left.mp h hc.1 hc.2
      by_cases hs : c ∈ S <;> by_cases ht : c ∈ T <;> cases b <;>
        simp_all [Equiv.Perm.mul_apply, smoothingPairing, smoothingPairingMap,
          crossingVisitFlip]

/-- A single cut is exactly the transposition of its two actual visits. -/
theorem smoothingPairing_singleton (q : Fin n → PlanarPoint K)
    (c : PolygonCrossing q) :
    smoothingPairing q {c} =
      Equiv.swap (Sum.inr (c, false) : PolygonEvent q) (Sum.inr (c, true)) := by
  ext x
  cases x with
  | inl e => simp [smoothingPairing, smoothingPairingMap, Equiv.swap_apply_def]
  | inr v =>
      rcases v with ⟨d, b⟩
      by_cases h : d = c
      · subst d
        cases b <;> simp [smoothingPairing, smoothingPairingMap,
          crossingVisitFlip, Equiv.swap_apply_def, Sum.inr.injEq, Prod.mk.injEq]
      · have hl : (Sum.inr (d, b) : PolygonEvent q) ≠ Sum.inr (c, false) := by
          intro he
          exact h (congrArg Prod.fst (Sum.inr.inj he))
        have hr : (Sum.inr (d, b) : PolygonEvent q) ≠ Sum.inr (c, true) := by
          intro he
          exact h (congrArg Prod.fst (Sum.inr.inj he))
        simp only [Equiv.swap_apply_def]
        simp [smoothingPairing, smoothingPairingMap, h, hl, hr]

/-- Each support pairing has order dividing two, including the empty support. -/
theorem smoothingPairing_mul_self (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) :
    smoothingPairing q S * smoothingPairing q S = 1 := by
  ext x
  exact smoothingPairingMap_involutive q S x

/-- Exact moved-event criterion; this does not count permutation components. -/
theorem smoothingPairing_moved_iff (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingPairing q S x ≠ x ↔
      match x with
      | .inl _ => False
      | .inr v => v.1 ∈ S := by
  cases x with
  | inl e => simp [smoothingPairing, smoothingPairingMap]
  | inr v => simpa only [not_not] using not_congr (smoothingPairing_visit_fixed_iff q S v)

end DirectGLSSW
