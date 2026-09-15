import SM.ShiftReversal

/-! Source lem:shift (frame SM15, sm-1-polygons.tex:496), all four clauses as
printed. σ is `shift 1`, ρ is `reversal`. Clause (iii) carries the SM15 zero-turn
count z(P) = `zeroTurns P`; the count identity is stated in ℤ so that the
subtraction is the genuine one. The generic specialisation ℓ(P̄) = n − ℓ(P) uses
lem:g1(ii) (every turn of a generic polygon is ±1). Clause (iv) is stated on the
regular locus, with its closure under σ and ρ. -/

namespace SM

variable {n : ℕ} [NeZero n]

/-- z(P): the number of zero turns of a labelled tuple (SM15 lem:shift(iii)). -/
noncomputable def zeroTurns (P : LabelledTuple n) : ℕ :=
  (Finset.univ.filter (fun i => turn P i = 0)).card

/-- Every index carries exactly one of the three turn values. -/
theorem leftTurns_add_rightTurns_add_zeroTurns (P : LabelledTuple n) :
    leftTurns P + rightTurns P + zeroTurns P = n := by
  classical
  have hone : ∀ i : ZMod n,
      ((if turn P i = 1 then 1 else 0) + (if turn P i = -1 then 1 else 0) +
        (if turn P i = 0 then 1 else 0) : ℕ) = 1 := by
    intro i
    rcases SignType.trichotomy (turn P i) with h | h | h <;> simp +decide [h]
  unfold leftTurns rightTurns zeroTurns
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [hone, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]

/-- SM15 lem:shift(iii): the left turns of the reversal are the right turns of
the original, which number n − ℓ(P) − z(P). -/
theorem leftTurns_reversal_int (P : LabelledTuple n) :
    (leftTurns (reversal P) : ℤ) = n - leftTurns P - zeroTurns P := by
  have h := leftTurns_add_rightTurns_add_zeroTurns P
  rw [leftTurns_reversal_eq_right]
  omega

/-- On the generic locus every turn is ±1 (lem:g1(ii)), so z(P) = 0. -/
theorem zeroTurns_eq_zero_of_generic (hn : 3 ≤ n) {P : LabelledTuple n}
    (h : Generic P) : zeroTurns P = 0 := by
  classical
  have : Fact (1 < n) := ⟨by omega⟩
  unfold zeroTurns
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rw [turn_det]
  exact sign_ne_zero.mpr (g1_turn_nonzero hn h.1 i)

/-- All four clauses of SM15 lem:shift for the labelled tuple `P` (n ≥ 3):
(i) the chirotope and edge identities under σ = `shift 1` and ρ = `reversal`;
(ii) σ and ρ map the generic locus onto itself, map (labelled and cyclic)
chambers onto chambers, and relabel the crossing set; (iii) the turn identities
and ℓ(P̄) = n − ℓ(P) − z(P), with ℓ(P̄) = n − ℓ(P) for generic P; (iv) on the
regular locus σP and P̄ are regular, rot(σP) = rot(P) and rot(P̄) = −rot(P). -/
theorem shift_reversal (hn : 3 ≤ n) (P : LabelledTuple n) :
    (∀ i j k, chi (shift 1 P) i j k = chi P (i + 1) (j + 1) (k + 1)) ∧
    (∀ i j k, chi (reversal P) i j k = chi P (2 - i) (2 - j) (2 - k)) ∧
    (∀ i, edge (shift 1 P) i = edge P (i + 1)) ∧
    (∀ i t, edgePoint (shift 1 P) i t = edgePoint P (i + 1) t) ∧
    (∀ i, edge (reversal P) i = -edge P (1 - i)) ∧
    (∀ i t, edgePoint (reversal P) i t = edgePoint P (1 - i) (1 - t)) ∧
    (Generic (shift 1 P) ↔ Generic P) ∧
    (Generic (reversal P) ↔ Generic P) ∧
    Function.Surjective (genericShift (1 : ZMod n)) ∧
    Function.Surjective (genericReversal (n := n)) ∧
    (∀ Q : GenericTuple n,
      genericShift 1 '' labelledChamber Q = labelledChamber (genericShift 1 Q)) ∧
    (∀ Q : GenericTuple n, polygonProjection (genericShift 1 Q) = polygonProjection Q) ∧
    (∀ Q : GenericTuple n,
      genericReversal '' labelledChamber Q = labelledChamber (genericReversal Q)) ∧
    (∀ Q : GenericPolygon n,
      genericPolygonReversal '' chamber Q = chamber (genericPolygonReversal Q)) ∧
    crossingSet (shift 1 P) = (crossingSet P).image (translateSupport (-1)) ∧
    crossingSet (reversal P) = (crossingSet P).image reverseSupport ∧
    (∀ i, turn (shift 1 P) i = turn P (i + 1)) ∧
    (∀ i, turn (reversal P) i = -turn P (2 - i)) ∧
    (leftTurns (reversal P) : ℤ) = n - leftTurns P - zeroTurns P ∧
    (Generic P → zeroTurns P = 0 ∧ (leftTurns (reversal P) : ℤ) = n - leftTurns P) ∧
    (Regular P → Regular (shift 1 P) ∧ Regular (reversal P) ∧
      rotationNumber (shift 1 P) = rotationNumber P ∧
      rotationNumber (reversal P) = -rotationNumber P) := by
  refine ⟨chi_shift 1 P, chi_reversal P, edge_shift 1 P, edgePoint_shift 1 P,
    edge_reversal P, edgePoint_reversal P, generic_shift 1 P, generic_reversal P,
    (genericShiftHomeomorph 1).surjective, genericReversalHomeomorph.surjective,
    genericShift_labelledChamber 1, projection_genericShift 1,
    genericReversal_labelledChamber, genericPolygonReversal_chamber,
    crossingSet_shift P 1, crossingSet_reversal P, turn_shift 1 P, turn_reversal P,
    leftTurns_reversal_int P, ?_, ?_⟩
  · intro h
    have hz := zeroTurns_eq_zero_of_generic hn h
    have hl := leftTurns_reversal_int P
    exact ⟨hz, by omega⟩
  · intro h
    exact ⟨regular_shift_forward 1 h, regular_reversal_forward h,
      rotationNumber_shift 1 P, rotationNumber_reversal h⟩

end SM
