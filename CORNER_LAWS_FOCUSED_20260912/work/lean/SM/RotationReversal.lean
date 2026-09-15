import SM.RotationNumber
import SM.Reversal

/-! The actual traversal reversal i -> 2-i preserves regularity and negates
the principal turns and their sum. This is the reversal part of lem:rot(iii). -/

namespace SM

theorem euclideanLength_neg (u : Plane) : euclideanLength (-u) = euclideanLength u := by
  simp only [euclideanLength, planeComplex_neg, norm_neg]

theorem planeDot_reverse (u v : Plane) : planeDot (-v) (-u) = planeDot u v := by
  simp [planeDot]
  ring

theorem det_reverse_neg (u v : Plane) : det (-v) (-u) = -det u v := by
  simp [det]
  ring

theorem principalAngleSpec_reverse {u v : Plane} {θ : ℝ} (h : PrincipalAngleSpec u v θ) :
    PrincipalAngleSpec (-v) (-u) (-θ) := by
  refine ⟨⟨by linarith [h.1.2], by linarith [h.1.1]⟩, ?_, ?_⟩
  · rw [Real.cos_neg, h.2.1, planeDot_reverse, euclideanLength_neg, euclideanLength_neg,
      mul_comm (euclideanLength v) (euclideanLength u)]
  · rw [Left.sign_neg, h.2.2, det_reverse_neg, Left.sign_neg]

theorem regularPair_reverse {u v : Plane} (h : RegularPair u v) : RegularPair (-v) (-u) :=
  regularPair_of_principalAngleSpec (principalAngleSpec_reverse (principalAngle_spec h))

theorem principalAngle_reverse {u v : Plane} (h : RegularPair u v) :
    principalAngle (-v) (-u) = -principalAngle u v :=
  principalAngleSpec_unique (principalAngle_spec (regularPair_reverse h))
    (principalAngleSpec_reverse (principalAngle_spec h))

variable {n : ℕ}

theorem regular_reversal_forward {P : LabelledTuple n} (h : Regular P) : Regular (reversal P) := by
  intro i
  have ha : (1 : ZMod n) - (i - 1) = 2 - i := by ring
  have hb : (2 : ZMod n) - i - 1 = 1 - i := by ring
  simpa only [edge_reversal, ha, hb] using regularPair_reverse (h (2 - i))

theorem regular_reversal (P : LabelledTuple n) : Regular (reversal P) ↔ Regular P := by
  constructor
  · intro h
    simpa only [reversal_involutive P] using regular_reversal_forward h
  · exact regular_reversal_forward

theorem principalTurn_reversal {P : LabelledTuple n} (h : Regular P) (i : ZMod n) :
    principalTurn (reversal P) i = -principalTurn P (2 - i) := by
  have ha : (1 : ZMod n) - (i - 1) = 2 - i := by ring
  have hb : (2 : ZMod n) - i - 1 = 1 - i := by ring
  simpa only [principalTurn, edge_reversal, ha, hb] using principalAngle_reverse (h (2 - i))

theorem rotationNumber_reversal [NeZero n] {P : LabelledTuple n} (h : Regular P) :
    rotationNumber (reversal P) = -rotationNumber P := by
  have hs : (∑ i : ZMod n, principalTurn P (2 - i)) = ∑ i : ZMod n, principalTurn P i := by
    exact Equiv.sum_comp (Equiv.subLeft 2) (principalTurn P)
  unfold rotationNumber
  simp_rw [principalTurn_reversal h]
  rw [Finset.sum_neg_distrib, hs, neg_div]

end SM
