namespace GatesEquivarianceIndependentReview
open SM

-- The source generator sigma sends the root g exactly to g-1.
theorem source_generator {n : ℕ} [NeZero n] (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    gatesData (shift 1 P) (g1_shift_forward 1 hP) (g - 1) = gatesData P hP g :=
  gatesData_shift P hP g 1

-- Any two allowed representative/root presentations give the same whole data.
-- A different proof of G1 for the shifted representative cannot change it.
theorem rooted_representative_descent {n : ℕ} [NeZero n]
    (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q) (g h a : ZMod n)
    (hQeq : Q = shift a P) (hroot : h = g - a) :
    gatesData Q hQ h = gatesData P hP g := by
  subst Q
  subst h
  exact gatesData_shift P hP g a

-- The proof-carrying nonzero interface carries no numerical proof dependence.
theorem G1_proof_independence {n : ℕ} [NeZero n] (P : LabelledTuple n)
    (hP hP' : G1 P) (g : ZMod n) : gatesData P hP g = gatesData P hP' g := rfl

end GatesEquivarianceIndependentReview
