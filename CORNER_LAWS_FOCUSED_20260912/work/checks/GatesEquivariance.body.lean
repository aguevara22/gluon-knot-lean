namespace SM

noncomputable section

theorem ordinaryGate_congr {d h d' h' : SignType} (ed : d = d') (eh : h = h')
    (hd : d ≠ 0) (hh : h ≠ 0) (hd' : d' ≠ 0) (hh' : h' ≠ 0) :
    ordinaryGate d h hd hh = ordinaryGate d' h' hd' hh' := by
  cases ed
  cases eh
  rfl

theorem rootGate_congr {d h d' h' : SignType} (ed : d = d') (eh : h = h')
    (hd : d ≠ 0) (hh : h ≠ 0) (hd' : d' ≠ 0) (hh' : h' ≠ 0) :
    rootGate d h hd hh = rootGate d' h' hd' hh' := by
  cases ed
  cases eh
  rfl

variable {n : ℕ} [NeZero n]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearSign_shift (P : LabelledTuple n) (g a : ZMod n) (k : Fin (π.parts - 1)) :
    π.nearSign (shift a P) (g - a) k = π.nearSign P g k := by
  unfold nearSign
  rw [chi_shift]
  congr 1 <;> unfold boundaryIndex <;> ring

theorem farSign_shift (P : LabelledTuple n) (g a : ZMod n) (k : Fin (π.parts - 1)) :
    π.farSign (shift a P) (g - a) k = π.farSign P g k := by
  unfold farSign
  rw [chi_shift]
  congr 1 <;> unfold boundaryIndex <;> ring

theorem ordinaryWeight_eq_of_signs (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q)
    (g h : ZMod n) (hd : ∀ k, π.nearSign P g k = π.nearSign Q h k)
    (hh : ∀ k, π.farSign P g k = π.farSign Q h k) :
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ h := by
  apply Finset.prod_congr rfl
  intro k _
  exact ordinaryGate_congr (hd k) (hh k) _ _ _ _

theorem rootWeight_eq_of_signs (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q)
    (g h : ZMod n) (hd : ∀ k, π.nearSign P g k = π.nearSign Q h k)
    (hh : ∀ k, π.farSign P g k = π.farSign Q h k) :
    π.rootWeight P hP g = π.rootWeight Q hQ h := by
  apply Finset.prod_congr rfl
  intro k _
  exact rootGate_congr (hd k) (hh k) _ _ _ _

theorem ordinaryWeight_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    π.ordinaryWeight (shift a P) (g1_shift_forward a hP) (g - a) =
      π.ordinaryWeight P hP g :=
  π.ordinaryWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_shift P g a) (π.farSign_shift P g a)

theorem rootWeight_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    π.rootWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.rootWeight P hP g :=
  π.rootWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_shift P g a) (π.farSign_shift P g a)

end IntervalComposition

/-- All gates descend under the exact simultaneous source relabelling of the
polygon and its physical root edge, including arbitrary cyclic shifts. -/
theorem gatesData_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    gatesData (shift a P) (g1_shift_forward a hP) (g - a) = gatesData P hP g := by
  funext I π
  have hd := funext (π.nearSign_shift P g a)
  have hh := funext (π.farSign_shift P g a)
  dsimp only [gatesData]
  rw [hd, hh, π.ordinaryWeight_shift P hP g a, π.rootWeight_shift P hP g a]

end

end SM
