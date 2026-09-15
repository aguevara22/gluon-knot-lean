namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.nearSign P g k = π.nearSign Q g k := hchi _ _ _

theorem farSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.farSign P g k = π.farSign Q g k := hchi _ _ _

theorem ordinaryWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g :=
  π.ordinaryWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

theorem rootWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.rootWeight P hP g = π.rootWeight Q hQ g :=
  π.rootWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

end IntervalComposition

theorem openTreeSum_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (I : BoundaryInterval n) :
    openTreeSum P hP g I = openTreeSum Q hQ g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_eq_of_chi hP hQ hchi g

theorem treeCoefficient_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_eq_of_chi hP hQ hchi g
  · funext J π
    exact π.rootWeight_eq_of_chi hP hQ hchi g

theorem openTreeSum_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n)
    (I : BoundaryInterval n) :
    openTreeSum (shift a P) (g1_shift_forward a hP) (g - a) I = openTreeSum P hP g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_shift P hP g a

theorem treeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (shift a P) (g1_shift_forward a hP) (g - a) hn =
      treeCoefficient P hP g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_shift P hP g a
  · funext J π
    exact π.rootWeight_shift P hP g a

/-- Fixed label zero on the shifted representative corresponds to label a on
the original representative. No independence of different physical roots is assumed. -/
theorem mainTreeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (a : ZMod n) (hn : 3 ≤ n) :
    mainTreeCoefficient (shift a P) (g1_shift_forward a hP) hn = treeCoefficient P hP a hn := by
  simpa only [mainTreeCoefficient, sub_self] using treeCoefficient_shift P hP a a hn

theorem treesumData_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treesumData (shift a P) (g1_shift_forward a hP) (g - a) hn =
      (openTreeSum P hP g, treeCoefficient P hP g hn, treeCoefficient P hP a hn) := by
  unfold treesumData
  rw [funext (openTreeSum_shift P hP g a), treeCoefficient_shift P hP g a hn,
    mainTreeCoefficient_shift P hP a hn]

end

end SM
