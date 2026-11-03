import DirectGLSSW.GateFidelity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Cartesian realization of the nonzero GLSSW gates

Source: `ep:H`, `ep:linear-gates`, and the momentum-edge convention in
Section 1 of the frozen note. Coordinates over a linearly ordered field use
the usual oriented Cartesian determinant. In particular, the note's H
determinant is the NEGATIVE of the
Cartesian turn determinant. No identification of this determinant with the
published GLSSW spinor bracket is assumed or asserted here.

The real-coordinate specialization requires a real-number import and is
not included in this module.

The sign function below requires a nonzero input. The total extension of
`scalarPositiveStep` at zero is only an implementation choice; every gate
identification has explicit nonvanishing hypotheses.
-/

namespace DirectGLSSW

variable {K : Type*}

abbrev PlanarPoint (K : Type*) := K × K

section Determinants

variable [CommRing K]

/-- The determinant in the explicitly chosen Cartesian orientation. -/
def planarDet (u v : PlanarPoint K) : K := u.1 * v.2 - u.2 * v.1

/-- The directed chord from vertex `a` to vertex `b`. -/
def polygonChord (q : ℕ → PlanarPoint K) (a b : ℕ) : PlanarPoint K := q b - q a

/-- One external momentum in an opened boundary word. -/
def polygonMomentum (q : ℕ → PlanarPoint K) (a : ℕ) : PlanarPoint K :=
  polygonChord q a (a + 1)

/-- The scalar determinant whose sign is H in `ep:H`. -/
def polygonHDet (q : ℕ → PlanarPoint K) (i k j : ℕ) : K :=
  planarDet (q k - q j) (q i - q j)

/-- The source's H determinant is minus the Cartesian turn determinant.
No ordering or noncollinearity is needed for this polynomial identity. -/
theorem polygonHDet_eq_neg_turn (q : ℕ → PlanarPoint K) (a b c : ℕ) :
    polygonHDet q a b c =
      -planarDet (polygonChord q a b) (polygonChord q b c) := by
  simp only [polygonHDet, planarDet, polygonChord, Prod.fst_sub, Prod.snd_sub]
  ring

/-- The determinant of the preceding partial momentum and the whole chord
is the same Cartesian determinant as that of the two partial momenta. -/
theorem polygonDet_partial_total (q : ℕ → PlanarPoint K) (i k j : ℕ) :
    planarDet (polygonChord q i k) (polygonChord q i j) =
      planarDet (polygonChord q i k) (polygonChord q k j) := by
  simp only [planarDet, polygonChord, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Both the corner and far Cartesian determinants are negatives of their
H determinants, so their product has no residual orientation minus sign. -/
theorem polygonDet_corner_far_product (q : ℕ → PlanarPoint K)
    (a b c i k j : ℕ) :
    planarDet (polygonChord q a b) (polygonChord q b c) *
        planarDet (polygonChord q i k) (polygonChord q i j) =
      polygonHDet q a b c * polygonHDet q i k j := by
  rw [polygonDet_partial_total, polygonHDet_eq_neg_turn,
    polygonHDet_eq_neg_turn]
  ring

/-- Consecutive external momenta telescope to their polygon chord. This is
an open-word identity; cyclic relabelling is not asserted here. -/
theorem polygonMomentum_sum (q : ℕ → PlanarPoint K) (a n : ℕ) :
    ∑ r ∈ Finset.range n, polygonMomentum q (a + r) =
      polygonChord q a (a + n) := by
  induction n with
  | zero => simp [polygonChord]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [polygonMomentum, polygonChord, Nat.add_succ]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring

/-- The two partial block sums in a far Cartesian determinant really are
the corresponding polygon chords. -/
theorem polygonMomentum_far_det (q : ℕ → PlanarPoint K) (a m n : ℕ) :
    planarDet (∑ r ∈ Finset.range m, polygonMomentum q (a + r))
        (∑ r ∈ Finset.range n, polygonMomentum q (a + m + r)) =
      -polygonHDet q a (a + m) (a + m + n) := by
  rw [polygonMomentum_sum, polygonMomentum_sum, polygonHDet_eq_neg_turn]
  simp only [neg_neg]

end Determinants

section OrderedSigns

variable [Field K] [LinearOrder K]

/-- The exact two-valued sign of a nonzero ordered-field scalar. -/
noncomputable def nonzeroScalarSign (x : K) (_hx : x ≠ 0) : Sign :=
  if x < 0 then .neg else .pos

theorem nonzeroScalarSign_value_pos_iff (x : K) (hx : x ≠ 0) :
    (nonzeroScalarSign x hx).value = 1 ↔ 0 < x := by
  by_cases hn : x < 0
  · norm_num [nonzeroScalarSign, hn, Sign.value, not_lt_of_gt hn]
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)
    simp [nonzeroScalarSign, hn, Sign.value, hp]

theorem nonzeroScalarSign_value_neg_iff (x : K) (hx : x ≠ 0) :
    (nonzeroScalarSign x hx).value = -1 ↔ x < 0 := by
  by_cases hn : x < 0 <;> norm_num [nonzeroScalarSign, hn, Sign.value]

/-- The positive-input indicator on ordered-field determinant expressions. -/
noncomputable def scalarPositiveStep (x : K) : ℚ := if 0 < x then 1 else 0

variable [IsStrictOrderedRing K]

/-- Taking signs of two nonzero ordered-field scalars preserves the step of their product. -/
theorem scalarPositiveStep_mul_sign (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    scalarPositiveStep (x * y) =
      positiveStep ((nonzeroScalarSign x hx).value * (nonzeroScalarSign y hy).value) := by
  by_cases hn : x < 0
  · by_cases hm : y < 0
    · have hp := mul_pos_of_neg_of_neg hn hm
      simp [scalarPositiveStep, hp, nonzeroScalarSign, hn, hm, Sign.value, positiveStep]
    · have hp : 0 < y := lt_of_le_of_ne (le_of_not_gt hm) (Ne.symm hy)
      have hn' := mul_neg_of_neg_of_pos hn hp
      norm_num [scalarPositiveStep, not_lt_of_gt hn', nonzeroScalarSign, hn, hm,
        Sign.value, positiveStep]
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)
    by_cases hm : y < 0
    · have hn' := mul_neg_of_pos_of_neg hp hm
      norm_num [scalarPositiveStep, not_lt_of_gt hn', nonzeroScalarSign, hn, hm,
        Sign.value, positiveStep]
    · have hq : 0 < y := lt_of_le_of_ne (le_of_not_gt hm) (Ne.symm hy)
      have hp' := mul_pos hp hq
      simp [scalarPositiveStep, hp', nonzeroScalarSign, hn, hm, Sign.value, positiveStep]

/-- Complementarity is used only away from zero. -/
theorem scalarPositiveStep_neg (x : K) (hx : x ≠ 0) :
    scalarPositiveStep (-x) = 1 - scalarPositiveStep x := by
  by_cases hp : 0 < x
  · simp [scalarPositiveStep, hp, not_lt_of_gt hp]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [scalarPositiveStep, hp, hn]

/-- Raw nonzero determinant inputs give the source's ordinary sign gate. -/
theorem ordinaryGate_scalar_heaviside (d h : K) (hd : d ≠ 0) (hh : h ≠ 0) :
    (nonzeroScalarSign d hd).value * scalarPositiveStep (-(h * d)) =
      ordinaryGate (nonzeroScalarSign d hd) (nonzeroScalarSign h hh) := by
  rw [scalarPositiveStep_neg _ (mul_ne_zero hh hd), scalarPositiveStep_mul_sign]
  cases hs : nonzeroScalarSign h hh <;> cases ds : nonzeroScalarSign d hd <;>
    norm_num [positiveStep, ordinaryGate, Sign.value]

/-- Raw nonzero determinant inputs give the source's marked sign gate. -/
theorem markedGate_scalar_heaviside (d h : K) (hd : d ≠ 0) (hh : h ≠ 0) :
    (nonzeroScalarSign d hd).value * scalarPositiveStep (h * d) =
      markedGate (nonzeroScalarSign d hd) (nonzeroScalarSign h hh) := by
  rw [scalarPositiveStep_mul_sign]
  exact markedGate_heaviside _ _

/-- The geometric sign in `ep:H`; the near specialization uses this same
definition with the three consecutive cuts of the current vertex. -/
noncomputable def polygonHSign (q : ℕ → PlanarPoint K) (i k j : ℕ)
    (h : polygonHDet q i k j ≠ 0) : Sign :=
  nonzeroScalarSign (polygonHDet q i k j) h

theorem polygon_ordinaryGate (q : ℕ → PlanarPoint K) (a b c i j : ℕ)
    (hd : polygonHDet q a b c ≠ 0) (hh : polygonHDet q i b j ≠ 0) :
    (polygonHSign q a b c hd).value *
        scalarPositiveStep (-(polygonHDet q i b j * polygonHDet q a b c)) =
      ordinaryGate (polygonHSign q a b c hd) (polygonHSign q i b j hh) := by
  exact ordinaryGate_scalar_heaviside _ _ hd hh

theorem polygon_markedGate (q : ℕ → PlanarPoint K) (a b c i j : ℕ)
    (hd : polygonHDet q a b c ≠ 0) (hh : polygonHDet q i b j ≠ 0) :
    (polygonHSign q a b c hd).value *
        scalarPositiveStep (polygonHDet q i b j * polygonHDet q a b c) =
      markedGate (polygonHSign q a b c hd) (polygonHSign q i b j hh) := by
  exact markedGate_scalar_heaviside _ _ hd hh

omit [IsStrictOrderedRing K] in
/-- At a binary ordinary vertex the near and far triangles coincide,
and the geometric ordinary gate vanishes. -/
theorem polygon_binary_ordinaryGate (q : ℕ → PlanarPoint K) (a b c : ℕ)
    (h : polygonHDet q a b c ≠ 0) :
    ordinaryGate (polygonHSign q a b c h) (polygonHSign q a b c h) = 0 := by
  simp [ordinaryGate]

end OrderedSigns

end DirectGLSSW
