import SM.CriticalSourceResponse
import Mathlib.Data.Sign.Basic

namespace SM

noncomputable section

/-- The far sign on three actual points, in the source's reversed order. -/
def pointFarSign (a r c : Plane) : SignType :=
  SignType.sign (det (r - c) (a - c))

/-- A nonzero scalar has an involutive sign, so rescaling a determinant
can be inverted at the level of signs even when that determinant is0. -/
theorem sign_rescale_nonzero (s a : ℝ) (hs : s ≠ 0) :
    SignType.sign a = SignType.sign s * SignType.sign (s * a) := by
  have hh : SignType.sign s * SignType.sign s = 1 :=
    mul_inv_cancel₀ (sign_ne_zero.mpr hs)
  rw [sign_mul, ← mul_assoc, hh, one_mul]

def wallLeftEpsilon (x y z : ℝ) : SignType := SignType.sign ((y - x) / (z - x))

def wallRightEpsilon (x y z : ℝ) : SignType := SignType.sign ((z - y) / (z - x))

/-- The printed distinct scalar coordinates make both epsilon ratios nonzero. -/
theorem wall_epsilons_nonzero (x y z : ℝ) (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    wallLeftEpsilon x y z ≠ 0 ∧ wallRightEpsilon x y z ≠ 0 := by
  exact ⟨sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hyx) (sub_ne_zero.mpr hzx)),
    sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx))⟩

theorem wall_epsilons_one_or_neg_one (x y z : ℝ)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    (wallLeftEpsilon x y z = 1 ∨ wallLeftEpsilon x y z = -1) ∧
      (wallRightEpsilon x y z = 1 ∨ wallRightEpsilon x y z = -1) := by
  have hn := wall_epsilons_nonzero x y z hyx hzy hzx
  constructor
  · rcases SignType.trichotomy (wallLeftEpsilon x y z) with h | h | h
    · exact Or.inr h
    · exact (hn.1 h).elim
    · exact Or.inl h
  · rcases SignType.trichotomy (wallRightEpsilon x y z) with h | h | h
    · exact Or.inr h
    · exact (hn.2 h).elim
    · exact Or.inl h

/-- The two actual ratios sum to1, so at least one epsilon is positive.
This does not assume where the middle labelled point lies on the line. -/
theorem wall_epsilon_positive (x y z : ℝ) (hzx : z ≠ x) :
    wallLeftEpsilon x y z = 1 ∨ wallRightEpsilon x y z = 1 := by
  have he : (y - x) / (z - x) + (z - y) / (z - x) = 1 := by
    rw [← add_div]
    have ha : y - x + (z - y) = z - x := by ring
    rw [ha, div_self (sub_ne_zero.mpr hzx)]
  by_cases hl : 0 < (y - x) / (z - x)
  · exact Or.inl (sign_eq_one_iff.mpr hl)
  · have hr : 0 < (z - y) / (z - x) := by linarith [le_of_not_gt hl]
    exact Or.inr (sign_eq_one_iff.mpr hr)

theorem affine_line_difference (p ω : Plane) (x y : ℝ) :
    (p + y • ω) - (p + x • ω) = (y - x) • ω := by
  ext <;> dsimp <;> ring

/-- The left-gap far-sign identity uses the actual common first endpoint. -/
theorem collinear_left_gate_sign (a b c r : Plane) (s : ℝ) (hs : s ≠ 0)
    (h : b - a = s • (c - a)) :
    pointFarSign a r c = SignType.sign s * pointFarSign a r b := by
  unfold pointFarSign
  rw [area_cyclic a c r, area_cyclic a b r, h]
  have hd : det (s • (c - a)) (r - a) = s * det (c - a) (r - a) := by
    dsimp [det]
    ring
  rw [hd]
  exact sign_rescale_nonzero s _ hs

/-- The right-gap far-sign identity uses the actual common last endpoint. -/
theorem collinear_right_gate_sign (a b c r : Plane) (s : ℝ) (hs : s ≠ 0)
    (h : b - c = s • (a - c)) :
    pointFarSign a r c = SignType.sign s * pointFarSign b r c := by
  unfold pointFarSign
  rw [h]
  have hd : det (r - c) (s • (a - c)) = s * det (r - c) (a - c) := by
    dsimp [det]
    ring
  rw [hd]
  exact sign_rescale_nonzero s _ hs

/-- Substitute the source's affine coordinates and its actual left ratio. -/
theorem affine_collinear_left_gate (p ω r : Plane) (x y z : ℝ)
    (hyx : y ≠ x) (hzx : z ≠ x) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      wallLeftEpsilon x y z * pointFarSign (p + x • ω) r (p + y • ω) := by
  apply collinear_left_gate_sign _ _ _ _ ((y - x) / (z - x))
    (div_ne_zero (sub_ne_zero.mpr hyx) (sub_ne_zero.mpr hzx))
  rw [affine_line_difference, affine_line_difference, smul_smul,
    div_mul_cancel₀ _ (sub_ne_zero.mpr hzx)]

/-- The right ratio has the printed orientation; both differences reverse
together when expressed using vectors based at the last endpoint. -/
theorem affine_collinear_right_gate (p ω r : Plane) (x y z : ℝ)
    (hzy : z ≠ y) (hzx : z ≠ x) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      wallRightEpsilon x y z * pointFarSign (p + y • ω) r (p + z • ω) := by
  apply collinear_right_gate_sign _ _ _ _ ((z - y) / (z - x))
    (div_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx))
  rw [affine_line_difference, affine_line_difference, smul_smul]
  have he : ((z - y) / (z - x)) * (x - z) = y - z := by
    field_simp [sub_ne_zero.mpr hzx]
    ring
  rw [he]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- The actual geometric far-array entry is the reversed-order point sign,
cast through the source integer sign into the allowed coefficient ring. -/
theorem geometricBoundaryArray_pointFarSign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := R) P g t =
      ((pointFarSign (boundaryWord P g t.lower) (boundaryWord P g t.middle)
        (boundaryWord P g t.upper) : ℤ) : R) := rfl

/-- The source left-gap identity at actual boundary positions and actual
geometric array entries. The intermediate vertex may be anywhere in the gap. -/
theorem boundary_collinear_left_sign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzx : z ≠ x) (r : Fin n)
    (hl : t.lower < r) (hr : r < t.middle) :
    geometricBoundaryArray (R := R) P g
        ⟨t.lower, r, t.upper, hl, lt_trans hr t.middle_upper⟩ =
      (((wallLeftEpsilon x y z : ℤ) : R)) *
        geometricBoundaryArray P g ⟨t.lower, r, t.middle, hl, hr⟩ := by
  have hs := affine_collinear_left_gate p ω (boundaryWord P g r) x y z hyx hzx
  rw [← hx, ← hy, ← hz] at hs
  have hc := congrArg (fun s : SignType => ((s : ℤ) : R)) hs
  simpa only [geometricBoundaryArray_pointFarSign, SignType.coe_mul, Int.cast_mul] using hc

/-- The source right-gap identity retains the original physical last
endpoint and the printed orientation of epsilon_R. -/
theorem boundary_collinear_right_sign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hzy : z ≠ y) (hzx : z ≠ x) (r : Fin n)
    (hl : t.middle < r) (hr : r < t.upper) :
    geometricBoundaryArray (R := R) P g
        ⟨t.lower, r, t.upper, lt_trans t.lower_middle hl, hr⟩ =
      (((wallRightEpsilon x y z : ℤ) : R)) *
        geometricBoundaryArray P g ⟨t.middle, r, t.upper, hl, hr⟩ := by
  have hs := affine_collinear_right_gate p ω (boundaryWord P g r) x y z hzy hzx
  rw [← hx, ← hy, ← hz] at hs
  have hc := congrArg (fun s : SignType => ((s : ℤ) : R)) hs
  simpa only [geometricBoundaryArray_pointFarSign, SignType.coe_mul, Int.cast_mul] using hc

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Every interior cut of the actual left gap samples a noncritical triple
at each pair of endpoints. Thus nearby-array agreement transfers the wall sign
identity to its complete composition gate, even though the nearby points need
not themselves be collinear. -/
theorem boundary_left_gap_gate (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzx : z ≠ x)
    (π : IntervalComposition t.leftInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) =
      -((((wallLeftEpsilon x y z : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R) := by
  have hl : t.lower < π.interiorPosition k := (π.farTriple k).lower_middle
  have hr : π.interiorPosition k < t.middle := (π.farTriple k).middle_upper
  have hu : π.interiorPosition k < t.upper := lt_trans hr t.middle_upper
  have hwhole : (⟨t.lower, π.interiorPosition k, t.upper, hl, hu⟩ : IncreasingBoundaryTriple n) ≠ t := by
    intro he
    have hm := congrArg IncreasingBoundaryTriple.middle he
    exact (ne_of_lt hr) hm
  have hgap : π.farTriple k ≠ t := by
    intro he
    have hu := congrArg IncreasingBoundaryTriple.upper he
    exact (ne_of_lt t.middle_upper) hu
  have hs : H ⟨t.lower, π.interiorPosition k, t.upper, hl, hu⟩ =
      (((wallLeftEpsilon x y z : ℤ) : R)) * H (π.farTriple k) := by
    rw [hH _ hwhole, hH _ hgap]
    exact boundary_collinear_left_sign P g t p ω x y z hx hy hz hyx hzx
      (π.interiorPosition k) hl hr
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨hl, hu⟩, hs]

/-- The right-gap transfer retains the actual last endpoint and the source's
right epsilon orientation. The local triple differs from the critical triple
already at its first endpoint. -/
theorem boundary_right_gap_gate (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hzy : z ≠ y) (hzx : z ≠ x)
    (π : IntervalComposition t.rightInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) =
      -((((wallRightEpsilon x y z : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R) := by
  have hl : t.middle < π.interiorPosition k := (π.farTriple k).lower_middle
  have hr : π.interiorPosition k < t.upper := (π.farTriple k).middle_upper
  have hd : t.lower < π.interiorPosition k := lt_trans t.lower_middle hl
  have hwhole : (⟨t.lower, π.interiorPosition k, t.upper, hd, hr⟩ : IncreasingBoundaryTriple n) ≠ t := by
    intro he
    have hm := congrArg IncreasingBoundaryTriple.middle he
    exact (ne_of_gt hl) hm
  have hgap : π.farTriple k ≠ t := by
    intro he
    have hd := congrArg IncreasingBoundaryTriple.lower he
    exact (ne_of_gt t.lower_middle) hd
  have hs : H ⟨t.lower, π.interiorPosition k, t.upper, hd, hr⟩ =
      (((wallRightEpsilon x y z : ℤ) : R)) * H (π.farTriple k) := by
    rw [hH _ hwhole, hH _ hgap]
    exact boundary_collinear_right_sign P g t p ω x y z hx hy hz hzy hzx
      (π.interiorPosition k) hl hr
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨hd, hr⟩, hs]

end
end SM

#print axioms SM.boundary_left_gap_gate
#print axioms SM.boundary_right_gap_gate
