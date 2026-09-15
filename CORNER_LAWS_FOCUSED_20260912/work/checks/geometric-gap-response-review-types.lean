import SM.CriticalSourceResponse
import SM.FiniteChiStability
import SM.GermNeighborhood
import Mathlib.Tactic
import Mathlib.Data.Sign.Basic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

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
variable {n : ℕ} [NeZero n]

namespace IncreasingBoundaryTriple

def positionSet (t : IncreasingBoundaryTriple n) : Finset (Fin n) :=
  {t.lower, t.middle, t.upper}

theorem positionSet_bounds (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ∈ t.positionSet) : t.lower ≤ x ∧ x ≤ t.upper := by
  simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨le_rfl, le_of_lt (lt_trans t.lower_middle t.middle_upper)⟩
  · exact ⟨le_of_lt t.lower_middle, le_of_lt t.middle_upper⟩
  · exact ⟨le_of_lt (lt_trans t.lower_middle t.middle_upper), le_rfl⟩

/-- The unordered position set determines the increasing triple. Min/max
fix both endpoints, and the distinct remaining position fixes the middle. -/
theorem positionSet_injective : Function.Injective (positionSet (n := n)) := by
  intro t u he
  have hl : t.lower = u.lower := by
    apply le_antisymm
    · exact (t.positionSet_bounds u.lower (by rw [he]; simp [positionSet])).1
    · exact (u.positionSet_bounds t.lower (by rw [← he]; simp [positionSet])).1
  have hr : t.upper = u.upper := by
    apply le_antisymm
    · exact (u.positionSet_bounds t.upper (by rw [← he]; simp [positionSet])).2
    · exact (t.positionSet_bounds u.upper (by rw [he]; simp [positionSet])).2
  have hm : t.middle = u.middle := by
    have hx : t.middle ∈ u.positionSet := by rw [← he]; simp [positionSet]
    simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ((ne_of_gt t.lower_middle) (h.trans hl.symm)).elim
    · exact h
    · exact ((ne_of_lt t.middle_upper) (h.trans hr.symm)).elim
  exact eq_of_entries hl hm hr

/-- The actual unordered source vertex support in the chosen root reading. -/
def vertexSet (g : ZMod n) (t : IncreasingBoundaryTriple n) : Finset (ZMod n) :=
  t.positionSet.image (boundaryIndex g)

theorem vertexSet_injective (g : ZMod n) : Function.Injective (vertexSet g) := by
  intro t u he
  apply positionSet_injective
  exact Finset.image_injective (boundaryIndex_injective g) he

theorem vertexSet_reversed (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    t.vertexSet g = {boundaryIndex g t.upper, boundaryIndex g t.middle, boundaryIndex g t.lower} := by
  ext x
  simp [vertexSet, positionSet, or_comm, or_left_comm, or_assoc]

end IncreasingBoundaryTriple

/-- Unique zero support implies every other increasing boundary triple has
a nonzero determinant sign. This uses label injectivity of the root reading,
without inferring geometric vertex distinctness from singleton Zpt at n=3. -/
theorem boundary_chi_nonzero_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g})
    (u : IncreasingBoundaryTriple n) (hu : u ≠ t) :
    chi P (boundaryIndex g u.upper) (boundaryIndex g u.middle) (boundaryIndex g u.lower) ≠ 0 := by
  apply chi_nonzero_outside_singleton hP
  · exact fun h => (ne_of_gt u.middle_upper) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt u.lower_middle) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt (lt_trans u.lower_middle u.middle_upper)) (boundaryIndex_injective g h)
  · intro he
    have hs : u.vertexSet g = t.vertexSet g := (u.vertexSet_reversed g).trans he
    exact hu (IncreasingBoundaryTriple.vertexSet_injective g hs)

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The full reversed-far output on J depends only on the far array inside
J. All coefficient factors and every actual child inverse value are compared
in the complete composition sum, including the unary case. -/
theorem farOnlyOutput_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u : IncreasingBoundaryTriple n, J.left ≤ u.lower → u.upper ≤ J.right → H₁ u = H₂ u) :
    farOnlyOutput H₁ J = farOnlyOutput H₂ J := by
  unfold farOnlyOutput farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  have hw : π.nearFarWeight 0 (-H₁) = π.nearFarWeight 0 (-H₂) := by
    unfold IntervalComposition.nearFarWeight
    apply Finset.prod_congr rfl
    intro k _
    simp only [Pi.zero_apply, Pi.neg_apply]
    rw [h (π.farTriple k) le_rfl le_rfl]
  rw [hw]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  apply farOnlyCoordinates_local (π.part k) H₁ H₂
  intro u hl hr
  exact h u (le_trans (π.part_bounds k).1 hl) (le_trans hr (π.part_bounds k).2)

/-- Changing a single far entry leaves every full output coordinate whose
interval excludes the complete critical span unchanged. -/
theorem farOnlyOutput_unchanged_off_critical (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    farOnlyOutput H₁ J = farOnlyOutput H₂ J := by
  apply farOnlyOutput_local J H₁ H₂
  intro u hl hr
  apply h u
  intro he
  subst u
  exact hJ ⟨hl, hr⟩

end
end SM

namespace SM

open Filter Topology

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- A single neighborhood preserves every noncritical geometric far entry
simultaneously. The proof uses actual finite chirotope stability and the exact
unordered-support/increasing-triple correspondence. -/
theorem geometric_array_persists_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g}) :
    ∀ᶠ Q in 𝓝 P, ∀ u : IncreasingBoundaryTriple n, u ≠ t →
      geometricBoundaryArray (R := R) Q g u = geometricBoundaryArray P g u := by
  filter_upwards [finite_nonzero_chi_persists (P := P)] with Q hQ
  intro u hu
  exact congrArg (fun s : SignType => ((s : ℤ) : R))
    (hQ (boundaryIndex g u.upper) (boundaryIndex g u.middle) (boundaryIndex g u.lower)
      (boundary_chi_nonzero_off_critical P g t hP u hu))

/-- All inverse coordinates outside the critical span retain their wall
values on one common neighborhood, not separate radii for separate intervals. -/
theorem geometric_inverse_persists_off_span (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g}) :
    ∀ᶠ Q in 𝓝 P, ∀ J : BoundaryInterval n,
      ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
      farOnlyCoordinates (geometricBoundaryArray (R := R) Q g) J =
        farOnlyCoordinates (geometricBoundaryArray P g) J := by
  filter_upwards [geometric_array_persists_off_critical (R := R) P g t hP] with Q hQ
  intro J hJ
  exact farOnlyCoordinates_unchanged_off_critical _ _ t hQ J hJ

/-- The complete B outputs on all excluded intervals also retain their
wall values on a common neighborhood, with one-leaf outputs included. -/
theorem geometric_output_persists_off_span (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g}) :
    ∀ᶠ Q in 𝓝 P, ∀ J : BoundaryInterval n,
      ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
      farOnlyOutput (geometricBoundaryArray (R := R) Q g) J =
        farOnlyOutput (geometricBoundaryArray P g) J := by
  filter_upwards [geometric_array_persists_off_critical (R := R) P g t hP] with Q hQ
  intro J hJ
  exact farOnlyOutput_unchanged_off_critical _ _ t hQ J hJ

end
end SM

namespace SM.WallGerm

open Filter Topology

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- One positive radius preserves all noncritical geometric far entries and
all inverse/output coordinates outside the critical span, on both sides of the
actual continuous germ. The center is included in this local assertion. -/
theorem boundary_values_stable_near_center (w : WallGerm n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g}) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧ ∀ s : w.Parameter, |s.val| < δ →
      (∀ u : IncreasingBoundaryTriple n, u ≠ t →
        geometricBoundaryArray (R := R) (w.curve s) g u =
          geometricBoundaryArray w.center g u) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyCoordinates (geometricBoundaryArray (R := R) (w.curve s) g) J =
          farOnlyCoordinates (geometricBoundaryArray w.center g) J) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyOutput (geometricBoundaryArray (R := R) (w.curve s) g) J =
          farOnlyOutput (geometricBoundaryArray w.center g) J) := by
  apply (w.eventually_center_iff_radius _).mp
  have h : ContinuousAt w.curve w.zeroParameter := w.continuous_curve.continuousAt
  filter_upwards [h.eventually (geometric_array_persists_off_critical (R := R) w.center g t hZ),
    h.eventually (geometric_inverse_persists_off_span (R := R) w.center g t hZ),
    h.eventually (geometric_output_persists_off_span (R := R) w.center g t hZ)] with s hA hC hB
  exact ⟨hA, hC, hB⟩

end
end SM.WallGerm

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The source U switches between the exact unit array E and full B output.
Its consumers require the actual wall epsilon to be either1 or-1. -/
def wallGapU (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then boundaryUnitArray I else farOnlyOutput H I

/-- The source V interchanges the same two complete interval values. -/
def wallGapV (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then farOnlyOutput H I else boundaryUnitArray I

/-- Every raw composition is retained. The actual signed far gates identify
the complete weighted sum with source U through the proved inverse equation. -/
theorem cutWeightedSum_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum f (farOnlyCoordinates H) I = wallGapU H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapU, if_pos rfl]
    calc
      cutWeightedSum f (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using h π k
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I
  · rw [wallGapU, if_neg (by decide)]
    change cutWeightedSum f (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using h π k

/-- Reversing every far gate interchanges E and B, including the unary gap
whose empty gate product remains1. -/
theorem cutWeightedSum_neg_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum (-f) (farOnlyCoordinates H) I = wallGapV H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapV, if_pos rfl]
    change cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using congrArg Neg.neg (h π k)
  · rw [wallGapV, if_neg (by decide)]
    calc
      cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using congrArg Neg.neg (h π k)
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I

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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Geometric wall signs identify both complete gap sums and their reversed
counterparts with the source U/V values. Agreement is required only away from
the critical triple; the nearby array need not have a zero critical gate. -/
theorem geometric_gap_sums (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.leftInterval =
      wallGapU H t.leftInterval (wallLeftEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.rightInterval =
      wallGapU H t.rightInterval (wallRightEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate (-H)) (farOnlyCoordinates H) t.leftInterval =
      wallGapV H t.leftInterval (wallLeftEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate (-H)) (farOnlyCoordinates H) t.rightInterval =
      wallGapV H t.rightInterval (wallRightEpsilon x y z)) := by
  have hε := wall_epsilons_one_or_neg_one x y z hyx hzy hzx
  have hL := boundary_left_gap_gate P g t H hH p ω x y z hx hy hz hyx hzx
  have hR := boundary_right_gap_gate P g t H hH p ω x y z hx hy hz hzy hzx
  have hn : t.fixedFarGate (-H) = -t.fixedFarGate H :=
    funext (t.fixedFarGate_neg H)
  refine ⟨cutWeightedSum_signed_inverse _ H _ _ hε.1 hL,
    cutWeightedSum_signed_inverse _ H _ _ hε.2 hR, ?_, ?_⟩
  · rw [hn]
    exact cutWeightedSum_neg_signed_inverse _ H _ _ hε.1 hL
  · rw [hn]
    exact cutWeightedSum_neg_signed_inverse _ H _ _ hε.2 hR

/-- The derived critical inverse jump now uses the actual geometric U gap
values. This is a critical-span formula, not a propagation assumption. -/
theorem geometric_critical_inverse_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z)) := by
  have hs := geometric_gap_sums P g t H₁ h₁ p ω x y z hx hy hz hyx hzy hzx
  rw [critical_inverse_source_jump H₁ H₂ t (fun u hu => (h₁ u hu).trans (h₂ u hu).symm),
    hs.1, hs.2.1]

/-- Both ordinary and reversed geometric gap contributions occur in the
complete critical output response. No contracted output is used or presumed. -/
theorem geometric_critical_output_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        ((wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z)) +
         (wallGapV H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapV H₁ t.rightInterval (wallRightEpsilon x y z))) := by
  have hs := geometric_gap_sums P g t H₁ h₁ p ω x y z hx hy hz hyx hzy hzx
  rw [critical_output_source_jump H₁ H₂ t (fun u hu => (h₁ u hu).trans (h₂ u hu).symm),
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual rooted tree coefficients satisfy the full-span response on
both sufficiently close punctured sides of the genuine continuous germ. All
four gap values are evaluated at the wall center. This establishes the displayed
full-span identity; the proper-span contraction branch is separate. -/
theorem full_span_tree_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hspan : t.spanInterval = fullBoundaryInterval hn)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
          (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
          ((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
            geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R)) *
            ((wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
             (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) := by
  obtain ⟨δ, hδ, hrad, hs⟩ := w.boundary_values_stable_near_center (R := R) g t hZ
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hsMinus := hs sMinus hnearMinus
  have hsPlus := hs sPlus hnearPlus
  have hleft : ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  have hright : ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl
  have hL := hsMinus.2.2 t.leftInterval hleft
  have hR := hsMinus.2.2 t.rightInterval hright
  have hc := geometric_critical_output_response w.center g t
    (geometricBoundaryArray (R := R) (w.curve sMinus) g)
    (geometricBoundaryArray (w.curve sPlus) g) hsMinus.1 hsPlus.1
    p ω x y z hx hy hz hyx hzy hzx
  rw [hspan] at hc
  rw [treeCoefficient_farOnly (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn,
    treeCoefficient_farOnly (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn]
  simpa only [wallGapU, wallGapV, hL, hR] using hc

end
end SM.WallGerm

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The label map for the already defined closed contiguous word, with
residue zero still labeling its actual last vertex. -/
def restrictedVertexIndex (g : ZMod n) (J : BoundaryInterval n)
    (j : ZMod (J.leaves + 1)) : ZMod n :=
  boundaryIndex g (J.globalPosition ⟨(j - 1).val, ZMod.val_lt _⟩)

theorem restrictedVertexIndex_injective (g : ZMod n) (J : BoundaryInterval n) :
    Function.Injective (restrictedVertexIndex g J) := by
  intro i j he
  have hp := J.globalPosition_strict.injective (boundaryIndex_injective g he)
  have hv := congrArg Fin.val hp
  have hz : i - 1 = j - 1 := ZMod.val_injective (J.leaves + 1) hv
  simpa only [sub_add_cancel] using congrArg (fun v : ZMod (J.leaves + 1) => v + 1) hz

/-- A closed contiguous word excluding the complete critical span has no
zero distinct-label triple. This proves its actual G1 condition directly from
the singleton zero-support hypothesis, without assuming global G1 at the wall. -/
theorem restrictedWord_G1_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    G1 (restrictedWordTuple P g J) := by
  intro i j k hij hjk hik
  change chi P (restrictedVertexIndex g J i) (restrictedVertexIndex g J j)
    (restrictedVertexIndex g J k) ≠ 0
  apply chi_nonzero_outside_singleton hZ
  · exact fun he => hij (restrictedVertexIndex_injective g J he)
  · exact fun he => hjk (restrictedVertexIndex_injective g J he)
  · exact fun he => hik (restrictedVertexIndex_injective g J he)
  · intro he
    have hb (a : Fin n) (v : ZMod (J.leaves + 1))
        (h : boundaryIndex g a = restrictedVertexIndex g J v) :
        J.left ≤ a ∧ a ≤ J.right := by
      have hp : a = J.globalPosition ⟨(v - 1).val, ZMod.val_lt _⟩ :=
        boundaryIndex_injective g h
      rw [hp]
      exact J.globalPosition_bounds _
    have hs (a : Fin n)
        (ha : boundaryIndex g a ∈ ({restrictedVertexIndex g J i,
          restrictedVertexIndex g J j, restrictedVertexIndex g J k} : Finset (ZMod n))) :
        J.left ≤ a ∧ a ≤ J.right := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with hi | hj | hk
      · exact hb a i hi
      · exact hb a j hj
      · exact hb a k hk
    have hl := hs t.lower (by
      rw [he]
      simp [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet])
    have hu := hs t.upper (by
      rw [he]
      simp [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet])
    exact hJ ⟨hl.1, hu.2⟩

/-- Both nonleaf closed gap polygons satisfy G1. The explicit leaf-count
premises retain the source distinction between polygon amplitudes and the
formal one-leaf convention. -/
theorem critical_closed_gaps_G1 (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g}) :
    (2 ≤ t.leftInterval.leaves → G1 (restrictedWordTuple P g t.leftInterval)) ∧
      (2 ≤ t.rightInterval.leaves → G1 (restrictedWordTuple P g t.rightInterval)) := by
  constructor
  · intro _
    apply restrictedWord_G1_off_critical P g t hZ
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  · intro _
    apply restrictedWord_G1_off_critical P g t hZ
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl

end
end SM

namespace BoundaryGateStabilityIndependentReview
open SM Filter Topology
noncomputable section
variable {n : ℕ} [NeZero n]

theorem support_has_three_positions (t : IncreasingBoundaryTriple n) : t.positionSet.card = 3 := by
  apply Finset.card_triple_eq_three_iff.mpr
  exact ⟨ne_of_lt t.lower_middle, ne_of_lt (lt_trans t.lower_middle t.middle_upper),
    ne_of_lt t.middle_upper⟩

theorem support_has_three_labels (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    (t.vertexSet g).card = 3 := by
  rw [IncreasingBoundaryTriple.vertexSet, Finset.card_image_of_injective _ (boundaryIndex_injective g)]
  exact support_has_three_positions t

theorem support_equality_exactly_ordered_equality (g : ZMod n) (t u : IncreasingBoundaryTriple n) :
    t.vertexSet g = u.vertexSet g ↔ t = u :=
  ⟨fun h => IncreasingBoundaryTriple.vertexSet_injective g h, fun h => h ▸ rfl⟩

theorem actual_noncritical_point_sign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hp : pointZeroTriples P = {t.vertexSet g})
    (u : IncreasingBoundaryTriple n) (hu : u ≠ t) :
    pointFarSign (boundaryWord P g u.lower) (boundaryWord P g u.middle)
      (boundaryWord P g u.upper) ≠ 0 :=
  boundary_chi_nonzero_off_critical P g t hp u hu

theorem actual_critical_point_sign_is_zero (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hp : pointZeroTriples P = {t.vertexSet g}) :
    pointFarSign (boundaryWord P g t.lower) (boundaryWord P g t.middle)
      (boundaryWord P g t.upper) = 0 := by
  have hm : t.vertexSet g ∈ pointZeroTriples P := by rw [hp]; simp
  have hz := ((mem_pointZeroTriples P _).mp hm).2
  apply hz
  all_goals simp [IncreasingBoundaryTriple.vertexSet_reversed]

theorem epsilon_middle_between : wallLeftEpsilon 0 1 2 = 1 ∧ wallRightEpsilon 0 1 2 = 1 := by
  constructor <;> apply sign_eq_one_iff.mpr <;> norm_num

theorem epsilon_middle_before : wallLeftEpsilon 0 (-1) 2 = -1 ∧ wallRightEpsilon 0 (-1) 2 = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr; norm_num
  · apply sign_eq_one_iff.mpr; norm_num

theorem epsilon_middle_after : wallLeftEpsilon 0 3 2 = 1 ∧ wallRightEpsilon 0 3 2 = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr; norm_num
  · apply sign_eq_neg_one_iff.mpr; norm_num

theorem both_negative_epsilons_impossible (x y z : ℝ) (hzx : z ≠ x) :
    ¬ (wallLeftEpsilon x y z = -1 ∧ wallRightEpsilon x y z = -1) := by
  rintro ⟨hl, hr⟩
  rcases wall_epsilon_positive x y z hzx with h | h
  · rw [hl] at h; exact (by decide : (-1 : SignType) ≠ 1) h
  · rw [hr] at h; exact (by decide : (-1 : SignType) ≠ 1) h

theorem scalar_rescaling_allows_zero_gate (s : ℝ) (hs : s ≠ 0) :
    (0 : SignType) = SignType.sign s * SignType.sign (s * (0 : ℝ)) := by
  simpa using sign_rescale_nonzero s 0 hs

theorem actual_left_negative_ratio (p ω r : Plane) :
    pointFarSign (p + (0 : ℝ) • ω) r (p + (2 : ℝ) • ω) =
      -pointFarSign (p + (0 : ℝ) • ω) r (p + (-1 : ℝ) • ω) := by
  have h := affine_collinear_left_gate p ω r 0 (-1) 2 (by norm_num) (by norm_num)
  rw [epsilon_middle_before.1] at h
  simpa only [neg_one_mul] using h

theorem actual_right_negative_ratio (p ω r : Plane) :
    pointFarSign (p + (0 : ℝ) • ω) r (p + (2 : ℝ) • ω) =
      -pointFarSign (p + (3 : ℝ) • ω) r (p + (2 : ℝ) • ω) := by
  have h := affine_collinear_right_gate p ω r 0 3 2 (by norm_num) (by norm_num)
  rw [epsilon_middle_after.2] at h
  simpa only [neg_one_mul] using h

theorem n3_has_only_one_increasing_triple (t u : IncreasingBoundaryTriple 3) : t = u := by
  have ht₁ := t.lower_middle
  have ht₂ := t.middle_upper
  have hu₁ := u.lower_middle
  have hu₂ := u.middle_upper
  apply IncreasingBoundaryTriple.eq_of_entries <;> apply Fin.ext
  all_goals
    change t.lower.val < t.middle.val at ht₁
    change t.middle.val < t.upper.val at ht₂
    change u.lower.val < u.middle.val at hu₁
    change u.middle.val < u.upper.val at hu₂
    have ht := t.upper.isLt
    have hu := u.upper.isLt
    omega

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem complete_left_gap_output_unchanged (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyOutput H₁ t.leftInterval = farOnlyOutput H₂ t.leftInterval := by
  apply farOnlyOutput_unchanged_off_critical H₁ H₂ t h
  intro hc
  exact (not_le_of_gt t.middle_upper) hc.2

theorem complete_right_gap_output_unchanged (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyOutput H₁ t.rightInterval = farOnlyOutput H₂ t.rightInterval := by
  apply farOnlyOutput_unchanged_off_critical H₁ H₂ t h
  intro hc
  exact (not_le_of_gt t.lower_middle) hc.1

theorem leaf_output_needs_no_array_agreement (H₁ H₂ : TripleArray n R)
    (J : BoundaryInterval n) (hj : J.leaves = 1) : farOnlyOutput H₁ J = farOnlyOutput H₂ J :=
  (farOnly_leaf_values H₁ J hj).2.trans (farOnly_leaf_values H₂ J hj).2.symm

theorem arbitrary_critical_update_preserves_output (H : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (v : R) (J : BoundaryInterval n)
    (hj : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    farOnlyOutput (Function.update H t v) J = farOnlyOutput H J := by
  apply farOnlyOutput_unchanged_off_critical _ _ t _ J hj
  intro u hu
  exact Function.update_of_ne hu v H

theorem one_neighborhood_all_arrays_and_coordinates (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hp : pointZeroTriples P = {t.vertexSet g}) :
    ∀ᶠ Q in 𝓝 P,
      (∀ u : IncreasingBoundaryTriple n, u ≠ t → geometricBoundaryArray (R := R) Q g u = geometricBoundaryArray P g u) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyCoordinates (geometricBoundaryArray (R := R) Q g) J = farOnlyCoordinates (geometricBoundaryArray P g) J ∧
        farOnlyOutput (geometricBoundaryArray (R := R) Q g) J = farOnlyOutput (geometricBoundaryArray P g) J) := by
  filter_upwards [geometric_array_persists_off_critical (R := R) P g t hp,
    geometric_inverse_persists_off_span (R := R) P g t hp,
    geometric_output_persists_off_span (R := R) P g t hp] with Q hq hc hb
  exact ⟨hq, fun J hj => ⟨hc J hj, hb J hj⟩⟩

theorem two_tuples_in_same_neighborhood_have_same_outputs (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hp : pointZeroTriples P = {t.vertexSet g}) :
    ∃ S ∈ 𝓝 P, ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, ∀ J : BoundaryInterval n,
      ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
      farOnlyOutput (geometricBoundaryArray (R := R) Q₁ g) J =
        farOnlyOutput (geometricBoundaryArray Q₂ g) J := by
  let S := {Q : LabelledTuple n | ∀ J : BoundaryInterval n,
    ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
    farOnlyOutput (geometricBoundaryArray (R := R) Q g) J =
      farOnlyOutput (geometricBoundaryArray P g) J}
  have hs : S ∈ 𝓝 P := geometric_output_persists_off_span (R := R) P g t hp
  exact ⟨S, hs, fun Q₁ h₁ Q₂ h₂ J hj => (h₁ J hj).trans (h₂ J hj).symm⟩

end
end BoundaryGateStabilityIndependentReview

namespace GeometricGapResponseIndependentReview
open SM Filter Topology
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem gap_values_have_exact_four_cases (H : TripleArray n R) (I : BoundaryInterval n) :
    wallGapU H I 1 = boundaryUnitArray I ∧ wallGapV H I 1 = farOnlyOutput H I ∧
    wallGapU H I (-1) = farOnlyOutput H I ∧ wallGapV H I (-1) = boundaryUnitArray I := by
  simp [wallGapU, wallGapV]

theorem leaf_gap_values_are_both_one (H : TripleArray n R) (I : BoundaryInterval n)
    (hI : I.leaves = 1) (ε : SignType) : wallGapU H I ε = 1 ∧ wallGapV H I ε = 1 := by
  simp [wallGapU, wallGapV, boundaryUnitArray_leaf I hI, (farOnly_leaf_values H I hI).2]

theorem reversing_nonzero_epsilon_exchanges_gap_values (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1) :
    wallGapU H I (-ε) = wallGapV H I ε ∧ wallGapV H I (-ε) = wallGapU H I ε := by
  rcases hε with rfl | rfl <;> simp [wallGapU, wallGapV]

theorem nonleaf_positive_U_and_negative_V_vanish (H : TripleArray n R)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    wallGapU H I 1 = 0 ∧ wallGapV H I (-1) = 0 := by
  have he : boundaryUnitArray (R := R) I = 0 := by
    rw [← farOnlyCoordinates_equation H]
    exact farOnly_nonleaf_E H I hI
  simp [wallGapU, wallGapV, he]

theorem critical_entry_changes_no_excluded_gap_value (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval n) (hj : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    wallGapU H₁ J ε = wallGapU H₂ J ε ∧ wallGapV H₁ J ε = wallGapV H₂ J ε := by
  have hb := farOnlyOutput_unchanged_off_critical H₁ H₂ t h J hj
  simp only [wallGapU, wallGapV, hb, and_self]

theorem restricted_labels_read_the_actual_original_tuple (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) (j : ZMod (J.leaves + 1)) :
    restrictedWordTuple P g J j = P (restrictedVertexIndex g J j) := rfl

theorem restricted_label_equality_is_exact (g : ZMod n) (J : BoundaryInterval n)
    (i j : ZMod (J.leaves + 1)) :
    restrictedVertexIndex g J i = restrictedVertexIndex g J j ↔ i = j :=
  ⟨fun h => restrictedVertexIndex_injective g J h, fun h => h ▸ rfl⟩

theorem off_span_word_has_G1_and_physical_closing_edge (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hz : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hj : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    G1 (restrictedWordTuple P g J) ∧
      edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right :=
  ⟨restrictedWord_G1_off_critical P g t hz J hj, restrictedWord_closing_edge P g J⟩

theorem off_span_nonleaf_output_is_actual_closed_tree (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hz : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hj : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (hleaf : 2 ≤ J.leaves) :
    farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
      (treeCoefficient (restrictedWordTuple P g J)
        (restrictedWord_G1_off_critical P g t hz J hj) 0 (by omega : 3 ≤ J.leaves + 1) : R) :=
  farOnlyOutput_restricted_tree P g J hleaf (restrictedWord_G1_off_critical P g t hz J hj)

theorem common_radius_covers_both_actual_side_maps (w : WallGerm n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hz : pointZeroTriples w.center = {t.vertexSet g}) :
    ∃ d : ℝ, 0 < d ∧ d ≤ w.radius ∧ ∀ s : w.SideParameter, s.val < d → ∀ positive : Bool,
      (∀ u : IncreasingBoundaryTriple n, u ≠ t →
        geometricBoundaryArray (R := R) (w.sideTuple positive s).val g u =
          geometricBoundaryArray w.center g u) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyCoordinates (geometricBoundaryArray (R := R) (w.sideTuple positive s).val g) J =
          farOnlyCoordinates (geometricBoundaryArray w.center g) J ∧
        farOnlyOutput (geometricBoundaryArray (R := R) (w.sideTuple positive s).val g) J =
          farOnlyOutput (geometricBoundaryArray w.center g) J) := by
  obtain ⟨d, hd, hr, hs⟩ := w.boundary_values_stable_near_center (R := R) g t hz
  refine ⟨d, hd, hr, ?_⟩
  intro s hsd positive
  have ha : |(w.sideTime positive s).val| < d := by
    cases positive <;> simpa [WallGerm.sideTime, abs_of_pos s.property.1] using hsd
  have h := hs (w.sideTime positive s) ha
  exact ⟨h.1, fun J hj => ⟨h.2.1 J hj, h.2.2 J hj⟩⟩

theorem arbitrary_critical_value_retains_geometric_gap_sum (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (v : R) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    cutWeightedSum (t.fixedFarGate (Function.update (geometricBoundaryArray P g) t v))
      (farOnlyCoordinates (Function.update (geometricBoundaryArray P g) t v)) t.leftInterval =
      wallGapU (geometricBoundaryArray P g) t.leftInterval (wallLeftEpsilon x y z) := by
  let H : TripleArray n R := Function.update (geometricBoundaryArray P g) t v
  have hh : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u := by
    intro u hu
    exact Function.update_of_ne hu v (geometricBoundaryArray P g)
  have hs := (geometric_gap_sums P g t H hh p ω x y z hx hy hz hyx hzy hzx).1
  have hj : ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
    intro h; exact (not_le_of_gt t.middle_upper) h.2
  exact hs.trans (critical_entry_changes_no_excluded_gap_value H _ t hh _ hj _).1

theorem full_tree_response_at_equal_positive_side_distances (w : WallGerm n) (g : ZMod n)
    (hn : 3 ≤ n) (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hspan : t.spanInterval = fullBoundaryInterval hn) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ d : ℝ, 0 < d ∧ d ≤ w.radius ∧ ∀ s : w.SideParameter, s.val < d →
      (treeCoefficient (w.sideTuple true s).val (w.sideTuple true s).property.1 g hn : R) -
        (treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn : R) =
        ((geometricBoundaryArray (R := R) (w.sideTuple true s).val g t -
          geometricBoundaryArray (w.sideTuple false s).val g t) * ⅟ (2 : R)) *
          ((wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
            wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
           (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
            wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) := by
  obtain ⟨d, hd, hr, h⟩ := w.full_span_tree_response (R := R) g hn t hZ hspan p ω x y z hx hy hz hyx hzy hzx
  refine ⟨d, hd, hr, ?_⟩
  intro s hs
  have hm : (w.sideTime false s).val < 0 := by
    change -s.val < 0
    linarith [s.property.1]
  have hp : 0 < (w.sideTime true s).val := by simpa [WallGerm.sideTime] using s.property.1
  have ham : |(w.sideTime false s).val| < d := by
    simpa [WallGerm.sideTime, abs_of_pos s.property.1] using hs
  have hap : |(w.sideTime true s).val| < d := by
    simpa [WallGerm.sideTime, abs_of_pos s.property.1] using hs
  exact h (w.sideTime false s) (w.sideTime true s) hm hp ham hap

end
end GeometricGapResponseIndependentReview

#check SM.pointFarSign
#print axioms SM.pointFarSign
#check SM.sign_rescale_nonzero
#print axioms SM.sign_rescale_nonzero
#check SM.wallLeftEpsilon
#print axioms SM.wallLeftEpsilon
#check SM.wallRightEpsilon
#print axioms SM.wallRightEpsilon
#check SM.wall_epsilons_nonzero
#print axioms SM.wall_epsilons_nonzero
#check SM.wall_epsilons_one_or_neg_one
#print axioms SM.wall_epsilons_one_or_neg_one
#check SM.wall_epsilon_positive
#print axioms SM.wall_epsilon_positive
#check SM.affine_line_difference
#print axioms SM.affine_line_difference
#check SM.collinear_left_gate_sign
#print axioms SM.collinear_left_gate_sign
#check SM.collinear_right_gate_sign
#print axioms SM.collinear_right_gate_sign
#check SM.affine_collinear_left_gate
#print axioms SM.affine_collinear_left_gate
#check SM.affine_collinear_right_gate
#print axioms SM.affine_collinear_right_gate
#check SM.geometricBoundaryArray_pointFarSign
#print axioms SM.geometricBoundaryArray_pointFarSign
#check SM.boundary_collinear_left_sign
#print axioms SM.boundary_collinear_left_sign
#check SM.boundary_collinear_right_sign
#print axioms SM.boundary_collinear_right_sign
#check SM.IncreasingBoundaryTriple.positionSet
#print axioms SM.IncreasingBoundaryTriple.positionSet
#check SM.IncreasingBoundaryTriple.positionSet_bounds
#print axioms SM.IncreasingBoundaryTriple.positionSet_bounds
#check SM.IncreasingBoundaryTriple.positionSet_injective
#print axioms SM.IncreasingBoundaryTriple.positionSet_injective
#check SM.IncreasingBoundaryTriple.vertexSet
#print axioms SM.IncreasingBoundaryTriple.vertexSet
#check SM.IncreasingBoundaryTriple.vertexSet_injective
#print axioms SM.IncreasingBoundaryTriple.vertexSet_injective
#check SM.IncreasingBoundaryTriple.vertexSet_reversed
#print axioms SM.IncreasingBoundaryTriple.vertexSet_reversed
#check SM.boundary_chi_nonzero_off_critical
#print axioms SM.boundary_chi_nonzero_off_critical
#check SM.farOnlyOutput_local
#print axioms SM.farOnlyOutput_local
#check SM.farOnlyOutput_unchanged_off_critical
#print axioms SM.farOnlyOutput_unchanged_off_critical
#check SM.geometric_array_persists_off_critical
#print axioms SM.geometric_array_persists_off_critical
#check SM.geometric_inverse_persists_off_span
#print axioms SM.geometric_inverse_persists_off_span
#check SM.geometric_output_persists_off_span
#print axioms SM.geometric_output_persists_off_span
#check SM.WallGerm.boundary_values_stable_near_center
#print axioms SM.WallGerm.boundary_values_stable_near_center
#check SM.wallGapU
#print axioms SM.wallGapU
#check SM.wallGapV
#print axioms SM.wallGapV
#check SM.cutWeightedSum_signed_inverse
#print axioms SM.cutWeightedSum_signed_inverse
#check SM.cutWeightedSum_neg_signed_inverse
#print axioms SM.cutWeightedSum_neg_signed_inverse
#check SM.boundary_left_gap_gate
#print axioms SM.boundary_left_gap_gate
#check SM.boundary_right_gap_gate
#print axioms SM.boundary_right_gap_gate
#check SM.geometric_gap_sums
#print axioms SM.geometric_gap_sums
#check SM.geometric_critical_inverse_response
#print axioms SM.geometric_critical_inverse_response
#check SM.geometric_critical_output_response
#print axioms SM.geometric_critical_output_response
#check SM.WallGerm.full_span_tree_response
#print axioms SM.WallGerm.full_span_tree_response
#check SM.restrictedVertexIndex
#print axioms SM.restrictedVertexIndex
#check SM.restrictedVertexIndex_injective
#print axioms SM.restrictedVertexIndex_injective
#check SM.restrictedWord_G1_off_critical
#print axioms SM.restrictedWord_G1_off_critical
#check SM.critical_closed_gaps_G1
#print axioms SM.critical_closed_gaps_G1
#print SM.pointFarSign
#print SM.wallLeftEpsilon
#print SM.wallRightEpsilon
#print SM.IncreasingBoundaryTriple
#print SM.IncreasingBoundaryTriple.positionSet
#print SM.IncreasingBoundaryTriple.vertexSet
#print SM.boundaryIndex
#print SM.boundaryWord
#print SM.geometricBoundaryArray
#print SM.PointZeroTriple
#print SM.pointZeroTriples
#print SM.chi
#print SM.farOnlyCoordinates
#print SM.farOnlyOutput
#print SM.farTransform
#print SM.nearFarTransform
#print SM.IntervalComposition.nearFarWeight
#print SM.BoundaryInterval
#print SM.IncreasingBoundaryTriple.leftInterval
#print SM.IncreasingBoundaryTriple.rightInterval
#print SM.wallGapU
#print SM.wallGapV
#print SM.cutWeightedSum
#print SM.IncreasingBoundaryTriple.fixedFarGate
#print SM.restrictedVertexIndex
#print SM.restrictedWordTuple
#print SM.WallGerm
#print SM.WallGerm.sideTime
#print SM.WallGerm.sideTuple
#print SM.WallGerm.center
#print SM.WallGerm.zeroParameter
#check SM.boundaryIndex_injective
#check SM.chi_nonzero_outside_singleton
#check SM.chi_locally_constant_of_ne_zero
#check SM.finite_nonzero_chi_persists
#check SM.farOnlyCoordinates_local
#check SM.farOnlyCoordinates_unchanged_off_critical
#check SM.IntervalComposition.part_bounds
#check SM.WallGerm.eventually_center_iff_radius
#check SM.treeCoefficient_farOnly
#check SM.farOnlyOutput_restricted_tree
#check SM.restrictedWord_closing_edge
#check SM.BoundaryInterval.globalPosition_strict
#check SM.BoundaryInterval.globalPosition_bounds
#print axioms BoundaryGateStabilityIndependentReview.support_has_three_positions
#print axioms BoundaryGateStabilityIndependentReview.support_has_three_labels
#print axioms BoundaryGateStabilityIndependentReview.support_equality_exactly_ordered_equality
#print axioms BoundaryGateStabilityIndependentReview.actual_noncritical_point_sign
#print axioms BoundaryGateStabilityIndependentReview.actual_critical_point_sign_is_zero
#print axioms BoundaryGateStabilityIndependentReview.epsilon_middle_between
#print axioms BoundaryGateStabilityIndependentReview.epsilon_middle_before
#print axioms BoundaryGateStabilityIndependentReview.epsilon_middle_after
#print axioms BoundaryGateStabilityIndependentReview.both_negative_epsilons_impossible
#print axioms BoundaryGateStabilityIndependentReview.scalar_rescaling_allows_zero_gate
#print axioms BoundaryGateStabilityIndependentReview.actual_left_negative_ratio
#print axioms BoundaryGateStabilityIndependentReview.actual_right_negative_ratio
#print axioms BoundaryGateStabilityIndependentReview.n3_has_only_one_increasing_triple
#print axioms BoundaryGateStabilityIndependentReview.complete_left_gap_output_unchanged
#print axioms BoundaryGateStabilityIndependentReview.complete_right_gap_output_unchanged
#print axioms BoundaryGateStabilityIndependentReview.leaf_output_needs_no_array_agreement
#print axioms BoundaryGateStabilityIndependentReview.arbitrary_critical_update_preserves_output
#print axioms BoundaryGateStabilityIndependentReview.one_neighborhood_all_arrays_and_coordinates
#print axioms BoundaryGateStabilityIndependentReview.two_tuples_in_same_neighborhood_have_same_outputs
#print axioms GeometricGapResponseIndependentReview.gap_values_have_exact_four_cases
#print axioms GeometricGapResponseIndependentReview.leaf_gap_values_are_both_one
#print axioms GeometricGapResponseIndependentReview.reversing_nonzero_epsilon_exchanges_gap_values
#print axioms GeometricGapResponseIndependentReview.nonleaf_positive_U_and_negative_V_vanish
#print axioms GeometricGapResponseIndependentReview.critical_entry_changes_no_excluded_gap_value
#print axioms GeometricGapResponseIndependentReview.restricted_labels_read_the_actual_original_tuple
#print axioms GeometricGapResponseIndependentReview.restricted_label_equality_is_exact
#print axioms GeometricGapResponseIndependentReview.off_span_word_has_G1_and_physical_closing_edge
#print axioms GeometricGapResponseIndependentReview.off_span_nonleaf_output_is_actual_closed_tree
#print axioms GeometricGapResponseIndependentReview.common_radius_covers_both_actual_side_maps
#print axioms GeometricGapResponseIndependentReview.arbitrary_critical_value_retains_geometric_gap_sum
#print axioms GeometricGapResponseIndependentReview.full_tree_response_at_equal_positive_side_distances
