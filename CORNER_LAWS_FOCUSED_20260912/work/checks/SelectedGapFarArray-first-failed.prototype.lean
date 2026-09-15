import SM.Farout
import SM.EuclideanPlane
import SM.WeakGeometry
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic

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

/-- Translating the point on the common line contributes a parallel vector,
whose determinant with the line direction is zero. -/
theorem det_line_base_translation (p ω r : Plane) (t : ℝ) :
    det ω (r - (p + t • ω)) = det ω (r - p) := by
  dsimp [det]
  ring

/-- The reversed far determinant is the endpoint difference times the
transverse determinant, with the source's exact orientation. -/
theorem affine_line_far_determinant (p ω r : Plane) (x z : ℝ) :
    det (r - (p + z • ω)) ((p + x • ω) - (p + z • ω)) =
      (z - x) * det ω (r - p) := by
  rw [area_cyclic (p + x • ω) (p + z • ω) r, affine_line_difference]
  calc
    det ((z - x) • ω) (r - (p + x • ω)) =
        (z - x) * det ω (r - (p + x • ω)) := by
      dsimp [det]
      ring
    _ = (z - x) * det ω (r - p) := by rw [det_line_base_translation]

/-- Both endpoints of an internal gap may differ from the outer endpoints.
No condition on the transverse point is imposed, so zero determinants remain. -/
theorem affine_internal_gap_determinant (p ω r : Plane) (x z a b : ℝ)
    (hzx : z ≠ x) :
    det (r - (p + b • ω)) ((p + a • ω) - (p + b • ω)) =
      ((b - a) / (z - x)) *
        det (r - (p + z • ω)) ((p + x • ω) - (p + z • ω)) := by
  rw [affine_line_far_determinant, affine_line_far_determinant]
  rw [← mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hzx)]

/-- Source pf:gap-sign-identity for arbitrary internal-gap endpoints in
arbitrary affine coordinates, including a further silent cut. -/
theorem affine_internal_gap_sign (p ω r : Plane) (x z a b : ℝ)
    (hzx : z ≠ x) (hba : b ≠ a) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      SignType.sign ((b - a) / (z - x)) *
        pointFarSign (p + a • ω) r (p + b • ω) := by
  unfold pointFarSign
  rw [affine_internal_gap_determinant p ω r x z a b hzx]
  exact sign_rescale_nonzero _ _
    (div_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hzx))

/-- Silent further cuts are exactly the same for the outer and gap lines. -/
theorem affine_internal_gap_zero_iff (p ω r : Plane) (x z a b : ℝ)
    (hzx : z ≠ x) (hba : b ≠ a) :
    pointFarSign (p + x • ω) r (p + z • ω) = 0 ↔
      pointFarSign (p + a • ω) r (p + b • ω) = 0 := by
  rw [affine_internal_gap_sign p ω r x z a b hzx hba, mul_eq_zero]
  have hs : SignType.sign ((b - a) / (z - x)) ≠ 0 :=
    sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hzx))
  simp only [hs, false_or]

/-- The same identity in any commutative coefficient ring, without
division by a geometric sign or a transverse determinant. -/
theorem affine_internal_gap_sign_cast {R : Type*} [CommRing R]
    (p ω r : Plane) (x z a b : ℝ) (hzx : z ≠ x) (hba : b ≠ a) :
    ((pointFarSign (p + x • ω) r (p + z • ω) : ℤ) : R) =
      ((SignType.sign ((b - a) / (z - x)) : ℤ) : R) *
        ((pointFarSign (p + a • ω) r (p + b • ω) : ℤ) : R) := by
  have h := congrArg (fun s : SignType => ((s : ℤ) : R))
    (affine_internal_gap_sign p ω r x z a b hzx hba)
  simpa only [SignType.coe_mul, Int.cast_mul] using h

end
end SM

namespace SM

noncomputable section
variable {n : ℕ}

/-- Weak genericity already separates every pair of actual vertices, even
when selected triples are collinear. No G1 assumption is used. -/
theorem weak_vertices_injective {P : LabelledTuple n} (hP : WeakGeneric P) :
    Function.Injective P := by
  intro i j he
  by_contra hij
  by_cases hn : i = j + 1
  · apply hP.1 j
    unfold edge
    rw [← hn, he, sub_self]
  · apply hP.2.2.1 i j ((nonincident_iff i j).mpr ⟨hij, hn⟩)
    rw [he]
    exact ⟨0, le_rfl, by norm_num, (edgePoint_zero P j).symm⟩

theorem weak_boundaryWord_injective [NeZero n] {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) : Function.Injective (boundaryWord P g) :=
  (weak_vertices_injective hP).comp (boundaryIndex_injective g)

/-- Exact affine interpolation before any geometric nondegeneracy premise. -/
theorem line_coordinate_interpolation (p ω : Plane) (x y z : ℝ) (hxy : x ≠ y) :
    p + z • ω = (p + x • ω) + ((z - x) / (y - x)) •
      ((p + y • ω) - (p + x • ω)) := by
  ext <;> dsimp <;> field_simp [sub_ne_zero.mpr hxy.symm] <;> ring

/-- A scalar strictly between either ordered pair gives an interior affine
parameter for that exact oriented edge. Both orientations are retained. -/
theorem line_coordinate_between_parameter (x y z : ℝ)
    (h : (x < z ∧ z < y) ∨ (y < z ∧ z < x)) :
    x ≠ y ∧ 0 < (z - x) / (y - x) ∧ (z - x) / (y - x) < 1 := by
  rcases h with h | h
  · have hd : 0 < y - x := by linarith
    exact ⟨by linarith, div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩
  · have hd : y - x < 0 := by linarith
    exact ⟨by linarith, div_pos_of_neg_of_neg (by linarith) hd,
      (div_lt_one_of_neg hd).mpr (by linarith)⟩

/-- An original edge of a weak polygon cannot skip another selected point
on the same line. Its two orientations have the same exclusion. -/
theorem weak_line_edge_no_between {P : LabelledTuple n} (hP : WeakGeneric P)
    (i k : ZMod n) (hk0 : k ≠ i) (hk1 : k ≠ i + 1)
    (p ω : Plane) (x y z : ℝ)
    (hx : P i = p + x • ω) (hy : P (i + 1) = p + y • ω)
    (hz : P k = p + z • ω) :
    ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  intro h
  obtain ⟨hxy, ht0, ht1⟩ := line_coordinate_between_parameter x y z h
  apply hP.2.2.1 k i ((nonincident_iff k i).mpr ⟨hk0, hk1⟩)
  refine ⟨(z - x) / (y - x), ht0.le, ht1.le, ?_⟩
  change P k = P i + ((z - x) / (y - x)) • (P (i + 1) - P i)
  rw [hx, hy, hz]
  exact line_coordinate_interpolation p ω x y z hxy

/-- Three consecutive original vertices on one affine line contradict the
actual nonzero turn in WeakGeneric, without assuming point-triple G1. -/
theorem weak_not_three_consecutive_on_line {P : LabelledTuple n} (hP : WeakGeneric P)
    (i : ZMod n) (p ω : Plane) (x y z : ℝ)
    (hx : P (i - 1) = p + x • ω) (hy : P i = p + y • ω)
    (hz : P (i + 1) = p + z • ω) : False := by
  apply hP.2.1 i
  have hd : det (P i - P (i - 1)) (P (i + 1) - P (i - 1)) = 0 := by
    rw [hx, hy, hz]
    dsimp [det]
    ring
  simp only [turn, chi, hd, sign_zero]

theorem boundaryIndex_successive [NeZero n] (g : ZMod n) (a b : Fin n)
    (hab : b.val = a.val + 1) : boundaryIndex g b = boundaryIndex g a + 1 := by
  unfold boundaryIndex
  rw [hab, Nat.cast_add, Nat.cast_one]
  ring

/-- A leaf gap in an actual boundary word is precisely an original oriented
edge, so all selected line points other than its endpoints are excluded. -/
theorem weak_boundary_leaf_no_between [NeZero n] {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (a b c : Fin n) (hab : b.val = a.val + 1)
    (hca : c ≠ a) (hcb : c ≠ b) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g a = p + x • ω)
    (hy : boundaryWord P g b = p + y • ω)
    (hz : boundaryWord P g c = p + z • ω) :
    ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  have hb := boundaryIndex_successive g a b hab
  apply weak_line_edge_no_between hP (boundaryIndex g a) (boundaryIndex g c)
    (fun h => hca (boundaryIndex_injective g h))
    (fun h => hcb (boundaryIndex_injective g (h.trans hb.symm))) p ω x y z hx
  · rw [← hb]
    exact hy
  · exact hz

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryIndex_first_of_val (g : ZMod n) (a : Fin n) (ha : a.val = 0) :
    boundaryIndex g a = g + 1 := by simp [boundaryIndex, ha]

theorem boundaryIndex_last_of_val (g : ZMod n) (a : Fin n) (ha : a.val = n - 1) :
    boundaryIndex g a = g := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have he : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by simp
      _ = (n : ZMod n) := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.sub_add_cancel hn)
      _ = 0 := ZMod.natCast_self n
  simp only [boundaryIndex, ha, add_assoc, he, add_zero]

/-- Consecutive physical labels, including the wraparound root labels, cannot
all be on one line in a weak polygon. The successor equations are explicit. -/
theorem weak_not_successive_labels_on_line {P : LabelledTuple n} (hP : WeakGeneric P)
    (a b c : ZMod n) (hab : b = a + 1) (hbc : c = b + 1)
    (p ω : Plane) (x y z : ℝ) (hx : P a = p + x • ω)
    (hy : P b = p + y • ω) (hz : P c = p + z • ω) : False := by
  have ha : b - 1 = a := by rw [hab]; ring
  apply weak_not_three_consecutive_on_line hP b p ω x y z
  · rw [ha]
    exact hx
  · exact hy
  · rw [← hbc]
    exact hz

theorem weak_line_coordinate_injective {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω) : Function.Injective t := by
  intro a b he
  apply hr.injective
  apply weak_boundaryWord_injective hP g
  rw [hline a, hline b, he]

/-- Every one-leaf selected gap is an actual edge and contains no other
selected line coordinate. Endpoint indices are included in the quantifier. -/
theorem weak_line_selection_clear {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (j : Fin k) (hj : (r j.succ).val = (r j.castSucc).val + 1) (l : Fin (k + 1)) :
    ¬ (t j.castSucc < t l ∧ t l < t j.succ) ∧
      ¬ (t j.succ < t l ∧ t l < t j.castSucc) := by
  by_cases h0 : l = j.castSucc
  · subst l
    exact ⟨fun h => (lt_irrefl _ h.1), fun h => (lt_irrefl _ h.2)⟩
  by_cases h1 : l = j.succ
  · subst l
    exact ⟨fun h => (lt_irrefl _ h.2), fun h => (lt_irrefl _ h.1)⟩
  have h := weak_boundary_leaf_no_between hP g (r j.castSucc) (r j.succ) (r l) hj
    (fun he => h0 (hr.injective he)) (fun he => h1 (hr.injective he))
    p ω (t j.castSucc) (t j.succ) (t l) (hline _) (hline _) (hline _)
  exact ⟨fun h0 => h (Or.inl h0), fun h1 => h (Or.inr h1)⟩

/-- Two successive selected gaps cannot both be original edges on the line. -/
theorem weak_line_selection_no_successive_leaves {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (j l : Fin k) (hjl : j.val + 1 = l.val) :
    ¬ ((r j.succ).val = (r j.castSucc).val + 1 ∧
      (r l.succ).val = (r l.castSucc).val + 1) := by
  rintro ⟨hj, hl⟩
  have hm : j.succ = l.castSucc := Fin.ext hjl
  have hnext := boundaryIndex_successive g (r l.castSucc) (r l.succ) hl
  rw [← hm] at hnext
  exact weak_not_successive_labels_on_line hP _ _ _
    (boundaryIndex_successive g _ _ hj) hnext
    p ω (t j.castSucc) (t j.succ) (t l.succ) (hline _) (hline _) (hline _)

/-- With both full-word endpoints selected, the physical root edge cannot
contain any other selected coordinate. This has no arbitrary-interval analogue. -/
theorem weak_line_selection_root_clear {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (hfirst : (r 0).val = 0) (hlast : (r (Fin.last k)).val = n - 1)
    (l : Fin (k + 1)) : ¬ (t 0 < t l ∧ t l < t (Fin.last k)) := by
  by_cases h0 : l = 0
  · subst l
    exact fun h => lt_irrefl _ h.1
  by_cases h1 : l = Fin.last k
  · subst l
    exact fun h => lt_irrefl _ h.2
  have hf := boundaryIndex_first_of_val g (r 0) hfirst
  have hh := boundaryIndex_last_of_val g (r (Fin.last k)) hlast
  have h := weak_line_edge_no_between hP g (boundaryIndex g (r l))
    (fun he => h1 (hr.injective (boundaryIndex_injective g (he.trans hh.symm))))
    (fun he => h0 (hr.injective (boundaryIndex_injective g (he.trans hf.symm))))
    p ω (t (Fin.last k)) (t 0) (t l)
    (by simpa only [boundaryWord, hh] using hline (Fin.last k))
    (by simpa only [boundaryWord, hf] using hline 0) (hline l)
  exact fun ht => h (Or.inr ht)

theorem weak_line_selection_first_not_leaf {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (hk : 0 < k) (r : Fin (k + 1) → Fin n)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (hfirst : (r 0).val = 0) (hlast : (r (Fin.last k)).val = n - 1) :
    ¬ ((r (⟨0, hk⟩ : Fin k).succ).val = (r (⟨0, hk⟩ : Fin k).castSucc).val + 1) := by
  intro hleaf
  let j : Fin k := ⟨0, hk⟩
  have hj0 : j.castSucc = 0 := Fin.ext rfl
  have hf := boundaryIndex_first_of_val g (r 0) hfirst
  have hh := boundaryIndex_last_of_val g (r (Fin.last k)) hlast
  have hclose : boundaryIndex g (r j.castSucc) = boundaryIndex g (r (Fin.last k)) + 1 := by
    rw [hj0, hf, hh]
  exact weak_not_successive_labels_on_line hP _ _ _ hclose
    (boundaryIndex_successive g _ _ hleaf) p ω (t (Fin.last k)) (t j.castSucc) (t j.succ)
    (hline _) (hline _) (hline _)

theorem weak_line_selection_last_not_leaf {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {k : ℕ} (hk : 0 < k) (r : Fin (k + 1) → Fin n)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (hfirst : (r 0).val = 0) (hlast : (r (Fin.last k)).val = n - 1) :
    ¬ ((r (⟨k - 1, by omega⟩ : Fin k).succ).val =
      (r (⟨k - 1, by omega⟩ : Fin k).castSucc).val + 1) := by
  intro hleaf
  let j : Fin k := ⟨k - 1, by omega⟩
  have hjlast : j.succ = Fin.last k := by apply Fin.ext; change k - 1 + 1 = k; omega
  have hf := boundaryIndex_first_of_val g (r 0) hfirst
  have hh := boundaryIndex_last_of_val g (r (Fin.last k)) hlast
  have hclose : boundaryIndex g (r 0) = boundaryIndex g (r j.succ) + 1 := by
    rw [hjlast, hf, hh]
  exact weak_not_successive_labels_on_line hP _ _ _
    (boundaryIndex_successive g _ _ hleaf) hclose p ω (t j.castSucc) (t j.succ) (t 0)
    (hline _) (hline _) (hline _)

end
end SM

namespace SM

noncomputable section
variable {k : ℕ}

/-- The printed gap ratio uses the ordered endpoints of the whole selected list. -/
def lineGapEpsilon (t : Fin (k + 1) → ℝ) (j : Fin k) : SignType :=
  SignType.sign ((t j.succ - t j.castSucc) / (t (Fin.last k) - t 0))

def normalizedLineCoordinate (t : Fin (k + 1) → ℝ) (l : Fin (k + 1)) : ℝ :=
  (t l - t 0) / (t (Fin.last k) - t 0)

theorem selected_endpoint_difference_nonzero (hk : 0 < k)
    (t : Fin (k + 1) → ℝ) (hinj : Function.Injective t) : t (Fin.last k) - t 0 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hi := congrArg Fin.val (hinj he)
  change k = 0 at hi
  omega

theorem normalizedLineCoordinate_first (t : Fin (k + 1) → ℝ) :
    normalizedLineCoordinate t 0 = 0 := by simp [normalizedLineCoordinate]

theorem normalizedLineCoordinate_last (t : Fin (k + 1) → ℝ)
    (hd : t (Fin.last k) - t 0 ≠ 0) :
    normalizedLineCoordinate t (Fin.last k) = 1 := by
  exact div_self hd

theorem normalizedLineCoordinate_injective (t : Fin (k + 1) → ℝ)
    (hinj : Function.Injective t) (hd : t (Fin.last k) - t 0 ≠ 0) :
    Function.Injective (normalizedLineCoordinate t) := by
  intro a b he
  apply hinj
  have hc := congrArg (fun x : ℝ => x * (t (Fin.last k) - t 0)) he
  have hsub : t a - t 0 = t b - t 0 := by
    simpa only [normalizedLineCoordinate, div_mul_cancel₀ _ hd] using hc
  linarith

/-- Normalization changes neither the selected points nor their line, even
when the original endpoint difference is negative. -/
theorem normalizedLineCoordinate_representation (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hd : t (Fin.last k) - t 0 ≠ 0) (l : Fin (k + 1)) :
    p + t l • ω = (p + t 0 • ω) + normalizedLineCoordinate t l •
      ((t (Fin.last k) - t 0) • ω) := by
  rw [smul_smul]
  simp only [normalizedLineCoordinate, div_mul_cancel₀ _ hd]
  ext <;> dsimp <;> ring

theorem normalizedLineCoordinate_gap (t : Fin (k + 1) → ℝ) (j : Fin k) :
    normalizedLineCoordinate t j.succ - normalizedLineCoordinate t j.castSucc =
      (t j.succ - t j.castSucc) / (t (Fin.last k) - t 0) := by
  unfold normalizedLineCoordinate
  rw [← sub_div]
  congr 1
  ring

theorem lineGapEpsilon_positive (t : Fin (k + 1) → ℝ) (j : Fin k) :
    lineGapEpsilon t j = 1 ↔
      normalizedLineCoordinate t j.castSucc < normalizedLineCoordinate t j.succ := by
  unfold lineGapEpsilon
  rw [sign_eq_one_iff, ← normalizedLineCoordinate_gap, sub_pos]

theorem lineGapEpsilon_negative (t : Fin (k + 1) → ℝ) (j : Fin k) :
    lineGapEpsilon t j = -1 ↔
      normalizedLineCoordinate t j.succ < normalizedLineCoordinate t j.castSucc := by
  unfold lineGapEpsilon
  rw [sign_eq_neg_one_iff, ← normalizedLineCoordinate_gap, sub_neg]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {k : ℕ}

/-- The actual dot-product coordinate on the line from the first selected
point to the last. Its endpoints will be proved to have coordinates0 and1. -/
def selectedLineCoordinate (P : LabelledTuple n) (g : ZMod n)
    (r : Fin (k + 1) → Fin n) (l : Fin (k + 1)) : ℝ :=
  let ω := boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)
  planeDot ω (boundaryWord P g (r l) - boundaryWord P g (r 0)) / planeDot ω ω

/-- Zero actual determinants on the selected line supply all affine data
and distinct coordinates; no separate collinearity or injectivity oracle is
assumed. This uses only WeakGeneric, even with arbitrarily many silent zeros. -/
theorem weak_selected_line_coordinates {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (hk : 0 < k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0) :
    (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0) ≠ 0) ∧
    (∀ l, boundaryWord P g (r l) = boundaryWord P g (r 0) +
      selectedLineCoordinate P g r l •
        (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))) ∧
    Function.Injective (selectedLineCoordinate P g r) ∧
    selectedLineCoordinate P g r 0 = 0 ∧
    selectedLineCoordinate P g r (Fin.last k) = 1 := by
  let p := boundaryWord P g (r 0)
  let ω := boundaryWord P g (r (Fin.last k)) - p
  have hω : ω ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hi := hr.injective (weak_boundaryWord_injective hP g he)
    have hv := congrArg Fin.val hi
    change k = 0 at hv
    omega
  have hline : ∀ l, boundaryWord P g (r l) = p + selectedLineCoordinate P g r l • ω := by
    intro l
    have hd : det ω (boundaryWord P g (r l) - p) = 0 := by
      rw [det_swap]
      change -det (boundaryWord P g (r l) - boundaryWord P g (r 0))
        (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0
      rw [hcol l, neg_zero]
    have hs := scalar_of_det_zero hω hd
    change boundaryWord P g (r l) - p = selectedLineCoordinate P g r l • ω at hs
    calc
      _ = p + (boundaryWord P g (r l) - p) := by abel
      _ = _ := by rw [hs]
  refine ⟨hω, hline, weak_line_coordinate_injective hP g r hr p ω _ hline, ?_, ?_⟩
  · simp [selectedLineCoordinate, planeDot]
  · exact div_self (ne_of_gt (planeDot_self_pos hω))

end
end SM

namespace SM

noncomputable section
variable {n k : ℕ} [NeZero n]

/-- The actual outer triple for a cut strictly inside a selected gap. -/
def selectedOuterCutTriple (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (j : Fin k) (u : Fin n) (hleft : r j.castSucc < u) (hright : u < r j.succ) :
    IncreasingBoundaryTriple n where
  lower := r 0
  middle := u
  upper := r (Fin.last k)
  lower_middle := lt_of_le_of_lt (hr.monotone (by omega)) hleft
  middle_upper := lt_of_lt_of_le hright (hr.monotone (by omega))

/-- The same physical cut with the actual selected gap endpoints. -/
def selectedGapCutTriple (r : Fin (k + 1) → Fin n) (j : Fin k) (u : Fin n)
    (hleft : r j.castSucc < u) (hright : u < r j.succ) : IncreasingBoundaryTriple n where
  lower := r j.castSucc
  middle := u
  upper := r j.succ
  lower_middle := hleft
  middle_upper := hright

theorem selected_gap_epsilon_nonzero (hk : 0 < k) (t : Fin (k + 1) → ℝ)
    (hinj : Function.Injective t) (j : Fin k) : lineGapEpsilon t j ≠ 0 := by
  have hgap : t j.succ ≠ t j.castSucc := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    change j.val + 1 = j.val at hv
    omega
  exact sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hgap)
    (selected_endpoint_difference_nonzero hk t hinj))

/-- Actual weak geometry supplies distinct scalar endpoints for every gap;
the further point u may lie on or off the selected line. -/
theorem weak_selected_gap_far_sign {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (hk : 0 < k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω) (j : Fin k) (u : Fin n) :
    pointFarSign (boundaryWord P g (r 0)) (boundaryWord P g u)
      (boundaryWord P g (r (Fin.last k))) = lineGapEpsilon t j *
        pointFarSign (boundaryWord P g (r j.castSucc)) (boundaryWord P g u)
          (boundaryWord P g (r j.succ)) := by
  have hinj := weak_line_coordinate_injective hP g r hr p ω t hline
  have houter : t (Fin.last k) ≠ t 0 :=
    sub_ne_zero.mp (selected_endpoint_difference_nonzero hk t hinj)
  have hgap : t j.succ ≠ t j.castSucc := by
    intro he
    have hv := congrArg Fin.val (hinj he)
    change j.val + 1 = j.val at hv
    omega
  simpa only [hline, lineGapEpsilon] using
    affine_internal_gap_sign p ω (boundaryWord P g u)
      (t 0) (t (Fin.last k)) (t j.castSucc) (t j.succ) houter hgap

/-- Source pf:gap-sign-identity for the exact geometric array and physical
cut triples, over any commutative coefficient ring. -/
theorem weak_selected_gap_far_array {R : Type*} [CommRing R]
    {P : LabelledTuple n} (hP : WeakGeneric P) (g : ZMod n) (hk : 0 < k)
    (r : Fin (k + 1) → Fin n) (hr : StrictMono r) (p ω : Plane)
    (t : Fin (k + 1) → ℝ) (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω)
    (j : Fin k) (u : Fin n) (hleft : r j.castSucc < u) (hright : u < r j.succ) :
    geometricBoundaryArray (R := R) P g (selectedOuterCutTriple r hr j u hleft hright) =
      ((lineGapEpsilon t j : ℤ) : R) *
        geometricBoundaryArray P g (selectedGapCutTriple r j u hleft hright) := by
  change ((pointFarSign (boundaryWord P g (r 0)) (boundaryWord P g u)
      (boundaryWord P g (r (Fin.last k))) : ℤ) : R) = _
  have hs := congrArg (fun s : SignType => ((s : ℤ) : R))
    (weak_selected_gap_far_sign hP g hk r hr p ω t hline j u)
  simpa only [SignType.coe_mul, Int.cast_mul] using hs

/-- The array identity follows directly from determinant collinearity, with
the selected affine coordinates constructed from the actual polygon. -/
theorem weak_selected_gap_far_array_of_collinear {R : Type*} [CommRing R]
    {P : LabelledTuple n} (hP : WeakGeneric P) (g : ZMod n) (hk : 0 < k)
    (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0)
    (j : Fin k) (u : Fin n) (hleft : r j.castSucc < u) (hright : u < r j.succ) :
    geometricBoundaryArray (R := R) P g (selectedOuterCutTriple r hr j u hleft hright) =
      ((lineGapEpsilon (selectedLineCoordinate P g r) j : ℤ) : R) *
        geometricBoundaryArray P g (selectedGapCutTriple r j u hleft hright) := by
  have hcoords := weak_selected_line_coordinates hP g hk r hr hcol
  exact weak_selected_gap_far_array hP g hk r hr (boundaryWord P g (r 0))
    (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))
    (selectedLineCoordinate P g r) hcoords.2.1 j u hleft hright

end
end SM

#print axioms SM.selectedOuterCutTriple
#print axioms SM.selectedGapCutTriple
#print axioms SM.selected_gap_epsilon_nonzero
#print axioms SM.weak_selected_gap_far_sign
#print axioms SM.weak_selected_gap_far_array
#print axioms SM.weak_selected_gap_far_array_of_collinear
