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
