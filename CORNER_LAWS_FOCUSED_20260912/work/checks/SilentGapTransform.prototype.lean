import SM.Farout
import SM.EuclideanPlane
import SM.WeakGeometry
import SM.NearFarFactorization
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Fine raw compositions containing every selected outer cut correspond
exactly to the existing refining cut sets. -/
def refiningCompositionEquiv (π : IntervalComposition I) :
    {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts} ≃ RefiningCutSet π :=
  Equiv.subtypeEquiv (cutSetEquiv I) (fun _ => Iff.rfl)

/-- Fixing the selected outer cuts leaves one independent raw composition
in each actual gap. Unary inner compositions and one-leaf gaps are retained. -/
def nestedRefiningCompositionEquiv (π : IntervalComposition I) :
    (∀ k : Fin π.parts, IntervalComposition (π.part k)) ≃
      {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts} :=
  π.nestedCompositionEquiv.trans π.refiningCompositionEquiv.symm

theorem nestedRefiningCompositionEquiv_val (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    (π.nestedRefiningCompositionEquiv σ).val =
      (π.flattenCutSets (fun k => (σ k).cutSet)).toComposition := rfl

/-- Arbitrary selected interior positions produce the exact outer cuts,
including the empty selection. -/
theorem selectedComposition_interior (S : InteriorCutSet I) :
    (BoundaryCutSet.ofInterior S).toComposition.cutSet.interior = S := by
  rw [BoundaryCutSet.toComposition_cutSet, BoundaryCutSet.interior_ofInterior]

/-- Containment of all outer cuts is precisely containment of the selected
interior positions; the two global endpoints contribute no extra condition. -/
theorem selectedComposition_refines_iff (S : InteriorCutSet I)
    (ρ : IntervalComposition I) :
    (BoundaryCutSet.ofInterior S).toComposition.cutSet.cuts ⊆ ρ.cutSet.cuts ↔
      S.val ⊆ ρ.cutSet.interior.val := by
  rw [BoundaryCutSet.cuts_subset_iff_interior_subset, selectedComposition_interior]

/-- Every physical interior position occurs once, also for a unary
composition whose interior index type and cut set are both empty. -/
theorem prod_interior_positions {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (b : Fin n → R) :
    (∏ j : Fin (π.parts - 1), b (π.interiorPosition j)) =
      ∏ x ∈ π.cutSet.interior.val, b x := by
  calc
    _ = ∏ x : {x : Fin n // x ∈ π.cutSet.interior.val}, b x.val :=
      Fintype.prod_equiv π.interiorPositionEquiv _ _ (fun _ => rfl)
    _ = _ := (Finset.prod_subtype _ (fun _ => Iff.rfl) b).symm

/-- All inner cuts are exactly the unselected fine physical cuts. In
particular a selected mark cannot reappear inside a gap. -/
theorem prod_inner_positions {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π) (b : Fin n → R) :
    (∏ k : Fin π.parts, ∏ j : Fin ((π.refinementInner T k).parts - 1),
      b ((π.refinementInner T k).interiorPosition j)) =
      ∏ x ∈ T.val.interior.val \ π.cutSet.interior.val, b x := by
  calc
    _ = ∏ r : RefinementUnmarked π T,
        b (T.val.toComposition.interiorPosition r.val) :=
      π.prod_inner_nearTriples T (fun t => b t.middle)
    _ = ∏ r ∈ (π.refinementMarkIndices T)ᶜ,
        b (T.val.toComposition.interiorPosition r) :=
      π.prod_refinementUnmarked T (fun r => b (T.val.toComposition.interiorPosition r))
    _ = ∏ x ∈ (T.val.toComposition.indexMarks (π.refinementMarkIndices T)ᶜ).val,
        b x := T.val.toComposition.prod_indexMarks (π.refinementMarkIndices T)ᶜ b
    _ = _ := by
      rw [indexMarks_compl]
      unfold refinementMarkIndices
      rw [indexMarks_markIndices]
      simp only [refinementMarks, BoundaryCutSet.toComposition_cutSet]

/-- A gap summand with arbitrary weights at its actual interior positions,
and the original coordinates at every actual child interval. -/
def positionCutSummand {R : Type*} [CommMonoid R]
    (b : Fin n → R) (X : BoundaryInterval n → R) (π : IntervalComposition I) : R :=
  (∏ j : Fin (π.parts - 1), b (π.interiorPosition j)) *
    ∏ j : Fin π.parts, X (π.part j)

/-- Splitting a fixed refining cut set preserves every unselected cut
factor and every actual fine child coordinate, without arity restrictions. -/
theorem prod_refinement_gap_summands {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (T : RefiningCutSet π)
    (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, positionCutSummand b X (π.refinementInner T k)) =
      (∏ x ∈ T.val.interior.val \ π.cutSet.interior.val, b x) *
        ∏ j : Fin T.val.toComposition.parts, X (T.val.toComposition.part j) := by
  simp only [positionCutSummand, Finset.prod_mul_distrib]
  rw [π.prod_inner_positions T b, π.prod_refined_children T X]

/-- The complete termwise identity for an arbitrary independent family
of actual gap compositions, using the genuine ordered flattening. -/
theorem prod_nested_gap_summands {R : Type*} [CommMonoid R]
    (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k))
    (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∏ k : Fin π.parts, positionCutSummand b X (σ k)) =
      (∏ x ∈ (π.flattenCutSets (fun k => (σ k).cutSet)).interior.val \
        π.cutSet.interior.val, b x) *
        ∏ j : Fin (π.flattenCutSets (fun k => (σ k).cutSet)).toComposition.parts,
          X ((π.flattenCutSets (fun k => (σ k).cutSet)).toComposition.part j) := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  have ht : (fun k => π.refinementInner T k) = σ :=
    funext (π.refinementInner_flatten σ)
  have hp := congrArg
    (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
      ∏ k : Fin π.parts, positionCutSummand b X (η k)) ht
  exact hp.symm.trans (π.prod_refinement_gap_summands T b X)

/-- The exact fixed-selected-cut sum factors into independent gap sums.
No coefficient identity is assumed: this follows from the actual refining
composition equivalence, the full termwise identity, and finite distributivity. -/
theorem sum_refining_cut_products {R : Type*} [CommSemiring R]
    (π : IntervalComposition I) (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ ρ : {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts},
      (∏ x ∈ ρ.val.cutSet.interior.val \ π.cutSet.interior.val, b x) *
        ∏ j : Fin ρ.val.parts, X (ρ.val.part j)) =
      ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  classical
  symm
  calc
    _ = ∑ σ : ∀ k : Fin π.parts, IntervalComposition (π.part k),
        ∏ k : Fin π.parts, positionCutSummand b X (σ k) := Fintype.prod_sum _
    _ = _ := Fintype.sum_equiv π.nestedRefiningCompositionEquiv _ _ (by
      intro σ
      rw [π.nestedRefiningCompositionEquiv_val σ, BoundaryCutSet.toComposition_cutSet]
      exact π.prod_nested_gap_summands σ b X)

/-- Restoring the selected factors gives the product decomposition used
by the source top-coefficient calculation. Zero unselected weights are
allowed, so other silent cuts can be killed without changing the indexing. -/
theorem sum_refining_selected_cut_products {R : Type*} [CommSemiring R]
    (π : IntervalComposition I) (a b : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ ρ : {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts},
      (∏ x ∈ π.cutSet.interior.val, a x) *
        ((∏ x ∈ ρ.val.cutSet.interior.val \ π.cutSet.interior.val, b x) *
          ∏ j : Fin ρ.val.parts, X (ρ.val.part j))) =
      (∏ x ∈ π.cutSet.interior.val, a x) *
        ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  rw [← Finset.mul_sum, π.sum_refining_cut_products b X]

/-- A constant selected weight contributes its power with exponent equal
to the number of actual selected interior positions. -/
theorem sum_refining_constant_selected_factor {R : Type*} [CommSemiring R]
    (π : IntervalComposition I) (q : R) (b : Fin n → R) (X : BoundaryInterval n → R) :
    (∑ ρ : {ρ : IntervalComposition I // π.cutSet.cuts ⊆ ρ.cutSet.cuts},
      q ^ π.cutSet.interior.val.card *
        ((∏ x ∈ ρ.val.cutSet.interior.val \ π.cutSet.interior.val, b x) *
          ∏ j : Fin ρ.val.parts, X (ρ.val.part j))) =
      q ^ π.cutSet.interior.val.card *
        ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  simpa only [Finset.prod_const] using π.sum_refining_selected_cut_products (fun _ => q) b X

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The synthetic near and far factors add the two arbitrary positional
weights. Invertibility of two is the only division assumption. -/
theorem positional_cut_half_add (a b : R) :
    ((2 * b) - (-(2 * a))) * ⅟ (2 : R) = a + b := by
  calc
    _ = ((a + b) * 2) * ⅟ (2 : R) := by ring
    _ = a + b := by rw [mul_assoc, mul_invOf_self, mul_one]

namespace IntervalComposition
variable {I : BoundaryInterval n}

/-- Both the near and far triples have the same actual interior position.
The synthetic arrays therefore produce the sum of the positional weights. -/
theorem nearFarWeight_position_add (π : IntervalComposition I) (a b : Fin n → R) :
    π.nearFarWeight (fun t => 2 * b t.middle) (fun t => -(2 * a t.middle)) =
      ∏ j : Fin (π.parts - 1), (a (π.interiorPosition j) + b (π.interiorPosition j)) := by
  unfold nearFarWeight
  apply Finset.prod_congr rfl
  intro j _
  change ((2 * b (π.interiorPosition j)) - (-(2 * a (π.interiorPosition j)))) *
    ⅟ (2 : R) = a (π.interiorPosition j) + b (π.interiorPosition j)
  exact positional_cut_half_add _ _

/-- The near-only synthetic array gives exactly the b product, including
an empty product when the composition is unary. -/
theorem nearFarWeight_position_near (π : IntervalComposition I) (b : Fin n → R) :
    π.nearFarWeight (fun t => 2 * b t.middle) 0 =
      ∏ j : Fin (π.parts - 1), b (π.interiorPosition j) := by
  have hz : (fun _ : IncreasingBoundaryTriple n => -(2 * (0 : R))) =
      (0 : TripleArray n R) := by funext t; simp
  have h := π.nearFarWeight_position_add (fun _ => 0) b
  rw [hz] at h
  simpa only [zero_add] using h

/-- The far-only synthetic array gives exactly the a product; its negative
sign cancels the negative far factor in the actual transform definition. -/
theorem nearFarWeight_position_far (π : IntervalComposition I) (a : Fin n → R) :
    π.nearFarWeight 0 (fun t => -(2 * a t.middle)) =
      ∏ j : Fin (π.parts - 1), a (π.interiorPosition j) := by
  have hz : (fun _ : IncreasingBoundaryTriple n => 2 * (0 : R)) =
      (0 : TripleArray n R) := by funext t; simp
  have h := π.nearFarWeight_position_add a (fun _ => 0)
  rw [hz] at h
  simpa only [add_zero] using h

end IntervalComposition
open IntervalComposition

/-- The mixed synthetic transform is exactly the positional sum with
weight a+b at each actual cut and the unchanged actual child coordinates. -/
theorem nearFarTransform_position_add (a b : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    nearFarTransform (fun t => 2 * b t.middle) (fun t => -(2 * a t.middle)) X I =
      ∑ π : IntervalComposition I, positionCutSummand (a + b) X π := by
  unfold nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_position_add a b]
  rfl

/-- Exact near-transform identification at every actual interval. -/
theorem nearTransform_position (b : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    nearTransform (fun t => 2 * b t.middle) X I =
      ∑ π : IntervalComposition I, positionCutSummand b X π := by
  unfold nearTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_position_near b]
  rfl

/-- Exact far-transform identification at every actual interval. -/
theorem farTransform_position (a : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    farTransform (fun t => -(2 * a t.middle)) X I =
      ∑ π : IntervalComposition I, positionCutSummand a X π := by
  unfold farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  rw [π.nearFarWeight_position_far a]
  rfl

/-- The full polynomial decomposition for arbitrary positional weights:
select the a-cuts as the actual outer composition and independently sum
all b-compositions of every actual gap. This is a specialization of the
proved source near/far factorization, with no coefficient identity assumed. -/
theorem positionCutSum_add_decomposition (a b : Fin n → R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    (∑ ρ : IntervalComposition I, positionCutSummand (a + b) X ρ) =
      ∑ π : IntervalComposition I,
        (∏ x ∈ π.cutSet.interior.val, a x) *
          ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k), positionCutSummand b X σ := by
  calc
    _ = nearFarTransform (fun t => 2 * b t.middle) (fun t => -(2 * a t.middle)) X I :=
      (nearFarTransform_position_add a b X I).symm
    _ = farTransform (fun t => -(2 * a t.middle))
        (nearTransform (fun t => 2 * b t.middle) X) I :=
      (nearFar_factorization_coordinate (fun t => 2 * b t.middle)
        (fun t => -(2 * a t.middle)) X I).symm
    _ = ∑ π : IntervalComposition I,
        positionCutSummand a (nearTransform (fun t => 2 * b t.middle) X) π :=
      farTransform_position a _ I
    _ = _ := by
      apply Finset.sum_congr rfl
      intro π _
      unfold positionCutSummand
      rw [π.prod_interior_positions a]
      apply congrArg (fun y : R => (∏ x ∈ π.cutSet.interior.val, a x) * y)
      apply Finset.prod_congr rfl
      intro k _
      exact nearTransform_position b X (π.part k)

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- Read the far entry with fixed outer endpoints at a physical position.
The value outside that open interval is irrelevant to its compositions. -/
def intervalFarValue (H : TripleArray n R) (I : BoundaryInterval n) (u : Fin n) : R := by
  classical
  exact if h : I.left < u ∧ u < I.right then H ⟨I.left, u, I.right, h.1, h.2⟩ else 0

theorem intervalFarValue_interior (H : TripleArray n R) {I : BoundaryInterval n}
    (π : IntervalComposition I) (j : Fin (π.parts - 1)) :
    intervalFarValue H I (π.interiorPosition j) = H (π.farTriple j) := by
  have hb : I.left < π.interiorPosition j ∧ π.interiorPosition j < I.right :=
    ⟨(π.farTriple j).lower_middle, (π.farTriple j).middle_upper⟩
  unfold intervalFarValue
  rw [dif_pos hb]
  rfl

theorem intervalFarValue_map {S : Type*} [CommRing S] (f : R →+* S)
    (H : TripleArray n R) (I : BoundaryInterval n) (u : Fin n) :
    f (intervalFarValue H I u) = intervalFarValue (fun t => f (H t)) I u := by
  by_cases h : I.left < u ∧ u < I.right <;> simp [intervalFarValue, h]

variable [Invertible (2 : R)]

def intervalFarCutWeight (H : TripleArray n R) (I : BoundaryInterval n) (u : Fin n) : R :=
  -intervalFarValue H I u * ⅟ (2 : R)

theorem intervalFarCutWeight_add (H U : TripleArray n R) (I : BoundaryInterval n) :
    intervalFarCutWeight (H + U) I = intervalFarCutWeight U I + intervalFarCutWeight H I := by
  funext u
  by_cases h : I.left < u ∧ u < I.right
  · simp only [intervalFarCutWeight, intervalFarValue, dif_pos h, Pi.add_apply]
    ring
  · simp [intervalFarCutWeight, intervalFarValue, h]

/-- Fixed-endpoint positional weights reproduce each complete actual
far-transform summand and its unchanged actual child-coordinate product. -/
theorem positionCutSummand_intervalFar (H : TripleArray n R) (X : IntervalArray n R)
    {I : BoundaryInterval n} (π : IntervalComposition I) :
    IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X π =
      π.nearFarWeight 0 H * ∏ j : Fin π.parts, X (π.part j) := by
  unfold IntervalComposition.positionCutSummand IntervalComposition.nearFarWeight
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [intervalFarCutWeight, intervalFarValue_interior, Pi.zero_apply, zero_sub]

theorem farTransform_positionCutSum (H : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) :
    farTransform H X I = ∑ π : IntervalComposition I,
      IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X π := by
  unfold farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  exact (positionCutSummand_intervalFar H X π).symm

/-- Exact polynomial expansion of the top coordinate around H, with all
child coordinates fixed to X. The outer cuts carry U and independent gap
compositions carry H read using the original outer endpoints. This holds
for arbitrary arrays in the full ring, with no realizability restriction. -/
theorem farTransform_add_decomposition (H U : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    farTransform (H + U) X I =
      ∑ π : IntervalComposition I,
        (∏ x ∈ π.cutSet.interior.val, intervalFarCutWeight U I x) *
          ∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k),
            IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ := by
  rw [farTransform_positionCutSum, intervalFarCutWeight_add]
  exact positionCutSum_add_decomposition (intervalFarCutWeight U I)
    (intervalFarCutWeight H I) X I

end
end SM

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

namespace SM.FiniteLineOrder

noncomputable section

/-- An endpoint below a maximum is at least every other selected value if
no selected value lies strictly between those two endpoints. Injectivity
makes each selected value other than the maximum strictly smaller than it. -/
theorem second_max_bound {ι : Type*} (t : ι → ℝ) (hinj : Function.Injective t)
    (a m : ι) (hmax : ∀ l, t l ≤ t m)
    (hclear : ∀ l, ¬ (t a < t l ∧ t l < t m)) :
    ∀ l, l ≠ m → t l ≤ t a := by
  intro l hl
  apply le_of_not_gt
  intro ha
  exact hclear l ⟨ha, lt_of_le_of_ne (hmax l) (hinj.ne hl)⟩

/-- Abstract increasing-gap assertion. The only restrictions on a leaf
gap are absence of any selected coordinate in its open segment and the
prohibition on two successive leaf gaps. The endpoints are merely ordered;
their coordinates need not be normalized to zero and one. -/
theorem exists_increasing_nonleaf_gap (k : ℕ) (hk : 2 ≤ k)
    (t : Fin (k + 1) → ℝ) (hinj : Function.Injective t) (leaf : Fin k → Prop)
    (hend : t 0 < t (Fin.last k))
    (hclear : ∀ j : Fin k, leaf j → ∀ l : Fin (k + 1),
      ¬ (t j.castSucc < t l ∧ t l < t j.succ) ∧
      ¬ (t j.succ < t l ∧ t l < t j.castSucc))
    (hnext : ∀ j l : Fin k, j.val + 1 = l.val → ¬ (leaf j ∧ leaf l)) :
    ∃ j : Fin k, t j.castSucc < t j.succ ∧ ¬ leaf j := by
  classical
  by_contra hn
  have hleaf : ∀ j : Fin k, t j.castSucc < t j.succ → leaf j := by
    intro j hj
    by_contra hnot
    exact hn ⟨j, hj, hnot⟩
  obtain ⟨m, hmax⟩ := Finite.exists_max t
  have hm0 : 0 < m.val := by
    by_contra h
    have he : m = 0 := by
      apply Fin.ext
      change m.val = 0
      omega
    have h := hmax (Fin.last k)
    rw [he] at h
    exact (not_le_of_gt hend) h
  let j : Fin k := ⟨m.val - 1, by have := m.isLt; omega⟩
  have hjs : j.succ = m := by
    apply Fin.ext
    change m.val - 1 + 1 = m.val
    omega
  have hjm : j.castSucc ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val - 1 = m.val at hv
    omega
  have hjup : t j.castSucc < t j.succ := by
    rw [hjs]
    exact lt_of_le_of_ne (hmax j.castSucc) (hinj.ne hjm)
  have hjleaf := hleaf j hjup
  have hsecond : ∀ l : Fin (k + 1), l ≠ m → t l ≤ t j.castSucc :=
    second_max_bound t hinj j.castSucc m hmax (by
      intro l
      simpa only [hjs] using (hclear j hjleaf l).1)
  have hm2 : 2 ≤ m.val := by
    by_contra h
    have hm1 : m.val = 1 := by omega
    have hj0 : j.castSucc = (0 : Fin (k + 1)) := by
      apply Fin.ext
      change m.val - 1 = 0
      omega
    have hlast : Fin.last k ≠ m := by
      intro he
      have hv := congrArg Fin.val he
      change k = m.val at hv
      omega
    have h := hsecond (Fin.last k) hlast
    rw [hj0] at h
    exact (not_le_of_gt hend) h
  let i : Fin k := ⟨m.val - 2, by have := m.isLt; omega⟩
  have his : i.succ = j.castSucc := by
    apply Fin.ext
    change m.val - 2 + 1 = m.val - 1
    omega
  have him : i.castSucc ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val - 2 = m.val at hv
    omega
  have hij : i.castSucc ≠ j.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    change m.val - 2 = m.val - 1 at hv
    omega
  have hiup : t i.castSucc < t i.succ := by
    rw [his]
    exact lt_of_le_of_ne (hsecond i.castSucc him) (hinj.ne hij)
  have hileaf := hleaf i hiup
  have hadj : i.val + 1 = j.val := by
    change m.val - 2 + 1 = m.val - 1
    omega
  exact hnext i j hadj ⟨hileaf, hjleaf⟩

/-- Abstract decreasing-gap assertion for a list closed by its ordered
last-to-first step. The additional hypotheses explicitly state the closing
segment exclusion and the two nonleaf gaps next to that closing step. -/
theorem exists_decreasing_nonleaf_gap (k : ℕ) (hk : 2 ≤ k)
    (t : Fin (k + 1) → ℝ) (hinj : Function.Injective t) (leaf : Fin k → Prop)
    (hend : t 0 < t (Fin.last k))
    (hclear : ∀ j : Fin k, leaf j → ∀ l : Fin (k + 1),
      ¬ (t j.castSucc < t l ∧ t l < t j.succ) ∧
      ¬ (t j.succ < t l ∧ t l < t j.castSucc))
    (hnext : ∀ j l : Fin k, j.val + 1 = l.val → ¬ (leaf j ∧ leaf l))
    (hclose : ∀ l : Fin (k + 1), ¬ (t 0 < t l ∧ t l < t (Fin.last k)))
    (hfirst : ¬ leaf ⟨0, by omega⟩)
    (hlast : ¬ leaf ⟨k - 1, by omega⟩) :
    ∃ j : Fin k, t j.succ < t j.castSucc ∧ ¬ leaf j := by
  classical
  by_contra hn
  have hleaf : ∀ j : Fin k, t j.succ < t j.castSucc → leaf j := by
    intro j hj
    by_contra hnot
    exact hn ⟨j, hj, hnot⟩
  let f : Fin k := ⟨0, by omega⟩
  have hfne : f.castSucc ≠ f.succ := by
    intro he
    have hv := congrArg Fin.val he
    change (0 : ℕ) = 1 at hv
    omega
  have hfup : t f.castSucc < t f.succ := by
    have hnot : ¬ (t f.succ < t f.castSucc) := fun h => hfirst (hleaf f h)
    exact lt_of_le_of_ne (le_of_not_gt hnot) (hinj.ne hfne)
  have hfup0 : t 0 < t f.succ := hfup
  have hfl : f.succ ≠ Fin.last k := by
    intro he
    have hv := congrArg Fin.val he
    change 1 = k at hv
    omega
  have hlastbelow : t (Fin.last k) < t f.succ := by
    have hnot : ¬ (t f.succ < t (Fin.last k)) := fun h => hclose f.succ ⟨hfup0, h⟩
    exact lt_of_le_of_ne (le_of_not_gt hnot) (hinj.ne hfl).symm
  obtain ⟨m, hmax⟩ := Finite.exists_max t
  have hmk : m.val < k := by
    have hmne : m ≠ Fin.last k := by
      intro he
      have h := hmax f.succ
      rw [he] at h
      exact (not_le_of_gt hlastbelow) h
    by_contra h
    apply hmne
    apply Fin.ext
    change m.val = k
    have := m.isLt
    omega
  let j : Fin k := ⟨m.val, hmk⟩
  have hjc : j.castSucc = m := by
    apply Fin.ext
    rfl
  have hjsm : j.succ ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val + 1 = m.val at hv
    omega
  have hjdown : t j.succ < t j.castSucc := by
    rw [hjc]
    exact lt_of_le_of_ne (hmax j.succ) (hinj.ne hjsm)
  have hjleaf := hleaf j hjdown
  have hsecond : ∀ l : Fin (k + 1), l ≠ m → t l ≤ t j.succ :=
    second_max_bound t hinj j.succ m hmax (by
      intro l
      simpa only [hjc] using (hclear j hjleaf l).2)
  have hmnext : m.val + 1 < k := by
    by_contra h
    have he : j = (⟨k - 1, by omega⟩ : Fin k) := by
      apply Fin.ext
      change m.val = k - 1
      omega
    exact hlast (he ▸ hjleaf)
  let i : Fin k := ⟨m.val + 1, hmnext⟩
  have hic : i.castSucc = j.succ := by
    apply Fin.ext
    rfl
  have hism : i.succ ≠ m := by
    intro he
    have hv := congrArg Fin.val he
    change m.val + 1 + 1 = m.val at hv
    omega
  have hisj : i.succ ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    change m.val + 1 + 1 = m.val + 1 at hv
    omega
  have hidown : t i.succ < t i.castSucc := by
    rw [hic]
    exact lt_of_le_of_ne (hsecond i.succ hism) (hinj.ne hisj)
  have hileaf := hleaf i hidown
  have hadj : j.val + 1 = i.val := rfl
  exact hnext j i hadj ⟨hjleaf, hileaf⟩

end
end SM.FiniteLineOrder

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
variable {n : ℕ} [NeZero n]

/-- Both assertions of source pf:line-gap for every actual selected collinear
list in a weak polygon, using its exact endpoint-normalized sign ratios.
The negative assertion requires both endpoints of the physical root word. -/
theorem silent_line_gap (hn : 3 ≤ n) {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (k : ℕ) (hk : 2 ≤ k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hline : ∀ l, boundaryWord P g (r l) = p + t l • ω) :
    (∃ j : Fin k, lineGapEpsilon t j = 1 ∧
      2 ≤ (r j.succ).val - (r j.castSucc).val) ∧
    ((r 0).val = 0 → (r (Fin.last k)).val = n - 1 →
      ∃ j : Fin k, lineGapEpsilon t j = -1 ∧
        2 ≤ (r j.succ).val - (r j.castSucc).val) := by
  have hinj := weak_line_coordinate_injective hP g r hr p ω t hline
  have hd := selected_endpoint_difference_nonzero (by omega : 0 < k) t hinj
  let u := normalizedLineCoordinate t
  let p' := p + t 0 • ω
  let ω' := (t (Fin.last k) - t 0) • ω
  have hu : ∀ l, boundaryWord P g (r l) = p' + u l • ω' := by
    intro l
    exact (hline l).trans (normalizedLineCoordinate_representation p ω t hd l)
  have hui : Function.Injective u := normalizedLineCoordinate_injective t hinj hd
  have hend : u 0 < u (Fin.last k) := by
    change normalizedLineCoordinate t 0 < normalizedLineCoordinate t (Fin.last k)
    rw [normalizedLineCoordinate_first, normalizedLineCoordinate_last t hd]
    norm_num
  let leaf : Fin k → Prop := fun j => (r j.succ).val = (r j.castSucc).val + 1
  have hclear : ∀ j : Fin k, leaf j → ∀ l : Fin (k + 1),
      ¬ (u j.castSucc < u l ∧ u l < u j.succ) ∧
      ¬ (u j.succ < u l ∧ u l < u j.castSucc) :=
    fun j hj l => weak_line_selection_clear hP g r hr p' ω' u hu j hj l
  have hnext : ∀ j l : Fin k, j.val + 1 = l.val → ¬ (leaf j ∧ leaf l) :=
    fun j l hjl => weak_line_selection_no_successive_leaves hP g r p' ω' u hu j l hjl
  have hlength (j : Fin k) (hj : ¬ leaf j) :
      2 ≤ (r j.succ).val - (r j.castSucc).val := by
    have hpos : r j.castSucc < r j.succ := hr Fin.castSucc_lt_succ
    change (r j.castSucc).val < (r j.succ).val at hpos
    change ¬ ((r j.succ).val = (r j.castSucc).val + 1) at hj
    omega
  constructor
  · obtain ⟨j, hj, hl⟩ := FiniteLineOrder.exists_increasing_nonleaf_gap
      k hk u hui leaf hend hclear hnext
    exact ⟨j, (lineGapEpsilon_positive t j).mpr hj, hlength j hl⟩
  · intro hfirst hlast
    have hclose : ∀ l, ¬ (u 0 < u l ∧ u l < u (Fin.last k)) :=
      weak_line_selection_root_clear hP g r hr p' ω' u hu hfirst hlast
    have hf : ¬ leaf ⟨0, by omega⟩ :=
      weak_line_selection_first_not_leaf hP g (by omega) r p' ω' u hu hfirst hlast
    have hh : ¬ leaf ⟨k - 1, by omega⟩ :=
      weak_line_selection_last_not_leaf hP g (by omega) r p' ω' u hu hfirst hlast
    obtain ⟨j, hj, hl⟩ := FiniteLineOrder.exists_decreasing_nonleaf_gap
      k hk u hui leaf hend hclear hnext hclose hf hh
    exact ⟨j, (lineGapEpsilon_negative t j).mpr hj, hlength j hl⟩

/-- The source lemma applied directly to vanishing actual determinants.
The printed distinct line coordinates are constructed from the selected
points themselves; no affine-data oracle is required of the caller. -/
theorem silent_line_gap_of_collinear (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (k : ℕ) (hk : 2 ≤ k)
    (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0) :
    Function.Injective (selectedLineCoordinate P g r) ∧
    selectedLineCoordinate P g r 0 = 0 ∧
    selectedLineCoordinate P g r (Fin.last k) = 1 ∧
    (∃ j : Fin k, lineGapEpsilon (selectedLineCoordinate P g r) j = 1 ∧
      2 ≤ (r j.succ).val - (r j.castSucc).val) ∧
    ((r 0).val = 0 → (r (Fin.last k)).val = n - 1 →
      ∃ j : Fin k, lineGapEpsilon (selectedLineCoordinate P g r) j = -1 ∧
        2 ≤ (r j.succ).val - (r j.castSucc).val) := by
  have hdata := weak_selected_line_coordinates hP g (by omega : 0 < k) r hr hcol
  exact ⟨hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2,
    silent_line_gap hn hP g k hk r hr (boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))
      (selectedLineCoordinate P g r) hdata.2.1⟩

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
  lower_middle := lt_of_le_of_lt (hr.monotone (by change 0 ≤ j.val; omega)) hleft
  middle_upper := lt_of_lt_of_le hright (hr.monotone (by change j.val + 1 ≤ k; omega))

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
      (boundaryWord P g (r (Fin.last k))) : ℤ) : R) =
    ((lineGapEpsilon t j : ℤ) : R) *
      ((pointFarSign (boundaryWord P g (r j.castSucc)) (boundaryWord P g u)
        (boundaryWord P g (r j.succ)) : ℤ) : R)
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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A zero rational geometric far entry is exactly collinearity. The
change from reversed far orientation to the endpoint-line determinant
only negates that determinant and does not change its zero set. -/
theorem rational_geometric_far_zero_iff (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := ℚ) P g t = 0 ↔
      det (boundaryWord P g t.middle - boundaryWord P g t.lower)
        (boundaryWord P g t.upper - boundaryWord P g t.lower) = 0 := by
  have hs (s : SignType) : ((s : ℤ) : ℚ) = 0 ↔ s = 0 := by
    cases s <;> norm_num
  unfold geometricBoundaryArray
  rw [hs, chi, sign_eq_zero_iff]
  change det (boundaryWord P g t.middle - boundaryWord P g t.upper)
      (boundaryWord P g t.lower - boundaryWord P g t.upper) = 0 ↔ _
  have hd : det (boundaryWord P g t.middle - boundaryWord P g t.upper)
      (boundaryWord P g t.lower - boundaryWord P g t.upper) =
      -det (boundaryWord P g t.middle - boundaryWord P g t.lower)
        (boundaryWord P g t.upper - boundaryWord P g t.lower) := by
    dsimp [det]
    ring
  rw [hd, neg_eq_zero]

/-- If every selected top cut is silent, every point in the actual
composition cut list lies on its endpoint line. Endpoints are included
explicitly, and no independence of determinant differentials is used. -/
theorem silent_composition_cuts_collinear (P : LabelledTuple n) (g : ZMod n)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∀ l, det (boundaryWord P g (π.cut l) - boundaryWord P g (π.cut 0))
      (boundaryWord P g (π.cut (Fin.last π.parts)) - boundaryWord P g (π.cut 0)) = 0 := by
  intro l
  by_cases hfirst : l = 0
  · subst l
    simp [det]
  by_cases hlast : l = Fin.last π.parts
  · subst l
    simp [det, mul_comm]
  have hlo : 0 < l.val := by
    by_contra h
    apply hfirst
    apply Fin.ext
    change l.val = 0
    omega
  have hhi : l.val < π.parts := by
    have hv := l.isLt
    by_contra h
    apply hlast
    apply Fin.ext
    change l.val = π.parts
    omega
  let j : Fin (π.parts - 1) := ⟨l.val - 1, by omega⟩
  have hm : π.interiorPosition j = π.cut l := by
    unfold IntervalComposition.interiorPosition
    congr 1
    apply Fin.ext
    change (l.val - 1) + 1 = l.val
    omega
  have hd := (rational_geometric_far_zero_iff P g (π.farTriple j)).mp (hzero j)
  change det (boundaryWord P g (π.interiorPosition j) - boundaryWord P g I.left)
    (boundaryWord P g I.right - boundaryWord P g I.left) = 0 at hd
  rw [hm] at hd
  rw [π.first, π.last]
  exact hd

/-- Every nonempty silent selection has a positive gap of at least two
leaves in the actual composition, ready for its zero inverse-coordinate
factor. The rational zero array supplies the collinearity premise. -/
theorem silent_composition_positive_gap (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) {I : BoundaryInterval n}
    (π : IntervalComposition I) (hparts : 2 ≤ π.parts)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∃ j : Fin π.parts, lineGapEpsilon (selectedLineCoordinate P g π.cut) j = 1 ∧
      2 ≤ (π.part j).leaves := by
  have h := silent_line_gap_of_collinear hn hP g π.parts hparts π.cut π.strict
    (silent_composition_cuts_collinear P g π hzero)
  exact h.2.2.2.1

/-- The negative gap assertion is used only on the full physical root
interval; the source's endpoint condition is discharged by π.first/last. -/
theorem silent_composition_full_negative_gap (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (π : IntervalComposition (fullBoundaryInterval hn))
    (hparts : 2 ≤ π.parts)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∃ j : Fin π.parts, lineGapEpsilon (selectedLineCoordinate P g π.cut) j = -1 ∧
      2 ≤ (π.part j).leaves := by
  have h := silent_line_gap_of_collinear hn hP g π.parts hparts π.cut π.strict
    (silent_composition_cuts_collinear P g π hzero)
  apply h.2.2.2.2
  · rw [π.first]
    rfl
  · rw [π.last]
    rfl

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- Scaling a far array scales its fixed-endpoint positional value, also
outside the interval where both values are defined to be zero. -/
theorem intervalFarValue_left_mul (η : R) (H : TripleArray n R)
    (I : BoundaryInterval n) (u : Fin n) :
    intervalFarValue (fun t => η * H t) I u = η * intervalFarValue H I u := by
  by_cases h : I.left < u ∧ u < I.right <;> simp [intervalFarValue, h]

/-- Every actual interior cut of every actual selected gap has the source
outer-to-gap far-array identity. All line coordinates and nonzero endpoint
differences are derived from the actual rational silent top cuts and WeakGeneric. -/
theorem silent_gap_intervalFarValue {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (σ : IntervalComposition (π.part k)) (j : Fin (σ.parts - 1)) :
    intervalFarValue (geometricBoundaryArray (R := R) P g) I (σ.interiorPosition j) =
      ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
        geometricBoundaryArray P g (σ.farTriple j) := by
  have hl : π.cut k.castSucc < σ.interiorPosition j := (σ.farTriple j).lower_middle
  have hr : σ.interiorPosition j < π.cut k.succ := (σ.farTriple j).middle_upper
  have hp := π.part_bounds k
  have hb : I.left < σ.interiorPosition j ∧ σ.interiorPosition j < I.right :=
    ⟨lt_of_le_of_lt hp.1 hl, lt_of_lt_of_le hr hp.2⟩
  have h := weak_selected_gap_far_array_of_collinear (R := R) hP g π.parts_pos
    π.cut π.strict (silent_composition_cuts_collinear P g π hzero)
    k (σ.interiorPosition j) hl hr
  have hout : selectedOuterCutTriple π.cut π.strict k (σ.interiorPosition j) hl hr =
      (⟨I.left, σ.interiorPosition j, I.right, hb.1, hb.2⟩ : IncreasingBoundaryTriple n) := by
    apply IncreasingBoundaryTriple.eq_of_entries
    · exact π.first
    · rfl
    · exact π.last
  have hgap : selectedGapCutTriple π.cut k (σ.interiorPosition j) hl hr = σ.farTriple j := by
    apply IncreasingBoundaryTriple.eq_of_entries <;> rfl
  rw [hout, hgap] at h
  unfold intervalFarValue
  rw [dif_pos hb]
  exact h

variable [Invertible (2 : R)]

/-- The complete scalar cut weight, including its negative sign and half,
uses the same source epsilon and the actual inner far triple. Zero far
entries are allowed and are never divided out. -/
theorem silent_gap_intervalFarCutWeight {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (σ : IntervalComposition (π.part k)) (j : Fin (σ.parts - 1)) (η : R) :
    intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I (σ.interiorPosition j) =
      -(η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
        geometricBoundaryArray P g (σ.farTriple j)) * ⅟ (2 : R) := by
  unfold intervalFarCutWeight
  rw [intervalFarValue_left_mul, silent_gap_intervalFarValue hP g π hzero k σ j]
  ring

/-- All inner cut factors and all actual child coordinates agree termwise.
Unary inner compositions retain both their empty cut product and sole child. -/
theorem silent_gap_positionCutSummand {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (σ : IntervalComposition (π.part k))
    (η : R) (X : IntervalArray n R) :
    IntervalComposition.positionCutSummand
        (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I) X σ =
      σ.nearFarWeight 0
        (fun t => η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
          geometricBoundaryArray P g t) * ∏ j : Fin σ.parts, X (σ.part j) := by
  unfold IntervalComposition.positionCutSummand IntervalComposition.nearFarWeight
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [Pi.zero_apply, zero_sub]
  exact silent_gap_intervalFarCutWeight hP g π hzero k σ j η

/-- Every gap sum in the positional top decomposition is exactly the
geometric far transform with the source's eta-times-epsilon multiplier.
Every raw inner composition is retained, including a one-leaf gap and
compositions containing further silent cuts with zero factors. -/
theorem silent_gap_positionCutSum {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0)
    (k : Fin π.parts) (η : R) (X : IntervalArray n R) :
    (∑ σ : IntervalComposition (π.part k),
      IntervalComposition.positionCutSummand
        (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I) X σ) =
      farTransform
        (fun t => η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
          geometricBoundaryArray P g t) X (π.part k) := by
  unfold farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro σ _
  exact silent_gap_positionCutSummand hP g π hzero k σ η X

end
end SM

#print axioms SM.intervalFarValue_left_mul
#print axioms SM.silent_gap_intervalFarValue
#print axioms SM.silent_gap_intervalFarCutWeight
#print axioms SM.silent_gap_positionCutSummand
#print axioms SM.silent_gap_positionCutSum
