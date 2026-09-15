import SM.Farout
import Mathlib.Algebra.MvPolynomial.Invertible
import SM.EuclideanPlane
import SM.WeakGeometry
import SM.NearFarFactorization
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic
import SM.PlaneTreeFormal
import SM.ConsecutiveTriples
import SM.CriticalFarOccurrence
import Mathlib.Algebra.MvPolynomial.Eval
import SM.SinglePointTriple
import SM.CriticalSourceResponse

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


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The empty selection is the unique unary outer composition. Its gap
sum is the whole zero-specialized top transform. -/
theorem topFar_single_summand (H U : TripleArray n R) (X : IntervalArray n R)
    (I : BoundaryInterval n) :
    (∏ x ∈ (IntervalComposition.single I).cutSet.interior.val, intervalFarCutWeight U I x) *
      (∏ k : Fin (IntervalComposition.single I).parts,
        ∑ σ : IntervalComposition ((IntervalComposition.single I).part k),
          IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ) =
      farTransform H X I := by
  have hp : (∏ x ∈ (IntervalComposition.single I).cutSet.interior.val,
      intervalFarCutWeight U I x) = 1 := by
    rw [← (IntervalComposition.single I).prod_interior_positions]
    change (∏ j : Fin 0, intervalFarCutWeight U I
      ((IntervalComposition.single I).interiorPosition j)) = 1
    exact Fin.prod_univ_zero _
  rw [hp, one_mul]
  have hg := IntervalComposition.single_product
    (fun J : BoundaryInterval n => ∑ σ : IntervalComposition J,
      IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ) I
  rw [hg]
  exact (farTransform_positionCutSum H X I).symm

/-- A purely algebraic cancellation principle for the exact top expansion.
The explicit hypothesis concerns every nonunary contribution; geometric
consumers must prove it, rather than assume formal constancy. -/
theorem farTransform_add_eq_of_nonunary_zero (H U : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n)
    (hzero : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      (∏ x ∈ π.cutSet.interior.val, intervalFarCutWeight U I x) *
        (∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k),
          IntervalComposition.positionCutSummand (intervalFarCutWeight H I) X σ) = 0) :
    farTransform (H + U) X I = farTransform H X I := by
  classical
  rw [farTransform_add_decomposition]
  rw [Finset.sum_eq_single (IntervalComposition.single I)]
  · exact topFar_single_summand H U X I
  · intro π _ hπ
    apply hzero π
    have hp := π.parts_pos
    have hne : π.parts ≠ 1 := fun he => hπ (π.eq_single_of_parts_eq_one he)
    omega
  · simp

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Exact top cancellation with fixed geometric inverse coordinates.
The explicit gap hypothesis will be discharged by the positive/full-root
negative source gap lemmas in the following two theorems. -/
theorem silent_scaled_top_eq {P : LabelledTuple n} (hP : WeakGeneric P) (g : ZMod n)
    (I : BoundaryInterval n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) (η : R)
    (hgap : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      (∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) →
      ∃ k : Fin π.parts,
        η * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) = 1 ∧
          2 ≤ (π.part k).leaves) :
    farTransform (fun t => η * (geometricBoundaryArray P g t + U t))
      (farOnlyCoordinates (geometricBoundaryArray P g)) I =
    farTransform (fun t => η * geometricBoundaryArray P g t)
      (farOnlyCoordinates (geometricBoundaryArray P g)) I := by
  classical
  have hs : (fun t => η * (geometricBoundaryArray P g t + U t)) =
      (fun t => η * geometricBoundaryArray P g t) + (fun t => η * U t) := by
    funext t
    exact mul_add _ _ _
  rw [hs]
  apply farTransform_add_eq_of_nonunary_zero
  intro π hparts
  by_cases hz : ∀ j : Fin (π.parts - 1),
      geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0
  · obtain ⟨k, hε, hlength⟩ := hgap π hparts hz
    have hf : (∑ σ : IntervalComposition (π.part k),
        IntervalComposition.positionCutSummand
          (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I)
          (farOnlyCoordinates (geometricBoundaryArray P g)) σ) = 0 := by
      rw [silent_gap_positionCutSum hP g π hz k η]
      have he : (fun t => η *
          ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) *
            geometricBoundaryArray P g t) = geometricBoundaryArray P g := by
        funext t
        rw [hε, one_mul]
      rw [he]
      exact farOnly_nonleaf_E (geometricBoundaryArray P g) (π.part k) hlength
    have hp : (∏ k : Fin π.parts, ∑ σ : IntervalComposition (π.part k),
        IntervalComposition.positionCutSummand
          (intervalFarCutWeight (fun t => η * geometricBoundaryArray P g t) I)
          (farOnlyCoordinates (geometricBoundaryArray P g)) σ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hf
    rw [hp, mul_zero]
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    have hu := hU (π.farTriple j) hj
    have hw : intervalFarCutWeight (fun t => η * U t) I (π.interiorPosition j) = 0 := by
      unfold intervalFarCutWeight
      rw [intervalFarValue_interior, hu, mul_zero, neg_zero, zero_mul]
    have hp : (∏ x ∈ π.cutSet.interior.val,
        intervalFarCutWeight (fun t => η * U t) I x) = 0 :=
      Finset.prod_eq_zero (π.interiorPosition_mem j) hw
    rw [hp, zero_mul]

/-- All forward top coordinates are unchanged by any simultaneous
perturbation supported on the rational geometric zero entries. -/
theorem silent_supported_forward_top (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0)
    (I : BoundaryInterval n) :
    farTransform (geometricBoundaryArray P g + U)
      (farOnlyCoordinates (geometricBoundaryArray P g)) I =
      farTransform (geometricBoundaryArray P g) (farOnlyCoordinates (geometricBoundaryArray P g)) I := by
  have hg : ∀ π : IntervalComposition I, 2 ≤ π.parts →
      (∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) →
      ∃ k : Fin π.parts,
        (1 : R) * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) = 1 ∧
          2 ≤ (π.part k).leaves := by
    intro π hp hz
    obtain ⟨k, he, hl⟩ := silent_composition_positive_gap hn hP g π hp hz
    exact ⟨k, by simp [he], hl⟩
  have h := silent_scaled_top_eq hP g I U hU 1 hg
  have ha : (fun t => (1 : R) * (geometricBoundaryArray P g t + U t)) =
      geometricBoundaryArray P g + U := by funext t; exact one_mul _
  have hb : (fun t => (1 : R) * geometricBoundaryArray P g t) =
      geometricBoundaryArray P g := by funext t; exact one_mul _
  rw [ha, hb] at h
  exact h

/-- Reversed-far top cancellation uses the physical root interval and
the negative gap supplied there. No arbitrary-open-interval claim is made. -/
theorem silent_supported_reversed_full_top (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) :
    farTransform (-(geometricBoundaryArray P g + U))
      (farOnlyCoordinates (geometricBoundaryArray P g)) (fullBoundaryInterval hn) =
      farTransform (-geometricBoundaryArray P g)
        (farOnlyCoordinates (geometricBoundaryArray P g)) (fullBoundaryInterval hn) := by
  have hg : ∀ π : IntervalComposition (fullBoundaryInterval hn), 2 ≤ π.parts →
      (∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) →
      ∃ k : Fin π.parts,
        (-1 : R) * ((lineGapEpsilon (selectedLineCoordinate P g π.cut) k : ℤ) : R) = 1 ∧
          2 ≤ (π.part k).leaves := by
    intro π hp hz
    obtain ⟨k, he, hl⟩ := silent_composition_full_negative_gap hn hP g π hp hz
    exact ⟨k, by simp [he], hl⟩
  have h := silent_scaled_top_eq hP g (fullBoundaryInterval hn) U hU (-1) hg
  have ha : (fun t => (-1 : R) * (geometricBoundaryArray P g t + U t)) =
      -(geometricBoundaryArray P g + U) := by funext t; exact neg_one_mul _
  have hb : (fun t => (-1 : R) * geometricBoundaryArray P g t) =
      -geometricBoundaryArray P g := by funext t; exact neg_one_mul _
  rw [ha, hb] at h
  exact h

/-- Uniqueness of the actual triangular inverse converts the fixed-child
top equations into equality of the complete inverse arrays. -/
theorem silent_supported_coordinates (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) :
    farOnlyCoordinates (geometricBoundaryArray P g + U) =
      farOnlyCoordinates (geometricBoundaryArray P g) := by
  symm
  apply nearFar_solution_unique 0 (geometricBoundaryArray P g + U)
  funext I
  change farTransform (geometricBoundaryArray P g + U)
    (farOnlyCoordinates (geometricBoundaryArray P g)) I = boundaryUnitArray I
  rw [silent_supported_forward_top hn hP g U hU I, farOnlyCoordinates_equation]

/-- The complete reversed-far root output is unchanged as well, after
the full inverse array has been shown equal. -/
theorem silent_supported_output (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (U : TripleArray n R)
    (hU : ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 → U t = 0) :
    farOnlyOutput (geometricBoundaryArray P g + U) (fullBoundaryInterval hn) =
      farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn) := by
  unfold farOnlyOutput
  rw [silent_supported_coordinates hn hP g U hU]
  exact silent_supported_reversed_full_top hn hP g U hU

end
end SM


namespace SM

noncomputable section
universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v}
  [CommRing R] [CommRing S] [Invertible (2 : R)] [Invertible (2 : S)]

/-- The designated inverses of two are respected by every ring map,
including maps into polynomial rings. No cancellation assumption is needed. -/
theorem ringHom_map_half (f : R →+* S) : f (⅟ (2 : R)) = ⅟ (2 : S) := by
  have hprod : f (⅟ (2 : R)) * (2 : S) = 1 := by
    calc
      _ = f (⅟ (2 : R) * 2) := by rw [map_mul, map_ofNat]
      _ = 1 := by rw [invOf_mul_self, map_one]
  calc
    f (⅟ (2 : R)) = f (⅟ (2 : R)) * ((2 : S) * ⅟ (2 : S)) := by
      rw [mul_invOf_self, mul_one]
    _ = (f (⅟ (2 : R)) * (2 : S)) * ⅟ (2 : S) := by rw [mul_assoc]
    _ = ⅟ (2 : S) := by rw [hprod, one_mul]

theorem map_nearFarWeight (f : R →+* S) (D H : TripleArray n R)
    {I : BoundaryInterval n} (π : IntervalComposition I) :
    f (π.nearFarWeight D H) = π.nearFarWeight (fun t => f (D t)) (fun t => f (H t)) := by
  simp only [IntervalComposition.nearFarWeight, map_prod, map_mul, map_sub,
    ringHom_map_half]

theorem map_boundaryUnitArray (f : R →+* S) (I : BoundaryInterval n) :
    f (boundaryUnitArray (R := R) I) = boundaryUnitArray (R := S) I := by
  by_cases h : I.right.val = I.left.val + 1 <;> simp [boundaryUnitArray, h]

/-- Naturality preserves the complete sum, including its unary term and
all actual child intervals. -/
theorem map_nearFarTransform (f : R →+* S) (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarTransform D H X I) = nearFarTransform (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (X J)) I := by
  simp only [nearFarTransform, map_sum, map_mul, map_prod, map_nearFarWeight]

theorem map_farTransform (f : R →+* S) (H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    f (farTransform H X I) = farTransform (fun t => f (H t)) (fun J => f (X J)) I := by
  have hz : (fun t : IncreasingBoundaryTriple n => f ((0 : TripleArray n R) t)) =
      (0 : TripleArray n S) := by funext t; exact map_zero f
  have h := map_nearFarTransform f 0 H X I
  rw [hz] at h
  exact h

/-- The existing well-founded inverse recursion commutes with every ring
map, after mapping its actual near/far weights. -/
theorem map_nearFarInverse (f : R →+* S) (D H : TripleArray n R)
    (Y : IntervalArray n R) (I : BoundaryInterval n) :
    f (nearFarInverse D H Y I) = nearFarInverse (fun t => f (D t))
      (fun t => f (H t)) (fun J => f (Y J)) I := by
  simpa only [nearFarInverse, map_nearFarWeight] using
    map_triangularInverse f (fun _ π => π.nearFarWeight D H) Y I

theorem map_farOnlyCoordinates (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyCoordinates H I) = farOnlyCoordinates (fun t => f (H t)) I := by
  have hz : (fun t : IncreasingBoundaryTriple n => f ((0 : TripleArray n R) t)) =
      (0 : TripleArray n S) := by funext t; exact map_zero f
  have he : (fun J : BoundaryInterval n => f (boundaryUnitArray (R := R) J)) =
      boundaryUnitArray (R := S) := funext (map_boundaryUnitArray f)
  have h := map_nearFarInverse f 0 H boundaryUnitArray I
  rw [hz, he] at h
  exact h

theorem map_farOnlyOutput (f : R →+* S) (H : TripleArray n R)
    (I : BoundaryInterval n) :
    f (farOnlyOutput H I) = farOnlyOutput (fun t => f (H t)) I := by
  have hn : (fun t => f ((-H) t)) = -(fun t => f (H t)) := by
    funext t
    exact map_neg f (H t)
  have hc : (fun J => f (farOnlyCoordinates H J)) = farOnlyCoordinates (fun t => f (H t)) :=
    funext (map_farOnlyCoordinates f H)
  have h := map_farTransform f (-H) (farOnlyCoordinates H) I
  rw [hn, hc] at h
  exact h

end
end SM


namespace SM

noncomputable section
universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- Exactly one independent variable for each zero entry of the fixed
far array. No realizability relation is imposed on this variable type. -/
def SilentFarEntry (H0 : TripleArray n R) := {t : IncreasingBoundaryTriple n // H0 t = 0}

def silentFarArray (H0 : TripleArray n R) : TripleArray n (MvPolynomial (SilentFarEntry H0) R) := by
  classical
  exact fun t => if h : H0 t = 0 then MvPolynomial.X ⟨t, h⟩ else MvPolynomial.C (H0 t)

/-- The variable part vanishes identically at every initially nonzero entry. -/
def silentFarVariable (H0 : TripleArray n R) : TripleArray n (MvPolynomial (SilentFarEntry H0) R) := by
  classical
  exact fun t => if h : H0 t = 0 then MvPolynomial.X ⟨t, h⟩ else 0

theorem silentFarArray_eq_constant_add_variable (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) :
    silentFarArray H0 t = MvPolynomial.C (H0 t) + silentFarVariable H0 t := by
  by_cases h : H0 t = 0 <;> simp [silentFarArray, silentFarVariable, h]

theorem silentFarArray_at_zero_entry (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : H0 t = 0) :
    silentFarArray H0 t = MvPolynomial.X (⟨t, h⟩ : SilentFarEntry H0) := by
  exact dif_pos h

theorem silentFarArray_at_nonzero_entry (H0 : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : H0 t ≠ 0) :
    silentFarArray H0 t = MvPolynomial.C (H0 t) := by
  simp [silentFarArray, h]

def silentFarZeroHom (H0 : TripleArray n R) : MvPolynomial (SilentFarEntry H0) R →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)

theorem silentFarZeroHom_array (H0 : TripleArray n R) :
    (fun t => silentFarZeroHom H0 (silentFarArray H0 t)) = H0 := by
  funext t
  by_cases h : H0 t = 0
  · rw [silentFarArray_at_zero_entry H0 t h]
    change MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)
      (MvPolynomial.X (⟨t, h⟩ : SilentFarEntry H0)) = H0 t
    rw [MvPolynomial.eval₂Hom_X', h]
  · rw [silentFarArray_at_nonzero_entry H0 t h]
    exact MvPolynomial.eval₂Hom_C (RingHom.id R) (fun _ => 0) (H0 t)

variable [Invertible (2 : R)]

/-- The numeral two in the polynomial ring inherits its actual inverse
through the constant ring map. This supplies an instance, not a new premise. -/
local instance silentPolynomialTwoInvertible (σ : Type*) :
    Invertible (2 : MvPolynomial σ R) := by
  have h : MvPolynomial.C (2 : R) = (2 : MvPolynomial σ R) := map_ofNat MvPolynomial.C 2
  exact h ▸ MvPolynomial.invertibleC σ (2 : R)

/-- The fixed child coordinates from the source, lifted as constants. -/
def constantFarCoordinates (H0 : TripleArray n R) :
    IntervalArray n (MvPolynomial (SilentFarEntry H0) R) :=
  fun I => MvPolynomial.C (farOnlyCoordinates H0 I)

/-- Lifting c0 through the constant ring map preserves its defining
zero-specialized equation on every interval. -/
theorem constantFarCoordinates_equation (H0 : TripleArray n R) :
    farTransform (fun t => MvPolynomial.C (H0 t)) (constantFarCoordinates H0) =
      boundaryUnitArray := by
  funext I
  have h := map_farTransform (MvPolynomial.C : R →+* MvPolynomial (SilentFarEntry H0) R)
    H0 (farOnlyCoordinates H0) I
  rw [congrFun (farOnlyCoordinates_equation H0) I, map_boundaryUnitArray] at h
  exact h.symm

theorem constantFarCoordinates_inverse (H0 : TripleArray n R) :
    constantFarCoordinates H0 = farOnlyCoordinates (fun t => MvPolynomial.C (H0 t)) := by
  funext I
  exact map_farOnlyCoordinates
    (MvPolynomial.C : R →+* MvPolynomial (SilentFarEntry H0) R) H0 I

/-- Evaluating all formal variables at zero recovers c0. This is only
specialization; it does not assert independence from those variables. -/
theorem silentFarCoordinates_zero_specialization (H0 : TripleArray n R)
    (I : BoundaryInterval n) :
    silentFarZeroHom H0 (farOnlyCoordinates (silentFarArray H0) I) = farOnlyCoordinates H0 I := by
  have h := map_farOnlyCoordinates (silentFarZeroHom H0) (silentFarArray H0) I
  rw [silentFarZeroHom_array] at h
  exact h

/-- Zero specialization also commutes with the full reversed-far output.
Formal constancy is a separate, still necessary proof obligation. -/
theorem silentFarOutput_zero_specialization (H0 : TripleArray n R)
    (I : BoundaryInterval n) :
    silentFarZeroHom H0 (farOnlyOutput (silentFarArray H0) I) = farOnlyOutput H0 I := by
  have h := map_farOnlyOutput (silentFarZeroHom H0) (silentFarArray H0) I
  rw [silentFarZeroHom_array] at h
  exact h

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Geometric arrays use integer signs, so every ring map transports
their values exactly, including zero entries. -/
theorem map_geometricBoundaryArray {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : LabelledTuple n) (g : ZMod n) :
    (fun t => f (geometricBoundaryArray (R := R) P g t)) =
      geometricBoundaryArray (R := S) P g := by
  funext t
  exact map_intCast f _

attribute [local instance] silentPolynomialTwoInvertible

/-- The exact formal replacement array splits into the geometric constant
array and the independent variables at its zero entries. -/
theorem silentFarArray_geometric_split (P : LabelledTuple n) (g : ZMod n) :
    silentFarArray (geometricBoundaryArray (R := ℚ) P g) =
      geometricBoundaryArray P g + silentFarVariable (geometricBoundaryArray (R := ℚ) P g) := by
  funext t
  rw [silentFarArray_eq_constant_add_variable]
  have h := congrFun (map_geometricBoundaryArray
    (MvPolynomial.C : ℚ →+* MvPolynomial
      (SilentFarEntry (geometricBoundaryArray (R := ℚ) P g)) ℚ) P g) t
  rw [h]
  rfl

theorem silentFarVariable_geometric_support (P : LabelledTuple n) (g : ZMod n) :
    ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 →
      silentFarVariable (geometricBoundaryArray (R := ℚ) P g) t = 0 := by
  intro t ht
  simp [silentFarVariable, ht]

/-- Full source pf:formal-cancellation. Every zero geometric far entry is
replaced by its own unrestricted polynomial variable. The complete inverse
array equals its constant zero-specialization, and the complete reversed-far
output agrees at the physical root. No realizability or independence of
zero-determinant differentials is required. -/
theorem formal_silent_cancellation (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) :
    farOnlyCoordinates (silentFarArray (geometricBoundaryArray (R := ℚ) P g)) =
      constantFarCoordinates (geometricBoundaryArray (R := ℚ) P g) ∧
    farOnlyOutput (silentFarArray (geometricBoundaryArray (R := ℚ) P g))
        (fullBoundaryInterval hn) =
      MvPolynomial.C (farOnlyOutput (geometricBoundaryArray (R := ℚ) P g)
        (fullBoundaryInterval hn)) := by
  let H0 := geometricBoundaryArray (R := ℚ) P g
  let C : ℚ →+* MvPolynomial (SilentFarEntry H0) ℚ := MvPolynomial.C
  have hcast : (fun t => C (H0 t)) = geometricBoundaryArray P g :=
    map_geometricBoundaryArray C P g
  have hU := silentFarVariable_geometric_support P g
  constructor
  · rw [silentFarArray_geometric_split,
      silent_supported_coordinates hn hP g (silentFarVariable H0) hU]
    have hc := constantFarCoordinates_inverse H0
    rw [hcast] at hc
    exact hc.symm
  · rw [silentFarArray_geometric_split,
      silent_supported_output hn hP g (silentFarVariable H0) hU]
    have ho := map_farOnlyOutput C H0 (fullBoundaryInterval hn)
    rw [hcast] at ho
    exact ho.symm

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
variable {n : ℕ} [NeZero n]

/-- Position in the source's increasing physical label order 1,...,n.
The source label n is represented by residue zero, and has position n-1. -/
def canonicalPosition (i : ZMod n) : Fin n := ⟨(i - 1).val, ZMod.val_lt _⟩

theorem canonical_label (k : Fin n) :
    boundaryIndex 0 k = ((k.val + 1 : ℕ) : ZMod n) := by
  simp [boundaryIndex]

theorem canonical_label_range (k : Fin n) : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ n := by
  have := k.isLt
  omega

@[simp] theorem boundaryIndex_canonicalPosition (i : ZMod n) :
    boundaryIndex 0 (canonicalPosition i) = i := by
  change 0 + ((i - 1).val : ZMod n) + 1 = i
  rw [ZMod.natCast_zmod_val]
  ring

@[simp] theorem canonicalPosition_boundaryIndex (k : Fin n) :
    canonicalPosition (boundaryIndex 0 k) = k := by
  apply boundaryIndex_injective 0
  exact boundaryIndex_canonicalPosition _

theorem canonicalPosition_injective : Function.Injective (canonicalPosition (n := n)) := by
  intro i j h
  have he := congrArg (boundaryIndex 0) h
  simpa only [boundaryIndex_canonicalPosition] using he

/-- Exact six-order sorting with parity, before any polynomial relations.
The three positions must be distinct; repeated ordered labels will be zero. -/
def sortTriplePositions (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IncreasingBoundaryTriple n × ℚ :=
  if hab' : a < b then
    if hbc' : b < c then (⟨a, b, c, hab', hbc'⟩, 1)
    else
      have hcb : c < b := lt_of_le_of_ne (le_of_not_gt hbc') hbc.symm
      if hac' : a < c then (⟨a, c, b, hac', hcb⟩, -1)
      else
        have hca : c < a := lt_of_le_of_ne (le_of_not_gt hac') hac.symm
        (⟨c, a, b, hca, hab'⟩, 1)
  else
    have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab') hab.symm
    if hac' : a < c then (⟨b, a, c, hba, hac'⟩, -1)
    else
      have hca : c < a := lt_of_le_of_ne (le_of_not_gt hac') hac.symm
      if hbc' : b < c then (⟨b, c, a, hbc', hca⟩, 1)
      else
        have hcb : c < b := lt_of_le_of_ne (le_of_not_gt hbc') hbc.symm
        (⟨c, b, a, hcb, hba⟩, -1)

theorem sortTriplePositions_sign (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (sortTriplePositions a b c hab hac hbc).2 = 1 ∨
      (sortTriplePositions a b c hab hac hbc).2 = -1 := by
  unfold sortTriplePositions
  split_ifs <;> simp

theorem sortTriplePositions_positionSet (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (sortTriplePositions a b c hab hac hbc).1.positionSet = {a, b, c} := by
  unfold sortTriplePositions
  split_ifs <;> ext x <;>
    simp [IncreasingBoundaryTriple.positionSet, or_comm, or_left_comm, or_assoc]

/-- Evaluation of the source variable X_(a+1,b+1,c+1), with a<b<c. -/
def canonicalTripleValue (P : LabelledTuple n) (t : IncreasingBoundaryTriple n) : ℚ :=
  ((chi P (boundaryIndex 0 t.lower) (boundaryIndex 0 t.middle)
    (boundaryIndex 0 t.upper) : ℤ) : ℚ)

/-- Alternation gives the exact rational sign for all six orders, for every
tuple, including collinear triples. No G1 hypothesis is used. -/
theorem sortTriplePositions_evaluation (P : LabelledTuple n) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((chi P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c) : ℤ) : ℚ) =
      (sortTriplePositions a b c hab hac hbc).2 *
        canonicalTripleValue P (sortTriplePositions a b c hab hac hbc).1 := by
  unfold sortTriplePositions
  split_ifs <;> simp only [canonicalTripleValue, one_mul, neg_one_mul]
  · rw [chi_swap_last P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c),
      SignType.coe_neg, Int.cast_neg, neg_neg]
  · rw [chi_cyclic P (boundaryIndex 0 b) (boundaryIndex 0 c) (boundaryIndex 0 a),
      chi_cyclic P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c)]
  · rw [chi_swap_first P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c),
      SignType.coe_neg, Int.cast_neg, neg_neg]
  · rw [chi_cyclic P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c)]
  · rw [chi_swap_outer P (boundaryIndex 0 a) (boundaryIndex 0 b) (boundaryIndex 0 c),
      SignType.coe_neg, Int.cast_neg, neg_neg]

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A canonical physical triple and its exact orientation parity. -/
def orderedTripleData (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    IncreasingBoundaryTriple n × ℚ :=
  sortTriplePositions (canonicalPosition i) (canonicalPosition j) (canonicalPosition k)
    (fun h => hij (canonicalPosition_injective h))
    (fun h => hik (canonicalPosition_injective h))
    (fun h => hjk (canonicalPosition_injective h))

theorem orderedTripleData_sign (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (orderedTripleData i j k hij hik hjk).2 = 1 ∨
      (orderedTripleData i j k hij hik hjk).2 = -1 :=
  sortTriplePositions_sign _ _ _ _ _ _

theorem orderedTripleData_vertexSet (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (orderedTripleData i j k hij hik hjk).1.vertexSet 0 = {i, j, k} := by
  unfold orderedTripleData IncreasingBoundaryTriple.vertexSet
  rw [sortTriplePositions_positionSet]
  simp only [Finset.image_insert, Finset.image_singleton, boundaryIndex_canonicalPosition]

theorem orderedTripleData_evaluation (P : LabelledTuple n) (i j k : ZMod n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((chi P i j k : ℤ) : ℚ) = (orderedTripleData i j k hij hik hjk).2 *
      canonicalTripleValue P (orderedTripleData i j k hij hik hjk).1 := by
  have h := sortTriplePositions_evaluation P (canonicalPosition i) (canonicalPosition j)
    (canonicalPosition k) (fun h => hij (canonicalPosition_injective h))
    (fun h => hik (canonicalPosition_injective h))
    (fun h => hjk (canonicalPosition_injective h))
  simpa only [boundaryIndex_canonicalPosition, orderedTripleData] using h

/-- Ordered chirotopes interpreted in the unrestricted polynomial ring.
Repeated labels are zero. Distinct labels give exactly one signed variable. -/
def formalOrderedChi (i j k : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  if h : i ≠ j ∧ i ≠ k ∧ j ≠ k then
    MvPolynomial.C (orderedTripleData i j k h.1 h.2.1 h.2.2).2 *
      MvPolynomial.X (orderedTripleData i j k h.1 h.2.1 h.2.2).1
  else 0

theorem formalOrderedChi_distinct (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    formalOrderedChi i j k = MvPolynomial.C (orderedTripleData i j k hij hik hjk).2 *
      MvPolynomial.X (orderedTripleData i j k hij hik hjk).1 := by
  simp only [formalOrderedChi, dif_pos (show i ≠ j ∧ i ≠ k ∧ j ≠ k from ⟨hij, hik, hjk⟩)]

theorem formalOrderedChi_repeated (i j k : ZMod n) (h : i = j ∨ i = k ∨ j = k) :
    formalOrderedChi i j k = 0 := by
  rcases h with rfl | rfl | rfl <;> simp [formalOrderedChi]

/-- Polynomial evaluation recovers every actual chirotope, including zero
values and repeated labels. This does not use realizability to identify
different polynomials. -/
theorem eval_formalOrderedChi (P : LabelledTuple n) (i j k : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (formalOrderedChi i j k) =
      ((chi P i j k : ℤ) : ℚ) := by
  classical
  by_cases h : i ≠ j ∧ i ≠ k ∧ j ≠ k
  · rw [formalOrderedChi_distinct i j k h.1 h.2.1 h.2.2,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact (orderedTripleData_evaluation P i j k h.1 h.2.1 h.2.2).symm
  · have he : i = j ∨ i = k ∨ j = k := by tauto
    rw [formalOrderedChi_repeated i j k he, map_zero]
    rcases he with rfl | rfl | rfl <;> simp

/-- The source's actual reversed boundary order for near/far entries. -/
def boundaryTripleData (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    IncreasingBoundaryTriple n × ℚ :=
  orderedTripleData (boundaryIndex g t.upper) (boundaryIndex g t.middle)
    (boundaryIndex g t.lower)
    (fun h => (ne_of_gt t.middle_upper) (boundaryIndex_injective g h))
    (fun h => (ne_of_gt (lt_trans t.lower_middle t.middle_upper)) (boundaryIndex_injective g h))
    (fun h => (ne_of_gt t.lower_middle) (boundaryIndex_injective g h))

theorem boundaryTripleData_vertexSet (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    (boundaryTripleData g t).1.vertexSet 0 = t.vertexSet g := by
  exact (orderedTripleData_vertexSet _ _ _ _ _ _).trans (t.vertexSet_reversed g).symm

theorem boundaryTripleData_injective (g : ZMod n) :
    Function.Injective (fun t : IncreasingBoundaryTriple n => (boundaryTripleData g t).1) := by
  intro t u h
  apply IncreasingBoundaryTriple.vertexSet_injective g
  have he := congrArg (IncreasingBoundaryTriple.vertexSet 0) h
  simpa only [boundaryTripleData_vertexSet] using he

def formalBoundaryChi (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  formalOrderedChi (boundaryIndex g t.upper) (boundaryIndex g t.middle)
    (boundaryIndex g t.lower)

theorem formalBoundaryChi_eq (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    formalBoundaryChi g t = MvPolynomial.C (boundaryTripleData g t).2 *
      MvPolynomial.X (boundaryTripleData g t).1 :=
  formalOrderedChi_distinct _ _ _ _ _ _

theorem eval_formalBoundaryChi (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    MvPolynomial.eval (canonicalTripleValue P) (formalBoundaryChi g t) =
      ((chi P (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) : ℤ) : ℚ) :=
  eval_formalOrderedChi P _ _ _

end
end SM


namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- The two formal triple variables sampled by one actual cut factor.
For a binary composition this is a singleton, not two independent variables. -/
def cutTripleSet (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    Finset (IncreasingBoundaryTriple n) := by
  classical
  exact {π.nearTriple k, π.farTriple k}

theorem mem_cutTripleSet (π : IntervalComposition I) (k : Fin (π.parts - 1))
    (t : IncreasingBoundaryTriple n) :
    t ∈ π.cutTripleSet k ↔ t = π.nearTriple k ∨ t = π.farTriple k := by
  classical
  simp only [cutTripleSet, Finset.mem_insert, Finset.mem_singleton]

/-- Distinct cut indices have different near triples, because their actual
middle cut positions differ under the strict cut map. -/
theorem nearTriple_injective (π : IntervalComposition I) : Function.Injective π.nearTriple := by
  intro k l h
  exact π.interiorPosition_injective (congrArg IncreasingBoundaryTriple.middle h)

/-- Near/far coincidence is exactly the binary case at the same cut.
The endpoint equalities force the first and last indices, not merely a
coincidence of geometric coordinates. -/
theorem nearTriple_eq_farTriple_iff (π : IntervalComposition I)
    (k l : Fin (π.parts - 1)) :
    π.nearTriple k = π.farTriple l ↔ π.parts = 2 ∧ k = l := by
  constructor
  · intro h
    have hl := congrArg IncreasingBoundaryTriple.lower h
    have hu := congrArg IncreasingBoundaryTriple.upper h
    change π.cut ⟨k.val, by have := k.isLt; omega⟩ = I.left at hl
    change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ = I.right at hu
    rw [← π.first] at hl
    rw [← π.last] at hu
    have hli := congrArg Fin.val (π.strict.injective hl)
    have hui := congrArg Fin.val (π.strict.injective hu)
    change k.val = 0 at hli
    change k.val + 2 = π.parts at hui
    refine ⟨by omega, ?_⟩
    exact π.interiorPosition_injective (congrArg IncreasingBoundaryTriple.middle h)
  · rintro ⟨hp, hkl⟩
    subst l
    have hk : k.val = 0 := by have := k.isLt; omega
    apply IncreasingBoundaryTriple.eq_of_entries
    · change π.cut ⟨k.val, by have := k.isLt; omega⟩ = I.left
      have he : (⟨k.val, by have := k.isLt; omega⟩ : Fin (π.parts + 1)) = 0 := by
        apply Fin.ext
        exact hk
      rw [he, π.first]
    · rfl
    · change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ = I.right
      have he : (⟨k.val + 2, by have := k.isLt; omega⟩ : Fin (π.parts + 1)) =
          Fin.last π.parts := by
        apply Fin.ext
        change k.val + 2 = π.parts
        omega
      rw [he, π.last]

/-- Every two distinct factors have disjoint triple-variable supports.
No three-or-more-parts assumption discards the binary or unary cases. -/
theorem cutTripleSet_disjoint (π : IntervalComposition I)
    {k l : Fin (π.parts - 1)} (hkl : k ≠ l) :
    Disjoint (π.cutTripleSet k) (π.cutTripleSet l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t htk htl
  rcases (π.mem_cutTripleSet k t).mp htk with hk | hk
  · rcases (π.mem_cutTripleSet l t).mp htl with hl | hl
    · exact hkl (π.nearTriple_injective (hk.symm.trans hl))
    · exact hkl ((π.nearTriple_eq_farTriple_iff k l).mp (hk.symm.trans hl)).2
  · rcases (π.mem_cutTripleSet l t).mp htl with hl | hl
    · exact hkl (((π.nearTriple_eq_farTriple_iff l k).mp (hl.symm.trans hk)).2.symm)
    · exact hkl (π.farTriple_injective (hk.symm.trans hl))

/-- Every sampled triple lies within its actual parent interval. -/
theorem cutTripleSet_bounds (π : IntervalComposition I) (k : Fin (π.parts - 1))
    {t : IncreasingBoundaryTriple n} (ht : t ∈ π.cutTripleSet k) :
    I.left ≤ t.lower ∧ t.upper ≤ I.right := by
  rcases (π.mem_cutTripleSet k t).mp ht with rfl | rfl
  · constructor
    · change I.left ≤ π.cut ⟨k.val, by have := k.isLt; omega⟩
      rw [← π.first]
      exact π.strict.monotone (Fin.zero_le _)
    · change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ ≤ I.right
      rw [← π.last]
      exact π.strict.monotone (Fin.le_last _)
  · exact ⟨le_rfl, le_rfl⟩

/-- The middle of either sampled triple is a genuine cut position of the
same composition, including when the near and far triples coincide. -/
theorem cutTripleSet_middle_mem (π : IntervalComposition I) (k : Fin (π.parts - 1))
    {t : IncreasingBoundaryTriple n} (ht : t ∈ π.cutTripleSet k) :
    t.middle ∈ π.cutSet.cuts := by
  classical
  have hm : π.interiorPosition k ∈ π.cutSet.cuts := by
    exact Finset.mem_image.mpr
      ⟨⟨k.val + 1, by have := k.isLt; omega⟩, Finset.mem_univ _, rfl⟩
  rcases (π.mem_cutTripleSet k t).mp ht with rfl | rfl
  · exact hm
  · exact hm

/-- A parent cut triple cannot fit inside any one actual child interval.
Such containment would put its middle cut strictly between two consecutive
cuts of that same composition. All endpoint inequalities are explicit. -/
theorem cutTripleSet_not_contained_in_part (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) {t : IncreasingBoundaryTriple n}
    (ht : t ∈ π.cutTripleSet k) (j : Fin π.parts) :
    ¬ ((π.part j).left ≤ t.lower ∧ t.upper ≤ (π.part j).right) := by
  intro h
  have hm := π.cutTripleSet_middle_mem k ht
  have hc := π.part_consecutive j
  exact hc.2.2 t.middle hm
    ⟨lt_of_le_of_lt h.1 t.lower_middle, lt_of_lt_of_le t.middle_upper h.2⟩

/-- An increasing triple can lie in at most one child interval. The possible
shared boundary endpoint between two children cannot contain its two distinct
extreme positions. No cut-membership assumption is imposed on this triple. -/
theorem triple_containing_part_unique (π : IntervalComposition I)
    (t : IncreasingBoundaryTriple n) {j k : Fin π.parts}
    (hj : (π.part j).left ≤ t.lower ∧ t.upper ≤ (π.part j).right)
    (hk : (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right) : j = k := by
  have ht : t.lower < t.upper := lt_trans t.lower_middle t.middle_upper
  rcases lt_trichotomy j k with h | h | h
  · have ho := π.part_order h
    have he : t.upper ≤ t.lower := le_trans hj.2 (le_trans ho hk.1)
    exact False.elim ((not_le_of_gt ht) he)
  · exact h
  · have ho := π.part_order h
    have he : t.upper ≤ t.lower := le_trans hk.2 (le_trans ho hj.1)
    exact False.elim ((not_le_of_gt ht) he)

end
end SM.IntervalComposition


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Rational gate identities are proved directly on all four nonzero sign
pairs; integer division is not transported through a cast. -/
theorem gate_pair_rational (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    (ordinaryGate d h hd hh : ℚ) = (1 / 2 : ℚ) * ((d : ℤ) - (h : ℤ)) ∧
    (rootGate d h hd hh : ℚ) = (1 / 2 : ℚ) * ((d : ℤ) + (h : ℤ)) := by
  cases d <;> cases h <;>
    first | exact (hd rfl).elim | exact (hh rfl).elim |
      norm_num [ordinaryGate, rootGate, signTheta]

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- Source ordinary half-difference, in independent canonical triple variables. -/
def tripleOrdinaryFactor (g : ZMod n) (k : Fin (π.parts - 1)) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) *
    (formalBoundaryChi g (π.nearTriple k) - formalBoundaryChi g (π.farTriple k))

/-- Source root half-sum, with the same physical root reading. -/
def tripleRootFactor (g : ZMod n) (k : Fin (π.parts - 1)) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) *
    (formalBoundaryChi g (π.nearTriple k) + formalBoundaryChi g (π.farTriple k))

def tripleOrdinaryWeight (g : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  ∏ k : Fin (π.parts - 1), π.tripleOrdinaryFactor g k

def tripleRootWeight (g : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  ∏ k : Fin (π.parts - 1), π.tripleRootFactor g k

theorem tripleFactors_binary (g : ZMod n) (hp : π.parts = 2) (k : Fin (π.parts - 1)) :
    π.tripleOrdinaryFactor g k = 0 ∧
      π.tripleRootFactor g k = formalBoundaryChi g (π.nearTriple k) := by
  have he := (π.nearTriple_eq_farTriple_iff k k).mpr ⟨hp, rfl⟩
  have hc : (MvPolynomial.C (1 / 2 : ℚ) : MvPolynomial (IncreasingBoundaryTriple n) ℚ) +
      MvPolynomial.C (1 / 2 : ℚ) = 1 := by
    rw [← map_add]
    norm_num
  constructor
  · simp only [tripleOrdinaryFactor, he, sub_self, mul_zero]
  · unfold tripleRootFactor
    rw [← he]
    calc
      _ = (MvPolynomial.C (1 / 2 : ℚ) + MvPolynomial.C (1 / 2 : ℚ)) *
          formalBoundaryChi g (π.nearTriple k) := by ring
      _ = formalBoundaryChi g (π.nearTriple k) := by rw [hc, one_mul]

theorem tripleWeights_unary (g : ZMod n) (hp : π.parts = 1) :
    π.tripleOrdinaryWeight g = 1 ∧ π.tripleRootWeight g = 1 := by
  letI : IsEmpty (Fin (π.parts - 1)) := ⟨fun k => by have := k.isLt; omega⟩
  simp [tripleOrdinaryWeight, tripleRootWeight]

theorem tripleOrdinaryWeight_binary (g : ZMod n) (hp : π.parts = 2) :
    π.tripleOrdinaryWeight g = 0 := by
  let k : Fin (π.parts - 1) := ⟨0, by omega⟩
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  exact (π.tripleFactors_binary g hp k).1

theorem tripleRootWeight_binary (g : ZMod n) (hp : π.parts = 2)
    (k : Fin (π.parts - 1)) :
    π.tripleRootWeight g = formalBoundaryChi g (π.nearTriple k) := by
  calc
    _ = π.tripleRootFactor g k := by
      apply Finset.prod_eq_single k
      · intro l _ hl
        exfalso
        apply hl
        apply Fin.ext
        have := l.isLt
        have := k.isLt
        omega
      · simp
    _ = _ := (π.tripleFactors_binary g hp k).2

theorem eval_tripleOrdinaryFactor (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleOrdinaryFactor g k) =
      (ordinaryGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k) : ℚ) := by
  rw [tripleOrdinaryFactor, map_mul, MvPolynomial.eval_C, map_sub,
    eval_formalBoundaryChi, eval_formalBoundaryChi]
  exact (gate_pair_rational _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).1.symm

theorem eval_tripleRootFactor (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleRootFactor g k) =
      (rootGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k) : ℚ) := by
  rw [tripleRootFactor, map_mul, MvPolynomial.eval_C, map_add,
    eval_formalBoundaryChi, eval_formalBoundaryChi]
  exact (gate_pair_rational _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).2.symm

theorem eval_tripleOrdinaryWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleOrdinaryWeight g) =
      (π.ordinaryWeight P hP g : ℚ) := by
  simp only [tripleOrdinaryWeight, ordinaryWeight, map_prod, Int.cast_prod,
    eval_tripleOrdinaryFactor π P hP g]

theorem eval_tripleRootWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleRootWeight g) =
      (π.rootWeight P hP g : ℚ) := by
  simp only [tripleRootWeight, rootWeight, map_prod, Int.cast_prod,
    eval_tripleRootFactor π P hP g]

end IntervalComposition

/-- Exactly the polynomial prescribed by the finite rooted tree recursion,
using signed canonical physical triple variables for each original cut. -/
def canonicalTreePolynomial (g : ZMod n) (hn : 3 ≤ n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  rootedTreeRec (fun _ π => π.tripleOrdinaryWeight g)
    (fun _ π => π.tripleRootWeight g) (fullBoundaryInterval hn)

/-- The actual signed finite-tree sum, without independent composition variables. -/
theorem canonicalTreePolynomial_eq_signed_tree_sum (g : ZMod n) (hn : 3 ≤ n) :
    canonicalTreePolynomial g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : MvPolynomial (IncreasingBoundaryTriple n) ℚ) ^ T.ordinaryCount *
        T.fst.tripleRootWeight g * T.ordinaryProduct (fun _ π => π.tripleOrdinaryWeight g) :=
  rootedTreeRec_eq_signed_planeTreeSum _ _ _

/-- Exact G1 evaluation of the prescribed polynomial at the same physical root.
This theorem does not yet assert its individual-variable degree bound. -/
theorem eval_canonicalTreePolynomial (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) =
      (treeCoefficient P hP g hn : ℚ) := by
  unfold canonicalTreePolynomial
  rw [map_rootedTreeRec]
  change rootedTreeRec _ _ _ = (Int.castRingHom ℚ) (rootedTreeRec _ _ _)
  rw [map_rootedTreeRec]
  congr 1
  · funext I π
    exact π.eval_tripleOrdinaryWeight P hP g
  · funext I π
    exact π.eval_tripleRootWeight P hP g

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual open tree recursion solves the complete near/far system
for arbitrary arrays in the full ring, without a geometric specialization. -/
theorem openTreeRec_nearFar_equation (D H : TripleArray n R) :
    nearFarTransform D H (openTreeRec (fun _ π => π.nearFarWeight D H)) = boundaryUnitArray := by
  rw [nearFarTransform_eq_triangular]
  funext I
  have hp := I.leaves_pos
  have hi : I.right.val = I.left.val + 1 ↔ I.leaves = 1 := by
    have := I.increasing
    unfold BoundaryInterval.leaves
    change I.left.val < I.right.val at this
    omega
  by_cases hI : I.leaves = 1
  · letI : IsEmpty {π : IntervalComposition I // 2 ≤ π.parts} :=
      ⟨fun π => by have := π.val.parts_eq_one_of_leaves_eq_one hI; have := π.property; omega⟩
    simp [triangularTransform, boundaryUnitArray, hi.mpr hI, openTreeRec_one _ I hI]
  · have hm : 2 ≤ I.leaves := by omega
    simp only [triangularTransform, boundaryUnitArray,
      show ¬I.right.val = I.left.val + 1 from fun h => hI (hi.mp h), if_false]
    rw [openTreeRec_many _ I hm]
    exact neg_add_cancel _

/-- Uniqueness identifies the actual formal recursion with the existing
polynomial inverse on every interval. -/
theorem openTreeRec_nearFar_inverse (D H : TripleArray n R) :
    openTreeRec (fun _ π => π.nearFarWeight D H) = nearFarInverse D H boundaryUnitArray :=
  nearFar_solution_unique D H _ _ (openTreeRec_nearFar_equation D H)

/-- The actual rooted recursion is the far-only output as a full ring
identity, with each root weight the entire reversed-far cut product. -/
theorem rootedTreeRec_nearFar_farOnly (D H : TripleArray n R) (I : BoundaryInterval n) :
    rootedTreeRec (fun _ π => π.nearFarWeight D H)
      (fun _ π => π.nearFarWeight D (-H)) I = farOnlyOutput H I := by
  exact congrFun (reversedFar_output_of_solution D H
    (openTreeRec (fun _ π => π.nearFarWeight D H)) boundaryUnitArray
    (openTreeRec_nearFar_equation D H)) I

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] silentPolynomialTwoInvertible

theorem canonicalPolynomial_half :
    (MvPolynomial.C (1 / 2 : ℚ) : MvPolynomial (IncreasingBoundaryTriple n) ℚ) =
      ⅟ (2 : MvPolynomial (IncreasingBoundaryTriple n) ℚ) := by
  simpa only [invOf_eq_inv, one_div] using
    (ringHom_map_half (MvPolynomial.C : ℚ →+* MvPolynomial (IncreasingBoundaryTriple n) ℚ))

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- Every ordinary gate variable is specialized to its entire cut product,
not to one linear factor representing the whole composition. -/
theorem tripleOrdinaryWeight_nearFar (g : ZMod n) :
    π.tripleOrdinaryWeight g = π.nearFarWeight (formalBoundaryChi g) (formalBoundaryChi g) := by
  unfold tripleOrdinaryWeight nearFarWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [tripleOrdinaryFactor, canonicalPolynomial_half]
  exact mul_comm _ _

/-- The root weight specializes to the entire reversed-far product,
including the empty product for a unary root. -/
theorem tripleRootWeight_nearFar (g : ZMod n) :
    π.tripleRootWeight g = π.nearFarWeight (formalBoundaryChi g) (-formalBoundaryChi g) := by
  unfold tripleRootWeight nearFarWeight
  apply Finset.prod_congr rfl
  intro k _
  simp only [tripleRootFactor, canonicalPolynomial_half, Pi.neg_apply, sub_neg_eq_add]
  exact mul_comm _ _

end IntervalComposition

/-- The actual prescribed canonical physical-triple polynomial equals the
far-only output as an identity in its unrestricted rational polynomial ring. -/
theorem canonicalTreePolynomial_farOnly (g : ZMod n) (hn : 3 ≤ n) :
    canonicalTreePolynomial g hn = farOnlyOutput (formalBoundaryChi g) (fullBoundaryInterval hn) := by
  unfold canonicalTreePolynomial
  simp_rw [IntervalComposition.tripleOrdinaryWeight_nearFar,
    IntervalComposition.tripleRootWeight_nearFar]
  exact rootedTreeRec_nearFar_farOnly (formalBoundaryChi g) (formalBoundaryChi g) _

/-- Polynomial evaluation at every tuple, including simultaneous silent
zeros, equals the geometric far-only output. No step-function gate at zero
or genericity assumption enters this full polynomial identity. -/
theorem eval_canonicalTreePolynomial_farOnly (P : LabelledTuple n) (g : ZMod n)
    (hn : 3 ≤ n) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) =
      farOnlyOutput (geometricBoundaryArray (R := ℚ) P g) (fullBoundaryInterval hn) := by
  rw [canonicalTreePolynomial_farOnly]
  have h := map_farOnlyOutput (MvPolynomial.eval (canonicalTripleValue P))
    (formalBoundaryChi g) (fullBoundaryInterval hn)
  have he : (fun t => MvPolynomial.eval (canonicalTripleValue P) (formalBoundaryChi g t)) =
      geometricBoundaryArray (R := ℚ) P g := by
    funext t
    exact eval_formalBoundaryChi P g t
  rw [he] at h
  exact h

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Fix precisely the initially nonzero canonical physical-triple entries.
Every zero entry remains its own independent variable in the full free ring. -/
def canonicalFreezeValue (P : LabelledTuple n) (t : IncreasingBoundaryTriple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  if canonicalTripleValue P t = 0 then MvPolynomial.X t
  else MvPolynomial.C (canonicalTripleValue P t)

def canonicalFreezeHom (P : LabelledTuple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ →+*
      MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (canonicalFreezeValue P)

theorem canonicalFreezeHom_C (P : LabelledTuple n) (a : ℚ) :
    canonicalFreezeHom P (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem canonicalFreezeHom_X_zero (P : LabelledTuple n) (t : IncreasingBoundaryTriple n)
    (ht : canonicalTripleValue P t = 0) :
    canonicalFreezeHom P (MvPolynomial.X t) = MvPolynomial.X t := by
  simp [canonicalFreezeHom, canonicalFreezeValue, ht]

theorem canonicalFreezeHom_X_nonzero (P : LabelledTuple n) (t : IncreasingBoundaryTriple n)
    (ht : canonicalTripleValue P t ≠ 0) :
    canonicalFreezeHom P (MvPolynomial.X t) = MvPolynomial.C (canonicalTripleValue P t) := by
  simp [canonicalFreezeHom, canonicalFreezeValue, ht]

/-- Any assignment agreeing on the fixed entries evaluates a polynomial and
its freezing identically. No realizability condition is imposed on v. -/
theorem eval_canonicalFreezeHom_of_agree (P : LabelledTuple n)
    (v : IncreasingBoundaryTriple n → ℚ)
    (hv : ∀ t, canonicalTripleValue P t ≠ 0 → v t = canonicalTripleValue P t)
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ) :
    MvPolynomial.eval v (canonicalFreezeHom P p) = MvPolynomial.eval v p := by
  have he : (MvPolynomial.eval v).comp (canonicalFreezeHom P) = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, canonicalFreezeHom_C]
    · intro t
      simp only [RingHom.comp_apply]
      by_cases ht : canonicalTripleValue P t = 0
      · rw [canonicalFreezeHom_X_zero P t ht]
      · rw [canonicalFreezeHom_X_nonzero P t ht,
          MvPolynomial.eval_C, MvPolynomial.eval_X, hv t ht]
  exact DFunLike.congr_fun he p

theorem eval_canonicalFreezeHom_base (P : LabelledTuple n)
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalFreezeHom P p) =
      MvPolynomial.eval (canonicalTripleValue P) p :=
  eval_canonicalFreezeHom_of_agree P _ (fun _ _ => rfl) p

/-- The exact parity and canonical label attached to a reversed boundary
triple recover its geometric sign, including zero. -/
theorem boundaryTripleData_geometric (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    (boundaryTripleData g t).2 * canonicalTripleValue P (boundaryTripleData g t).1 =
      geometricBoundaryArray (R := ℚ) P g t := by
  have h := eval_formalBoundaryChi P g t
  rw [formalBoundaryChi_eq, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
  exact h

/-- Every nonzero geometric boundary entry becomes exactly its constant
under the canonical freezing, with the reversed-order parity retained. -/
theorem canonicalFreezeHom_formalBoundaryChi_nonzero (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n)
    (ht : geometricBoundaryArray (R := ℚ) P g t ≠ 0) :
    canonicalFreezeHom P (formalBoundaryChi g t) =
      geometricBoundaryArray (R := MvPolynomial (IncreasingBoundaryTriple n) ℚ) P g t := by
  have he := boundaryTripleData_geometric P g t
  have hc : canonicalTripleValue P (boundaryTripleData g t).1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact ht he.symm
  rw [formalBoundaryChi_eq, map_mul, canonicalFreezeHom_C,
    canonicalFreezeHom_X_nonzero P _ hc, ← map_mul, he]
  exact map_intCast MvPolynomial.C _

end
end SM


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] silentPolynomialTwoInvertible

/-- The residual formal boundary entries after fixing the nonzero physical
canonical variables, measured from the entire geometric constant array. -/
def canonicalSilentPerturbation (P : LabelledTuple n) (g : ZMod n) :
    TripleArray n (MvPolynomial (IncreasingBoundaryTriple n) ℚ) :=
  fun t => canonicalFreezeHom P (formalBoundaryChi g t) - geometricBoundaryArray P g t

theorem canonicalSilentPerturbation_support (P : LabelledTuple n) (g : ZMod n) :
    ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 →
      canonicalSilentPerturbation P g t = 0 := by
  intro t ht
  unfold canonicalSilentPerturbation
  rw [canonicalFreezeHom_formalBoundaryChi_nonzero P g t ht, sub_self]

theorem canonicalFreezeBoundary_split (P : LabelledTuple n) (g : ZMod n) :
    (fun t => canonicalFreezeHom P (formalBoundaryChi g t)) =
      geometricBoundaryArray P g + canonicalSilentPerturbation P g := by
  funext t
  simp only [Pi.add_apply, canonicalSilentPerturbation]
  ring

/-- Formal constancy of the prescribed tree polynomial after exactly the
nonzero canonical chirotope entries are fixed. All zero variables remain
independent in the unrestricted rational polynomial ring. -/
theorem canonicalTreePolynomial_freeze_constancy (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) :
    canonicalFreezeHom P (canonicalTreePolynomial g hn) =
      MvPolynomial.C (MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn)) := by
  rw [eval_canonicalTreePolynomial_farOnly, canonicalTreePolynomial_farOnly]
  have hm := map_farOnlyOutput (canonicalFreezeHom P)
    (formalBoundaryChi g) (fullBoundaryInterval hn)
  rw [canonicalFreezeBoundary_split,
    silent_supported_output hn hP g (canonicalSilentPerturbation P g)
      (canonicalSilentPerturbation_support P g)] at hm
  have hc := map_farOnlyOutput
    (MvPolynomial.C : ℚ →+* MvPolynomial (IncreasingBoundaryTriple n) ℚ)
    (geometricBoundaryArray (R := ℚ) P g) (fullBoundaryInterval hn)
  rw [map_geometricBoundaryArray] at hc
  exact hm.trans hc.symm

/-- The formal identity also controls every rational assignment of silent
entries, including assignments that are not realizable chirotopes. -/
theorem eval_canonicalTreePolynomial_of_nonzero_agree (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (v : IncreasingBoundaryTriple n → ℚ)
    (hv : ∀ t, canonicalTripleValue P t ≠ 0 → v t = canonicalTripleValue P t) :
    MvPolynomial.eval v (canonicalTreePolynomial g hn) =
      MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) := by
  rw [← eval_canonicalFreezeHom_of_agree P v hv,
    canonicalTreePolynomial_freeze_constancy hn hP g, MvPolynomial.eval_C]

end
end SM

#print axioms SM.canonicalSilentPerturbation
#print axioms SM.canonicalSilentPerturbation_support
#print axioms SM.canonicalFreezeBoundary_split
#print axioms SM.canonicalTreePolynomial_freeze_constancy
#print axioms SM.eval_canonicalTreePolynomial_of_nonzero_agree
