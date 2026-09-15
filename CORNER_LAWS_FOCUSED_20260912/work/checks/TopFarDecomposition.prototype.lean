import SM.NearFarFactorization
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

#print axioms SM.intervalFarValue
#print axioms SM.intervalFarValue_interior
#print axioms SM.intervalFarValue_map
#print axioms SM.intervalFarCutWeight
#print axioms SM.intervalFarCutWeight_add
#print axioms SM.positionCutSummand_intervalFar
#print axioms SM.farTransform_positionCutSum
#print axioms SM.farTransform_add_decomposition
