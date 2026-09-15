import SM.TransportPolynomials

/-! Nonvanishing of every actual named control implies the source's actual G1
and G2 conditions. Only this direction is asserted: inactive concurrence zeros
can occur at generic tuples and must not automatically become wall events. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem area_nonzero_of_named_controls (P : LabelledTuple n)
    (h : ∀ name : PolynomialControlName n, eval (scalarCoordinates P) (namedControlPolynomial name) ≠ 0)
    (i j k : ZMod n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    det (P j - P i) (P k - P i) ≠ 0 := by
  rw [← eval_areaPolynomial]
  rcases vertexControlNameOf_coverage i j k hij hik hjk with he | he
  · rw [he]
    exact h _
  · rw [he, map_neg]
    exact neg_ne_zero.mpr (h _)

theorem concurrence_nonzero_of_named_controls (P : LabelledTuple n)
    (h : ∀ name : PolynomialControlName n, eval (scalarCoordinates P) (namedControlPolynomial name) ≠ 0)
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    concurrenceDet P e f g ≠ 0 := by
  rw [← eval_concurrencePolynomial]
  rcases edgeControlNameOf_coverage e f g hef heg hfg with he | he
  · rw [he]
    exact h _
  · rw [he, map_neg]
    exact neg_ne_zero.mpr (h _)

theorem generic_of_named_controls_nonzero (hn : 3 ≤ n) (P : LabelledTuple n)
    (h : ∀ name : PolynomialControlName n, eval (scalarCoordinates P) (namedControlPolynomial name) ≠ 0) :
    Generic P := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have h1 : G1 P := by
    intro i j k hij hjk hik
    exact sign_ne_zero.mpr (area_nonzero_of_named_controls P h i j k hij hik hjk)
  refine ⟨h1, ?_⟩
  rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
  have hrij := g1_common_interiors_remote hn h1 hij hi hj
  have hrik := g1_common_interiors_remote hn h1 hik hi hk
  have hrjk := g1_common_interiors_remote hn h1 hjk hj hk
  have hz := concurrenceDet_eq_zero_of_closedTriple P i j k
    ⟨x, edgeInterior_subset_edgeSegment P i hi, edgeInterior_subset_edgeSegment P j hj,
      edgeInterior_subset_edgeSegment P k hk⟩
  exact concurrence_nonzero_of_named_controls P h i j k hrij hrik hrjk hz

end

end SM
