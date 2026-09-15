namespace SM

noncomputable section

/-- Actual distinct collinear points admit the affine coordinates used in the
wall theorem. The direction is the endpoint difference; no choice of a
collinearity oracle or additional dimension assumption is required. -/
theorem distinct_collinear_affine_data (a b c : Plane)
    (hba : b ≠ a) (hcb : c ≠ b) (hca : c ≠ a)
    (hd : det (b - a) (c - a) = 0) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ a = p + x • ω ∧ b = p + y • ω ∧ c = p + z • ω ∧
      y ≠ x ∧ z ≠ y ∧ z ≠ x := by
  have hω : c - a ≠ 0 := sub_ne_zero.mpr hca
  let q := planeDot (c - a) (b - a) / planeDot (c - a) (c - a)
  have hd' : det (c - a) (b - a) = 0 := by rw [det_swap, hd, neg_zero]
  have hs : b - a = q • (c - a) := scalar_of_det_zero hω hd'
  have hb : b = a + q • (c - a) := by
    calc
      b = a + (b - a) := by abel
      _ = a + q • (c - a) := by rw [hs]
  have hc : c = a + (1 : ℝ) • (c - a) := by simp
  have hq0 : q ≠ 0 := by
    intro hq
    exact hba (by simpa only [hq, zero_smul, add_zero] using hb)
  have h1q : (1 : ℝ) ≠ q := by
    intro hq
    exact hcb (hc.trans ((congrArg (fun r : ℝ => a + r • (c - a)) hq).trans hb.symm))
  exact ⟨a, c - a, 0, q, 1, hω, by simp, hb, hc, hq0, h1q, by norm_num⟩

variable {n : ℕ} [NeZero n]

/-- Apply the constructed affine coordinates to the actual critical boundary
points. Physical pairwise distinctness is explicit and is not inferred from
a singleton zero support, which would fail at arity three. -/
theorem critical_boundary_affine_data (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hba : boundaryWord P g t.middle ≠ boundaryWord P g t.lower)
    (hcb : boundaryWord P g t.upper ≠ boundaryWord P g t.middle)
    (hca : boundaryWord P g t.upper ≠ boundaryWord P g t.lower) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ boundaryWord P g t.lower = p + x • ω ∧
      boundaryWord P g t.middle = p + y • ω ∧
      boundaryWord P g t.upper = p + z • ω ∧ y ≠ x ∧ z ≠ y ∧ z ≠ x := by
  have hdata := singlePointTriple_data hZ
  have hχ : chi P (boundaryIndex g t.lower) (boundaryIndex g t.middle)
      (boundaryIndex g t.upper) = 0 := by
    apply hdata.2
    all_goals rw [t.vertexSet_reversed g]; simp
  have hd : det (boundaryWord P g t.middle - boundaryWord P g t.lower)
      (boundaryWord P g t.upper - boundaryWord P g t.lower) = 0 := sign_eq_zero_iff.mp hχ
  exact distinct_collinear_affine_data _ _ _ hba hcb hca hd

end
end SM
