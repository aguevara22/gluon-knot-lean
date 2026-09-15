namespace SM

open Set
noncomputable section
variable {n : ℕ} [NeZero n]

/-- A shifted wall germ on the actual path agrees with that path at every
point in its radius, using the exact parameter identity rather than endpoints. -/
theorem WallGerm.shifted_curve_eq_path (w : WallGerm n)
    (p : unitInterval → LabelledTuple n) (t : unitInterval)
    (hcurve : ∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      w.curve s = p ⟨(t : ℝ) + s.val, hs⟩)
    (u : unitInterval) (hu : |(u : ℝ) - (t : ℝ)| < w.radius) :
    w.curve ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hu⟩ = p u := by
  obtain ⟨hs, he⟩ := hcurve ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hu⟩
  have htu : (⟨(t : ℝ) + ((u : ℝ) - (t : ℝ)), hs⟩ : unitInterval) = u := by
    apply Subtype.ext
    dsimp
    ring
  rw [htu] at he
  exact he

/-- Actual punctured-generic germs at every nongeneric path parameter ensure
density of generic parameters, including the interval endpoints. No finite
set is asserted empty, and no independent density hypothesis is required. -/
theorem generic_path_dense_of_germs (p : unitInterval → LabelledTuple n)
    (hevent : ∀ t : unitInterval, ¬ Generic (p t) → ∃ w : WallGerm n,
      ∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
        w.curve s = p ⟨(t : ℝ) + s.val, hs⟩) :
    Dense {t : unitInterval | Generic (p t)} := by
  intro t
  by_cases ht : Generic (p t)
  · exact subset_closure ht
  obtain ⟨w, hcurve⟩ := hevent t ht
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let q : ℝ := min w.radius ε / 2
  have hq0 : 0 < q := div_pos (lt_min w.radius_pos hε) (by norm_num)
  have hqr : q < w.radius := by dsimp [q]; linarith [min_le_left w.radius ε]
  have hqε : q < ε := by dsimp [q]; linarith [min_le_right w.radius ε]
  let s : w.Parameter := ⟨q, by constructor <;> linarith [w.radius_pos]⟩
  obtain ⟨hs, he⟩ := hcurve s
  let u : unitInterval := ⟨(t : ℝ) + s.val, hs⟩
  have hgu : Generic (p u) := by
    rw [← he]
    exact w.generic_punctured s (ne_of_gt hq0)
  refine ⟨u, hgu, ?_⟩
  change dist (t : ℝ) ((t : ℝ) + q) < ε
  rw [Real.dist_eq]
  have hsub : (t : ℝ) - ((t : ℝ) + q) = -q := by ring
  rw [hsub, abs_neg, abs_of_pos hq0]
  exact hqε

end
end SM
