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
      ∀ s₋ s₊ : w.Parameter, ∀ h₋ : s₋.val < 0, ∀ h₊ : 0 < s₊.val,
        |s₋.val| < δ → |s₊.val| < δ →
        (treeCoefficient (w.curve s₊) (w.generic_punctured s₊ (ne_of_gt h₊)).1 g hn : R) -
          (treeCoefficient (w.curve s₋) (w.generic_punctured s₋ (ne_of_lt h₋)).1 g hn : R) =
          ((geometricBoundaryArray (R := R) (w.curve s₊) g t -
            geometricBoundaryArray (w.curve s₋) g t) * ⅟ (2 : R)) *
            ((wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
             (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) := by
  obtain ⟨δ, hδ, hrad, hs⟩ := w.boundary_values_stable_near_center (R := R) g t hZ
  refine ⟨δ, hδ, hrad, ?_⟩
  intro s₋ s₊ h₋ h₊ hnear₋ hnear₊
  have hs₋ := hs s₋ hnear₋
  have hs₊ := hs s₊ hnear₊
  have hleft : ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  have hright : ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl
  have hL := hs₋.2.2 t.leftInterval hleft
  have hR := hs₋.2.2 t.rightInterval hright
  have hc := geometric_critical_output_response w.center g t
    (geometricBoundaryArray (R := R) (w.curve s₋) g)
    (geometricBoundaryArray (w.curve s₊) g) hs₋.1 hs₊.1
    p ω x y z hx hy hz hyx hzy hzx
  rw [hspan] at hc
  rw [treeCoefficient_farOnly (w.curve s₊) (w.generic_punctured s₊ (ne_of_gt h₊)).1 g hn,
    treeCoefficient_farOnly (w.curve s₋) (w.generic_punctured s₋ (ne_of_lt h₋)).1 g hn]
  simpa only [wallGapU, wallGapV, hL, hR] using hc

end
end SM.WallGerm
