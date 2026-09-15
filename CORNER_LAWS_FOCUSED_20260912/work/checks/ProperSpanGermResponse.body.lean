namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The proper-span response for actual tree coefficients on both sufficiently
close punctured sides of the continuous germ. All gap and contracted data on
the right are at the wall center. Sign-change normalization is a separate step. -/
theorem proper_span_tree_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn)
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
          (((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
            geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R)) *
            (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) *
            (treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
              (t.contractedSize_of_proper hn hproper) : R) := by
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
  have hc := geometric_proper_output_response w.center g t hn hZ hproper
    (geometricBoundaryArray (R := R) (w.curve sMinus) g)
    (geometricBoundaryArray (w.curve sPlus) g) hsMinus.1 hsPlus.1
    p ω x y z hx hy hz hyx hzy hzx
  rw [treeCoefficient_farOnly (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn,
    treeCoefficient_farOnly (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn]
  simpa only [wallGapU, hL, hR] using hc

end
end SM.WallGerm
