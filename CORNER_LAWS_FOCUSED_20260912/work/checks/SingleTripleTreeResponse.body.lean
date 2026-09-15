namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero
attribute [local instance] Classical.propDecidable

/-- Both single-triple response branches, with an actual fixed signed jump,
for every affine coordinate choice satisfying the printed source conditions.
The piecewise expression uses a closed contracted polygon only in the proper
branch; the full-span branch uses the separately proved barred source jump. -/
theorem single_triple_tree_response_of_affine (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hZc : concurrenceTriples w.center = ∅)
    (hchange : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)))
    (p ω : Plane) (x y z : ℝ) (hω : ω ≠ 0)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        ((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
          geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R) = (d : R)) ∧
        ((treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
          (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
          (d : R) *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) *
                (treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                  (t.contractedSize_of_proper hn hp) : R)
            else
              (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
              (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)))) := by
  obtain ⟨d, hd, hjump⟩ := w.boundary_half_jump_signed (R := R) g t hchange
  refine ⟨d, hd, ?_⟩
  by_cases hp : t.spanInterval ≠ fullBoundaryInterval hn
  · obtain ⟨δ, hδ, hrad, hresponse⟩ :=
      w.proper_span_tree_response (R := R) g hn t hZ hp p ω x y z hx hy hz hyx hzy hzx
    refine ⟨δ, hδ, hrad, ?_⟩
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    have hj := hjump sMinus sPlus hMinus hPlus
    have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    refine ⟨hj, ?_⟩
    rw [dif_pos hp]
    rw [hj] at hr
    simpa only [mul_assoc] using hr
  · have hfull : t.spanInterval = fullBoundaryInterval hn := not_ne_iff.mp hp
    obtain ⟨δ, hδ, hrad, hresponse⟩ :=
      w.full_span_tree_response (R := R) g hn t hZ hfull p ω x y z hx hy hz hyx hzy hzx
    refine ⟨δ, hδ, hrad, ?_⟩
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    have hj := hjump sMinus sPlus hMinus hPlus
    have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    refine ⟨hj, ?_⟩
    rw [dif_neg hp]
    rw [hj] at hr
    exact hr

/-- The printed physically distinct wall domain supplies the affine data as
well as the response, including arity three. The preceding theorem separately
establishes the response for every valid affine representation, not just this
constructed witness. No author-supplied coordinate choice remains necessary. -/
theorem single_triple_tree_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hZc : concurrenceTriples w.center = ∅)
    (hba : boundaryWord w.center g t.middle ≠ boundaryWord w.center g t.lower)
    (hcb : boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.middle)
    (hca : boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.lower)
    (hchange : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ))) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ boundaryWord w.center g t.lower = p + x • ω ∧
      boundaryWord w.center g t.middle = p + y • ω ∧
      boundaryWord w.center g t.upper = p + z • ω ∧ y ≠ x ∧ z ≠ y ∧ z ≠ x ∧
      (wallLeftEpsilon x y z = 1 ∨ wallLeftEpsilon x y z = -1) ∧
      (wallRightEpsilon x y z = 1 ∨ wallRightEpsilon x y z = -1) ∧
      (wallLeftEpsilon x y z = 1 ∨ wallRightEpsilon x y z = 1) ∧
      ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
        ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
          |sMinus.val| < δ → |sPlus.val| < δ →
          ((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
            geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R) = (d : R)) ∧
          ((treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
            (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
            (d : R) *
              (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
                (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                  wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) *
                  (treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                    (t.contractedSize_of_proper hn hp) : R)
              else
                (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                  wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
                (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                  wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)))) := by
  obtain ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx⟩ :=
    critical_boundary_affine_data w.center g t hZ hba hcb hca
  have hε := wall_epsilons_one_or_neg_one x y z hyx hzy hzx
  refine ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx,
    hε.1, hε.2, wall_epsilon_positive x y z hzx, ?_⟩
  exact w.single_triple_tree_response_of_affine (R := R) g hn t hZ hZc hchange
    p ω x y z hω hx hy hz hyx hzy hzx

end
end SM.WallGerm
