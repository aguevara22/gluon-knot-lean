namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero
attribute [local instance] Classical.propDecidable

/-- Construct the affine data and the complete integer response from the
physically distinct critical points, including arity three. -/
theorem single_triple_integer_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
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
        (geometricBoundaryArray (R := ℤ) (w.curve sPlus) g t -
          geometricBoundaryArray (R := ℤ) (w.curve sMinus) g t = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) *
                treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                  (t.contractedSize_of_proper hn hp)
            else
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) +
              (criticalGapVInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapVInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)))) := by
  obtain ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx⟩ :=
    critical_boundary_affine_data w.center g t hZ hba hcb hca
  have hε := wall_epsilons_one_or_neg_one x y z hyx hzy hzx
  refine ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx,
    hε.1, hε.2, wall_epsilon_positive x y z hzx, ?_⟩
  exact w.single_triple_integer_response_of_affine g hn t hZ hZc hchange
    p ω x y z hω hx hy hz hyx hzy hzx

/-- A supplied unordered support yields its unique boundary reading, affine
coordinates, signed normalization, and both integer wall equations. Every
conversion is constructed from the source premises; no ordering, coordinate
choice, or additional geometric genericity premise is required of the caller. -/
theorem single_triple_integer_response_of_support (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (K : Finset (ZMod n)) (hZ : pointZeroTriples w.center = {K})
    (hZc : concurrenceTriples w.center = ∅)
    (hsep : (K : Set (ZMod n)).Pairwise (fun i j => w.center i ≠ w.center j))
    (a b c : ZMod n) (habc : ({a, b, c} : Finset (ZMod n)) = K)
    (hchange : w.SignChanges (fun P => (chi P a b c : ℝ))) :
    ∃ t : IncreasingBoundaryTriple n, ∃ hZt : pointZeroTriples w.center = {t.vertexSet g},
      t.vertexSet g = K ∧ (∀ u : IncreasingBoundaryTriple n, u.vertexSet g = K → u = t) ∧
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
        (geometricBoundaryArray (R := ℤ) (w.curve sPlus) g t -
          geometricBoundaryArray (R := ℤ) (w.curve sMinus) g t = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (criticalGapUInteger w.center g t hZt t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZt t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) *
                treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZt) 0
                  (t.contractedSize_of_proper hn hp)
            else
              (criticalGapUInteger w.center g t hZt t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZt t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) +
              (criticalGapVInteger w.center g t hZt t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapVInteger w.center g t hZt t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)))) := by
  obtain ⟨t, ht, _⟩ := w.single_triple_boundary_data g K hZ hsep a b c habc hchange
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by rw [ht.1]; exact hZ
  refine ⟨t, hZt, ht.1, ?_, ?_⟩
  · intro u hu
    exact IncreasingBoundaryTriple.vertexSet_injective g (hu.trans ht.1.symm)
  · exact w.single_triple_integer_response g hn t hZt hZc
      ht.2.1.1 ht.2.1.2.1 ht.2.1.2.2 ht.2.2

end
end SM.WallGerm
