namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Combine the derived source jump with complete proper-output contraction.
The factor on the contracted polygon is its actual rooted tree coefficient,
with G1 and its arity proved from the wall support and proper contraction. -/
theorem geometric_proper_output_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hZ : pointZeroTriples P = {t.vertexSet g})
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn)
    (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyOutput H₂ (fullBoundaryInterval hn) - farOnlyOutput H₁ (fullBoundaryInterval hn) =
      (((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z))) *
        (treeCoefficient (contractedWordTuple P g t) (contractedWord_G1 P g t hZ) 0
          (t.contractedSize_of_proper hn hproper) : R) := by
  have hH : ∀ u, u ≠ t → H₁ u = H₂ u := fun u hu => (h₁ u hu).trans (h₂ u hu).symm
  have hQ : contractedTripleArray t H₁ = contractedTripleArray t (geometricBoundaryArray P g) :=
    contractedTripleArray_eq_off_critical t H₁ (geometricBoundaryArray P g) h₁
  rw [farOnlyOutput_full_contraction t H₁ H₂ hH hn hproper,
    geometric_critical_inverse_response P g t H₁ H₂ h₁ h₂ p ω x y z hx hy hz hyx hzy hzx,
    hQ, contracted_output_tree P g t hn hZ hproper]

end
end SM
