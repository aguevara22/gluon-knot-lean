namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- No triple of surviving positions can be the critical triple because
its middle position was deleted. This is purely about actual boundary labels. -/
theorem IncreasingBoundaryTriple.expandTriple_ne_critical (t : IncreasingBoundaryTriple n)
    (u : IncreasingBoundaryTriple t.contractedSize) : t.expandTriple u ≠ t := by
  intro he
  have hm : t.expandPosition u.middle = t.middle := congrArg IncreasingBoundaryTriple.middle he
  have hs := t.expandPosition_survives u.middle
  rw [hm] at hs
  rcases hs with hl | hr
  · exact (not_le_of_gt t.lower_middle) hl
  · exact (not_le_of_gt t.middle_upper) hr

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Both punctured arrays have exactly the same contracted array whenever
the only entry permitted to differ is the critical one. -/
theorem contractedTripleArray_eq_off_critical (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    contractedTripleArray t H₁ = contractedTripleArray t H₂ := by
  funext u
  exact h (t.expandTriple u) (t.expandTriple_ne_critical u)

theorem contractedTripleArray_neg (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    contractedTripleArray t (-H) = -contractedTripleArray t H := rfl

/-- The contracted array is the chirotope array of the actual contracted
polygon at its retained physical closing root. No genericity is needed for
this equality of the sampled determinants. -/
theorem geometricBoundaryArray_contractedWord (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := R) (contractedWordTuple P g t) 0 =
      contractedTripleArray t (geometricBoundaryArray P g) := by
  funext u
  simp only [contractedTripleArray, geometricBoundaryArray, chi]
  change ((SignType.sign (det
    (boundaryWord (contractedWordTuple P g t) 0 u.middle -
      boundaryWord (contractedWordTuple P g t) 0 u.upper)
    (boundaryWord (contractedWordTuple P g t) 0 u.lower -
      boundaryWord (contractedWordTuple P g t) 0 u.upper)) : ℤ) : R) = _
  rw [contractedWord_boundary, contractedWord_boundary, contractedWord_boundary]
  rfl

/-- The propagation base uses the formal open-word leaf value one, also
when the complete contraction has only two positions. -/
theorem contracted_leaf_inverse_value (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    farOnlyCoordinates (contractedTripleArray t H) t.contractedLeaf = 1 :=
  farOnlyCoordinates_leaf _ _ t.contractedLeaf_leaves

/-- For a proper contraction the complete barred output is the actual
rooted tree coefficient of Q. The G1 and arity proofs are supplied locally;
the physical root is the one identified by contractedWord_physical_root. -/
theorem contracted_output_tree (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hZ : pointZeroTriples P = {t.vertexSet g})
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    farOnlyOutput (contractedTripleArray t (geometricBoundaryArray (R := R) P g))
      (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) =
      (treeCoefficient (contractedWordTuple P g t) (contractedWord_G1 P g t hZ) 0
        (t.contractedSize_of_proper hn hproper) : R) := by
  rw [← geometricBoundaryArray_contractedWord]
  exact (treeCoefficient_farOnly (contractedWordTuple P g t)
    (contractedWord_G1 P g t hZ) 0 (t.contractedSize_of_proper hn hproper)).symm

end
end SM
