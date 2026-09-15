namespace SM

noncomputable section

/-- All clauses of source lem:farout. The inverse is given by actual coordinate
polynomials; factorization and near-array freedom concern full arrays; the
nonleaf restriction uses the original physical closing edge and only local G1.
The final two conjuncts separately retain the open one-leaf convention and the
closed polygon coefficient, so no two-gon amplitude is introduced. -/
theorem farout (n : ℕ) [NeZero n] (R : Type*) [CommRing R] [Invertible (2 : R)] (hn : 3 ≤ n) :
    (∀ D H : TripleArray n R,
      (∃ Ψ : BoundaryInterval n → MvPolynomial (BoundaryInterval n) R,
        (∀ Y : IntervalArray n R,
          nearFarTransform D H (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = Y) ∧
        (∀ X : IntervalArray n R,
          (fun I => MvPolynomial.eval₂Hom (RingHom.id R) (nearFarTransform D H X) (Ψ I)) = X)) ∧
      nearFarTransform D H = farTransform H ∘ nearTransform D) ∧
    (∀ (P : LabelledTuple n) (hP : G1 P) (g : ZMod n),
      nearFarTransform (geometricBoundaryArray (R := R) P g) (geometricBoundaryArray P g)
          (fun I => (openTreeSum P hP g I : R)) = boundaryUnitArray ∧
      (treeCoefficient P hP g hn : R) =
        nearFarTransform (geometricBoundaryArray P g) (-geometricBoundaryArray P g)
          (fun I => (openTreeSum P hP g I : R)) (fullBoundaryInterval hn) ∧
      (treeCoefficient P hP g hn : R) =
        farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn)) ∧
    (∀ (D₁ D₂ H : TripleArray n R) (X₁ X₂ : IntervalArray n R),
      nearFarTransform D₁ H X₁ = boundaryUnitArray →
      nearFarTransform D₂ H X₂ = boundaryUnitArray →
      nearFarTransform D₁ (-H) X₁ = nearFarTransform D₂ (-H) X₂) ∧
    (∀ (H : TripleArray n R) (J : BoundaryInterval n),
      (2 ≤ J.leaves → farTransform H (farOnlyCoordinates H) J = 0) ∧
      (J.leaves = 1 → farTransform H (farOnlyCoordinates H) J = 1 ∧ farOnlyOutput H J = 1)) ∧
    (∀ (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
        (hJ : 2 ≤ J.leaves) (hP : G1 (restrictedWordTuple P g J)),
      edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right ∧
      farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
        (treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega : 3 ≤ J.leaves + 1) : R)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro D H
    exact ⟨nearFar_has_polynomial_inverse D H, nearFar_factorization D H⟩
  · intro P hP g
    exact ⟨geometric_nearFar_open P hP g, geometric_nearFar_root P hP g hn,
      treeCoefficient_farOnly P hP g hn⟩
  · intro D₁ D₂ H X₁ X₂ h₁ h₂
    exact complete_output_near_independent D₁ D₂ H X₁ X₂ boundaryUnitArray h₁ h₂
  · intro H J
    exact ⟨farOnly_nonleaf_E H J, farOnly_leaf_values H J⟩
  · intro P g J hJ hP
    exact ⟨restrictedWord_closing_edge P g J, farOnlyOutput_restricted_tree P g J hJ hP⟩

end
end SM
