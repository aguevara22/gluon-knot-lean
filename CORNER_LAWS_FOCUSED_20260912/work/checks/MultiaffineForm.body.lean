namespace SM

noncomputable section
open scoped Classical
variable {n : ℕ} [NeZero n]

/-- All clauses of source lem:multiaffine for the prescribed polynomial in
canonical physical triple variables. The polynomial ring is unrestricted;
the exact original tree, cut factors and fixed root are retained throughout. -/
theorem multiaffine_form (g : ZMod n) (hn : 3 ≤ n) :
    (canonicalTreePolynomial g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : MvPolynomial (IncreasingBoundaryTriple n) ℚ) ^ T.ordinaryCount *
        T.fst.tripleRootWeight g * T.ordinaryProduct (fun _ π => π.tripleOrdinaryWeight g)) ∧
    (∀ t : IncreasingBoundaryTriple n, (canonicalTreePolynomial g hn).degreeOf t ≤ 1) ∧
    (∀ (P : LabelledTuple n) (hP : G1 P),
      MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) =
        (treeCoefficient P hP g hn : ℚ)) ∧
    (∀ (I : BoundaryInterval n) (T : RootedPlaneTree I) (a b : T.CutOccurrence)
        (t : IncreasingBoundaryTriple n),
      t ∈ canonicalSupport g (T.cutTripleSupport a) →
        t ∈ canonicalSupport g (T.cutTripleSupport b) → a = b) ∧
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I), π.parts = 2 →
      ∀ k : Fin (π.parts - 1),
        formalBoundaryChi g (π.nearTriple k) = formalBoundaryChi g (π.farTriple k) ∧
        π.tripleOrdinaryFactor g k = 0 ∧
        π.tripleRootFactor g k = formalBoundaryChi g (π.nearTriple k)) ∧
    (∀ (I : BoundaryInterval n) (T : RootedPlaneTree I) (a b : T.InternalOccurrence),
      a ≠ b → T.internalInterval a = T.internalInterval b →
        T.fst.parts = 1 ∧
          ((a = T.rootOccurrence ∧ T.IsImmediateChild b) ∨
            (b = T.rootOccurrence ∧ T.IsImmediateChild a))) ∧
    (∀ (I : BoundaryInterval n) (T : RootedPlaneTree I), T.fst.parts = 1 →
      T.fst.tripleRootWeight g = 1) := by
  refine ⟨canonicalTreePolynomial_eq_signed_tree_sum g hn,
    canonicalTreePolynomial_multiaffine g hn,
    fun P hP => eval_canonicalTreePolynomial P hP g hn, ?_, ?_, ?_, ?_⟩
  · intro I T a b t ha hb
    exact T.canonical_cut_nonrepetition g ha hb
  · intro I π hp k
    refine ⟨?_, π.tripleFactors_binary g hp k⟩
    exact congrArg (formalBoundaryChi g) ((π.nearTriple_eq_farTriple_iff k k).mpr ⟨hp, rfl⟩)
  · intro I T a b hab he
    exact T.internalInterval_eq_of_distinct hab he
  · intro I T hp
    exact (T.fst.tripleWeights_unary g hp).2

end
end SM
