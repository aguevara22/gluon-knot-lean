import SM.DirectionPolynomials

-- Independent review evidence only; not part of the theorem library.

example {n : ℕ} (hn : 3 ≤ n) : Nontrivial (ZMod n) := by
  letI : Fact (1 < n) := ⟨by omega⟩
  infer_instance

#check @SM.determinantPolynomial_irreducible
#print axioms SM.determinantPolynomial_irreducible
#check @SM.polynomialShearSub_comp_add
#print axioms SM.polynomialShearSub_comp_add
#check @SM.polynomialShearAdd_comp_sub
#print axioms SM.polynomialShearAdd_comp_sub
#check @SM.polynomialShear
#print axioms SM.polynomialShear
#check @SM.scalarCoordinateEquiv
#print axioms SM.scalarCoordinateEquiv
#check @SM.eval_areaPolynomial
#print axioms SM.eval_areaPolynomial
#check @SM.areaPolynomial_irreducible
#print axioms SM.areaPolynomial_irreducible
#check @SM.areaPolynomial_ne_zero
#print axioms SM.areaPolynomial_ne_zero
#check @SM.separatedEdgeHeads_pair
#print axioms SM.separatedEdgeHeads_pair
#check @SM.tailDirectionTranslation
#print axioms SM.tailDirectionTranslation
#check @SM.eval_directionDeterminantPolynomial
#print axioms SM.eval_directionDeterminantPolynomial
#check @SM.directionDeterminantPolynomial_irreducible
#print axioms SM.directionDeterminantPolynomial_irreducible
#check @SM.directionDeterminantPolynomial_ne_zero
#print axioms SM.directionDeterminantPolynomial_ne_zero
