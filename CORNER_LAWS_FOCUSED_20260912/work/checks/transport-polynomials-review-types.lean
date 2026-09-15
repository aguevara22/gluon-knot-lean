import SM.TransportPolynomials

set_option pp.universes true

#print SM.ScalarCoordinate
#print SM.CoordinatePolynomial
#print SM.scalarCoordinateEquiv
#print SM.areaPolynomial
#print SM.linePolynomialRow
#print SM.concurrencePolynomial
#print SM.VertexControlName
#print SM.EdgeControlName
#print SM.PolynomialControlName
#print SM.selectThree
#print SM.namedControlPolynomial
#print SM.polynomialControlFamily
#print SM.RemainingPolynomial
#print SM.isolateCoordinate
#print SM.coordinateSlope
#print SM.coordinateIntercept
#print SM.coordinateResultant
#print SM.specializeCoordinate
#print SM.PolynomialControlsStatement
#print SM.transport_polynomials
#check @SM.polynomial_vars_subset_of_dvd
#print axioms SM.polynomial_vars_subset_of_dvd
#check @SM.polynomial_variable_of_eval_ne
#print axioms SM.polynomial_variable_of_eval_ne
#check @SM.areaPolynomial_vertexSupport
#print axioms SM.areaPolynomial_vertexSupport
#check @SM.sixEndpointMap_injective
#print axioms SM.sixEndpointMap_injective
#check @SM.concurrenceDet_extendSixEndpointTuple
#print axioms SM.concurrenceDet_extendSixEndpointTuple
#check @SM.concurrencePolynomial_X_endpoint
#print axioms SM.concurrencePolynomial_X_endpoint
#check @SM.concurrencePolynomial_vertexSupport
#print axioms SM.concurrencePolynomial_vertexSupport
#check @SM.endpointCollapseWitness_ne_zero
#print axioms SM.endpointCollapseWitness_ne_zero
#check @SM.concurrence_not_associated_of_crossed_slots
#print axioms SM.concurrence_not_associated_of_crossed_slots
#check @SM.cycle_no_reversed_edge
#print axioms SM.cycle_no_reversed_edge
#check @SM.concurrence_associated_first_mem
#print axioms SM.concurrence_associated_first_mem
#check @SM.concurrence_not_associated_of_tail_sets_ne
#print axioms SM.concurrence_not_associated_of_tail_sets_ne
#check @SM.area_concurrence_not_associated
#print axioms SM.area_concurrence_not_associated
#check @SM.namedControlPolynomial_irreducible
#print axioms SM.namedControlPolynomial_irreducible
#check @SM.namedControlPolynomial_ne_zero
#print axioms SM.namedControlPolynomial_ne_zero
#check @SM.namedControlPolynomial_not_associated
#print axioms SM.namedControlPolynomial_not_associated
#check @SM.namedControlPolynomial_affine
#print axioms SM.namedControlPolynomial_affine
#check @SM.namedControlPolynomial_injective
#print axioms SM.namedControlPolynomial_injective
#check @SM.polynomialControlFamily_card
#print axioms SM.polynomialControlFamily_card
#check @SM.vertexControlNameOf_coverage
#print axioms SM.vertexControlNameOf_coverage
#check @SM.edgeControlNameOf_coverage
#print axioms SM.edgeControlNameOf_coverage
#check @SM.coordinate_affine_decomposition
#print axioms SM.coordinate_affine_decomposition
#check @SM.coordinateSlope_ne_zero
#print axioms SM.coordinateSlope_ne_zero
#check @SM.coordinateResultant_ne_zero
#print axioms SM.coordinateResultant_ne_zero
#check @SM.specializeCoordinate_eval
#print axioms SM.specializeCoordinate_eval
#check @SM.specializeCoordinate_simple_root
#print axioms SM.specializeCoordinate_simple_root
#check @SM.specializeCoordinate_no_common_root
#print axioms SM.specializeCoordinate_no_common_root
#check @SM.transport_polynomials
#print axioms SM.transport_polynomials

-- Independent check that n ≥ 3 supplies the only auxiliary size instance.
example (n : ℕ) (hn : 3 ≤ n) : ∃ h : NeZero n, @SM.PolynomialControlsStatement n h := by
  letI : NeZero n := ⟨by omega⟩
  exact ⟨inferInstance, SM.transport_polynomials hn⟩
