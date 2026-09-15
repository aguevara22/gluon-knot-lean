# Soft newborn parameters and point

Author: /root/review_contraction_candidates, another agent of the same currently available model as root. This is an untested implementation draft, not an independent self-review, stronger-model fidelity approval, or source acceptance. No Lean kernel, build or audit was run. Root owns checking and independent review. Only new work/checks files and this note were written.

The source is def:soft and lem:soft-generic, SM2 lines 991–1150, particularly the supporting-line limit paragraph at 1086–1113. The twelve declarations are:

- `softNewbornIncomingParameter`, `softNewbornReturnParameter`, `softNewbornPoint`: Cramer's first/second parameters for the actual enlarged incoming and return bases/directions, and the incoming edgePoint at the first parameter. The total quotients are defined at every real parameter; geometric assertions require a proved nonzero denominator.
- `softNewborn_det_zero_ne`: n>=3 and parent G1 make the actual direction determinant at zero nonzero. The unchanged incoming edge and zero-parameter return are precisely the parent directions at j.
- `softNewborn_zero_meeting`: the actual incoming parameter one and return parameter zero meet at zero. The enlarged successor identity identifies their common point as the old attachment vertex, including the physical wrap.
- `softNewborn_values_zero`: Cramer's determinant identities applied to that meeting, followed by division by the proved nonzero determinant, give first parameter one and second parameter zero. Evaluating the actual incoming endpoint gives point P j.
- `softNewborn_continuousAt_zero`: continuous actual inserted vertices and edges feed the canonical Cramer continuity theorems. The nonzero denominator is derived from parent G1; affine point evaluation then gives point continuity.
- `softNewborn_limits`: the preceding continuity and exact zero values give two-sided limits 1, 0 and P j. These statements need no admissibility, child G1 or child Generic assumption.
- `softNewborn_small_det_ne`: continuity of the actual directions preserves their nonzero determinant on a two-sided positive-radius neighborhood.
- `softNewborn_parameters_intersection`: with an explicit nonzero actual determinant, Cramer's rule solves the two actual edgePoint equations. This is an algebraic helper, not a presumed crossing.
- `softNewborn_crossing_data`: for any actual crossing of this transverse pair, the chosen crossing parameters solve the same equations. Uniqueness of the two parameters identifies both choices with the constructed Cramer functions, then their edgePoint equality identifies the crossing point. No G1 or G2 is needed for this identification.
- `softNewborn_small_loop_data`: for parent G1 and actual SoftAdmissible, take the minimum of the determinant, local crossing and enlarged-G1 radii. On every positive parameter in this interval, the loop sign conjunction produces the actual unordered crossing, and derived child G1 makes both chosen parameters strictly interior. Their established identities transfer strictness to the constructed parameters and identify the constructed point with the actual crossing point.

The domain retains arbitrary j and every n>=3. The supporting-line statements allow arbitrary q; the final loop assertion uses exactly the actual admissibility predicate. Its radius is selected before the positive parameter and loop implication. No Generic assumption at the duplicate-vertex zero tuple, global soft-family lemma, root restriction, independence oracle or current parent-edge correspondence body is used.

This is local incoming/return data only. The proof does not assert that this pair is the only newborn among all polygon edges, prove separation from inherited crossing points, G2, a single chamber, edgewise visit order, or cyclic Gauss-word adjacency. Its point/parameter identification makes the two-sided supporting-line limits applicable to the actual crossing throughout the positive loop interval; explicit global crossing families remain for assembly.

The prototype unions canonical imports from the frozen passing LocalCrossing and G1 prototypes, orders each body's source receipt entries by actual position in that passing prototype, and deduplicates. The order is BoundaryTripleSupports, CanonicalTripleSigns, SoftInsertionIndices, SoftInsertionSuccessors, SoftInsertionTuple, SoftLocalDeterminants, SoftFamilyLocalCrossing, SoftFamilyG1, then SoftNewbornParameters. Each body occurs once. Ordered paths and all source receipt/body hashes are recorded in the dependency JSON files. Exact first-draft body/prototype copies were made before root testing.

## Exact draft hashes

- work/checks/SoftNewbornParameters.body.lean: 148ce2689a60a296274f4a665b2212366e30c0562bffa36e911a104b2fb7876e
- work/checks/SoftNewbornParameters.prototype.lean: 4f48497e246d129872524dd7b549d211c4871933940ac6ce8979d5e03669a1e5
- work/checks/SoftNewbornParameters-first-draft.body.lean: 148ce2689a60a296274f4a665b2212366e30c0562bffa36e911a104b2fb7876e
- work/checks/SoftNewbornParameters-first-draft.prototype.lean: 4f48497e246d129872524dd7b549d211c4871933940ac6ce8979d5e03669a1e5
- work/checks/SoftNewbornParameters-body-dependencies.json: 0234e6109d3368ac0efb3680f2637599a18e340c4fd47653cc70ea7cff88537b
- work/checks/SoftNewbornParameters-draft-dependency-bindings.json: 058d0fd22b45d2cdae7743b579a85d785da70454e7947996bcf96768ffe53aac
- reference/SM/sm-2-amplitude.tex: 014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf
