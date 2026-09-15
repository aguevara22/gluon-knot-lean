# Next source unit after full flat-side geometry

COMPLETED: the full original lem:wall-sides is independently accepted as
SM.wall_sides. Candidate039 passed; the complete review is
reviews/lem-wall-sides.json. All V localization and exact T visit exchanges are
implemented. Next: cusp-sides-next.md. The larger def:walls remains pending.
This file retains the original full source plan; do not redo its completed work.

Historical implementation plan for original lem:wall-sides.
Source: reference/SM/sm-1-polygons.tex:710–750 (named wall definitions) and
896–1020 (all sides clauses and proof). Keep frozen sources unchanged.

Implement transparent source predicates for F, K, V, T, E and C. Each must use
actual centre zero sets, segments, sign changes and actual crossing parameters.
Retain all remoteness requirements. In V distinguish bigon/sliding by the two
actual nonzero neighbour chirotope signs. In T require the three actual parameter
differences to change sign, not a derivative or supplied permutation. F already
has a fully implemented candidate geometric theorem. The full def:walls row
must remain pending until mutual exclusivity, side conventions, actual newborn
pair, empty cusp and fixed cyclic transport are all established; this may depend
on the separate full lem:cusp-sides. Do not manufacture cusp side uniqueness by
choice before proving exactly one actual crossing side.

For the full lem:wall-sides, establish the following source clauses:

1. Central distinctness and nonzero edges follow from at most one zero point
   triple (n>=4). Prove V/E remoteness implies n>=5 and C/T supports imply n>=6.
   Exclude consecutive zero triples for V/T/E/C using their actual index sets;
   this yields every central turn nonzero and Regular. F uses flat_sides.
2. All chirotopes outside the actual central zero set retain nonzero signs on
   one neighbourhood. Derive this from finite central nonzero determinants.
3. Classify every remote segment pair. A permitted endpoint incidence in V/E
   must be exactly M on E_a; in T/C there is none. Collinear overlap would give
   multiple zero triples. Use actual finite-segment stability for every other
   pair, including parallel disjoint pairs.
4. For E, each exceptional contact leg is compact-disjoint from E_a because
   its supporting line meets the base line only at the exterior M. For C,
   no exceptional pair exists. Derive actual CrossingGeometry, G2 and vertex
   exclusion, and then actual sorted visit/word records at zero and nearby.
   Do not evaluate Generic-only records at nongeneric E/C centres.
5. For V, prove the actual two-line intersection formula using h=det(D,M-A)
   and h_U=det(D,U-A): r=-h/(h_U-h), q=M+r(U-M). On the opposite-sign side,
   show both r in (0,1) AND the actual base-edge parameter in (0,1). The latter
   follows by continuity and strict central contact; line straddling alone
   is insufficient. Neighbour signs persist and are nonzero, so equal signs
   give both/neither crossings and opposite signs give exactly one each side.
   Prove the exact symmetric difference/exchange of unordered edge supports.
6. Localize every newborn V crossing near its actual contact parameter.
   Exclude persistent visits at that parameter from the singleton zero-set
   hypothesis. Use finitely many strict parameter separations to obtain one
   crossing-free contact neighbourhood. Every other persistent pair's order
   remains unchanged; spell out these actual comparisons.
7. For T, use full accepted triple_sides for adjacent triangle visits. Prove
   every nontriangle comparison persists, and combine the three actual
   SignChanges conditions with those adjacency assertions to prove precisely
   the three stated swaps. Central triangle visits coincide, so do not require
   global CrossingGeometry/G2 at the triple centre or a unique central word.
8. Assemble ALL F/V/T/E/C clauses on one genuine positive radius. Preserve
   source domains and actual geometric crossing/visit meanings. Review full
   transparent predicates, parameter domains, bodies and cyclic conventions
   before accepting lem:wall-sides. Partial predicates/helpers add no original
   claim count. Keep def:walls pending if its cusp/side clauses are unfinished.

Independent review must bind the exact final files and full audited semantic
closure. Do not alter original lem:shift: its separately verified obstruction
remains local and does not prevent this work.

## Existing proofs to reuse first

- SinglePointTriple already proves actual central vertex injectivity and nonzero
  edges from a singleton point-zero set for n>=4. TurnSupports supplies the
  exact turnSupport and its cardinality/injectivity. Generalize the nonzero-turn
  consequence to any singleton support unequal to every turnSupport, then
  discharge that combinatorial condition separately for V/E/C.
- WeakGeometry already proves turns_successive_intersection,
  turns_adjacent_intersection and weak_base_common_interiors_remote from actual
  nonzero turns/edges, without G1. Do not duplicate FlatAdjacent's special-case
  proof. Combined with concurrenceTriples=empty these give full G2 at V/E/C
  centres, despite V's allowed vertex contact.
- SingleTripleTransverse already proves every actual remote segment meeting is
  transverse for any singleton point-zero set, not just a flat support. For E/C
  combine it with actual nonincident-vertex exclusion and full G2 to derive
  CrossingGeometry and reuse GeometricRecords/FlatSpatial's general helpers.
- V centres have permitted endpoint contacts, so they do NOT satisfy the global
  CrossingGeometry predicate, whose remote closed meetings must be interior.
  Handle only persistent transverse-interior pairs at such centres, and build
  actual punctured Generic records after the contact pair classification.
