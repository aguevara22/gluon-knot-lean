# Integer single-triple response and physical deletion roots

Accepted original claims remain **19/132 (14.39%)**. Original checklist:
38/191 (19.90%); expanded checklist: 39/192 (20.31%); final targets: 0/8.
This work adds 30 checked candidate declarations, not 30 accepted source claims.

The single-triple response now accepts an arbitrary unordered critical support
at any physical root. It constructs the unique increasing boundary reading,
transports the sign-change premise through the actual permutation, preserves
physical pairwise distinctness, and constructs nonzero affine coordinates.
The result covers arity three as well as larger polygons. A companion theorem
proves the equation for every valid affine coordinate choice.

The final equations use integer tree coefficients and integer gap values. The
gap value is one on a formal leaf; on a nonleaf it is the actual tree coefficient
of the closed endpoint polygon, whose G1 and minimum arity are proved. Integer
U/V select these values or the unit array according to the source epsilon.
Cast lemmas identify these outputs with the earlier formal transforms. The
response is specialized to the rationals, then cast injectivity recovers the
integer equality. No integrality is asserted for inverse coordinates.

One fixed integer sign d is proved to be -1 or 1, and the geometric sign
difference is 2*d. This is the exact doubled form of the source half-jump. The
proper-span branch uses the actual contracted polygon and its proved root/G1/
arity data; the full-span branch uses the U-product plus V-product. Gap and
contracted inputs are at the wall center. Both nearby side parameters are
independent and share one proved positive radius.

The next application is the flat law. Seven additional candidates prove that
the existing fusionIndex realizes the deletion part of def:induced-roots:
both incident roots map to the predecessor-to-successor fused edge; each
remaining root retains both physical endpoints in order. The retained label is
unique, and its parametrized physical edge agrees for every parameter. This
does not prove the half-map definition or the flat equation itself.

## Checked evidence

| Candidate group | Declarations | Successful root session |
|---|---:|---:|
| UnorderedCriticalTriple | 8 | 94314, second attempt |
| IntegerCriticalGaps | 10 | 69894, first attempt |
| IntegerSingleTripleResponse | 3 | 74454, second attempt |
| UnorderedIntegerSingleTripleResponse | 2 | 17021, first attempt |
| PhysicalDeletionRoots | 7 | 15649, first attempt |

Every successful session exited 0; every printed axiom trace uses only propext,
Classical.choice and Quot.sound, or a subset. The failed unordered attempt
(4424) and integer-cast attempt (36650) are preserved. Their repairs changed
proof steps only: an explicit sign-negation rewrite replaced looping simp,
and the named type parameter to Int.cast_injective was corrected to alpha.
No source statement was changed to make a proof pass.

checks/verify_source_packaging_candidates.py verifies the 30 recorded traces,
43 distinct evidence files, 459 frozen baseline files and all 327 canonical
modules. Its diagnostic receipt is checkpoint-076-verification.json. This is
evidence verification, not a new canonical build or statement-fidelity approval.
The last canonical audit remains checkpoint 070. Passing bodies are frozen.

Separate-agent technical reviews use the same currently available model. They
are useful source comparisons, but do not supply the stronger statement and
definition-fidelity approval requested by the user. The accepted map, axiom
policy, canonical modules, sources and supplied references remain unchanged.
The row thm:single-triple remains pending; neither the final corner theorem nor
the soft theorem is newly accepted. Stronger review and controlled canonical
integration remain required for acceptance.

Reporting maintenance: a startup rerun changed only the UTC field of checkpoint
075's diagnostic verification report. Its checkpoint hash was transparently
rebound after all evidence reverified unchanged. The helper now preserves the
report bytes on identical reruns; the revalidation note records both hashes.
No proof or acceptance evidence was replaced by this maintenance.

Next: decisions/flat-boundary-specialization-next.md. Questions remain local and
nonblocking; the author need not choose ordering, coordinates, or implementation.
