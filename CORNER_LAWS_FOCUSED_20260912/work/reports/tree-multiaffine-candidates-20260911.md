# Full multi-affine form checked as a candidate

Checkpoint084 proves SM.multiaffine_form, covering all of source lem:multiaffine
(sm-2-amplitude.tex:714–797). The prescribed polynomial is in the unrestricted
rational ring on canonical physical unordered triples. It has degree at most
one in every variable and evaluates to the original integer tree coefficient
(cast to rationals) on every G1 tuple, at the same arbitrary root.

The theorem also exposes the exact signed finite-tree sum, physical triple
nonrepetition across actual node-and-cut occurrences, binary formal near/far
coincidence with ordinary factor zero and root factor equal to that entry,
and the full shared-interval exception for the unary root and its immediate
sole child. The unary root's product is one. Binary ordinary nodes are retained.
No realizability relation, quotient X^2=1, composition-variable replacement,
G2 premise, root independence, R premise, or caller-disjointness condition is
used for the degree conclusion. The gate API is never evaluated at zero.

Ten isolated/assembled groups add126 named kernel-checked candidate declarations,
including definitions and helpers; this is not126 additional source claims:

| Group | Declarations | Passing root session |
| --- | ---: | ---: |
| CompositionTripleSupports | 9 | 72033 first |
| CanonicalTripleSigns | 11 | 60299 second |
| FormalOrderedChi | 14 | 82948 second |
| FormalTriplePolynomial | 16 | 95654 first |
| PlaneTreeTripleSupports | 23 | 46937 second |
| SupportedMultiaffine | 14 | 75825 second |
| PlaneTreeInternalIntervals | 19 | 17495 first |
| CanonicalTripleDegree | 13 | 88201 first |
| TreeTripleDegree | 6 | 61050 first |
| MultiaffineForm | 1 | 20791 first |

All successful traces use only propext, Classical.choice and Quot.sound.
The four failed first runs11385,20845,65349,29366 are preserved exactly; their
repairs address imports/dependent elaboration/proof tactics, with every theorem
type unchanged. The evidence verifier passed126 traces,43 unique evidence files,
765 frozen baseline files and327 unchanged canonical modules. It did not rerun
the whole canonical build/audit (last070) or grant source fidelity. The seven
nonauthor same-model technical reviews found no defect in their stated scopes;
all quoted evidence hashes were checked. Reviewers' dependency authorship is
explicit and those dependencies have separate root reviews.

These additions remain candidates. Stronger statement/definition-fidelity
approval and controlled canonical integration/checker acceptance remain pending.
Accepted definitions, axioms, declaration map,327 canonical modules, sources
and all prior passing candidates are unchanged. Source proofs19/132 (14.39%);
original checklist38/191 (19.90%); expanded checklist39/192 (20.31%); final
corner targets0/8. This is a rooted-tree dependency, not a final corner theorem.

See checks/MultiaffineForm.body.lean for the complete type and proof,
checks/MultiaffineForm-prototype-result.json for exact embedded evidence,
checks/checkpoint-084-verification.json for verification, and the separate
checkpoints/goal-turn-084-candidates.json ledger. Next execute
 decisions/line-gap-after-multiaffine.md for full pf:line-gap, then
pf:formal-cancellation and cor:polyform. No author question is needed.
