# Full polynomial-continuation corollary checked as a candidate

`SM.polynomial_form_continuation` now passes Lean for the complete source
`cor:polyform` (SM2, label at line937). For every size n≥3, every fixed root,
and every weak tuple, the unique integer visible-chamber continuation equals
the prescribed canonical physical-triple polynomial. Fixing exactly the nonzero
chirotope entries yields the constant polynomial in the unrestricted rational
polynomial ring. All remaining variables stay independent, including simultaneous
silent zeros and assignments that are not realizable chirotopes.

The proof identifies the full open/root recursion with the far-only output,
retaining every cut factor and unary term. The explicit freezing homomorphism
preserves the signed physical labels. Its residual boundary array is proved
supported on the geometric zero entries, so the previously proved general
silent-cancellation theorem applies. A generic tuple in the actual visible chamber
preserves all initially nonzero signs; generic agreement and chamber constancy
then identify the constant with the already proved continuation. Its specification
does not assume polynomial agreement. No original step-function gate is evaluated
at zero, and no extra G1 premise is imposed on the weak tuple.

| Candidate group | Declarations | Successful root kernel |
|---|---:|---:|
| FormalNearFarRecursion | 3 | 19470 |
| CanonicalTreeFarOutput | 5 | 15687 |
| CanonicalFreezing | 9 | 14458 |
| VisibleGenericSignPersistence | 1 | 72929 |
| CanonicalSilentConstancy | 5 | 34366 |
| PolynomialContinuation | 3 | 34627 |

All26 declarations have axiom traces containing only `propext`, `Classical.choice`
and `Quot.sound`. The final prototype embeds90 exact dependency bodies.
Two failed runs are preserved: an invalid filter-membership field notation,
and an assembly that used receipt dictionary order as dependency order.
The repairs changed no theorem statement; the assembly repair changed no body.

Independent same-model technical reviews cover all six groups and found no
mathematical defect in their stated scope. Two sealed metadata notes document
one truncated header and16 header hashes that included a trailing ASCII space.
The originals remain preserved; corrected displayed-text hashes and all247
quoted file bindings were checked. These corrections affect review metadata,
not proof files or kernel results.

Evidence verification checked26 traces,113 evidence files,977 frozen baseline
files and327 unchanged canonical modules. See
[proof verification](../checks/checkpoint-087-verification.json),
[review binding verification](../checks/checkpoint-087-review-bindings.json),
[candidate ledger](../checkpoints/goal-turn-087-candidates.json), and
[final proof](../checks/PolynomialContinuation.body.lean).

Stronger statement/definition fidelity and controlled canonical integration
remain pending. No source claim is newly accepted: source proofs19/132 (14.39%),
original checklist38/191 (19.90%), expanded checklist39/192 (20.31%), final corner
targets0/8. The canonical declaration map remains frozen; its empty review queue
does not enumerate the separate candidate ledger. No whole-library audit was
rerun; the last canonical audit is070.

Goal active. Next implement the exact soft insertion and all four clauses of
the soft-family geometry, including inherited crossing order and the unique
newborn loop, following [the next execution note](../decisions/soft-geometry-after-polyform.md).
This corollary is a dependency of the corner-law project, not its final theorem.
