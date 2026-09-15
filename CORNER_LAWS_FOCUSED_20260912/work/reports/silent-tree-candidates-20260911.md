# Full triple and silent rooted-tree laws: candidate checkpoint082

Proved a Lean-checked candidate for all of source thm:A-R3E, culminating in
SM.tree_triple_and_silent_laws. At a triple wall, every ordinary/root
composition weight, every open sum, and the full rooted output agree. At an
exterior-extension or pure-cut wall, the complete rooted outputs agree. Every
physical root and both independently chosen full germ-side parameters remain
quantified. This is a rooted-tree dependency of the corner theorem, not the
final corner state-sum theorem or soft theorem.

All23 new declarations remain candidates. Accepted source proofs19/132
(14.39%), original checklist38/191 (19.90%), expanded39/192 (20.31%), and
final corner targets0/8 are unchanged. Same-model nonauthor technical reviews
found no defect in their scopes, but do not provide the stronger statement
and definition-fidelity approval requested by the user. Controlled canonical
integration and the acceptance checker remain separate subsequent steps.

Triple data constancy derives G1 at the actual wall center, uses finite
chirotope persistence, handles repeated labels explicitly, and transports
along both entire generic sides. It preserves all composition/open-sum data,
including leaves and unary compositions; crossing order is not an input.

Exterior silence uses the actual extension line witness and closed-segment
exclusion to derive both exterior scalar ranges. At the base root, opposite
epsilons kill BOTH full-span U/V products. On each inherited arc the relevant
nonleaf U factor is zero and the critical span is proper. The three root
cases are exhaustive, including endpoint-adjacent roots; no flat/cusp or
interior-contact premise is used.

Pure-cut silence derives n>=6 and actual vertex distinctness from the source
support. Nonadjacency proves both gaps and the cyclic wrap gap have length
at least two. The span is therefore proper, while either boundary endpoint
is separately permitted. For every affine order at least one epsilon is
positive, so the nonleaf U product vanishes. These two silence laws do not
assert constancy of individual open sums. A separately proved helper removes
the local radius restriction using chirotope constancy on each full side.

| Candidate group | Declarations | Successful root session |
| --- | ---: | ---: |
| TripleTreeData | 2 | 97775 |
| SilentIntegerFactors | 4 | 44434 |
| GermTreeEquality | 1 | 29206 |
| PureCutBoundaryBounds | 4 | 38666 |
| ExtensionAffineSigns | 4 | 22631 |
| PureCutTreeResponse | 2 | 73319 |
| ExtensionTreeResponse | 5 | 63236 |
| TripleSilentTreeLaws | 1 | 2126 |

All eight groups exited0; each printed axiom trace contains only propext,
Classical.choice and Quot.sound. No successful trace contains sorryAx.
GermTreeEquality first44970 and PureCutTreeResponse first55482 failed only
because canonical imports were missing. Their exact failed bodies/prototypes
and logs are preserved; both repaired bodies are byte-identical to the
originals. The import differences are checked explicitly in the verifier.

verify_silent_tree_candidates.py passed23 traces,77 candidate evidence files,
663 frozen baseline hashes and327 unchanged canonical modules. The final
aggregate receipt binds55 exact embedded bodies, its prototype and successful
log. Accepted definitions/axioms/map, sources and prior passing candidates
remain unchanged. Last canonical audit is070; no whole-library audit rerun.

Independent technical reports are sealed for algebra/triple data, geometry,
pure-cut response, exterior response, and the final aggregate. The reviewer of
the root's response/aggregate bodies authored two geometry dependencies, whose
separate review was supplied by the root. This relationship is disclosed;
none of these reports claims stronger-model fidelity approval.

Evidence: checks/checkpoint-082-verification.json and the eight bound receipts;
checkpoints/goal-turn-082-candidates.json records candidates separately from
the canonical acceptance map. All process handles are terminal. Reporter7712
stopped with exit0; retain the existing hourly app automation and restart one
ten-minute watcher on resumption.

Next execute decisions/tree-continuation-after-silent-laws.md: prove the
unique continuation on actual visible connected-component chambers, using
proved weak openness/density and relative general position with E/C silence.
No zero-gate evaluation or replacement by sign cells is permitted. The goal
remains active; the unrelated shift-scope obstruction does not stop this work.
