# Full visible-chamber tree continuation: candidate checkpoint083

Proved a Lean-checked candidate for all of source thm:A-continuation, culminating
in SM.A_continuation. For every fixed physical root and n>=3, there is a unique
integer-valued function on the whole weakly generic locus that is constant on
actual visible connected-component chambers and agrees with the original
rooted tree coefficient on every generic tuple. This includes weak tuples
with simultaneous silent zeros. No gate at zero is evaluated, and no root
independence or final corner theorem is claimed.

All24 new declarations remain candidates. Accepted source proofs19/132
(14.39%), original checklist38/191 (19.90%), expanded39/192 (20.31%), and
final corner targets0/8 are unchanged. Six nonauthor same-model technical
reports found no defect within their scopes. They do not provide the stronger
statement/definition-fidelity approval requested by the user. Controlled
canonical integration and acceptance checking remain subsequent steps.

The proof first derives every needed wall exclusion from WeakGeneric itself:
flat and cusp events have zero turns, vertex contacts violate nonincident
closed-segment exclusion, and triple events violate actual interior-concurrence
G2. A simple event at a weak center therefore has an actual E or C witness.

An actual continuous path in the open weak locus has compact Euclidean-coordinate
image. A proved positive thickening tolerance keeps a uniformly close path
inside the same locus. The existing relative-general-position theorem supplies
that close endpoint-fixed path, regularity, finite events and the actual shifted
wall germs. Weak regularity is derived from nonzero turns; the caller supplies
no event certificate, silent-law premise or R proposition.

Generic parameter density is proved from the actual punctured-generic shifted
germs at nongeneric parameters. At generic parameters, finite chi persistence
gives pairwise local tree-value constancy. At an event, the proved E/C laws and
same-side constancy identify every nearby generic path value, using the exact
whole-tuple identity with the germ. A proved dense-local-pair extension/gluing
lemma then gives equality of arbitrary generic values on the connected unit
interval. Endpoint tuple identities return the result to the input weak path.

The genuine visible component supplies a finite polygonal chain and hence an
actual path within the weak locus. Its generic points therefore have one
common coefficient. Ambient generic density in the actual open component
supplies a generic point in every visible chamber. The chosen common generic
value defines the continuation; choice independence, chamber constancy,
agreement and uniqueness are all proved. No replacement by sign cells occurs.

| Candidate group | Declarations | Successful root session |
| --- | ---: | ---: |
| DenseLocalPairs | 2 | 79413 |
| WeakCenterSilent | 5 | 15307 |
| GermPathGeometry | 2 | 54231 |
| WeakPathTolerance | 2 | 1291 |
| TreePathLocal | 4 | 1045 |
| TreePathGluing | 4 | 5804 |
| VisibleTreeContinuation | 5 | 90683 |

All seven groups exited0 with only propext, Classical.choice and Quot.sound in
their printed axiom traces. Failed first runs32126,26364,91465 are preserved.
Their repairs respectively supply existing radius positivity to arithmetic,
transport complete GenericTuple equality through the dependent coefficient
function, and add the canonical SilentCenter import. Every theorem type is
unchanged; the last body's bytes are identical. Failed traces are never
counted as passing evidence.

verify_tree_continuation_candidates.py passed24 new traces,85 candidate evidence
files,714 frozen baseline hashes and327 unchanged canonical modules. The final
receipt binds62 exact embedded bodies, its prototype and successful log.
Accepted definitions/axioms/map, sources and prior passing candidates remain
unchanged. Last canonical audit is070; no whole-library audit was rerun.

Six technical reports cover dense-local-pair topology, weak-center geometry,
path geometry/tolerance, local tree transport, path gluing and full continuation.
The response reviewer authored WeakCenterSilent; root independently reviewed
that body. This relationship is disclosed in the later reviews and does not
supply stronger-model fidelity approval.

Evidence: checks/checkpoint-083-verification.json and seven receipts;
checkpoints/goal-turn-083-candidates.json records candidates separately from
the canonical acceptance map. All kernel handles are terminal. Reporter79758
stopped with exit0; retain the hourly app automation and start one ten-minute
watcher when execution resumes.

Next execute decisions/multiaffine-after-continuation.md for full source
lem:multiaffine: the prescribed polynomial in canonical triple variables over Q,
its unrestricted degree bound, every tree cut-occurrence/unary/binary clause,
and exact G1 evaluation. The goal remains active; the unrelated shift-scope
obstruction does not stop this branch.
