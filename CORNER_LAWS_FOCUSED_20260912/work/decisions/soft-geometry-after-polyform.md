# Next source dependency: the complete soft-family geometry

Checkpoint087 checks the full cor:polyform candidate, SM.polynomial_form_continuation.
For every weak tuple and arbitrary fixed root, the unique integer continuation
equals the prescribed canonical physical-triple polynomial. Fixing exactly its
nonzero entries gives the constant polynomial in the unrestricted free ring.
No G1 premise at the weak tuple, realizability restriction, root independence,
or value of a step-function gate at zero is introduced. Stronger fidelity and
controlled canonical integration remain pending; accepted source proofs19/132.

Next read and implement def:soft (reference/SM/sm-2-amplitude.tex:991–1010)
and ALL four clauses of lem:soft-generic (1012–1150). No Soft module or candidate
was found in work/lean/SM or work/checks at087. This is a needed dependency of
the final corner soft theorem, not a replacement of that target by A-soft.

Begin with an explicit insertion map from the old cyclic labels into n+1 labels,
the newborn label, and the identification of unchanged, incoming, soft and return
edges. Prove the successor/wrap clauses and exact tuple/edge equations. Source
physical labels are1 throughn, with residue0 representing labeln; use the actual
canonicalPosition convention if implementing insertion via ordered positions.
Any temporary rotation or internal representation needs a proved transport back
to arbitrary j. Do not silently fix j or restrict the eventual root.
InsertionIndices already supplies insertIndex, insertedIndex, exhaustiveness,
and successor/predecessor wrap lemmas. Its append convention inserts at the
cyclic cut; inspect it for reuse with explicit transport. InsertedTuple and
VertexInsertion put the new point on the old edge, so their geometric family
is not the admissible transverse soft family and must not be substituted for it.

Define the actual tuple with newborn P(j)+epsilon*q and source admissibility.
Prove the two attachment-sign identities for every positive epsilon, and the
new-triple determinant formulas. Original triples are unchanged; new triples
either have a nonzero parent limit or include both j and the newborn and have
the explicit nonzero epsilon factor. Use finiteness to obtain one positive
interval with G1 and constant signs. The parent is fully Generic, not merely G1.

Prove the complete crossing geometry. The soft segment misses all remote parent
segments by compact separation; its two incident intersections are exactly the
endpoints. Disjoint return/remote pairs stay disjoint without requiring their
directions to be independent. Parent crossings persist with continuous Cramer
parameters and unchanged direction-determinant signs. Existing canonical tools
include disjoint_segments_persist in SegmentStability, ContinuousGeometry's Cramer
continuity and strict-order persistence, and Crossings' unique points/parameters.
Read their exact hypotheses before composing them.

For the incoming/return pair, prove both strict-straddle tests. Their conjunction
gives exactly the loop sector chi_minus=chi_plus=tau; there is no newborn crossing
in the same-sign or mixed sectors. Prove its point tends to P(j), incoming
parameter to1 and return parameter to0. Preserve all inherited visit orders and
separate every crossing point; derive G2 from the exhaustive pair classification.
Use the connected positive parameter interval to obtain one actual labelled
generic chamber. Prove retained turns, the two attachment turns, return direction
limits, and both ordered determinant signs. Build the actual inherited crossing
and visit correspondence in GaussWord/GaussVisits. In the loop sector prove the
two newborn visits are cyclically adjacent and deleting them yields the parent's
word. Clauses(i)–(iv) all belong to the target; G1 stability alone is incomplete.

After this geometry, continue the dependency DAG toward thm:C-soft and the corner
wall laws. If the rooted-tree chain consumes thm:A-soft (1152–1468), read its full
duplication proof and both boundary cases before implementation. Do not infer a
soft-root case or divide by a selector that can vanish. All soft sectors remain
required, including mixed zero-selector sectors.

Freeze all passing candidates, accepted maps,327 canonical modules and supplied
sources. Root owns one Lean kernel/build/audit at a time; independent reviewers
run none. Preserve exact failed body/prototype/log before any repair. The087
assembly failure was only body ordering: receipt dictionary order was not a
dependency order. Sort embedded bodies by their actual positions in their
already passing prototypes, then deduplicate; keep every body exact.

Keep separate candidate ledgers and technical reviews. Retain hourly app progress,
start one ten-minute watcher on resumption, relay its reports, and stop that exact
watcher on exit. Accepted source19/132 (14.39%), original checklist38/191 (19.90%),
expanded39/192 (20.31%), final targets0/8. Goal active; no author question is needed.
