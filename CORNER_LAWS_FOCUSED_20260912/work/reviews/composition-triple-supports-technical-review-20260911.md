# Composition cut supports: technical review

Reviewer root did not author CompositionTripleSupports; author is
review_contraction_candidates. This is independent same-model technical evidence,
not stronger statement/definition-fidelity approval. No source row is accepted.

Compared all nine declarations with full source lem:multiaffine,
sm-2-amplitude.tex:714–797, actual IntervalComposition, nearTriple, farTriple,
cutSet, part_consecutive, and part_order. No defect found in this scope.

The support is the actual finite set containing the near and far triples. Near
injectivity uses the strictly increasing middle cut; the near/far equivalence
projects endpoints through the injective cut map and forces exactly two parts,
then projects the common middle to identify cuts. Conversely the only binary
cut gives both endpoints. It does not omit binary or unary compositions.

Cut support disjointness exhausts all four near/far pairs, deriving equality of
the actual factor indices in each forbidden overlap. Bounds follow monotonicity
between actual first/last cuts. The middle is an actual cut, which would lie
strictly between consecutive child endpoints if a parent triple fit inside a
child. This supplies the contradiction without a caller separation premise.

Sibling uniqueness uses the ordered child endpoints and the strict distance
between the lower and upper triple positions. A shared boundary endpoint cannot
contain both. No geometry, n>=3, nonzero gate, tree support or disjointness
hypothesis has been inserted. These are local combinatorial prerequisites;
tree-level nonrepetition, formal variables, polynomial degree and exact
evaluation remain separate work.

Root first kernel72033 exited0. Nine traces use only propext, Classical.choice
and Quot.sound. The passing body/prototype/log and receipt are frozen.

work/checks/CompositionTripleSupports.body.lean SHA-256: c6600e67a028ccffb28c0aae1d02e782b689f24e823ddd3a49b297e0cb069cff
work/checks/CompositionTripleSupports.prototype.lean SHA-256: fd5de6917a5ad985205cea5a851c60e12e74ca1df373ed9eb7f22ab06032c5c3
work/checks/CompositionTripleSupports-first-kernel.log SHA-256: c0d65e762f6d8d62a83bf16081ae3c1fde7889840e1a34d66f291bd5bd6807b0
