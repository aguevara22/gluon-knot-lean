You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE proposition against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/prop-anchors-exist-source-excerpt-lines-399-405.tex.txt
   (= reference/SM/sm-5-transport.tex 399-405, prop:anchors-exist). Context, read ONLY to fix
   notation: reference/SM/sm-5-transport.tex 373-397 (def:anchors — the three cases (Z), (L), (L₀),
   the parent, the insertion vertex, the sectors) and 317-364 (lem:soft-rotation: the sectors);
   reference/SM/sm-2-amplitude.tex 996-1016 (def:soft: admissible q) and 1017-1100
   (lem:soft-generic); reference/SM/sm-1-polygons.tex 539-546 (def:admissible: admissible and
   minimal pairs), 100-130 (def:generic), 63-71 (def:chirotope), 386-406 (def:regular, rotation).
   The proof of the proposition (sm-5-transport.tex 406-460) may be read ONLY to disambiguate what
   "exactly one of the cases applies" means (its exhaustion paragraph).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/prop-anchors-exist-reviewer-input-statement.lean.txt. It contains the anchor
   structures and projections of the module SM.Anchors verbatim (SoftAnchorData, ZeroAnchor,
   LoopAnchor, LoopAnchorZero, the inductive Anchor, Anchor.data/polygon/parent/vertex/softEdge —
   these are the accepted-candidate definitions of def:anchors, reviewed separately) and the main
   declaration SM.anchors_exist. Its docstrings map notation — verify them, do not trust them.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): SoftInsertionTuple (softInsertion, SoftAdmissible, softAttachmentMinus,
   softAttachmentPlus), SoftInsertionIndices, SoftInsertionDefinition (accepted row def:soft),
   SoftGenericLemma (accepted row lem:soft-generic), SoftRotationLaw (accepted row
   lem:soft-rotation), Chambers and CyclicChambers, Admissible (Admissible, MinimalAdmissible),
   Generic (Generic), Chirotope (turn), RotationNumber and RegularDefinition (rotationNumber),
   Polygon (edge, shift, LabelledTuple), EuclideanPlane (Plane). Do NOT open
   work/lean/SM/Anchors.lean (it contains the proofs; every definition you need from it is
   reproduced verbatim in the statement file).

YOUR TASK: compare the printed sentences with the six conjuncts of SM.anchors_exist.
Sentence 1, "For every admissible (n, r) with n ≥ 4, exactly one of the cases (Z), (L), (L₀) of
def:anchors applies": conjunct 1 (stated for integer pairs (n, r): the disjunction and the three
pairwise exclusions — is "exactly one" fully rendered, and are the three case conditions exactly
those of def:anchors?). Sentence 2, "An anchor of that type exists, is generic, has n vertices and
rotation r": conjunct 2 (existence in each case, with the case hypothesis of def:anchors as the
assumption, plus the bundled Anchor under "(n, r) admissible, n ≥ 4" — note the parent count m with
n = m + 1) and conjunct 3 (every Anchor is generic and has rotation r; "n vertices" is the type
LabelledTuple (m + 1) — say whether that suffices). Sentence 3, "For a given generic parent P and
vertex j, the mixed sector and the loop sector both contain admissible vectors q": conjunct 4
(for 3 ≤ m, every generic P and every j: an admissible q in the mixed sector χ_- ≠ χ_+ and an
admissible q in the loop sector χ_- = χ_+ = τ_j — check the sector encodings). Sentence 3, "so in
case (Z) the insertion vertex may be prescribed": conjunct 5 (a zero anchor with prescribed parent
of rotation r and prescribed vertex). Conjunct 6 (prescribed parent and vertex in cases (L₀) and
(L)) has no printed counterpart: record it under stronger_than_source and say whether it is a
faithful strengthening or changes the meaning. Domain check: does any conjunct silently assume
more than the printed hypotheses, or less? Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER; any printed sub-clause without a Lean counterpart is a discrepancy. Default to
"not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
