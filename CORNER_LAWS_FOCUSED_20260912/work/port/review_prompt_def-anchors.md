You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/def-anchors-source-excerpt-lines-373-397.tex.txt
   (= reference/SM/sm-5-transport.tex 373-397, def:anchors). Context, read ONLY to fix notation:
   reference/SM/sm-2-amplitude.tex 996-1016 (def:soft: the soft insertion P^{(j,q)}_ε, admissible q,
   the labelling of the inserted polygon) and 1017-1100 (lem:soft-generic, in particular the bound
   ε₀ = ε₀(P,j,q) and the three sectors in clause (iv)); reference/SM/sm-5-transport.tex 317-364
   (lem:soft-rotation: the same-sign / mixed / loop sectors and the rotation law);
   reference/SM/sm-1-polygons.tex 539-546 (def:admissible: admissible and minimal pairs), 206-240
   (def:chamber), 100-130 (def:generic), 63-71 (def:chirotope: turns τ_j), 386-406 (def:regular,
   rotation number), 27-62 (def:polygon: labels, edges E_j from μ_j to μ_{j+1}).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/def-anchors-reviewer-input-statement.lean.txt. It contains (1) the anchor
   structures and projections of the module SM.Anchors verbatim (SoftAnchorData, ZeroAnchor,
   LoopAnchor, LoopAnchorZero, the inductive Anchor, Anchor.data/polygon/parent/vertex/softEdge) and
   (2) the row module SM.AnchorsDefinition (bundle AnchorsDefinitionData, main declaration
   SM.anchors_definition). Its module docstrings map notation — verify them, do not trust them.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): SoftInsertionTuple (softInsertion, SoftAdmissible, softAttachmentMinus,
   softAttachmentPlus), SoftInsertionIndices (softOldIndex, softNewIndex, softNewPosition,
   boundaryIndex, canonicalPosition), SoftInsertionDefinition (accepted row def:soft),
   SoftGenericLemma (accepted row lem:soft-generic — the bound and the sectors), SoftRotationLaw
   (accepted row lem:soft-rotation), Chambers and CyclicChambers (GenericTuple, labelledChamber,
   chamber, polygonProjection; accepted row def:chamber), Admissible (Admissible,
   MinimalAdmissible; accepted row def:admissible), Generic (Generic, G1, G2), Chirotope (turn, chi),
   RotationNumber and RegularDefinition (rotationNumber), Polygon (edge, shift, LabelledTuple),
   EuclideanPlane (Plane, det). Do NOT open work/lean/SM/Anchors.lean or
   work/lean/SM/AnchorsDefinition.lean (they contain proofs; every definition you need from
   Anchors.lean is reproduced verbatim in the statement file).

YOUR TASK: decide whether the Lean structures, as pinned down by the bundle
AnchorsDefinitionData, define exactly the printed anchors. Check clause by clause:
(a) the standing hypothesis "(n, r) admissible with n ≥ 4" and its rendering as
((m : ℤ) + 1, r) with parent vertex count m (so n - 1 = m and n ≥ 4 ↔ 3 ≤ m) — is the
admissibility of (n, r) itself required anywhere, and does each case hypothesis (Z: (n-1, r)
admissible; L: (n, r) minimal with |r| ≥ 2; L₀: (n, r) = (4, 0)) match the source exactly?
(b) the common data: "generic n-gon of the form P^{(j,q)}_ε for some generic (n-1)-gon P, some
vertex j, some admissible q and some small ε > 0", and the sentence "In all three cases q is
admissible and 0 < ε < ε₀, where ε₀ = ε₀(P,j,q) > 0 is the bound of lem:soft-generic: on (0, ε₀)
the insertion is generic and lies in one chamber ... This geometric bound is part of the anchor
data" — compare with the fields bound, bound_pos, bound_spec (one labelled chamber and one
chamber of the cyclic quotient), param, param_pos, param_lt, and with the `data` clause;
(c) case (Z): parent of rotation r, q in the mixed sector (χ_- ≠ χ_+ in the convention of
lem:soft-generic (iv) / lem:soft-rotation — check the encodings softAttachmentMinus /
softAttachmentPlus against the printed χ_-, χ_+);
(d) case (L): parent of rotation r - sgn(r), vertex j with τ_j(P) = -sgn(r), q in the loop sector
(χ_- = χ_+ = τ_j);
(e) case (L₀): a triangle parent, any vertex, loop sector;
(f) "P is the parent, j its insertion vertex, and the soft edge of the anchor is its edge E_j
(from μ_j to μ_* = μ_{j+1} in the labelling of the anchor)": check the softEdge clause against
the labelling of def:soft (softOldIndex j j is the anchor label of the old vertex μ_j, the next
label carries μ_* = μ_j + εq; edge Q i = Q (i+1) - Q i);
(g) the `cases` and `projections` clauses: does the inductive Anchor carry exactly one anchor
type per case, with the case hypotheses as printed, and nothing else?
Expand definitions to primitives; say where the Lean is STRONGER or WEAKER than the printed
definition; any printed condition without a Lean counterpart, or any Lean field without a printed
counterpart, is a discrepancy. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
