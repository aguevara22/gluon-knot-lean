You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE row against its printed source:
SM:corner_laws_and_soft (row 184; FIXED name `SM.corner_laws_and_soft`; the package's FINAL target), module SM/CornerLawsAndSoft.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed source, verbatim: work/reviews/sm-corner-laws-and-soft-source-excerpt-TARGETS.md-lines-1-29.txt (= TARGETS.md lines 1-29:
   the commissioned conclusion — "the conjunction of these actual C identities, with their printed quantifiers, signs and domains", NOT
   "a theorem about a freely supplied lawful function"; "must not retain an R assumption or assume the desired laws"; the six items of
   "Required coverage"; "the normalizations and reversal/cyclic identities inherited with cor:A-lawful as stated there"; "No stronger cusp
   domain is commissioned"; "the final assembly instantiates that conditional theorem with the separately proved R result"), and
   work/reviews/cor-A-lawful-source-excerpt-lines-105-116.tex.txt (= reference/SM/sm-6-comparison.tex 105-116, cor:A-lawful: the list of
   laws whose C versions are the fields). For each law's own printed statement: prop:C-chamber (sm-4-knotlaws.tex 36-39), prop:C-silent,
   thm:C-S3, thm:C-S5, thm:C-S7, thm:C-soft, hyp:R (grep the labels in reference/SM/sm-4-knotlaws.tex), cor:C-inherits
   (work/reviews/cor-c-inherits-source-excerpt-lines-313-369.tex.txt).
2. The Lean statement: work/reviews/sm-corner-laws-and-soft-reviewer-input-statement.lean.txt (SM/CornerLawsAndSoft.lean with the
   proofs replaced by sorry): the bundle `SM.CornerLawsAndSoftData` (11 fields) and `SM.corner_laws_and_soft : CornerLawsAndSoftData`
   (no hypotheses). Its field types are the ACCEPTED row bundles — read their definitions and docstrings (not proofs):
   `CChamberData` (SM/CChamber.lean), `CSilentData` (SM/CSilent.lean), `CS3Data`, `CS7Data`, `CSoftData` (SM/CornerChainStatements.lean),
   `hyp_R` (SM/HypR.lean), `CS5Data` (SM/CS5.lean), `CuspLawC`, `ReversalLawC` (SM/CInherits.lean), `TrianglesC` (SM/Comparison.lean),
   `CyclicLawC` (in the statement file itself). Their acceptance reviews (statement fidelity of each bundle against its own printed row)
   are in work/reviews/{prop-C-chamber,prop-C-silent,thm-C-S3,thm-C-S5,thm-C-S7,thm-C-soft,hyp-R,cor-c-inherits}.json (read the
   verdicts and the disclosed readings; you are not re-reviewing those rows, you are checking that the FINAL bundle assembles them
   correctly and completely against TARGETS.md).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/ (cornerStateSum, WallGerm, VertexEdgeAt,
   CuspAt, FlatAt, TripleAt, softInsertion, genericShift, generic_reversal, star_generic_law — grep).
4. Disclosed readings: work/AUTHOR_NOTES.md entries "D-CVT-5", "FR-F-184-1..4", "A-22" / "Row 184 port module PREPARED" and the row 184
   acceptance entry (the CInheritsData unification: the final reads only cusp_law / reversal_law / triangles of cor:C-inherits' bundle).

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing SM.CornerLawsAndSoft
if you wish): `SM.corner_laws_and_soft : SM.CornerLawsAndSoftData` has no hypothesis and no R parameter; axioms exactly the nine
registered [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness,
SM.ng_finite_word, SM.src_contact]; no sorryAx.

YOUR TASK. Check the bundle against TARGETS.md item by item: (i) chamber constancy AND silent-wall invariance (fields chamber, silent);
(ii) the flat deletion law (flat); (iii) both bigon branches and the sliding branch of the vertex-edge law with the stated sign and the
actual two child polygons (vertex_edge : CS7Data — `VertexEdgeAt` is bigon ∨ sliding); (iv) triple-wall invariance at every source simple
triple wall AFTER PROVING R (triple : hyp_R as a FIELD, i.e. proved, not assumed — check no R hypothesis remains anywhere in the
statement); (v) the full cusp jump on the source domain (deletion satisfies G1) including threaded cusps (cusp : CuspLawC — check the
domain is exactly cor:A-lawful's "when the deletion satisfies (G1)" and no emptiness hypothesis is added; "No stronger cusp domain is
commissioned") and the direct empty-cusp zero result retained (empty_cusp : CS5Data); (vi) the soft theorem in every sector including
zero-selector sectors (soft : CSoftData — check the sector quantification); plus the normalizations (triangles) and reversal/cyclic
identities (reversal, cyclic) "as stated" in cor:A-lawful. Is the conclusion about the source C (`cornerStateSum` of def:C) and not a
freely supplied function? Is anything STRONGER or WEAKER than TARGETS.md commissions, or MISSING from the required coverage? Label
non-blocking notes. Default to "not faithful" if in doubt. The proof route is NOT under review — only the statement.
