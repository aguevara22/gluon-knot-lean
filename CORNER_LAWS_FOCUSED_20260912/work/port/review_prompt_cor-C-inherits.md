You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE corollary row against ONE printed source
statement (frame SM15): cor:C-inherits (row 128; FIXED name `SM.cor_C_inherits`, statement `(hR : hyp_R) : CInheritsData`), module
SM/ComparisonRows.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cor-c-inherits-source-excerpt-lines-313-369.tex.txt (= reference/SM/sm-6-comparison.tex
   313-369, cor:C-inherits: "Under Hypothesis R, C satisfies every identity of cor:A-lawful on the domains stated there, in particular
   the cusp law C(P_loop) − C(P_no) = −κ C(P(0)∖j)", with its printed proof and domain checks) and
   work/reviews/cor-A-lawful-source-excerpt-lines-105-116.tex.txt (cor:A-lawful: the list of identities and their domains). Context ONLY to
   fix notation: reference/SM/sm-4-knotlaws.tex (hyp:R; the C-laws prop:C-chamber, prop:C-silent, thm:C-S3, thm:C-S7, thm:C-soft — grep
   labels), reference/SM/sm-1-polygons.tex (def:walls, def:deletion-halves, (G1), reversal), reference/SM/sm-3-statesum.tex 1688-1700 (def:C).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/cor-C-inherits-reviewer-input-statement.lean.txt (the row
   declaration `SM.cor_C_inherits (hR : hyp_R) : CInheritsData`) and the bundle `CInheritsData` (12 fields) with `CuspLawC`, `ReversalLawC`
   in work/lean/SM/CInherits.lean (definitions, docstrings and the §6 `example`s' statements only — NOT the proof of cor_C_inherits_of),
   `TrianglesC` in work/lean/SM/Comparison.lean. The accepted `ALawfulData` (work/lean/SM/ALawful.lean:37-131) is the A-side template the
   bundle mirrors field for field (FR-CM-8); read it to compare domains.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/ (WallGerm, CuspAt, CuspCase, cuspLoopSide,
   FlatAt, VertexEdgeAt, TripleAt, deleteVertex, G1, Generic, generic_shift, generic_reversal, softInsertion, treeCoefficient,
   cornerStateSum, star_generic_law — grep), and the accepted reviews work/reviews/cor-A-lawful.json, hyp-R.json, thm-C-S7.json (if
   present), thm-C-soft.json for the readings the fields reuse. Disclosed readings FR-CM-8..15 in work/AUTHOR_NOTES.md (grep "FR-CM-").

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing SM.ComparisonRows if you
wish): `SM.cor_C_inherits` has exactly one hypothesis `hR : SM.hyp_R`; axioms exactly the nine registered [propext, Classical.choice,
Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]; no sorryAx. Proof:
`cor_C_inherits_of hR thm_C_S7 thm_C_soft`.

YOUR TASK: decide whether `CInheritsData` pins down exactly "every identity of cor:A-lawful on the domains stated there" for C: go through
cor:A-lawful's list — well-definedness on generic polygons (shift_invariant, descends), chamber constancy and silence (chamber_constant,
silent), the flat law (flat_law: domain and sign), the cusp law "when the deletion satisfies (G1)" (cusp_law : CuspLawC — exactly that
domain, existential deletion genericity, κ = ±1 with the rotation-number clause, loop/no-loop sides; NO emptiness hypothesis — threaded
cusps included), the vertex–edge law (vertex_edge_law — the halves generic, sign s), the triple law (triple_law), the soft theorem "in
every sector" (soft_theorem — the ∃ hQ form vs thm:C-soft's ∀ hQ: same meaning?), reversal (reversal_law : ReversalLawC, (−1)^n), the
triangle values (triangles : TrianglesC — C(K₁) = −1, C(K₋₁) = +1 on the counterclockwise and clockwise triangles), plus the extra field
root_values (C(P) = A_g(P) for every root g — the corollary's "in particular"/the comparison content; is including it STRONGER than the
printed corollary, and is that non-blocking?). Note the A-specific per-induced-root sub-clause of the cusp law has no C analogue (FR-CM-9)
— is its omission faithful? Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; default to "not faithful" if in
doubt; label non-blocking discrepancies "non-blocking". The proof route is NOT under review — only the statement.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite source and
statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of strings),
"supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
