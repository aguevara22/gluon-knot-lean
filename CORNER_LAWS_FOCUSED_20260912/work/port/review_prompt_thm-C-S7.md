You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statement you are
reviewing and you must not read its proof. Your job is a statement-fidelity review of ONE theorem row against ONE printed source
statement (frame SM15): thm:C-S7 (row 110; FIXED name `SM.thm_C_S7`, FIXED statement `CS7Data`), module SM/CS7.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/thm-C-S7-source-excerpt-lines-266-276.tex.txt (= reference/SM/sm-4-knotlaws.tex 266-276,
   thm:C-S7 "vertex–edge law": at a simple vertex–edge wall at (M;a), of bigon or sliding type, with halves λ₁, λ₂ (def:deletion-halves)
   and contact sign s = χ_{a,a+1,M}(P₋), C(P₊) − C(P₋) = s C(λ₁) C(λ₂)). Context ONLY to fix notation: reference/SM/sm-4-knotlaws.tex
   277-420 (its printed proof: lem:C-X1, lem:wall-sides, lem:children, the bigon and sliding cases), reference/SM/sm-1-polygons.tex
   (def:walls — type (V) simple vertex–edge wall, bigon / sliding; def:deletion-halves; def:germ; grep the labels),
   reference/SM/sm-3-statesum.tex 1688-1700 (def:C).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/thm-C-S7-reviewer-input-statement.lean.txt (the row declaration
   `SM.thm_C_S7 : CS7Data`) and the bundle `CS7Data` with its companions `CS7Data.bigon` / `CS7Data.sliding` in
   work/lean/SM/CornerChainStatements.lean (statement-reviewed with the corner chain, readings FR-CC-7..9 in work/AUTHOR_NOTES.md — re-check,
   do not trust). Do NOT open work/lean/SM/CS7.lean or SM/CS7Units*.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/NamedWallPredicates.lean (VertexEdgeAt,
   BigonAt, SlidingAt, vertexEdge_bigon_or_sliding), NamedWallSides.lean (contactSign, contactSign_eq_at, vertex_contact_signs),
   DeletionHalves*.lean / Children*.lean (firstHalf, secondHalf, contactHalfSizes_bounds, vertex_halves_children — grep),
   WallGerm.lean / GermDefinition.lean (WallGerm, SideParameter, sideTuple, center), CornerStateSum.lean (cornerStateSum — def:C),
   the accepted reviews work/reviews/prop-C-silent.json and hyp-R.json for the C-row side-parameter convention.

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing SM.CS7 if you wish):
`SM.thm_C_S7 : SM.CS7Data` has no hypothesis; axioms exactly the nine registered [propext, Classical.choice, Quot.sound, SM.lit_homfly,
SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]; no sorryAx.

YOUR TASK: decide whether `CS7Data.vertex_edge_law` pins down exactly the printed theorem: (a) "a simple vertex–edge wall at (M;a), of
bigon or sliding type" = `g : WallGerm n`, `h : g.VertexEdgeAt M a` (is VertexEdgeAt exactly def:walls type (V), and is it the disjunction
bigon ∨ sliding — `vertexEdge_bigon_or_sliding`?); (b) "halves λ₁, λ₂ (def:deletion-halves)" = `firstHalf g.center M a`, `secondHalf
g.center M a` with genericity witnesses h₁ h₂ quantified (is quantifying over the witnesses the same as the printed halves, which are
generic by lem:children? sizes via contactHalfSizes_bounds); (c) "contact sign s = χ_{a,a+1,M}(P₋)" = `g.contactSign M a` (defined on
which side? constant on the negative side?); (d) "C(P₊) − C(P₋)" read at every pair of side parameters tp tm (the accepted C-row
convention; is ∀ tp tm faithful or stronger than the printed chamber values?); (e) the standing assumptions (n ≥ 3, NeZero n; the wall's
own n ≥ 4 if any inside VertexEdgeAt). Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; default to "not
faithful" if in doubt; label non-blocking discrepancies "non-blocking". The proof route is NOT under review — only the statement.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite source and
statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of strings),
"supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
