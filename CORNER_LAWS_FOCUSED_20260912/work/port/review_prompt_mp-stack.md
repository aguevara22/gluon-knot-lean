You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/mp-stack-source-excerpt-lines-1494-1536.tex.txt (= reference/SM/
   sm-3-statesum.tex 1494-1536: mp:stack, statement 1494-1512 and its printed proof 1513-1536). Context, ONLY to fix
   notation: reference/SM/sm-3-statesum.tex 1041-1063 (lp:core: P_D, δ = (a − a⁻¹) z⁻¹), 1180-1190 (lp:split-circle),
   1362-1426 (marked diagrams; "actual restriction" vocabulary), 325-351 (def:positive-lift: the polygonal diagram
   class; components; "actual"), 905-960 (lp:lm: UNDER-first, component order).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/mp-stack-reviewer-input-statement.lean.txt
   (module SM/Stack.lean). The row is at its END: the notation-map docstring, bundle `StackData`, main declaration
   `SM.stack`. The definitions the bundle uses are in the SAME file near its top (lines ≈ 55-75): `blockRestrict`
   (D.restrict to the fibre of blk over i), `BlockOrdered` (for every crossing x and strands s, t ∈ x, blk s.1 < blk t.1
   → D.underStrand x = s), `blockSet` — read them (definitions and docstrings). Everything else in the file (≈ 1300
   lines of record-level first-return machinery, block bookkeeping, induction) is the prover's infrastructure and NOT
   under review. Do NOT open work/lean/SM/Stack.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/LinkDiagram.lean
   (Diagram, Shadow (c components, hc : 0 < c), Strand (a component index and an edge), Crossing (a pair of strands),
   underStrand / overStrand, componentCount, restrict — the restriction to a nonempty set of components keeping the
   crossings internal to them, with its docstring), LinkMoves.lean (IsSplitCircleAddition, for comparison with the
   split-union clause), LocalPolynomial.lean (P), LinkLaurentRing.lean (R.delta), PolynomialBlock.lean END (the accepted
   lp:core / lp:split-circle bundles — statements only).

YOUR TASK: decide whether the bundle pins down exactly the printed theorem. (a) "Let D be an actual nonempty diagram
whose components are partitioned into q ≥ 1 nonempty tagged blocks": `D : Diagram` (nonempty: c ≥ 1 built in?) and a
surjection `blk : Fin D.Γ.c → Fin q` — is a surjection onto Fin q exactly a partition into q nonempty tagged blocks
(tags = indices 0..q−1, the printed "smaller-index block")? Is q ≥ 1 implied? (b) "at every crossing between different
blocks the smaller-index block is under the larger one": `BlockOrdered` — expand `underStrand`, `Strand`, `s ∈ x.val`;
is "between different blocks" rendered (blk s.1 < blk t.1 forces different blocks; crossings within a block are
unconstrained)? (c) "Let D_i be the actual restriction retaining all components in block i and all crossings internal
to it": `blockRestrict D blk hblk i = D.restrict (fibre of i)` — read `Diagram.restrict`'s definition/docstring: does it
keep exactly the components of the block and exactly the crossings internal to it? (d) eq. mp:stack-value `P_D =
δ^{q−1} ∏ P_{D_i}` — field `stack` (natural-number exponent q − 1 with q ≥ 1). (e) "There is no bound on the number of
components in a block, no restriction on crossings inside a block, and no requirement that their page images be
separated" — permissions, rendered by absence? (f) "A crossing-free disjoint union is the special case with no
crossings between blocks. In particular P_{A ⊔ B} = δ P_A P_B for two nonempty diagrams presented without mixed
crossings": field `split_union` — D partitioned into two blocks (surjection onto Fin 2) with every crossing internal to
a block (∀ x s t, s ∈ x → t ∈ x → blk s.1 = blk t.1) → P D = δ · P(block 0) · P(block 1). Is "two nonempty diagrams A, B
presented without mixed crossings" exactly "a diagram with two blocks and no between-block crossings" (A = D_0, B =
D_1)? Is anything printed missing or anything in Lean stronger? Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
