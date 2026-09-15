You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/thm-C-S3-source-excerpt-lines-153-159.tex.txt (= reference/SM/
   sm-4-knotlaws.tex 153-159, thm:C-S3: "At a simple flat wall at j, with n ≥ 4, C(P_right) − C(P_left) = C(P(0) ∖ j)").
   Context, ONLY to fix notation: reference/SM/sm-4-knotlaws.tex 160-229 (its printed proof: the selector rewrite,
   "Put D = P(0) ∖ j", cor:flat-carriers, "Proposition prop:C-chamber supplies the well-defined side values. The only
   state sum on the right is that of the generic deletion"), reference/SM/sm-1-polygons.tex 737-748 (def:walls (F):
   flat at j, n ≥ 4, Z_pt = {{j−1, j, j+1}}, Z_c = ∅, μ_j(0) strictly between μ_{j−1}(0) and μ_{j+1}(0), τ_j changes
   sign; "The right side is the side with τ_j = −1 and the left side the one with τ_j = +1"), 778-860 (lem:flat-sides:
   its hypotheses and clause (iii) on the deletion P(0) ∖ j being generic — grep `label{lem:flat-sides}`), and def:germ
   (grep `label{def:germ}`), reference/SM/sm-3-statesum.tex 1688-1700 (def:C).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/thm-C-S3-reviewer-input-statement.lean.txt
   (the module SM/CS3.lean; the row is at its END: the notation-map docstring, bundle `CS3Data`, main declaration
   `SM.thm_C_S3`). Everything before the bundle (≈ 2470 lines) is the prover's infrastructure and is NOT under review;
   you may glance at it only to confirm that no notion of the row statement is defined there. Do NOT open
   work/lean/SM/CS3.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review; accepted rows def:germ, def:walls,
   lem:flat-sides, def:flat-carriers, cor:flat-carriers, def:C, prop:C-chamber): work/lean/SM/WallGerm.lean (WallGerm,
   Parameter, SideParameter, sideTime, sideTuple, center), GermDefinition.lean (pointZeros, concurrences, SignChanges,
   turnSupport), NamedWallPredicates.lean (FlatAt — compare its clauses with the row's hypotheses hz hb hc hsc),
   StrictBetween.lean, FlatSides.lean (the accepted lem:flat-sides bundle FlatSidesData and theorem flat_sides —
   statement only; the hypotheses form), FlatCarriersDefs.lean (IsRightSide, IsLeftSide at lines 525-531, flat_hn1),
   DeletedTuple.lean (deleteVertex), DeletionGeneric.lean (generic_deleteVertex — statement), CornerStateSum.lean
   (cornerStateSum — def:C), Turn/Chirotope modules for `turn` (grep `def turn`).

YOUR TASK: decide whether the bundle pins down exactly the printed theorem. (a) "a simple flat wall at j, with
n ≥ 4": `g : WallGerm (n + 1)` with `3 ≤ n` and the four hypotheses `hz : g.pointZeros = {turnSupport j}`,
`hb : StrictBetween …`, `hc : g.concurrences = ∅`, `hsc : g.SignChanges (turn · j)` — are these exactly def:walls (F)
(compare with `WallGerm.FlatAt`), and is writing the vertex count as n + 1 with 3 ≤ n the printed n ≥ 4? (b)
"P_right", "P_left": for side parameters tR, tL below a radius δ (0 < δ ≤ g.radius), polygons `g.sideTuple bR tR`
with `IsRightSide g j bR tR` (turn at j = −1) and `g.sideTuple bL tL` with `IsLeftSide` (turn = +1) — is this the
printed "right side is the side with τ_j = −1", and is the existential δ ("after shrinking the interval", the
printed proof's "Proposition prop:C-chamber supplies the well-defined side values") faithful, weaker or stronger
than the printed statement about the two side chambers? Does quantifying over both Booleans b with the side
predicate correctly avoid presupposing which parameter sign is the right side? (c) "C(P(0) ∖ j)": `cornerStateSum hn
(generic_deleteVertex hn hz hb hc)` — the state sum of the deletion of vertex j from the centre, with the genericity
proof supplied by lem:flat-sides (iii); is `deleteVertex g.center j` the printed P(0) ∖ j? (d) the state sums on the
sides are taken with `flat_hn1 hn : 3 ≤ n + 1` — consistent? (e) the equation orientation right − left = deletion.
Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; default to "not faithful" if in doubt;
label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
