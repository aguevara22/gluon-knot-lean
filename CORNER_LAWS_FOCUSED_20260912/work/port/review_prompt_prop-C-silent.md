You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE proposition row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/prop-C-silent-source-excerpt-lines-101-105.tex.txt (= reference/SM/
   sm-4-knotlaws.tex 101-105, prop:C-silent: "At a simple exterior-extension wall (E) or a simple pure cut (C),
   C(P₊) = C(P₋)"). Context, ONLY to fix notation: reference/SM/sm-4-knotlaws.tex 106-152 (its printed proof: lem:wall-sides
   (E),(C); "the state sums in (ccf:silence) are evaluated on the generic sides. Proposition prop:C-chamber makes them
   independent of the chosen representatives in the respective side chambers"), reference/SM/sm-1-polygons.tex 680-700
   (def:germ: a wall germ, its two sides P((−ε,0)) and P((0,ε)) as chambers, F(P_±)), 737-770 (def:walls: the types,
   in particular (E) "Exterior extension at (M;a): M ∉ {a−1,a,a+1,a+2}, Z_pt = {{a,a+1,M}}, Z_c = ∅, μ_M(0) lies on the
   line of E_a(0) outside the closed segment E_a(0), and χ_{a,a+1,M} changes sign at 0" and (C) "Pure cut at {i,j,k}: no
   two of i,j,k are consecutive modulo n, Z_pt = {{i,j,k}}, Z_c = ∅, and χ_ijk changes sign at 0"; "The walls (E) and (C)
   are called silent"), 923-950 (lem:wall-sides (E),(C)), reference/SM/sm-3-statesum.tex 1688-1700 (def:C).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/prop-C-silent-reviewer-input-statement.lean.txt
   (module SM/CSilent.lean; the row is at its END: the notation-map docstring, bundle `CSilentData`, main declaration
   `SM.prop_C_silent` — the fixed target name). Everything before the bundle (≈ 1500 lines) is the prover's infrastructure
   and NOT under review; you may glance at it only to confirm that no notion of the row statement is defined there. Do
   NOT open work/lean/SM/CSilent.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review; accepted rows def:germ, def:walls,
   def:C, prop:C-chamber): work/lean/SM/WallGerm.lean (WallGerm, Parameter, SideParameter, sideTime, sideTuple, center),
   GermDefinition.lean (pointZeros, concurrences), GermSignChange.lean (SignChanges),
   NamedWallPredicates.lean (ExtensionAt, PureCutAt — read them and compare with def:walls (E),(C)), ContactIndices.lean
   / PureCutIndices.lean (ContactSeparated, contactSupport, NoConsecutive — definitions), EuclideanPlane.lean /
   Polygon.lean (edgePoint, edgeSegment), Chirotope.lean (chi), CornerStateSum.lean (cornerStateSum — def:C),
   CChamber.lean (the accepted prop:C-chamber bundle CChamberData — statement only).

YOUR TASK: decide whether the bundle pins down exactly the printed proposition. (a) "a simple exterior-extension wall
(E)": `g : WallGerm n` with `3 ≤ n` and `g.ExtensionAt M a` — expand ExtensionAt and compare clause by clause with
def:walls (E) (M ∉ {a−1,a,a+1,a+2} = ContactSeparated?; Z_pt = {{a,a+1,M}} = pointZeros = {contactSupport M a}?; Z_c = ∅;
"μ_M(0) lies on the line of E_a(0) outside the closed segment" = ∃ t, center M = edgePoint center a t ∧ center M ∉
edgeSegment center a?; sign change of χ_{a,a+1,M}); "a simple pure cut (C)": `g.PureCutAt i j k` versus def:walls (C)
(NoConsecutive {i,j,k}; pointZeros = {{i,j,k}}; concurrences = ∅; sign change of χ_ijk). Does "simple" add anything
beyond the type clauses (def:walls 738-739)? (b) "C(P₊) = C(P₋)": the fields state, for EVERY pair of side parameters
tp, tm, `cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property` — are
`sideTuple true`/`false` the two sides P((0,ε)) and P((−ε,0)) of def:germ? Is quantifying over all side parameters (no
shrinking radius) the printed statement about the two side chambers (each side of a germ lies in one chamber, on which
C is constant by prop:C-chamber — is that identification exact or does it presuppose something not accepted)? Is the
naming of ± immaterial for an equality? (c) the standing size hypothesis `3 ≤ n` and `[NeZero n]`. Expand definitions
to primitives; say where the Lean is STRONGER or WEAKER; default to "not faithful" if in doubt; label non-blocking
discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
