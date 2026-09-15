You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE proposition row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/prop-C-chamber-source-excerpt-lines-36-40.tex.txt (= reference/SM/
   sm-4-knotlaws.tex 36-40, prop:C-chamber: "The state sum C of Definition def:C is constant on every chamber.").
   Context, ONLY to fix notation: reference/SM/sm-4-knotlaws.tex 41-99 (its printed proof: the labelled path
   argument, then the descent to the cyclic quotient), reference/SM/sm-1-polygons.tex 206-230 (def:chamber: "A
   chamber is a connected component of the space of generic polygons 𝓤_n/(ℤ/n); its preimage in 𝓤_n is a union of
   at most n components permuted by σ, the labelled chambers"; prop:chambers), reference/SM/sm-3-statesum.tex
   1688-1700 (def:C, accepted).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/prop-C-chamber-reviewer-input-statement.lean.txt
   (bundle `CChamberData`, main declaration `SM.C_chamber`). Its module docstring maps notation — verify, do not trust.
   Do NOT open work/lean/SM/CChamber.lean or anything under work/drafts/cchamber/.
3. Lean definition modules (definitions and docstrings only): work/lean/SM/Chambers.lean (GenericTuple,
   genericCyclicSetoid, GenericPolygon = the quotient by cyclic relabelling, polygonProjection, labelledChamber,
   chamber = connectedComponent in the quotient — the accepted def:chamber), work/lean/SM/ChamberPaths.lean (the
   accepted prop:chambers statement `SM.chambers`), work/lean/SM/CornerStateSum.lean (cornerStateSum hn hP — the
   accepted def:C, on labelled generic polygons), work/lean/SM/Generic.lean, Polygon.lean (LabelledTuple, the cyclic
   action `cyclicSetoid` — grep).

YOUR TASK: decide whether the single field `constant : ∀ n [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
polygonProjection Q ∈ chamber (polygonProjection P) → cornerStateSum hn P.2 = cornerStateSum hn Q.2` is exactly
the printed sentence: "constant on every chamber" where chambers are components of 𝓤_n/(ℤ/n) (so two labelled
generic polygons whose classes lie in one chamber have equal C — is the quantification over LABELLED
representatives the right rendering, given that C is defined on labelled polygons? does the field entail the
invariance of C under cyclic relabelling, as the printed proof's last paragraph requires?); the domain (generic
polygons with n ≥ 3, [NeZero n]); whether `chamber` is the printed chamber (connected component of the quotient
space with the quotient topology) and not the labelled chamber. Anything printed missing, anything unprinted
added? Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; default to "not faithful" if
in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
