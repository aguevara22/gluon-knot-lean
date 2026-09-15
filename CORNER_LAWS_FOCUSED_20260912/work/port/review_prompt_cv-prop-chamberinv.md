You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row of the CV lane against ONE printed source statement of the paper "CV"
(reference/R/CV/, frozen): CV:prop:chamberinv (row 147), Lean declaration `CV.chamberinv : CV.ChamberInvData`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cv-prop-chamberinv-source-excerpt-lines-932-939.tex.txt (= reference/R/CV/d1_setup.tex
   932-939: "Fix n ≥ 3. (i) The generic locus 𝓤_n is open in (ℝ²)^n, and every chamber — every connected component of it — is open and
   path connected. (ii) X₁ is constant on each chamber."). Context, ONLY to fix notation: d1_setup.tex 940-961 (its proof — skim for the
   objects), 220-238 (def:generic: the guarded genericity, the generic locus 𝓤_n and chambers = connected components, clause (B)),
   908-930 (def:X1, accepted as CV.X1_definition), 932-961 as a whole.
2. The Lean statement with the row proofs replaced by `sorry`: work/reviews/cv-prop-chamberinv-reviewer-input-statement.lean.txt (module
   CV/ChamberInvRow.lean: the bundle ChamberInvData with fields open_locus, chamber_open, chamber_pathConnected, x1_constant and the
   theorems CV.chamberinv_ii, CV.chamberinv are UNDER REVIEW). Its module docstring maps the notation — verify, do not trust. Do NOT open
   work/lean/CV/ChamberInvRow.lean or work/lean/CV/PieceHomflyTransport.lean or work/lean/CV/ChamberInvII.lean (proof modules).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Setup.lean (LabelledTuple, Member,
   Generic, genericLocus, chamber = connectedComponentIn (genericLocus n) P — CV:def:generic (B)), CV/ChamberInv.lean (the accepted
   clause-(i) bundle ChamberInvIData and CV.chamberinv_i — statements only; compare its fields with the new bundle's (i) fields),
   CV/X1.lean (X1 and its bundle X1DefinitionData — accepted CV:def:X1: X1 hn P hG for hn : 3 ≤ n, hG : Generic P), CV/Events.lean (Ind),
   Mathlib's connectedComponentIn / IsPathConnected as needed.

DISCLOSED READINGS (judge each): (a) "Fix n ≥ 3" — clause (i) is stated for every n with [NeZero n] (the accepted clause-(i) bundle's
shape: the proof of (i) does not use n ≥ 3; chamberinv_i_of_three_le restates it on the printed domain), clause (ii) carries hn : 3 ≤ n
because X1 does; (b) chambers = CV.chamber P = connectedComponentIn (genericLocus n) P, exactly def:generic (B); (c) X₁ = CV.X1 hn Q hQ
(accepted definition) — "constant on each chamber" rendered as ∀ P Q generic, Q ∈ chamber P → X1 Q = X1 P.

YOUR TASK: decide whether the bundle renders exactly the printed proposition: (i) three fields (open locus; every chamber open; every
chamber path connected) — compare with the printed sentence and with the accepted ChamberInvIData; (ii) x1_constant — is the
quantification the printed "constant on each chamber" (every two generic polygons in one chamber have equal X₁; is the dependence of X1
on the proofs hn, hQ harmless (Prop arguments)?). Hypotheses added or dropped; the n ≥ 3 placement. Expand definitions to primitives; say
where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
