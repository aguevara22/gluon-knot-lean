You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/lp-coefficient-transport-source-excerpt-lines-981-992.tex.txt
   (= reference/SM/sm-3-statesum.tex 981-992, lp:coefficient-transport: statement and \status line).
   Context, read ONLY to fix notation: reference/SM/sm-3-statesum.tex 905-979 (the three literature
   inputs lit:homfly, lp:lm, lp:lm-uniqueness whose clauses this lemma's hypotheses mirror), 325-351
   (def:positive-lift: diagrams are the polygonal class), 993-1039 (the printed PROOF — you may read it
   only to understand what the statement means, e.g. what "skein triple" and "crossing-free circle"
   denote; the Lean proof is not under review).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/lp-coefficient-transport-reviewer-input-statement.lean.txt (bundle `RCompetitor`, main
   declaration `SM.coefficient_transport`). Its module docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; proofs not under review):
   LinkLaurentRing (namespace SM.Link: R, R.a, R.aInv, R.z — definitions only), LinkDiagram (Diagram,
   IsCrossingFreeCircle, componentCount, switch, IsPositive — definitions), LinkMoves (PlanarIsotopic,
   RI, RII, RIII, IsOrientedSmoothing, IsSkeinTriple, LinkEquiv — definitions and docstrings; use grep),
   LinkInterfaces (the ACCEPTED rows lit:homfly, lp:lm, lp:lm-uniqueness: structures HomflyClauses,
   LMClauses, LMCompetitor and the three axioms — read to compare the clause shapes; these rows were
   independently reviewed and accepted on 2026-09-13 and their readings — polygonal class, switch-and-
   smooth skein triples, planar isotopy = EqvGen(Reparam ∨ Deform), circle = every one-component
   crossing-free diagram — are NOT under review here; judge only whether THIS row uses the same notions
   consistently). Do NOT open work/lean/SM/CoefficientTransport.lean (it contains the row proof).

YOUR TASK: decide whether `RCompetitor` and `coefficient_transport` pin down exactly the printed
lemma. Check: (a) "Put R = ℤ[a^{±1}, z^{±1}]" — the codomain `R`; (b) "Any two maps D ↦ Q_D ∈ R on
oriented link diagrams" — `Q Q' : Diagram → R`, the conclusion `Q = Q'` (pointwise equality on every
diagram); (c) "invariant under planar isotopy and the three Reidemeister moves" — fields planar,
reidemeister_I/II/III; (d) "take the value 1 on the crossing-free circle" — field circle; (e) "satisfy
a Q_{D₊} − a⁻¹ Q_{D₋} = z Q_{D₀} on every skein triple" — field skein (equation, sign convention,
argument order of IsSkeinTriple Dp Dm D0 = (D₊, D₋, D₀)); (f) "No restriction on the support or on the
coefficients of the maps is imposed" — no further hypothesis; (g) the last two sentences ("transports
the uniqueness clause of lp:lm-uniqueness to R; asserts no existence, no ambient-isotopy invariance
and no descent theorem") — non-definitional, but confirm the Lean statement indeed asserts nothing
beyond the coincidence of two maps (in particular no existence claim and no descent field). Compare the
hypotheses with lit:homfly's HomflyClauses (this row's hypotheses should be exactly HomflyClauses
WITHOUT the descent field) and with LMCompetitor. Expand definitions to primitives; say where the Lean
is STRONGER or WEAKER; any printed clause without a Lean counterpart or Lean clause without a printed
counterpart is a discrepancy. Default to "not faithful" if in doubt. A discrepancy you consider
non-blocking must be labelled "non-blocking" in its text.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
