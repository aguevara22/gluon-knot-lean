You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
fd:parameter-avoidance (row 85), Lean declaration `SM.fd_parameter_avoidance : SM.ParameterAvoidanceData`.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/fd-parameter-avoidance-source-excerpt-lines-2561-2570.tex.txt (= reference/SM/sm-3-statesum.tex
   2561-2570, lem:fd:parameter-avoidance "Compact parameter avoidance": "Let K be a compact subset of a smooth d-dimensional coordinate
   manifold and B ⊂ ℝ^m a closed parameter ball. Suppose that F is smooth on a neighbourhood of K × B, takes values in ℝ^q, and has
   derivative of rank q > d at every zero in that product. The parameters a for which F(t,a) = 0 for some t ∈ K form a closed set with
   empty interior. The same assertion holds simultaneously for a finite collection of such maps."). Context, ONLY to fix notation:
   sm-3:2571-2585 (its proof — skim for the argument), 2586-2660 (fd:contact-motions and fd:generic-front, the consumers: how the lemma is
   applied — to which K (circles, tori), which parameter balls), 2395-2400 (the fd block's setting).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/fd-parameter-avoidance-reviewer-input-statement.lean.txt (module
   SM/ParameterAvoidance.lean: the hypothesis structure ParameterAvoidanceHyp (fields compact, smooth, rank, dim_lt), the bundle
   ParameterAvoidanceData (fields isClosed, interior_eq_empty, finite_collection) and the theorem SM.fd_parameter_avoidance are UNDER
   REVIEW; the general core in namespace SM.ParameterAvoidance (zeroSet, zeroParams, the dimH lemmas …) is proof material whose statements
   you may read to understand the definitions). Its module docstring maps the notation and lists readings FR-PA-1..FR-PA-5 — verify, do
   not trust. Do NOT open work/lean/SM/ParameterAvoidance.lean.
3. Mathlib (this project's pin) for the meanings of IsCompact, ContDiffOn ℝ ∞, fderiv, LinearMap.range, finrank, Metric.closedBall,
   interior, IsClosed, EuclideanSpace ℝ (Fin d) (written ℝ^d in the module).

DISCLOSED READINGS of the unit (judge each): FR-PA-1 (the main risk) "a compact subset of a smooth d-dimensional coordinate manifold" is
rendered as K compact in EuclideanSpace ℝ (Fin d) — the chart reading (the printed proof works in coordinates; the phrase occurs nowhere
else in the paper; the consumers' domains S¹, (S¹)², (S¹)³ reduce via periodic lifts and the finite-collection clause; a Mathlib
IsManifold statement was judged too costly); FR-PA-2 "derivative of rank q" rendered as finrank ℝ (fderiv ℝ F z).range = q (equivalent
to surjectivity); FR-PA-3 the conclusion is the printed one (closed, empty interior); Hausdorff-dimension and measure-zero facts are
theorems, not fields; FR-PA-4 B = Metric.closedBall c r (Euclidean, any radius); FR-PA-5 the finite collection with varying (d i, q i)
and a shared ball; "simultaneously" = the union is closed with empty interior.

YOUR TASK: decide whether the hypothesis structure + bundle render exactly the printed lemma: the hypotheses (K compact — on a chart vs a
manifold: is the narrowing faithful, disclosed and harmless for the consumers?; B a closed ball; F smooth on a neighbourhood of K × B —
is ContDiffOn ℝ ∞ on an open U ⊇ K × B the printed smoothness?; values in ℝ^q; rank q > d at every zero in K × B — is the rank
condition exactly the printed one, and is q > d the printed inequality?); the conclusion (the set of parameters a ∈ B? or a ∈ ℝ^m? with
a zero in K — check which set the Lean takes and whether the printed "parameters a" range over B; closed; empty interior — in ℝ^m or in
B?); the finite-collection sentence. Hypotheses added or dropped; the field shapes (∀ d m q K c r F, hyp → …). Expand definitions to
primitives; say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
