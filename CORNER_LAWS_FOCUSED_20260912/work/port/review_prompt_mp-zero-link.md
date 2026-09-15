You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma row against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/mp-zero-link-source-excerpt-lines-1538-1545.tex.txt (=
   reference/SM/sm-3-statesum.tex 1538-1545, mp:zero-link). Context, ONLY to fix notation: reference/SM/
   sm-3-statesum.tex 1546-1580 (its printed proof: fan triangles, "the argument counts traversed occurrences,
   not distinct points", "at each mixed crossing the decorated sign is either the fixed-order determinant
   sign or its negative"), 325-351 (def:positive-lift: diagrams are the polygonal class; decorated crossing
   signs sgn det(u_over, u_under)), 1494-1512 (mp:stack, where "stack" and "one component always over the
   other" come from), reference/SM/sm-1-polygons.tex 138-160 (def:crossings: transverse intersections of
   remote edges).
2. The Lean statement with the proof replaced by `sorry`: work/reviews/mp-zero-link-reviewer-input-statement.
   lean.txt (definitions `Shadow.MixedPair`, `mixedSignSum`; bundle `ZeroLinkData`; main declaration
   `SM.zero_link`). Its module docstring maps notation — verify, do not trust. Do NOT open work/lean/SM/ZeroLink.lean.
3. Lean definition modules (definitions and docstrings only): work/lean/SM/LinkDiagram.lean (namespace SM.Link:
   PolyComp, Shadow (components `Fin c`, `Strand = Σ i, ZMod k`, `seg`, `dir`, `Adjacent`, `IsCrossing`,
   `Crossing`, `Generic` (regular, tail_off, transverse, no_triple)), Diagram (overStrand, underStrand,
   IsPositive, sign), EuclideanPlane.lean (det), Polygon.lean (edgeSegment, edge).

YOUR TASK: decide whether the definitions + bundle pin down exactly the printed lemma. (a) "For two distinct
components of an actual generic oriented plane diagram" — `D : Diagram`, `i ≠ j : Fin D.Γ.c`; (b) "the sum of
sgn det(u₁, u₂) over their transverse intersections, in this fixed component order, is zero" — the double sum
over ordered strand pairs (s on i, t on j) forming a crossing (`MixedPair i j s t := s.1 = i ∧ t.1 = j ∧
IsCrossing {s, t}`) of `sign (det (dir s) (dir t))`: does each transverse intersection of the two components
correspond to exactly one such pair (IsCrossing = non-adjacent strands whose closed segments meet; is every
such meeting a transverse intersection for a generic diagram, and can a pair (s, t) with s on i, t on j be
adjacent?), and is u₁, u₂ the printed order (component i first)? (c) "Consequently the half-sum of decorated
crossing signs is an integer" — `∃ k, mixedSignSum D i j = 2 * k` where mixedSignSum sums `D.sign ⟨{s,t}, _⟩`
(the decorated sign of def:positive-lift) over the same pairs; (d) "and it is zero if one component is always
over the other" — the disjunction (over strand always on i) ∨ (always on j) → sum = 0. Also: the printed
"consequently" clauses are asserted as separate fields (fine) — anything printed missing, anything unprinted?
The classical decidability (`open Classical`) in the sums — harmless? Expand definitions to primitives; say
where the Lean is STRONGER or WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies
"non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
