You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE lemma against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/lem-A-small-values-source-excerpt-lines-5-13.tex.txt
   (= reference/SM/sm-6-comparison.tex 5-13, lem:A-small-values). Context, read ONLY to fix
   notation: reference/SM/sm-5-transport.tex 5-15 (def:star: the bow-tie K_0 and its four
   coordinates at the labels 1, 2, 3, 4); reference/SM/sm-2-amplitude.tex 10-65 (def:root: physical
   roots g and boundary words) and 66-140 (def:treesum: the tree coefficient A_g);
   reference/SM/sm-1-polygons.tex 27-62 (def:polygon: labelled tuples, the cyclic shift σ), 63-71
   (def:chirotope: turns τ_i), 100-130 (def:generic: condition (G1)), 398-406 (def:shift).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/lem-A-small-values-reviewer-input-statement.lean.txt (main declaration
   SM.A_small_values_lemma). Its module docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): TreeCoefficient (treeCoefficient and the definitions it is built from; accepted
   row def:treesum) together with the modules it imports that define open sums, gates and interval
   compositions (RootBoundary — accepted row def:root; IntervalComposition, OpenTreeSum, Gates or
   however they are named there — definitions only), Generic (G1, Generic, g1_shift_forward —
   statement only), Chirotope (turn, chi; accepted row def:chirotope), BowTie (bowTie),
   StarDefinition (accepted row def:star), Polygon (LabelledTuple, shift, edge; accepted row
   def:polygon), EuclideanPlane (Plane, det). Do NOT open work/lean/SM/SmallValues.lean or
   work/lean/SM/SmallValuesLemma.lean (they contain the proofs).

YOUR TASK: compare the two printed clauses with the two conjuncts.
(i) "For every labelled triangle satisfying (G1), all turns have a common sign τ, and A_g = -τ at
every physical root": is a labelled triangle a LabelledTuple 3, is (G1) the Lean G1, is "common
sign τ" rendered by ∃ τ : SignType, τ ≠ 0 ∧ ∀ i, turn P i = τ (the τ ≠ 0 is extra information —
record it and say whether it is implied by (G1)), is "every physical root" every g : ZMod 3, and
is A_g the Lean treeCoefficient P hP g _ (check def:treesum's rendering: the root g is an edge
label; the value is an integer). (ii) "For the bow-tie of def:star, A_g(σ^k K_0) = -1 for every
physical root g and every integer k": is bowTie the printed K_0 (compare the four coordinates and
labels with def:star and the accepted row StarDefinition), is σ^k for an integer k the Lean
shift (k : ZMod 4) (check the definition of shift and the direction of the shift against
def:polygon / def:shift — a direction mismatch is harmless here only if the set of shifts is the
same; say so explicitly), and is the (G1) witness g1_shift_forward (k : ZMod 4) bowTie_G1 only a
proof argument that does not change the value (treeCoefficient is a function of P, g and the
proofs; check whether it depends on the proof term). Expand definitions to primitives; say where
the Lean is STRONGER or WEAKER; any printed sub-clause without a Lean counterpart is a discrepancy.
Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
