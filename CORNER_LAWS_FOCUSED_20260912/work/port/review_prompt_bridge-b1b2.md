You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row of the Bridge lane against its printed source, the frozen
bridge specification reference/BRIDGE/BRIDGE.md (frame SM15). The row is named in your task:
Bridge:B1 (Lemma B1) or Bridge:B2 (Lemma B2).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: Bridge:B1 → work/reviews/bridge-b1-source-excerpt-lines-159-446.md.txt
   (= BRIDGE.md 159-446: the statement of Lemma B1, the quoted SM/CV definitions and its proof — the
   STATEMENT is lines 161-169 of BRIDGE.md; the rest is context you may use to fix what the
   statement means); Bridge:B2 → work/reviews/bridge-b2-source-excerpt-lines-448-491.md.txt (= BRIDGE.md
   448-491: Lemma B2 = "For the germ in B1, its CV zero set is Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g},
   G4_{g;e,f}}. These are four indexed members.", with its proof). Context: work/reviews/bridge-s0-context-
   lines-5-101.md.txt (= BRIDGE.md §0: frozen inputs, the labelled coordinate identification between SM
   tuples and CV polygons, the naming convention e<f<g for the central triple, scope), and the other
   excerpt. You may also read reference/R/CV/d1_setup.tex 42-218 (CV def:guarded: the members G1..G5 and
   their indexing), 220-238 (CV def:generic), 1072-1097 (CV def:event, zero set), and reference/SM/
   sm-1-polygons.tex 99-108 (SM def:generic) and the SM wall-germ definitions the excerpt quotes (follow
   its `sm-…tex:line` citations only).
2. The Lean statements with the two row proofs replaced by `sorry`:
   work/reviews/bridge-b1b2-reviewer-input-statement.lean.txt (module Bridge/B1.lean: the constructor
   `Bridge.eventOfTriple` — a definition whose proof fields are part of the construction, not under review
   as proofs — helper lemmas with proofs (not under review), `theorem Bridge.B1`, `theorem Bridge.B2`,
   `exists_sorted_tripleAt`). Its header maps notation and records shape decisions — verify them, do not
   trust them. Do NOT open work/lean/Bridge/B1.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/CV/Setup.lean
   (CV.IsPolygon, CV.rep, G1..G5, Member, Member.eval/Active/Relevant, Crosses, CV.Generic — accepted rows
   129-133; `CV.generic_of_sm` is the accepted row-132 theorem SM.Generic → CV.Generic), work/lean/CV/
   Events.lean (CV.Event: radius, curve, Parameter, center, sideCurve, zeroSet, SignChanges, Transversal —
   accepted row 148), and under work/lean/SM/: Generic.lean (SM.Generic), Polygon.lean (LabelledTuple, edge,
   det), NamedWallPredicates.lean / UnorderedWallTriples.lean / GermSignChange.lean and the accepted def:germ
   / def:walls modules (`WallGerm`, `WallGerm.pointZeros`, `concurrences`, `TripleAt`, `SignChanges`,
   `Parameter`, `curve`, `center` — definitions only; grep as needed).

YOUR TASK: for YOUR row, compare the printed lemma clause by clause with the Lean theorem. Bridge:B1:
(1) "𝓤_n^SM ⊆ 𝓤_n^CV" with the labelled coordinate identification of §0 — the Lean `∀ P : LabelledTuple n,
SM.Generic P → CV.Generic P` (is the identification of an SM labelled tuple with a CV polygon exactly §0's
SM_MAP: p_i = μ_i, d_i = edge P i, one-based tails on both sides? is `LabelledTuple n` the common type?);
(2) "Every SM11 wall germ satisfying the central conditions of type T is a CV event. This assertion is
restricted to that central type" — the Lean: for every `g : WallGerm n` and `h : g.TripleAt e f k`, an
event `E` with the same radius, the same curve (stated pointwise on the real parameter with both membership
proofs — judge the header's explanation) and `¬ CV.Generic g.center`; check that `TripleAt` is exactly
"the central conditions of type T" (pointZeros = ∅, concurrences = {{e,f,k}}, the three parameter-difference
sign changes — compare with the printed SM definitions the excerpt quotes) and that `CV.Event` (curve of
polygons, CV-generic off the centre, not CV-generic at the centre) is what "is a CV event" means; is
`hn : 3 ≤ n` a printed standing assumption? Bridge:B2: the zero set of that event equals the set of the four
INDEXED members `{Member.g3 e f k _, Member.g4 e f k _, Member.g4 f e k _, Member.g4 k e f _}` under the
naming `rep e < rep f < rep k` (§0's convention) — check the indexing convention of `Member.g4 a b c`
(= G4_{a;b,c}? read Setup.lean's definition and docstring), the side-condition arguments, that the Lean
`Event.zeroSet` is CV's printed zero set (members relevant at some t ≠ 0 and vanishing at the centre — read
def:event), and that `exists_sorted_tripleAt` really makes the sorted naming without loss. Expand
definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause without a Lean
counterpart or Lean clause without a printed counterpart is a discrepancy. Default to "not faithful" if in
doubt; label non-blocking discrepancies "non-blocking" in their text.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
