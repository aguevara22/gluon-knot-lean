You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE theorem against ONE printed source statement (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/thm-mycyclic-source-excerpt-lines-150-159.tex.txt
   (= reference/SM/sm-5-transport.tex 150-159, thm:mycyclic). Context, read ONLY to fix notation:
   reference/SM/sm-1-polygons.tex 27-62 (def:polygon: labelled tuples, the cyclic shift σ, the
   polygon space of cyclic orbits), 386-397 (def:regular: the regular locus ℛ_n and principal
   turns), 407-440 (lem:rot: the rotation number rot), 539-546 (def:admissible), 63-71
   (def:chirotope: turns, turn words); reference/SM/sm-5-transport.tex 5-15 (def:star: the bow-tie
   K_0). The proof of the theorem (sm-5-transport.tex 160-298) may be read ONLY to disambiguate the
   phrase "distinguished by their turn words" and "every fibre of cyclic polygon orbits".
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/thm-mycyclic-reviewer-input-statement.lean.txt (main declaration SM.mycyclic;
   bundle MycyclicData). Its module docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): RegularLocus and RegularPairs (Regular, RegularPair, principalTurn),
   RegularDefinition (accepted row def:regular), RotationNumber (rotationNumber), RotationTheorem
   (accepted row lem:rot — statement only), Polygon (LabelledTuple, shift, cyclicSetoid, Polygon,
   edge; accepted row def:polygon), Admissible (Admissible; accepted row def:admissible), BowTie
   (bowTie), StarDefinition (accepted row def:star), Chirotope (turn), EuclideanPlane (Plane).
   Mathlib's JoinedIn, IsPathConnected, Path and the quotient topology instTopologicalSpaceQuotient
   may be looked up in .lake/packages/mathlib (read-only). Do NOT open work/lean/SM/MyCyclicB.lean
   or work/lean/SM/MycyclicTheorem.lean (they contain the proofs).

YOUR TASK: compare the printed sentences with the seven bundle fields, under the printed
hypotheses "(n, r) admissible, P, P' ∈ ℛ_n labelled tuples with rot(P) = rot(P') = r".
Sentence 1, "If (n, r) ≠ (4, 0), a continuous path in ℛ_n ∩ rot⁻¹(r) joins P to P'": field
`joined` — is JoinedIn {Q | Regular Q ∧ rotationNumber Q = r} P P' exactly a continuous path in
that set (topology on LabelledTuple n = ZMod n → ℝ × ℝ), is the set ℛ_n ∩ rot⁻¹(r), and is the
exclusion ((n : ℤ), r) ≠ (4, 0) the printed one? Sentence 2, "If (n, r) = (4, 0), there is a
k ∈ ℤ/4 and such a path from P to σ^k P'": field `joined_shift` (k : ZMod n with n = 4 there;
is shift k P' the printed σ^k P' — check the direction convention of shift and whether it matters
here). Sentence 3, "The four shifts of K_0 lie in the four distinct labelled components,
distinguished by their turn words": fields `bowTie_mem` (the shifts lie in the fibre ℛ_4 ∩ rot⁻¹(0)),
`bowTie_components` (two shifts are joined in the fibre iff equal — is this "four distinct
labelled components"?), `turn_word_constant` (the turn word i ↦ turn Q i is constant along paths in
the fibre) and `bowTie_turn_words` (the turn words of the four shifts are pairwise distinct) — do
these four fields together render "distinguished by their turn words", and is "labelled
components" the path components of the fibre of labelled tuples? Sentence 4, "Thus every fibre of
cyclic polygon orbits is path connected": field `orbit_fibre_pathConnected` — is the polygon space
Polygon n hn = Quotient (cyclicSetoid n) with the quotient topology the printed space of cyclic
polygon orbits (def:polygon), and is the set of orbits of regular tuples of rotation r the printed
"fibre of cyclic polygon orbits" in the context of this theorem (ℛ_n), as opposed to the generic
fibre 𝒰_{n,r} of def:admissible — say which reading the printed theorem supports and whether the
Lean choice is faithful. Expand definitions to primitives; say where the Lean is STRONGER or
WEAKER; any printed sub-clause without a Lean counterpart is a discrepancy. Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
