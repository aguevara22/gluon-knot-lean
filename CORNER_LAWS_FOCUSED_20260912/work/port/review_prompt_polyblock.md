You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row of the polynomial block against ONE printed source statement
(frame SM15). The row is named in your task.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim, for your row: lp:core → work/reviews/lp-core-source-excerpt-lines-1041-1063.tex.txt
   (= reference/SM/sm-3-statesum.tex 1041-1063); rp:record-polynomial →
   work/reviews/rp-record-polynomial-source-excerpt-lines-1215-1229.tex.txt (1215-1229); lc:presentations →
   work/reviews/lc-presentations-source-excerpt-lines-1306-1320.tex.txt (1306-1320); lp:split-circle →
   work/reviews/lp-split-circle-source-excerpt-lines-1180-1190.tex.txt (1180-1190). Context, read ONLY to fix
   notation: the other three excerpts; reference/SM/sm-3-statesum.tex 1064-1075 (the Gaussian evaluation
   eq. lp:gaussian: R_G = ℤ[i][a^{±1}, z^{±1}], φ(l) = i a, φ(m) = −i z, P_D^G = φ(F_D), and eq.
   lp:gaussian-skein), 1076-1179 (the rest of lp:core's printed proof, only to see what "integral descent",
   "support" and "identification with H_D" denote), 905-990 (the three literature inputs lit:homfly, lp:lm,
   lp:lm-uniqueness: H_D, the source function F_D ∈ ℤ[l^{±1}, m^{±1}], UNDER-first, μ = −(l + l⁻¹) m⁻¹,
   initialization μ^{c−1}), 325-370 (def:positive-lift: the polygonal diagram class; def:gauss-record: the
   crossing record and named record isomorphisms), 1191-1214 (lp:split-circle's printed proof), 1230-1305
   (rp:record-polynomial's printed proof: component order, basepoints, bad crossings, (N, b) induction),
   1321-1344 (lc:presentations' printed proof).
2. The Lean statements with the four row proofs replaced by `sorry`:
   work/reviews/polyblock-reviewer-input-statement.lean.txt — the module SM/PolynomialBlock.lean; the four
   row declarations are at its END (section §7, from the line `/-! ## §7.`): bundle `RecordPolynomialData` /
   `SM.record_polynomial`, bundle `LpCoreData` / `SM.lp_core`, bundle `SplitCircleData` / `SM.split_circle`,
   and `SM.presentations` (a theorem with explicit arguments, no bundle). Immediately before §7 stand four
   docstrings mapping the printed notation of each row to Lean names — verify them, do not trust them.
   Everything before them (§0-§5: the record-level based order, induction principles, the pieces `G_*`,
   `P_*`, `Record.addFree`, …) is proof infrastructure written by the prover and is NOT under review; you
   may glance at it only to see that no definition used by a row statement is defined there (they are not:
   every notion in the four statements comes from the accepted modules of item 3). Do NOT open
   work/lean/SM/PolynomialBlock.lean.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; proofs not under review):
   LocalPolynomial (`SM.P D := reMap (phi (T.toTG (lmF D)))`, the coefficientwise real part of the Gaussian
   evaluation of the source value, and its sanity theorem's statement), LinkLaurentRing (namespace SM.Link:
   R, R.a, R.aInv, R.z, R.zInv, R.delta, coeffAt, InSupportM, T, T.l, T.m, T.mu, RG, TG, R.toRG, T.toTG, phi,
   reMap — definitions), LinkInterfaces (the accepted literature interfaces: HomflyClauses, LMClauses,
   the axioms lit_homfly / lp_lm / lp_lm_uniqueness, `homfly := Classical.choose lit_homfly`,
   `lmF := Classical.choose lp_lm`), LinkDiagram (Diagram, componentCount, IsCrossingFreeCircle, Basing,
   basedRank, UnderFirst, underVisit, overVisit, restrict, switch), LinkMoves (Reparam, PlanarIsotopic, RI,
   RII, RIII, IsOrientedSmoothing, IsSkeinTriple, IsSplitCircleAddition and its docstring, LinkEquiv),
   LinkRecord (Record, RecordIso — definitions), LinkDiagramRecord (Diagram.record, twin, nextVisit —
   definitions), GaussRecordDefinition (the accepted row def:gauss-record: bundle GaussRecordDefinitionData,
   statement only). You MAY also read the executor's recorded decision on the definition of P in
   work/AUTHOR_NOTES.md (entry "lp:coefficient-transport proved; the local polynomial P defined" of
   2026-09-13) and the accepted-row docstring of lc:single-crossing in work/lean/SM/SingleCrossing.lean
   (module docstring only).

YOUR TASK: for YOUR row only, decide whether the Lean statement, as pinned down by the bundle (or the theorem
statement for lc:presentations), renders exactly the printed statement, clause by clause. Specifics:
 lp:core — (i) "The same source construction has an evaluation P_D ∈ R" with eq. lp:gaussian: the Lean P is the
 real part of φ(F_D) and the field `gaussian` asserts `R.toRG (P D) = phi (T.toTG (lmF D))`, i.e. φ(F_D) lies
 in the image of R and P_D is that element — judge whether this pair renders the printed P_D (the printed
 proof's "integral descent"); (ii) eq. lp:skein on every skein triple (IsSkeinTriple: D₋ = D₊ switched at a
 positive crossing, D₀ its oriented smoothing) and δ = (a − a⁻¹) z⁻¹ = R.delta; (iii) "Its value on every
 UNDER-first c-component diagram is δ^{c−1}" (`underFirst_init` quantified over every basing B with
 D.UnderFirst B; note the natural-number subtraction c − 1 with c ≥ 1); (iv) "It equals H_D of lit:homfly"
 (`eq_homfly`, homfly = the chosen witness of lit_homfly); (v) uniqueness "on this exact diagram domain
 satisfying this skein and all these initialization values" (`unique`: every Q : Diagram → R with the skein
 and the UNDER-first initialization equals P — is the initialization hypothesis included, as the printed text
 insists?); (vi) eq. lp:support `P_D ∈ z^{1−c} ℤ[a^{±1}, z²]` (InSupportM c: every monomial a^d z^k present
 has k = 1 − c + 2j), `P_D ≠ 0`; (vii) "P_○ = 1" (IsCrossingFreeCircle: one component, no crossings);
 (viii) "knot evaluations are polynomials in z², with no negative z exponents" (`knot_support` on
 one-component diagrams: every present z-exponent is 2j, j : ℕ); (ix) "All local invariances in lp:lm are
 retained" (planar, reidemeister_I/II/III — compare with LMClauses' invariance fields). Is any printed clause
 missing, is any Lean field stronger than the printed text?
 rp:record-polynomial — "two actual nonempty finite generic oriented link diagrams" (Diagram: is nonemptiness
 built in — check the component count c ≥ 1 in the Diagram/Shadow structure); "a bijection of their
 components and crossing occurrences which preserves oriented cyclic successor, crossing pairing, over/under
 bits and crossing signs; the component bijection must also include all components with no crossing
 occurrences" (RecordIso D.record D'.record: e on ALL components, Φ on occurrences respecting comp, succ,
 pair, isOver, sgn — check against def:gauss-record); "Then F_D(l,m) = F_{D'}(l,m)" (`lmF_eq`);
 "Consequently any common Laurent-ring substitution of these two source values ... agrees" (`subst_eq`: every
 ring hom σ : T →+* A — is "Laurent-ring substitution" rendered, is quantifying over every commutative ring A
 faithful?), "and every coefficient of the substituted values agrees" (`P_eq`, `coeff_eq` on the Gaussian
 evaluation P — is restricting the coefficient clause to P a faithful instance of "the substituted values"?).
 lc:presentations — "two actual finite nonempty decorated diagrams" with "a specified bijection of their
 oriented parameter circles and crossing occurrences, preserving cyclic successor, pairing, over/under
 designations and signs" (RecordIso); "Their evaluations by the same local LM construction agree" (P D =
 P D'); the sentence listing instances (page-chart changes, clean crossing-free replacements, height choices)
 and the closing sentence (no ambient isotopy) — judge the docstring's claim that they are illustrative and
 that the theorem for every named record bijection covers them; "all crossing-free circles must be included"
 (the component bijection e of RecordIso).
 lp:split-circle — "D' formed from D by adding one simple crossing-free component having no crossings with D;
 it may surround some components of D; it need not lie in the unbounded complementary face"
 (IsSplitCircleAddition D D': some component j of D' carries no crossing occurrence and the restriction of D'
 to the other components is a Reparam of D — expand Reparam and Diagram.restrict; is "simple" (the added
 component is an embedded circle) implied by "no crossings" in the polygonal class where all double points
 are crossings? is the nesting freedom respected? is Reparam rather than equality the right reading of
 "formed from D"?); eq. lp:split `P_{D'} = δ P_D`; "In particular every crossing-free c-component diagram
 has value δ^{c−1}" (`crossing_free`).
Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed clause without a
Lean counterpart, or any Lean field without a printed counterpart, is a discrepancy. Default to "not
faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
