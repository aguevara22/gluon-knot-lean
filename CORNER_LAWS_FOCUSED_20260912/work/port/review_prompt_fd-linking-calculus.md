You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
fd:linking-calculus (row 88), Lean declaration `SM.fd_linking_calculus : SM.LinkingCalculusData` (module SM/LinkingCalculusRow.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/fd-linking-calculus-source-excerpt-lines-2785-2826.tex.txt (= reference/SM/sm-3-statesum.tex
   2785-2826, Lemma fd:linking-calculus "Linking calculus and uniform transverse framing": the normalized linking pairing
   fd:gauss-linking 2787-2793, "symmetric and constant under smooth families of disjoint oriented pairs" 2794-2795, generic directions and
   the finitely many transverse mixed crossings 2796-2799, the observer/orientation conventions and the crossing formula 2799-2804, the
   normalization sentence 2805-2806 (commentary), the framed families 2808-2814, the transverse families and sl 2816-2824). Context, ONLY
   to fix notation and to see which objects the statement names: sm-3:2827-3010 (its proof — skim: the divergence identity, the degree
   formula fd:regular-pole-count 2884-2916, the crossing computation 2917-2941, the normal chart 2942-2965), 2395-2410 (fd:transverse-
   neighborhood, the consumer of the transverse clauses), 3379-3400 (fd:ng-bound, which consumes the self-linking number sl).
2. The Lean statement: work/reviews/fd-linking-calculus-reviewer-input-statement.lean.txt — the row module SM/LinkingCalculusRow.lean with
   the row proof replaced by `sorry`: the bundle LinkingCalculusData (nine fields: symm, family_const, finite_crossings, crossing_formula,
   framing_uniform, framing_invariant, framing_homotopy, transverse_uniform, self_linking_invariant) and the theorem. It compiles. Do NOT
   open work/lean/SM/LinkingCalculusRow.lean or work/lean/SM/RegularPoleCount.lean or anything under work/drafts/fd/.
3. The definitions module work/lean/SM/LinkingCalculus.lean (definitions and docstrings ARE under review; its theorem proofs are helper
   material not under review — you may read theorem STATEMENTS to understand the definitions): E3 = EuclideanSpace ℝ (Fin 3) with
   coordinates p 0, p 1, p 2 = x, y, z; IsSmoothCircle (C^∞, P-periodic), DisjointPair, DisjointPairFamily, gaussMap G(u,v) =
   (C₂ v − C₁ u)/‖·‖, pderivU / pderivV (derivatives of the one-variable slices), gaussDensity G·(G_u × G_v), gaussIntegral, linking
   (= (1/4π) ∫_{[0,P]²} …), projAlong, Parallel, GenericDirection, mixedCrossings (in one fundamental domain [0,P)²), planeDet ν x y =
   det(x, y, ν), lcCrossingSign (the overpass-first sign: the strand nearer the observer — larger ⟪·,ν⟫ — is over), FramedFamily, pushoff
   C + ε v, lcContactForm (dz − y dx), ey = ∂_y, IsPositiveTransverseEmbedding, TransverseFamily, selfLinking sl(T) = ℓ(T, T + ε ∂_y), and
   the conditional bundle LinkingCalculusDataOf whose crossing_formula takes RegularPoleCount as a hypothesis (RegularPoleCount is the
   degree formula fd:regular-pole-count, sm-3:2894-2897, stated as a Prop and PROVED elsewhere as SM.regularPoleCount — the row bundle
   under review has NO such hypothesis). Also Mathlib (this project's pin) for ContDiff, Periodic, LinearIndependent, cross product,
   intervalIntegral, finsum (∑ᶠ), Real.sign.

DISCLOSED READINGS of the unit (judge each; you MAY read work/AUTHOR_NOTES.md entries "Decision D-F14" and "RegularPoleCount" of
2026-09-14): FR-LC-1 S¹ = ℝ/Pℤ with P > 0 a parameter of every definition (printed S¹ × S¹ with du dv, no period given; the consumer uses
2π); both circles share the period; reparametrisation invariance of ℓ is neither printed nor proved. FR-LC-2 G_u, G_v are the derivatives
of the one-variable slices. FR-LC-3 a "smooth family C_s, 0 ≤ s ≤ 1" is the restriction to s ∈ [0,1] of a jointly C^∞ map ℝ × ℝ → E3 with
the hypotheses (disjointness, embeddedness, independence, positivity) imposed only for s ∈ [0,1]. FR-LC-4 orientation of a circle =
parameter direction, of ℝ³ = standard; "orient the projection plane so that its positive basis followed by ν is positive" = planeDet ν x y
= det(x, y, ν) = ⟪ν, x × y⟫; "ν points toward the observer; the strand nearer the observer is over" = at a crossing C₂(v) − C₁(u) = t ν,
C₂ is over iff t > 0. FR-LC-5 "parallel to ν" = ∃ t, w = t • ν (both signs, as the printed proof says at 2919-2920); "projected along ν"
= orthogonal projection onto ν^⊥; crossings counted in one fundamental domain [0,P)²; self-crossings of a component are not part of the
statement (mixed crossings only); the field finite_crossings asserts finiteness, transversality being the defining independence.
FR-LC-6 the crossing formula is written with ∑ᶠ over mixedCrossings (equal to the finite sum by finiteness). FR-LC-7 "embedded circle" =
injective on ℝ/Pℤ; the immersion condition follows from the independence / positivity hypotheses and is not repeated. FR-LC-8 "disjoint
framed pairs" = DisjointPair of (C_s, C_s + ε v_s); "independent of that radius" is proved for EVERY common radius ε₀ with the disjointness
property (a slight strengthening); the paper's four-dimensional normal chart is not exported. FR-LC-9 ∂_y = ey; the positive transverse
embedding property of T_s itself is restated in the conclusion; only positivity of the pushoff's contact form is claimed (not the a₀/2
clearance). The sentence 2805-2806 ("Thus it has exactly the linking normalization used in the source's front calculations") is
commentary with no field.

YOUR TASK: decide whether the definitions + bundle render exactly the printed lemma, clause by clause: the pairing (is `linking` the printed
(1/4π)∫ G·(G_u × G_v) du dv with the printed G?), symmetry, constancy under smooth families, the generic-direction definition, finiteness of
the transverse mixed crossings, the crossing formula (one half the sum of the overpass-first signs sgn det(u_o, u_u) — check the sign
convention against FR-LC-4 by expanding lcCrossingSign and planeDet; check "one half"), the framed-family clauses (one common ε for the
whole family; pairing independent of radius and of s; the homotopy-of-framings sentence), the transverse clauses (T_s and T_s + ε∂_y
disjoint positive transverse embeddings for all s and 0 < ε ≤ ε₀; sl independent of ε and s). Hypotheses added or dropped; every field a
printed clause or a disclosed extra. Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; label non-blocking notes.
Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
