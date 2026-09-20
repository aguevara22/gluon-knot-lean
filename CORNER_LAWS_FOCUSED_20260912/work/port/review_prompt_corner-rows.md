You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the statements
you are reviewing and you must not read their proofs. Your job is a statement-fidelity review of ONE row against ONE
printed source statement (frame SM15); the row is named in your task: cb:singleton (row 103, `SM.cb_singleton :
SM.CbSingletonData`, module SM/CBSingleton.lean), lem:corner-values (row 105, `SM.corner_values : SM.CornerValuesData`,
module SM/CornerValues.lean), or thm:C-soft (row 112, `SM.thm_C_soft : SM.CSoftData`, module SM/CSoft.lean — a FIXED
target name of lean/axiom-policy.json). Their statement bundles live in SM/CornerChainStatements.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. Printed sources, verbatim: row 103 — work/reviews/cb-singleton-source-excerpt-lines-4697-4702.tex.txt (= reference/SM/
   sm-3-statesum.tex 4697-4702: "Let A be a uniform carrier of S, and suppose one of its self-crossing labels c interlaces no
   other self-crossing of A. Then c(A) = 0"); row 105 — work/reviews/lem-corner-values-source-excerpt-lines-4801-4809.tex.txt
   (sm-3:4801-4809: (i) "If Q is uniform and embedded (m_Q = 0) then |r_Q| = 1, d_Q = 0 and c(Q) = 1"; (ii) "If Q is uniform and
   {y} is a crossing of Q interlacing no other crossing of Q, then c(Q) = 0"); row 112 — work/reviews/thm-C-soft-source-excerpt-
   lines-984-991.tex.txt (reference/SM/sm-4-knotlaws.tex 984-991: "Let P be generic, j a vertex, q admissible, and P_ε the soft
   insertion of Definition def:soft, with attachment signs χ±. Then for all sufficiently small ε > 0, C(P_ε) = (χ₋ + χ₊)/2 · C(P)").
   Context ONLY to fix notation: sm-3:4703-4759 (proof of 103), 4810-4820 (proof of 105), sm-4:993-1147 (proof of 112), the
   definitions def:C (sm-3, grep "def:C" — c(A), H⁺, m_Q, r_Q, d_Q; and the accepted SM/CornerStateSum.lean), def:smoothing /
   cb:blocks / def:interlace (grep in sm-3), def:soft and lem:soft-generic (sm-4, grep "def:soft"), def:uniform (sm-3:245 region),
   lem:carriers, and the accepted siblings thm:C-S3 / thm:C-S5 / prop:C-chamber / prop:C-silent (their modules via
   work/lean/lean-declarations.json) for the statement conventions of the C rows.
2. The Lean statements: work/reviews/corner-rows-reviewer-input-statement.lean.txt (the three row modules, proofs withheld) and
   work/reviews/corner-chain-statements-reviewer-input.lean.txt (SM/CornerChainStatements.lean with proofs replaced by sorry:
   §0 the bridge lemmas to the accepted floor interface, §1 algebra, CbSingletonData, CornerValuesData (+ companions),
   CS7Data (+ companions; row 110 is NOT under review here), CSoftData (+ companions exists_generic / doubled)). Docstrings quote
   the source — verify them, do not trust them. Do NOT open SM/CornerChainUnits.lean (proofs).
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/CornerStateSum.lean (def:C:
   cornerStateSum, cornerCoefficient, cornerHomfly, cornerSlot, carrierCrossingCount, carrierCrossings, carrierRotation /
   carrierRotationInt, CarrierUniform, ccpCornerPolygon, IsDecomposition, Component), SM/CBProducts.lean, SM/CBlocks*.lean
   (Interlaces, def:interlace; blocks), SM/Children.lean, SM/SoftGenericLemma.lean and SM/SoftAmplitudeSectors.lean (softInsertion,
   SoftAdmissible, softAmplitudeMultiplier = (χ₋ + χ₊)/2, softAttachmentMinus/Plus), SM/CarrierFloor.lean (FloorTheoremData —
   consumed only in the PROOFS, not in the statements), SM/EmbeddedRotation.lean (row 104), SM/HypR.lean, and Mathlib.
4. Disclosed readings: work/AUTHOR_NOTES.md entry "Corner chain (rows 103 cb:singleton, 105 lem:corner-values, 110 thm:C-S7, 112
   thm:C-soft): design panel judged …" of 2026-09-15 (decisions D-CC-1..5 and the fidelity risks FR-CC-1..15) and the wave entries
   (the route deviation of sft_same_sign: homfly equality through the accepted record layer instead of Reparam + Deform — a
   PROOF matter, not a statement matter).

KERNEL FACTS (reported by the executor; re-check with `cd work/lean && lake env lean` on a scratch file importing SM.CSoft if you
wish — the machine is loaded, batch your checks): all three row theorems have no hypothesis; axioms exactly [propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word,
SM.src_contact] — all registered (inherited from SM.thm_floor, row 100, the a-degree floor these rows consume).

YOUR TASK. Row 103: compare the clause with CbSingletonData.isolated_zero (binders hn : 3 ≤ n, hP : Generic P, S with hS :
IsDecomposition, A a Component with CarrierUniform; "one of its self-crossing labels c" = c ∈ carrierCrossings A (def:smoothing's
crossings_of — FR-CC-1); "interlaces no other self-crossing of A" = ∀ c' ∈ carrierCrossings A, c' ≠ c → ¬ Interlaces c c' (the
interlacement graph G_P of def:interlace, the graph the printed proof uses, FR-CC-1); "c(A) = 0" = cornerCoefficient A hS = 0 (the
total coefficient, def:C, FR-CC-2). Row 105: (i) ↔ embedded_value ("uniform and embedded (m_Q = 0)" = CarrierUniform ∧
carrierCrossingCount = 0 — FR-CC-4: the hypothesis is the printed gloss m_Q = 0, embeddedness is a theorem; conclusions |r_Q| = 1
for the real carrierRotation (FR-CC-5), cornerSlot = 0, cornerCoefficient = 1); (ii) ↔ isolated_zero = 103's clause at (Q, y)
(FR-CC-6). Row 112: "Let P be generic, j a vertex, q admissible, P_ε the soft insertion of def:soft with attachment signs χ±. Then
for all sufficiently small ε > 0, C(P_ε) = (χ₋ + χ₊)/2 · C(P)" ↔ CSoftData.soft_theorem (SoftAdmissible → ∃ ε₁ > 0, ∀ ε < ε₁, ∀ hQ :
Generic (softInsertion P j q ε), (C(P_ε) : ℚ) = softAmplitudeMultiplier P j q · C(P) — FR-CC-11: the identity read in ℚ with the
accepted softAmplitudeMultiplier = (χ₋ + χ₊)/2 (integer division rejected); FR-CC-12: "for all sufficiently small ε" = ∃ ε₁ > 0 ∀ ε
∈ (0, ε₁); C(P_ε) presupposes P_ε generic, quantified ∀ hQ (lem:soft-generic (i) gives it; the accepted thm:A-soft uses ∃ hQ — the
companion exists_generic is proved); companion doubled: 2 C(P_ε) = (χ₋ + χ₊) C(P) in ℤ). Expand definitions to primitives (in
particular: is Interlaces the printed interlacement; is carrierCrossings the printed "self-crossing labels of A"; is
softAmplitudeMultiplier exactly (χ₋ + χ₊)/2 with def:soft's χ±; is the class of P_ε the printed one). Say where the Lean is STRONGER
or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite source and
statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of strings),
"supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
