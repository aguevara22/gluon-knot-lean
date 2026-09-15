You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
fd:transverse-neighborhood (row 84), Lean declaration `SM.fd_transverse_neighborhood : SM.TransverseNeighborhoodData`
(module SM/TransverseNeighborhood.lean, namespace SM.TransverseNeighborhood for the notions).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/fd-transverse-neighborhood-source-excerpt-lines-2395-2410.tex.txt (= reference/SM/sm-3-statesum.tex
   2395-2410, Lemma fd:transverse-neighborhood: "Let α = dz − y dx and let T : ℝ/(2πℤ) → ℝ³ be a smooth embedded oriented circle with
   α(T′) > 0. There are δ > 0 and a smooth embedding H : S¹ × D_δ → ℝ³ fixing the parametrized core T such that H^*α = hα₀, α₀ = dθ + u dv −
   v du, h > 0. There is an oriented Legendrian knot L in this neighbourhood whose positive transverse pushoff is transversely isotopic to T.
   An explicit compactly supported ordinary ambient isotopy carries the parametrized L to the parametrized T, preserving their
   orientations."). Context, ONLY to fix notation and to see which objects the statement names: sm-3:2411-2559 (its proof — skim: the chart F,
   the Moser field, the flow, the helix L, the annulus and the pushoff convention 2490-2504, the ambient isotopy 2522-2541), 2586-2597
   (fd:contact-motions, accepted), 3456-3470 (fd:contact, the consumer: how L, the pushoff and the ambient isotopy are used).
2. The Lean statement: work/reviews/fd-transverse-neighborhood-reviewer-input-statement.lean.txt — the module with EVERY theorem proof replaced
   by `sorry`; the definitions are shown in full and the STATEMENT PART (lines 1-205: alpha, alpha0, solidTorus, IsEmbeddedCircle,
   IsPositiveTransverse, IsLegendrian, IsTransverseModel, IsPushoffAnnulus, IsPositivePushoff, IsCircleReparam, TransverselyIsotopic,
   IsCompactlySupportedAmbientIsotopy, TransverseNeighborhoodHyp, TransverseNeighborhoodConclusion, TransverseNeighborhoodData) IS under
   review; everything after it (the chart, forms, Moser field, flows, helix, annulus, pushforward — namespace SM.TransverseNeighborhood's
   construction) is the proof's construction, shown only because definitions are not withheld. It compiles. Do NOT open
   work/lean/SM/TransverseNeighborhood.lean or anything under work/drafts/fd/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/ContactMotions.lean (row 86, accepted:
   alpha, IsGlobalFlow, globalFlow — the ambient isotopy of this row is a flow), and Mathlib (ContDiff, ContDiffOn, HasCompactSupport,
   Periodic, fderiv, deriv, EuclideanSpace ℝ (Fin 2/3), Metric.ball).

DISCLOSED READINGS of the unit (judge each; you MAY read work/AUTHOR_NOTES.md entries "fd rows 84 and 87 re-assessed" and "Row 84
fd:transverse-neighborhood PROVED" of 2026-09-14), verbatim from the design memo:
### 1.6 Fidelity risks (row 84)

* **FR-TN-1** (sm-3:2397) `S¹ = ℝ/2πℤ` as `2π`-periodic lifts; "embedded" = injective mod `2π` + immersion.
* **FR-TN-2** (sm-3:2399-2400) "smooth embedding `H : S¹ × D_δ → ℝ³`" = `C^∞` on the open solid torus +
  injective mod `2π` + immersion + images of open sets relatively open; the proof gives a global
  diffeomorphism onto an open set, so the field is weaker than what is proved, never stronger.
* **FR-TN-3** (sm-3:2401-2403) `h` quantified with `H`, only `h > 0` demanded (printed clause); the proof's
  `h` is smooth but smoothness is not a printed clause.
* **FR-TN-4** (sm-3:2405, 2490-2502) "positive transverse pushoff" = a small positive circle of a
  transverse annulus with `L` as zero circle (the paper's "source convention", sm-3:2501-2502);
  if a consumer needs Etnyre's pushoff a bridge lemma is required.
* **FR-TN-5** (sm-3:2405-2406, 2503-2504) transverse isotopy ends at an orientation-preserving
  reparametrization `T∘ρ` (`T(θ+κb)`).
* **FR-TN-6** (sm-3:2481-2482, 2501) the annulus domain is the open `(−ε, b)`; the closed end `s = b`
  is reached only through the isotopy clause.
* **FR-TN-7** (sm-3:2406-2408, 2538-2541) "ordinary ambient isotopy … preserving their orientations" =
  compactly supported family of `C^∞` diffeomorphisms of `ℝ³` with `Ψ_1∘L = T` as parametrized
  circles; the extension to `S³` and orientation-preservation of `Ψ_t` (sm-3:2538-2541) are not
  clauses of the statement and are not stated.


YOUR TASK: decide whether the hypothesis structure + conclusion render exactly the printed lemma: the hypotheses (T a smooth embedded
oriented circle — 2π-periodic lifts, injective mod 2π, immersion — with α(T′) > 0 everywhere); the model (δ > 0; H a smooth embedding of the
open solid torus S¹ × D_δ — smooth, injective mod period, immersion, open images; "fixing the parametrized core T" = H(θ, 0) = T θ;
H^*α = h α₀ with α₀ = dθ + u dv − v du — check the coordinate formula of alpha0 and the direction of the pullback identity; h > 0 — is h
quantified as printed?); the Legendrian knot L in the neighbourhood (embedded circle in the image of H with α(L′) = 0) whose positive
transverse pushoff (a small positive circle of a transverse annulus with L as its zero circle, the paper's convention 2490-2504) is
transversely isotopic to T (smooth family of positive transverse embedded circles, possibly ending at an orientation-preserving
reparametrization of T — FR-TN-5); the compactly supported ordinary ambient isotopy Ψ (t ∈ [0,1], jointly smooth, Ψ₀ = id, each Ψ_t a
smooth bijection with smooth inverse, identity outside a compact set) carrying the parametrized L to the parametrized T "preserving their
orientations" (Ψ₁ ∘ L = T as parametrized curves). Hypotheses added or dropped; every field a printed clause or a disclosed reading.
Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
