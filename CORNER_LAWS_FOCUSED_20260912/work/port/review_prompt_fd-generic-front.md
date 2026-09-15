You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
fd:generic-front (row 87, a theorem), Lean declaration `SM.fd_generic_front : SM.GenericFrontData`
(module SM/GenericFront.lean, namespace SM.GenericFront for the notions).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/fd-generic-front-source-excerpt-lines-2613-2630.tex.txt (= reference/SM/sm-3-statesum.tex
   2613-2630, Theorem fd:generic-front "A generic front preserving the chosen positive pushoff": "Every smooth oriented Legendrian embedding
   L : S¹ → ℝ³ admits a smooth ambient coorientation-preserving contact isotopy to a Legendrian embedding L_g whose xz front has only
   finitely many semicubical cusps and transverse double points, with no triple point and no cusp on another branch. At each cusp there is
   a smooth local coordinate u = y − y₀ in which x = x₀ + Au², y = y₀ + u, z = z₀ + A y₀ u² + (2/3) A u³, A ≠ 0 (fd:generic-exact-germ); the
   coordinate u may increase or decrease along the prescribed orientation. The isotopy carries a chosen thin positive-pushoff annulus and
   preserves its positive-pushoff transverse isotopy class, as well as the oriented topological knot type."). Context, ONLY to fix notation
   and to see which objects the statement names: sm-3:2631-2783 (its proof — skim: the Hamiltonian family Φ_a, the removal of double zeros
   of (x′, x″), the collar, the C/R avoidance, transverse double points, the cusp germ normalisation, the concatenation and the pushoff),
   2586-2597 (fd:contact-motions, accepted: composeFlows, the contact identity), 2395-2410 and 2488-2504 (fd:transverse-neighborhood,
   accepted, and the pushoff-annulus convention), 3456-3490 (fd:contact, the consumer: how L_g, the annulus, the transverse isotopy class
   and the knot type are used).
2. The Lean statement: work/reviews/fd-generic-front-reviewer-input-statement.lean.txt — the module with EVERY theorem proof replaced by
   `sorry`; the definitions are shown in full and the STATEMENT PART (lines 1-215: alpha, IsEmbeddedCircle, IsLegendrian, IsPushoffAnnulus,
   IsPositiveTransverse, IsCircleReparam, TransverselyIsotopic, IsCompactlySupportedAmbientIsotopy, IsContactIsotopy, front, coordX/coordY/
   coordZ, cuspSet, IsDoublePoint / SameParam, IsExactCuspGerm, IsGenericFront, GenericFrontHyp, GenericFrontConclusion, GenericFrontData)
   IS under review; everything after it (frontParam, Hamiltonian families, stages, the cusp flow — the proof's construction) is shown only
   because definitions are not withheld. It compiles. Do NOT open work/lean/SM/GenericFront.lean or anything under work/drafts/fd/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/ContactMotions.lean (row 86, accepted:
   alpha, hamVF, hamFlow, composeFlows, ContactMotionsData), work/lean/SM/TransverseNeighborhood.lean lines 1-205 (row 84, accepted: its
   IsPushoffAnnulus / IsPositivePushoff / TransverselyIsotopic / IsCompactlySupportedAmbientIsotopy — compare with this row's copies), and
   Mathlib (ContDiff, ContDiffOn, HasCompactSupport, Periodic, fderiv, deriv, Set.Finite, EuclideanSpace ℝ (Fin 3)).

DISCLOSED READINGS of the unit (judge each; you MAY read work/AUTHOR_NOTES.md entries "fd rows 84 and 87 re-assessed" (decision D-F15)
and "Row 87" of 2026-09-14), verbatim from the design memo:
### 2.6 Fidelity risks (row 87)

* **FR-GF-1** (2614) circles as `2π`-periodic lifts; "embedding" = injective mod `2π` + immersion.
* **FR-GF-2** (2614-2615) `IsContactIsotopy` includes **compact support**, absent from the printed
  statement, present in the printed proof (2632-2638, 2769-2772) and used by the consumer
  (sm-3:3480-3481 "the two smooth compactly supported ambient flows").  Deliberate strengthening.
* **FR-GF-3** (2616-2617) "cusp" = parameter with `x′ = 0` (consumer's reading sm-3:3470-3474);
  "semicubical" is carried by the germ clause; finiteness counted on one period.
* **FR-GF-4** (2617) double points as ordered pairs distinct mod `2π`; transversality = nonzero
  determinant of the front velocities `(x′, z′)`; the printed `x′(θ)x′(η)(y(η) − y(θ))` is this
  determinant for Legendrian curves (2717-2721).
* **FR-GF-5** (2621-2626) exact germ: `y′(θc) ≠ 0` makes `u = y − y₀` a local coordinate; "may
  increase or decrease" = no sign condition on `y′(θc)`; identities on a `θ`-neighbourhood.
* **FR-GF-6** (2627-2629) "a chosen thin positive-pushoff annulus" = any `IsPushoffAnnulus` of `L`
  (row 84's notion, sm-3:2490-2502); "thin" imposes no extra condition; the conclusion is quantified
  over all such annuli, which the proof supports (2773-2779).
* **FR-GF-7** (2629-2630) oriented knot type as in §2.4 (parametrized ambient isotopy class).
* **FR-GF-8** (2615) `L_g` is identified with the parametrized `Φ 1 ∘ L` (2632 "`Φ_a∘L`"); no
  reparametrization is allowed at the end of the contact isotopy.


YOUR TASK: decide whether the hypothesis structure + conclusion render exactly the printed theorem: the hypothesis (L a smooth oriented
Legendrian embedding S¹ → ℝ³ — 2π-periodic lift, injective mod 2π, immersion, α(L′) = 0); the isotopy (a smooth ambient
coorientation-preserving contact isotopy Φ: jointly smooth family on [0,1] from the identity of contactomorphisms with positive conformal
factor — is coorientation-preservation rendered? is compact support (FR-GF-2) a disclosed strengthening?); L_g = Φ₁ ∘ L (FR-GF-8) a
Legendrian embedding; "whose xz front has only finitely many semicubical cusps and transverse double points, with no triple point and no
cusp on another branch" (IsGenericFront: finite cuspSet, the exact germ at each cusp = "semicubical", finitely many double points, each
transverse, no triple, no cusp on another branch — check each field and the definitions front/cuspSet/IsDoublePoint/IsExactCuspGerm); the
exact germ clause with A ≠ 0 and u increasing or decreasing (no sign imposed on y′); "carries a chosen thin positive-pushoff annulus and
preserves its positive-pushoff transverse isotopy class" (FR-GF-6: for every pushoff annulus B of L, Φ₁ ∘ B is a pushoff annulus of L_g and
the positive circles are transversely isotopic — is "chosen thin" honoured by quantifying over all annuli?); "as well as the oriented
topological knot type" (FR-GF-7: a compactly supported ambient isotopy Ψ with Ψ₁ ∘ L = L_g — is this the right reading of "oriented
topological knot type", stronger, weaker?). Hypotheses added or dropped; every field a printed clause or a disclosed reading. Expand
definitions to primitives; say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
