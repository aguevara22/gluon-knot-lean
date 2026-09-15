You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
fd:contact-motions (row 86), Lean declaration `SM.fd_contact_motions : SM.ContactMotionsData` (module SM/ContactMotions.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/fd-contact-motions-source-excerpt-lines-2586-2597.tex.txt (= reference/SM/sm-3-statesum.tex
   2586-2597, Lemma fd:contact-motions "Explicit contact motions": "For a smooth compactly supported H : ℝ³ → ℝ, the vector field
   X_H = −H_y ∂_x + (H_x + y H_z) ∂_y + (H − y H_y) ∂_z has a global flow φ_H^s of coorientation-preserving contact diffeomorphisms for
   α = dz − y dx: (φ_H^s)^*α = c_s^H α with a smooth positive function c_s^H, its conformal factor. Finite compositions of their
   small-time flows depend smoothly on the times and are arbitrarily C^k-close to the identity on compact sets for each fixed finite k.").
   Context, ONLY to fix notation and to see which objects the statement names: sm-3:2598-2612 (its proof — skim: α(X_H) = H,
   L_{X_H}α = H_z α, the exponential formula for c, ODE continuation, "smooth ODE dependence proves the last assertion"), 2613-2660
   (fd:generic-front, the consumer: how the flows and their compositions Φ_a are used), 2395-2400 (the fd block's setting).
2. The Lean statement: work/reviews/fd-contact-motions-reviewer-input-statement.lean.txt — the module SM/ContactMotions.lean with EVERY
   theorem proof replaced by `sorry` (the row theorem and all helper theorems are withheld); the definitions are shown in full and ARE
   under review: e, alpha (α_p(v) = v_z − p_y v_x), pd (∂_i H = fderiv H p (e i)), hamVF (X_H), coordCLM, IsGlobalFlow (φ 0 p = p and
   ∂_s φ = X ∘ φ), globalFlow (Classical.epsilon of IsGlobalFlow — "the" global flow, whose existence and uniqueness are theorems),
   confFactorOf / confFactor (c_s^H = exp ∫_0^s H_z ∘ φ^v — the printed formula sm-3:2603-2606 taken as the DEFINITION of the conformal
   factor), hamFlow, ContactMotionsHyp (smooth, compactly supported), composeFlows (Φ_a = φ_{H_0}^{a_0} ∘ ⋯ ∘ φ_{H_{n−1}}^{a_{n−1}}),
   SmoothDependence (a Prop that is proved in the module — `SM.smoothDependence`; the row theorem does NOT assume it), and the bundle
   ContactMotionsData (fields isGlobalFlow, flow_add, diffeo, contact, confFactor_pos, confFactor_smooth, compositions_smooth,
   compositions_close). It compiles. Its module docstring maps notation — verify it, do not trust it. Do NOT open
   work/lean/SM/ContactMotions.lean or anything under work/drafts/fd/.
3. Mathlib (this project's pin) for the meanings of ContDiff ℝ ∞, HasCompactSupport, HasDerivAt, fderiv, iteratedFDeriv, uncurry,
   Function.LeftInverse/RightInverse, intervalIntegral, EuclideanSpace ℝ (Fin 3) (written ℝ³ in the module; coordinates p 0, p 1, p 2
   = x, y, z).

DISCLOSED READINGS of the unit (judge each; you MAY read work/AUTHOR_NOTES.md entries "fd:contact-motions (86)" of 2026-09-14 and
work/drafts/fd/FD_84_86_REPORT.md §4 ONLY): FR-CM-0 hamVF and alpha are written in coordinates (p 0, p 1, p 2 = x, y, z; e i the
standard basis; pd H i p = fderiv ℝ H p (e i)); hamFlow H = Classical.epsilon (IsGlobalFlow (hamVF H)) is a definite description of
the flow — unique under the hypothesis (a theorem, not a field) — and the bundle asserts IsGlobalFlow (hamVF H) (hamFlow H) rather
than an existential; FR-CM-1 the pullback identity (φ^s)^*α = c α is stated pointwise on tangent vectors: α_{φ_s p}(Dφ_s(p) v) = c_s(p) α_p(v) for all p, v
(Mathlib has no differential-form calculus); FR-CM-2 "coorientation-preserving" = c > 0 (the printed "positive"); FR-CM-3 "a smooth
positive function c_s^H" = c jointly C^∞ in (s, p) (containing the printed smoothness), with the printed exponential formula as its
definition; FR-CM-4 "diffeomorphisms" = each φ^s is C^∞ with C^∞ inverse φ^{−s} (left and right inverse), plus joint smoothness in
(s, p) of the flow; FR-CM-5 "finite compositions of their small-time flows depend smoothly on the times" = for every n and every family
of n Hamiltonians satisfying the hypothesis, (a, p) ↦ Φ_a(p) is jointly C^∞ (no smallness needed for smoothness); FR-CM-6 "arbitrarily
C^k-close to the identity on compact sets for each fixed finite k" = for every compact K, k and ε > 0 there is δ > 0 such that
|a_i| < δ for all i gives ‖D^j(Φ_a − id)(p)‖ < ε for all j ≤ k and p ∈ K (uniform bound on the iterated derivatives of the
difference; δ depends on K, k, ε and the Hamiltonians); FR-CM-7 "smooth ODE dependence" (sm-3:2611, a proof step) is the theorem
smoothDependence, proved in the module for any finite-dimensional real space and specialised to ℝ³ — it is not a hypothesis of the
row. Also: "global flow" = defined for all s ∈ ℝ with the group law φ^{s+t} = φ^s ∘ φ^t (field flow_add) and the flow
equation; the flow is the unique global flow (uniqueness is a theorem, not a field).

YOUR TASK: decide whether the hypothesis structure + bundle render exactly the printed lemma: the hypothesis (H smooth, compactly
supported); the vector field X_H (check the three components against the printed formula, including the signs and the y-factors —
hamVF's components versus −H_y, H_x + y H_z, H − y H_y, and pd's partial derivatives); "has a global flow" (IsGlobalFlow + flow_add);
"coorientation-preserving contact diffeomorphisms for α = dz − y dx" (diffeo, contact, confFactor_pos — is alpha exactly dz − y dx?);
"with a smooth positive function c_s^H, its conformal factor" (confFactor_smooth, confFactor_pos; is defining c by the printed
exponential formula and then asserting the contact identity with it faithful to "there is a smooth positive c with (φ^s)^*α = c α"?);
the last sentence (compositions_smooth, compositions_close — is "small-time" honoured; is "C^k-close on compact sets" the printed
notion?). Hypotheses added or dropped; every field a printed clause or a disclosed extra. Expand definitions to primitives; say where
the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
