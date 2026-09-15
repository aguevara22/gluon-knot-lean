You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/def-adeg-source-excerpt-lines-1887-1893.tex.txt
   (= reference/SM/sm-3-statesum.tex 1887-1893, def:adeg). Context, read ONLY to fix notation:
   reference/SM/sm-3-statesum.tex 916-980 (lit:homfly, lp:lm: the rings ℤ[a^{±1}, z^{±1}] and
   ℤ[l^{±1}, m^{±1}]), 1688-1700 (def:C: the coefficient extraction "[a^{d_Q} z^0] … (zero if that
   monomial is absent)"), 1894-1900 (the use of def:adeg right after it: d(F) = deg_a P_{S(F)}).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/def-adeg-reviewer-input-statement.lean.txt (bundle AdegDefinitionData, main
   declaration SM.adeg_definition). Its module docstring maps notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): LinkLaurentRing (namespace SM.Link: Laurent₂, R, T, R.a, R.z, R.aInv, R.zInv,
   R.aUnit, R.zUnit, Laurent₂.monoUnit, coeffAt, wtA, wtA', wtZ, wtZ', degA, mindegA, degZ, mindegZ,
   degAZ, mindegAZ, degZZ, mindegZZ — definitions and their docstrings only). Mathlib's
   AddMonoidAlgebra (single, coeff, supDegree, infDegree), WithBot, WithTop may be looked up in
   .lake/packages/mathlib (read-only). Do NOT open work/lean/SM/AdegDefinition.lean (it contains the
   proof; the statement file reproduces everything else in it).

YOUR TASK: decide whether the Lean bundle pins down exactly the printed definition. Check:
(a) the ring: the printed "nonzero Laurent polynomial f in a with coefficients in the integral domain
ℤ[z^{±1}]" versus the Lean reading of f as a nonzero element of R = ℤ[a^{±1}, z^{±1}] =
AddMonoidAlgebra ℤ (ℤ × ℤ) with the exponent pair (d, k) ↦ a^d z^k (field `monomial`; is the
identification of (ℤ[z^{±1}])[a^{±1}] with R faithful, and is the `domain` clause (IsDomain R) the
right rendering of "the integral domain ℤ[z^{±1}]"?); (b) the coefficient of a^d z^k as
`coeffAt d k f`, pinned by the field `coeff` (its value on monomials and that coefficients determine
f); (c) "deg_a f = maxdeg_a f denotes the largest a-exponent with nonzero coefficient and mindeg_a f
the smallest; both are integers": fields `degA` and `mindegA` — for f ≠ 0 the WithBot/WithTop-valued
degree equals the integer degAZ f / mindegAZ f, that integer is attained by a monomial with nonzero
coefficient and bounds every exponent of the support, and it is the unique such integer; (d) "The
same symbols with the subscript z denote the largest and smallest z-exponents of a nonzero element
of ℤ[a^{±1}, z^{±1}]": fields `degZ`, `mindegZ`. Also: does the Lean say anything about f = 0 (the
source does not define the degrees there; the Lean degAZ 0 = 0 by convention is not part of the
bundle — confirm that no clause asserts anything at f = 0); is the notation maxdeg_a rendered (the
source treats it as a synonym)? Expand definitions to primitives; say where the Lean is STRONGER or
WEAKER; any printed notion without a Lean counterpart, or any Lean clause without a printed
counterpart, is a discrepancy. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
