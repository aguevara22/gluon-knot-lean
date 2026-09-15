You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row (named in your task) against ONE printed source statement (frame SM15):
row 78 ng:front-II — `SM.ng_front_II : SM.NgFrontIIClauses` (fields typeII_D, typeII_w, typeII_d, typeII_B; module SM/FrontRowsW3b.lean), or
row 83 ng:local-front-bound (a THEOREM) — `SM.ng_local_front_bound : SM.NgLocalFrontBoundClauses` (field front_inequality; module
SM/FrontRowsW3b.lean; the structure is declared in SM/FrontRowsW3.lean), or
row 93 fd:ng-bound — `SM.fd_ng_bound : SM.NgBoundClauses` (fields slNg_eq, ng_input; module SM/NgBound.lean).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: row 78 = work/reviews/ng-front-ii-source-excerpt-lines-1972-1975.tex.txt (= reference/SM/sm-3-statesum.tex
   1972-1975, Lemma ng:front-II: "The front type-II moves preserve D, w, d, and hence B."); row 83 = work/reviews/ng-local-front-bound-
   source-excerpt-lines-2305-2313.tex.txt (= sm-3 2305-2313, Theorem ng:local-front-bound "Individual-front polynomial bound": "For every
   front F on the domain of Definition ng:front-domain, with the same polynomial evaluated on its actual ordinary cusp rounding,
   w(F) − D(F) ≤ −deg_a P_{S(F)} − 1 (ng:front-inequality)"; consumes Literature input ng:finite-word); row 93 = work/reviews/fd-ng-bound-
   source-excerpt-lines-3379-3390.tex.txt (= sm-3 3379-3390, Lemma fd:ng-bound "the individual-front bound in self-linking form": "Let F be a
   front on the domain of Definition ng:front-domain, with c↓(F) = D(F) its number of downward cusps, and let S(F) be an actual clean
   ordinary cusp smoothing of F as in that definition. Then sl_Ng(F) := w(F) − c↓(F) ≤ −max deg_a P_{S(F)}(a,z) − 1 (fd:ng-input). This is
   not an application of an ambient-invariant hypothesis to the local diagram construction, nor a maximum over front representatives.").
   Context, ONLY to fix notation and to see which objects the statements name: sm-3:1825-1841 (ng:front-domain: fronts, D, w, s, the
   rounding S(F)), 1843-1920 (the certificate B = D − w − d − 1 with d = deg_a P_{S(F)}; def:adeg; the words framework), 1921-1949
   (ng:commutation, accepted: every front is represented by a word), 1976-1989 (row 78's printed proof), 2314-2343 (row 83's printed proof:
   the strong induction on words using ng:finite-word and the seven certificate rows, then the transport to F by ng:commutation),
   3391-3399 (row 93's printed proof: "Inequality ng:front-inequality of Theorem ng:local-front-bound … deg_a P is the maximum a-degree"),
   and blueprint/AXIOM_REGISTRY.md section ng:finite-word (the accepted literature interface consumed by row 83).
2. The Lean statements with every theorem proof replaced by `sorry`: rows 78 and 83 = work/reviews/ng-front-ii-local-bound-reviewer-input-
   statement.lean.txt (module SM/FrontRowsW3b.lean, 192 theorems stripped: the type-II move construction (namespace SM.FrontRows.U6
   continuation) and the leaf typeII_move (≈1273) are PROOF material; under review: `ng_front_II` (≈1296) with its structure
   NgFrontIIClauses (declared in SM/FrontRowsW3.lean — read it there: `grep -n 'structure NgFrontIIClauses' work/lean/SM/FrontRowsW3.lean`,
   fields typeII_D/w/d/B on closed oriented words through SM.realize), `ng_local_front_bound` (≈1328) with its structure
   NgLocalFrontBoundClauses (SM/FrontRowsW3.lean line ≈81: `front_inequality : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
   F.writhe − (F.downCount : ℤ) ≤ −degAZ (P S) − 1`); `certificate_laws` (≈1310) and `word_bound` (≈1319) are the printed proof's
   word-level induction — evidence, not under review); row 93 = work/reviews/fd-ng-bound-reviewer-input-statement.lean.txt (module
   SM/NgBound.lean: the structure NgBoundClauses (≈66), the conditional `fd_ng_bound_of` (≈78, evidence) and the row theorem `fd_ng_bound`
   (≈108); `SmoothFront.slNg` is the accepted definition in SM/FrontSmooth.lean line ≈732 (`slNg : ℤ := F.writhe − F.downCount`) — read it
   there). The files compile. Do NOT open work/lean/SM/FrontRowsW3b.lean, work/lean/SM/NgBound.lean or anything under work/drafts/frontrows/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontSmooth.lean (SmoothFront — the accepted
   def ng:front-domain: downCount D, writhe w, sCount, IsRounding S (Nonempty Rounding = GeomRounding + Marking: an actual clean ordinary
   cusp rounding carrying the front's named record), defect S, slNg ≈732, defect_nonneg_iff_slNg ≈1528 — statement only), SM/FrontWords.lean
   (IsTypeII ≈430: the type-II patterns), SM/FrontWordsBase.lean / FrontWords.lean (OWord), SM/FrontRealize*.lean (SM.realize), SM/FrontPL.lean
   (PLFront: downCount, writhe, defect, diagram), SM/LocalPolynomial.lean (P), SM/LinkLaurentRing.lean (degAZ ≈446: (degA f).unbotD 0, the
   integer a-degree = max a-exponent of the support; degAZ_spec), SM/FrontInterfaces.lean (the axiom SM.ng_finite_word — statement),
   SM/FrontRowsW2.lean lines 1-100 and SM/FrontRowsW3.lean lines 1-100 (headers and statement parts). Do NOT open other work/ files.

DISCLOSED FIDELITY RISKS recorded BEFORE the rows were stated (work/AUTHOR_NOTES.md entries "Front certificate rows 76-83" ~07:27Z,
"Row 93 fd:ng-bound: statement and derivation prepared" ~15:00Z, and the later frontrows entries — you MAY read them; PLAN_FINAL.md §1, §7;
NGBOUND_PLAN.md §3): FR-1/FR-5 (accepted): the front block on the PL class and on closed oriented WORDS through SM.realize for the
move rows; FR-8: the move rows (77-82) on realizations of words — the class narrowing CLOSED by the accepted row 76 field represent (every
front is represented by a word, with equal D, w, s and a record isomorphism of every rounding); FR-13: d = degAZ (P ·) reaches SM.lp_lm
through P; FR-14: row 83 consumes the accepted axiom SM.ng_finite_word (its syntactic standard-circle base); FR-1/FR-16: for a smooth front
F, d(F) = degAZ (P S) on any rounding S with F.IsRounding S — row 83 and row 93 quantify over ALL such S ("its actual ordinary cusp
rounding" = any clean ordinary cusp rounding carrying the record; ng:smoothing-record makes P_{S(F)} independent of the choice); row 83 is
stated on the SMOOTH class SmoothFront (the printed domain), derived from the word-level induction through represent. Row 93 (verbatim
from NGBOUND_PLAN.md §3):
## 3. Fidelity readings / risks (cite in the review of row 93 together with FR-1, FR-8, FR-10, FR-16)

- **FR-NB-1 ("max deg_a P_{S(F)}(a,z)" = `degAZ (P S)`).**  `degAZ f := (degA f).unbotD 0` (LinkLaurentRing.lean:446),
  `degA f := f.supDegree wtA` = the sup of the `a`-exponents of the support (def:adeg, sm-3:1887-1891), `⊥` at `f = 0`;
  so `degAZ` is `0` at `f = 0` by convention.  The convention is never exercised: `P S ≠ 0` for every diagram
  (`P_ne_zero`, lp:core), and `degAZ_P_isMaxDegA S` states exactly the printed reading — `degAZ (P S)` is attained by a
  monomial of `P S` with nonzero coefficient and bounds every `a`-exponent of the support.  This is the printed proof's
  first sentence, made a theorem.  Row 83 already uses the same `degAZ (P S)` (`dOf`, FR-16), so the two rows bound
  the same integer; no "max" is a separate operation in Lean.
- **FR-NB-2 (`c↓(F) = D(F)`).**  The printed clause introduces `c↓` as a name for `D(F)`; Lean uses `F.downCount`
  directly ("Write D(F) for the number of downward cusps", FrontSmooth.lean:724, one of the FrontDomainDefinitionData
  clauses).  No alias declared (an alias would be a second name for an accepted def, and the display's `:=` is already
  rendered by `slNg_eq`).  A reviewer may ask that `c↓` appear by name; the docstring of `NgBoundClauses` records the
  identification.
- **FR-NB-3 (the definitional half of the display as a field).**  `sl_Ng(F) := w(F) − c↓(F)` is printed inside the
  lemma, so it is a field (`slNg_eq`, `rfl` on the accepted `SmoothFront.slNg`, whose docstring already names it
  "the quantity bounded in ng:local-front-bound / fd:ng-bound (`sl_Ng`)").  If the reviewers count the display as one
  clause, drop `slNg_eq` (one-line change in the structure and in `fd_ng_bound_of`/`of_defect_nonneg`); the inequality
  field is unaffected.  `slNg : ℤ` is `writhe : ℤ` minus the cast of `downCount : ℕ`, matching row 83's cast
  `F.writhe - (F.downCount : ℤ)`; the casts in the two rows are identical, so no `omega`/`push_cast` is needed.
- **FR-NB-4 (the rounding quantifier).**  "let S(F) be an actual clean ordinary cusp smoothing of F as in that
  definition" is read as: for every `S : Diagram` with `F.IsRounding S` (the accepted def ng:front-domain rounding,
  FR-1's polygonal reading: `S` carries the named record (`Marking`) of the cusp-free smooth curve `G` produced by the
  clean-disc replacement `GeomRounding`).  This is the same quantifier as row 83's `front_inequality`, so no transfer
  between roundings is needed; ng:smoothing-record (`P_{S(F)}` independent of the rounding; Lean: `presentations` via
  `defect_eq_of_recordIso`) is what makes the printed symbol `P_{S(F)}` well defined and is not an input of the Lean
  theorem — the bound holds for each rounding separately, which is the stronger reading.  Existence of a rounding is
  not asserted by either row (nor by the printed lemma, which says "let S(F) be").
- **FR-NB-5 (the class).**  `F : SmoothFront` is the accepted class of ng:front-domain (row 73/74 vocabulary,
  `front_domain_definition`).  Row 93 inherits row 83's class exactly; in particular the FR-8 class narrowing (rows
  77-82 on `OWord` realizations) does NOT reach row 93 as long as row 83 is stated on `SmoothFront` (which it is,
  through `represent`, FR-10).  If the FR-8 fallback is ever taken (class change on 76/83/93, D-F7), row 93's statement
  must change in the same way and this must be disclosed; nothing in this file anticipates the fallback.
- **FR-NB-6 (the two closing sentences).**  "This is not an application of an ambient-invariant hypothesis to the local
  diagram construction, nor a maximum over front representatives" describes what the statement is not; no field.  The
  Lean form makes it manifest: the hypotheses are `F : SmoothFront`, `S : Diagram`, `F.IsRounding S` (no ambient object,
  no knot type, no `sup` over representatives).
- **FR-NB-7 (`P` reaches `lp_lm`).**  As for every polynomial clause (FR-13): `#print axioms` of any theorem whose
  statement mentions `P` lists `SM.lp_lm`.  The final unconditional `fd_ng_bound` will additionally list
  `SM.ng_finite_word` (through `ng_local_front_bound`), as the row's `\status` predicts ("consumes Literature input

YOUR TASK (for YOUR row): compare the printed statement clause by clause with the Lean fields, expanding every definition to primitives.
Row 78: is IsTypeII exactly the printed type-II move patterns (all its variants; index shifts) and are D, w, d, B the printed quantities on
the realizations; class reading FR-8. Row 83: is the domain exactly "every front F on the domain of ng:front-domain" (SmoothFront); is "the
same polynomial evaluated on its actual ordinary cusp rounding" rendered by quantifying over every S with F.IsRounding S (faithful?
stronger? weaker? — could a front have no rounding, making the clause vacuous? is that the printed presupposition?); is the inequality
w(F) − D(F) ≤ −deg_a P_{S(F)} − 1 exactly front_inequality with degAZ = deg_a (integer casts; degAZ 0 = 0 convention inert since P ≠ 0);
does the theorem's axiom set (lp_lm, ng_finite_word) match "consumes Literature input ng:finite-word". Row 93: is sl_Ng(F) := w(F) − c↓(F)
the accepted slNg (slNg_eq is the definitional half of the display — a field or redundant?); is "max deg_a P_{S(F)}(a,z)" = degAZ (P S); is
the rounding quantifier the same as row 83's; are the two closing sentences commentary (no field). Every printed clause must have a field
and every field a printed clause or a disclosed extra. Say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
