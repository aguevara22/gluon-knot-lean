# NGBOUND_PLAN — row 93 fd:ng-bound (sm-3:3379-3390): statement, algebraic row theorem, porting recipe

Written 2026-09-14 14:48 UTC / 10:48am ET (front certificate rows lane, row 93 sub-lane).  Companion file:
`work/drafts/frontrows/NgBound_Statement.lean` (122 lines; `cd work/lean && lake env lean ../drafts/frontrows/NgBound_Statement.lean`:
**0 errors, 0 warnings, no sorry**; output = the two `#check` lines and
`'SM.fd_ng_bound_of' depends on axioms: [propext, Classical.choice, Quot.sound, lp_lm]`,
`'SM.degAZ_P_isMaxDegA' depends on axioms: [propext, Classical.choice, Quot.sound, lp_lm]` — `lp_lm` is the accepted
literature interface reached through `P` (FR-13), exactly as for `ng_circle`/`ng_cusp_skein`; `ng_finite_word` is absent
because row 83 is a hypothesis here).

## 1. What row 93 is

Lemma fd:ng-bound, `\status`: "Theorem ng:local-front-bound restated in Ng's self-linking form, so that the closure of
Theorem fd:contact contains it; consumes Literature input ng:finite-word through that theorem".  Its printed proof
(sm-3:3391-3399) is three sentences: lp:core gives `P_{S(F)} ≠ 0` and ng:smoothing-record makes `P_{S(F)}` well defined,
so `deg_a P_{S(F)}` is `max deg_a P_{S(F)}`; ng:front-inequality reads `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1`; this is the
display with `c↓(F) = D(F)`.  DEPENDENCIES.json: `fd:ng-bound → [lp:core, ng:front-domain, ng:local-front-bound,
ng:smoothing-record]`.  Row 93 is therefore pure algebra on top of row 83 (`NgLocalFrontBoundClauses`, being proved by the
U8R/delta lane — not touched here).

## 2. Clause map (tex lines → Lean)

| tex lines | printed text | Lean (all in `namespace SM`, `NgBound_Statement.lean`) |
|---|---|---|
| 3379 | `\begin{lemma}[the individual-front bound in self-linking form]\label{fd:ng-bound}` | `structure NgBoundClauses : Prop`; row theorem `fd_ng_bound_of (h83 : NgLocalFrontBoundClauses) : NgBoundClauses` |
| 3380 | "Let F be a front on the domain of Definition ng:front-domain" | binder `F : SmoothFront` (the accepted class of ng:front-domain, FrontSmooth.lean §3, `front_domain_definition`) |
| 3380-3381 | "with c↓(F) = D(F) its number of downward cusps" | `F.downCount : ℕ` (FrontSmooth.lean:724, "Write D(F) for the number of downward cusps"); `c↓` is the printed alias, no separate Lean name (FR-NB-2) |
| 3381-3382 | "and let S(F) be an actual clean ordinary cusp smoothing of F as in that definition" | binder `S : Diagram` with hypothesis `F.IsRounding S` (FrontSmooth.lean:1478-1480, `IsRounding S := Nonempty (F.Rounding S)`; FR-1) — universally quantified, as row 83 |
| 3383-3386 | display fd:ng-input, `sl_Ng(F) := w(F) − c↓(F)` | field `slNg_eq : ∀ F : SmoothFront, F.slNg = F.writhe - (F.downCount : ℤ)` — the accepted `SmoothFront.slNg` (FrontSmooth.lean:731-732), proof `slNg_def` (`rfl`) |
| 3383-3386 | display fd:ng-input, `… ≤ −max deg_a P_{S(F)}(a,z) − 1` | field `ng_input : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S → F.slNg ≤ -degAZ (P S) - 1`; `max deg_a P_{S(F)}` = `degAZ (P S)` certified by `degAZ_P_isMaxDegA` (FR-NB-1) |
| 3387-3388 | "This is not an application of an ambient-invariant hypothesis to the local diagram construction, nor a maximum over front representatives." | commentary on the form of the statement; no field.  The Lean bundle is visibly of that form: the bound is per `F` and per rounding `S`, with no ambient hypothesis and no `sup` |
| 3389 | `\status{…}` | provenance only |
| 3390 | `\end{lemma}` | — |
| 3391-3399 (proof) | lp:core ⇒ `P ≠ 0`; ng:smoothing-record; ng:front-inequality "is the display with c↓(F) = D(F)" | `degAZ_P_isMaxDegA` (from accepted `P_ne_zero`, PolynomialBlock.lean:793, and `degAZ_spec`, LinkLaurentRing.lean:455); `fd_ng_bound_of`: `rw [SmoothFront.slNg_def]; exact h83.front_inequality F S hS` |

Statement of the bundle, verbatim:

```lean
structure NgBoundClauses : Prop where
  slNg_eq : ∀ F : SmoothFront, F.slNg = F.writhe - (F.downCount : ℤ)
  ng_input : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.slNg ≤ -degAZ (P S) - 1
```

Also in the file (glue, all proved): `SmoothFront.dOf_eq_degAZ` (`rfl`), `NgBoundClauses.defect_nonneg`
(`ng_input` ⇒ `0 ≤ F.defect S`) and `NgBoundClauses.of_defect_nonneg` (the converse) — the cross-check that the field
is display ng:defect's `B ≥ 0 ⇔ w − D ≤ −d − 1` and nothing else (`defect_nonneg_iff_slNg`, FrontSmooth.lean:1528).

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
  ng:finite-word through that theorem").  No new axiom.

## 4. Non-algebraic leaves

**None.**  `fd_ng_bound_of` uses only `SmoothFront.slNg_def` (`rfl`) and the hypothesis `h83`.  `degAZ_P_isMaxDegA` uses
the accepted `P_ne_zero` (lp:core, PolynomialBlock.lean:793) and `degAZ_spec` (LinkLaurentRing.lean:455).  The whole
of row 93 waits on exactly one thing: the delta module's `SM.ng_local_front_bound : NgLocalFrontBoundClauses`.

## 5. Porting recipe (once row 83's delta module exists)

Names are final: `SM.NgLocalFrontBoundClauses` (row 83 statement), `SM.NgBoundClauses` (row 93 bundle),
`SM.fd_ng_bound_of` (conditional), `SM.fd_ng_bound : NgBoundClauses` (the unconditional row theorem; not a
checker-fixed name — row 93 is not in `axiom-policy.json` `targets`, so the mapping is free but should use this name).
Clash scan (2026-09-14): `NgBoundClauses`, `fd_ng_bound`, `fd_ng_bound_of`, `degAZ_P_isMaxDegA`, `dOf_eq_degAZ` occur
nowhere under `work/lean/SM`, `lean/`, or the drafts other than this file; `SmoothFront.slNg` is the accepted one and is
reused.

**The structure `SM.NgLocalFrontBoundClauses` may exist in exactly one module.**  W2_CLEAN_REPORT.md §3 item 6 tells
the delta module to re-declare it; this file declares it too.  Two Lean modules each declaring `SM.NgLocalFrontBoundClauses`
cannot both be imported (duplicate declaration), so choose ONE of:

**Recipe A (recommended: statement module first).**
1. Port `NgBound_Statement.lean` as `work/lean/SM/NgBoundStatement.lean` (`import SM.FrontRowsW2`), body verbatim EXCEPT
   the trailing `section DraftOnly … end DraftOnly` (the conditional alias `fd_ng_bound (h83)`), which is dropped;
   optionally drop the four `#check`/`#print` lines and the two `example`s.  Add `SM.NgBoundStatement` to the library's
   module list (the usual porting header line at L1).
2. The delta module (`import SM.FrontRowsW2`) adds `import SM.NgBoundStatement` and DELETES item 6 of its re-declaration
   list (the `structure NgLocalFrontBoundClauses`, Skeleton_W2 L119-122); everything else in W2_CLEAN_REPORT.md §3 stands.
   Its `theorem ng_local_front_bound : NgLocalFrontBoundClauses` (Skeleton_W2 L14878-14889) then refers to the
   statement module's structure.
3. At the end of the delta module (after `end FrontRows`, still in `namespace SM`), or in a 10-line module
   `SM.NgBound` importing the delta module, add the unconditional row theorem:
   ```lean
   /-- **fd:ng-bound** (row 93, sm-3:3379-3390): ng:local-front-bound in Ng's self-linking form. -/
   theorem fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound
   ```
   Expected `#print axioms SM.fd_ng_bound`: `[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.ng_finite_word]`
   (row 83's axioms; nothing new).
4. Map row 93 (`fd:ng-bound`) → `SM.fd_ng_bound` in the claims/mapping table; the bundle `SM.NgBoundClauses` is the
   statement the reviewers read (fields `slNg_eq`, `ng_input`), with FR-1, FR-8, FR-10, FR-16, FR-NB-1..7 cited.

**Recipe B (delta module lands first, re-declaring item 6 as W2_CLEAN_REPORT says).**
1. Port `NgBound_Statement.lean` as `work/lean/SM/NgBound.lean` with `import SM.<DeltaModule>` instead of
   `import SM.FrontRowsW2`, and with the `structure NgLocalFrontBoundClauses` block (three lines + section header) REMOVED
   (it now comes from the delta module) and the `DraftOnly` section REPLACED by
   `theorem fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound`.
2. Recompile with `lake env lean` before `lake build`; the only declarations changed are the removed structure and the
   final theorem; `fd_ng_bound_of` and `NgBoundClauses` are untouched.
3. Same mapping and axiom expectation as A.4 / A.3.

Either way the row theorem is unconditional, the bundle is the one in §2, and no proof beyond `fd_ng_bound_of` is
written for row 93.  Do not compile the draft after the delta module is ported under Recipe A's step 2 without first
removing the structure from one side — the duplicate would be the only error.

## 6. Files

- `work/drafts/frontrows/NgBound_Statement.lean` — the module (compiles, 0 errors).
- `work/drafts/frontrows/NGBOUND_PLAN.md` — this plan.
- Inputs read, not modified: `work/lean/SM/FrontSmooth.lean` (`slNg` 731-737, `dOf`/`defect` 1503-1506,
  `defect_nonneg_iff(_slNg)` 1522-1529, `IsRounding` 1478-1480), `work/lean/SM/LinkLaurentRing.lean` (`degA` 392,
  `degAZ` 446, `degA_eq_degAZ` 449, `degAZ_spec` 455, `coeffAt` 286), `work/lean/SM/PolynomialBlock.lean`
  (`P_ne_zero` 793), `work/lean/SM/LocalPolynomial.lean` (`P` 22), `work/lean/SM/FrontRowsW2.lean` (header 1-50,
  statements 55-82), `work/drafts/frontrows/Skeleton_W2.lean` (119-121, 14842-14890), `W2_CLEAN_REPORT.md` §3,
  `PLAN_FINAL.md` §6-7, `work/AUTHOR_NOTES.md` 3324-3330, 4168-4195, `reference/SM/sm-3-statesum.tex` 1825-1899,
  2305-2313, 3379-3399, `blueprint/DEPENDENCIES.json` (fd:ng-bound).
