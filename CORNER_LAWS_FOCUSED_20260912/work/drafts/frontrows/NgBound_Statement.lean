import SM.FrontRowsW2

/-! # fd:ng-bound (row 93) — statement module and the algebraic row theorem

Draft 2026-09-14 (front certificate rows lane, row 93 sub-lane; plan NGBOUND_PLAN.md next to this file).

Lemma fd:ng-bound (sm-3:3379-3390) is Theorem ng:local-front-bound (row 83, sm-3:2305-2313) "restated in
Ng's self-linking form".  Its only mathematical input is row 83 (DEPENDENCIES.json: lp:core, ng:front-domain,
ng:local-front-bound, ng:smoothing-record), so this module contains

* `SM.NgLocalFrontBoundClauses` — the row-83 statement, RE-DECLARED byte-identically from
  `work/drafts/frontrows/Skeleton_W2.lean` L119-121 (W2_CLEAN_REPORT.md §3 item 6; it is NOT in the ported
  `SM.FrontRowsW2`).  **It lives here only**: the delta module that proves row 83 must `import` this file (as the
  statement module) instead of re-declaring item 6, otherwise the two copies of `SM.NgLocalFrontBoundClauses` clash.
* the accepted `SM.SmoothFront.slNg F : ℤ := F.writhe - F.downCount` (FrontSmooth.lean:731-732, docstring
  "the quantity bounded in ng:local-front-bound / fd:ng-bound (`sl_Ng`)"), REUSED, not re-declared (a second
  `SM.SmoothFront.slNg` would clash with the accepted vocabulary); `slNg_def` is `rfl`.
* `SM.degAZ_P_isMaxDegA` — the printed proof's first sentence: "Theorem lp:core gives P_{S(F)} ≠ 0, ... so
  deg_a P_{S(F)} ... is the largest a exponent with nonzero coefficient, max deg_a P_{S(F)}".  Proved from the
  accepted `P_ne_zero` (lp:core) and `degAZ_spec`; it certifies that `degAZ (P S)` is the printed `max deg_a`
  (the `0`-at-`0` convention of `degAZ` is never exercised on a diagram polynomial).
* `SM.NgBoundClauses` — the row bundle, one field per assertion of the printed display fd:ng-input.
* `SM.fd_ng_bound_of (h83 : NgLocalFrontBoundClauses) : NgBoundClauses` — the row theorem, conditional on row 83;
  pure algebra (`slNg` unfolds to `w − D`; the inequality is row 83's clause verbatim).
* the draft-only conditional alias `SM.fd_ng_bound (h83)` (section `DraftOnly`, dropped at porting: the name is
  reserved for the unconditional row theorem `SM.fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound`
  in the delta module, once row 83 is proved there).

Fidelity readings FR-NB-1..FR-NB-7 in NGBOUND_PLAN.md; they cite FR-1 (polygonal reading of `S(F)`), FR-8/FR-10
(row 83 on the smooth class via `represent`), FR-16 (`d = degAZ (P S)`).  Checked with `cd work/lean && lake env lean`. -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

/-! ## Row 83's statement (Skeleton_W2.lean L119-121, byte-identical; the delta module imports this) -/

structure NgLocalFrontBoundClauses : Prop where
  front_inequality : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

/-! ## "max deg_a P_{S(F)}" is `degAZ (P S)` (the printed proof's first sentence, sm-3:3392-3395) -/

/-- "Theorem lp:core gives `P_{S(F)} ≠ 0`, ... so `deg_a P_{S(F)}` of display ng:defect is the largest `a`
exponent with nonzero coefficient, `max deg_a P_{S(F)}`" (sm-3:3392-3395): for every diagram `S` the integer
`degAZ (P S)` is attained by a monomial of `P S` with nonzero coefficient and bounds every `a`-exponent of the
support.  Uses the accepted `P_ne_zero` (lp:core) and `degAZ_spec` (def:adeg); no convention at `0` is used. -/
theorem degAZ_P_isMaxDegA (S : Diagram) :
    (∃ k, coeffAt (degAZ (P S)) k (P S) ≠ 0) ∧ ∀ d k, coeffAt d k (P S) ≠ 0 → d ≤ degAZ (P S) :=
  degAZ_spec (P_ne_zero S)

/-- On a rounding, `d(F)` of display ng:defect is the `max deg_a` of the printed display fd:ng-input
(`dOf` is `degAZ (P S)` by definition). -/
theorem SmoothFront.dOf_eq_degAZ (F : SmoothFront) (S : Diagram) : F.dOf S = degAZ (P S) := rfl

/-! ## Row 93: fd:ng-bound (sm-3:3379-3390), one field per assertion of display fd:ng-input -/

/-- **fd:ng-bound** (sm-3:3379-3390), "the individual-front bound in self-linking form".  "Let `F` be a front on
the domain of Definition ng:front-domain" = `F : SmoothFront` (the accepted class of that definition);
"with `c↓(F) = D(F)` its number of downward cusps" = `F.downCount`; "and let `S(F)` be an actual clean ordinary
cusp smoothing of `F` as in that definition" = any `S : Diagram` with `F.IsRounding S` (the accepted rounding of
ng:front-domain, FR-1), quantified exactly as row 83 quantifies its rounding.  Display fd:ng-input
`sl_Ng(F) := w(F) − c↓(F) ≤ −max deg_a P_{S(F)}(a,z) − 1` gives the two fields; `max deg_a P_{S(F)}` is
`degAZ (P S)` by `degAZ_P_isMaxDegA`.  The two closing sentences ("This is not an application of an
ambient-invariant hypothesis ..., nor a maximum over front representatives") are commentary on the form of the
statement — the bound is for each `F` and each of its roundings — and have no field. -/
structure NgBoundClauses : Prop where
  /-- the definitional half of display fd:ng-input, "`sl_Ng(F) := w(F) − c↓(F)`" (`rfl` on the accepted `slNg`) -/
  slNg_eq : ∀ F : SmoothFront, F.slNg = F.writhe - (F.downCount : ℤ)
  /-- the inequality of display fd:ng-input, "`sl_Ng(F) ≤ −max deg_a P_{S(F)}(a,z) − 1`", for every front `F` of
  the class and every clean ordinary cusp smoothing `S(F)` -/
  ng_input : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.slNg ≤ -degAZ (P S) - 1

/-- **fd:ng-bound** from row 83 (the printed proof, sm-3:3391-3399: "Inequality ng:front-inequality of Theorem
ng:local-front-bound reads `w(F) − D(F) ≤ −deg_a P_{S(F)} − 1`, which is the display with `c↓(F) = D(F)`").
Pure algebra: `slNg` unfolds to `w − D` and the clause is row 83's `front_inequality` verbatim.  The port makes this
unconditional: `theorem fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound`. -/
theorem fd_ng_bound_of (h83 : NgLocalFrontBoundClauses) : NgBoundClauses where
  slNg_eq := fun F => F.slNg_def
  ng_input := fun F S hS => by
    rw [SmoothFront.slNg_def]
    exact h83.front_inequality F S hS

/-- The inequality clause through the accepted defect: `B(F) ≥ 0` on the rounding is the same statement
(`defect_nonneg_iff_slNg`, FrontSmooth.lean:1528) — a cross-check that the field is display ng:defect's
`B ≥ 0 ⇔ w − D ≤ −d − 1` and nothing else. -/
theorem NgBoundClauses.defect_nonneg (h : NgBoundClauses) (F : SmoothFront) (S : Diagram)
    (hS : F.IsRounding S) : 0 ≤ F.defect S :=
  (F.defect_nonneg_iff_slNg S).2 (h.ng_input F S hS)

/-- Conversely the inequality field follows from `B ≥ 0` on every rounding (the shape in which the delta module
proves row 83). -/
theorem NgBoundClauses.of_defect_nonneg
    (h : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S → 0 ≤ F.defect S) : NgBoundClauses where
  slNg_eq := fun F => F.slNg_def
  ng_input := fun F S hS => (F.defect_nonneg_iff_slNg S).1 (h F S hS)

/-! ## Sanity checks (statement typechecks; the row theorem depends on nothing beyond the accepted layer) -/

example (h83 : NgLocalFrontBoundClauses) : NgBoundClauses := fd_ng_bound_of h83

example (h83 : NgLocalFrontBoundClauses) (F : SmoothFront) (S : Diagram) (hS : F.IsRounding S) :
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1 :=
  (fd_ng_bound_of h83).ng_input F S hS

#check @NgBoundClauses
#check @fd_ng_bound_of
#print axioms fd_ng_bound_of
#print axioms degAZ_P_isMaxDegA

/-! ## Draft-only: the requested conditional name.  DROPPED AT PORTING — `SM.fd_ng_bound` is reserved for the
unconditional row theorem in the delta module (`fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound`). -/

section DraftOnly

theorem fd_ng_bound (h83 : NgLocalFrontBoundClauses) : NgBoundClauses := fd_ng_bound_of h83

end DraftOnly

end SM
