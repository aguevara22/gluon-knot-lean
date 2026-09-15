# ASSEMBLY_REPORT — Smoothing_Assembled.lean (2026-09-13, 23:24 UTC / 7:24pm ET)

**Result.** `work/drafts/smoothing/Smoothing_Assembled.lean`, 8213 lines, compiles with
`cd work/lean && lake env lean ../drafts/smoothing/Smoothing_Assembled.lean`: exit 0, **0 errors,
0 `sorry`** (the word does not occur in the file), 25.4 s wall (27.5 s on the /tmp copy).  Only
linter warnings remain (5 unused-binder names, 1 `Set.mem_setOf_eq` deprecation, 1 auto-included
section variable in `origParam_mem`) — all inherited from the units, none touched.

**Axioms** (checked on a /tmp copy of the file with `#print axioms` appended; the assembled file
itself contains no `#print`):
`SM.Link.exists_smoothing`, `SM.Link.exists_smoothing_record`, `SM.Link.exists_smoothing_record_visit`,
`SM.Link.exists_smoothing_counts` (and `SM.Link.smoothingRecordClause_smoothDiagram`) each depend on
exactly `[propext, Classical.choice, Quot.sound]`.

## Merge method and order
Each unit file is `Skeleton_FINAL.lean` with its `sorry` lines replaced and helpers inserted, so each
unit's diff against the skeleton is a set of hunks anchored at skeleton line numbers (`/tmp/parse_hunks.py`,
`/tmp/merge2.py`).  Hunks of all eight units were sorted by skeleton anchor and spliced into one file in
unit order U1, U2, U3, U4, U5, U6a, U6b, U6c.  **No two units touched overlapping skeleton ranges and no
two units inserted at the same anchor**, so no manual hunk arbitration was needed.  Nine `c`-hunks also
swallowed a statement line; each was inspected: they are `:= by` → `:=` (term proofs) or `:= by` → `where`
(`clean_toDiagram`) with the statement text unchanged.  Independently, every skeleton declaration header
(310 of them; theorem statements up to `:=`/`where`, structures, defs) was checked to appear verbatim in
the assembled file — the only absent one is `seg_arc_subset_ball` (below).  No fixed definition or
statement was changed.

Staged checks (all exit 0): U1+U2 → 68 sorry-warnings (= 146 − 50 − 28; the false lemma's `sorry` was still
present at that stage), 8 s; U1–U4 → 30, 17 s; U1–U5 → 24, 23 s; all eight → 0, 27.5 s.

Per unit (skeleton `sorry` lines replaced / declarations added / pure-insertion anchors after skeleton line):
U1 50 / 18 / — (all in place, incl. `seg_arc_subset_closedBall` before the false lemma) · U2 28 / 18 / 738 ·
U3 16 / 61 (`u3_*`) / 767 · U4 21 / 59 / 136, 514, 885, 1038, 1048 · U5 18 lines (mixedModel/selfModel
fields + card lemmas) / 96 / 1140, 1199, 1302 · U6a 7 / 36 / 169, 1393 · U6b 9 / 2 / 1498 ·
U6c 8 / 74 / 1587, 1601, 1655.  Declarations: 310 in the skeleton → 661 assembled.

## De-duplications / renames (4 name clashes, all in `SM.Link.Smoothing`)
1. `eval_eq_edgePt`: U2's generic helper (`{Γ : Shadow} (q : Γ.Pt) : Γ.eval q = Γ.edgePt … := rfl`) comes
   first and is kept; U4's different model-level lemma (`(u θ h1 h2) : Γ₀.eval ⟨u.1,(u.2,θ)⟩ = D.Γ.edgePt
   (M.orig u) …`) was **renamed `eval_eq_edgePt_orig`** together with its 16 references, all inside U4's hunks.
2. `kind_ne_arc_of_mem`: U4 (section `Model`) and U6b (section `RecordBridge`) proved the identical
   statement with identical explicit arguments `D x M hε`; U6b's copy (and its docstring) deleted, a
   one-line comment left in its place; U6b's single use resolves to U4's.
3. `orderEmbOfFin_othersM_ne`, 4. `orderEmbOfFin_othersS_ne`: U5 and U6c proved identical statements
   (explicit args `D x l`); U6c's copies deleted (comment left), U6c's ~20 uses resolve to U5's.  U6c's
   helpers `mem_othersM`/`mem_othersS` stay (harmless).
Cross-namespace short names: only `orig` (`StrandKind.orig` vs `SpliceModel.orig`, both skeleton, dot-notation)
and `origParam_liftParam` (`StrandKind.origParam_liftParam`, a U4 helper, vs the skeleton chain lemma
`Smoothing.origParam_liftParam` proved by U6b); no `open StrandKind` exists, references are qualified, and
the compile shows no ambiguity.  No `Shadow`/`Smoothing` clash was found.

## False-lemma rule (`seg_arc_subset_ball`, skeleton l. 502–506)
Deleted from the assembled file (U1's counterexample docstring + skeleton statement + `sorry`); a short
`/-! … -/` note records the removal at that position, and the docstring of `seg_arc_subset_closedBall` now
points to it instead of to the deleted lemma.  Uses found by grep (5, none in U2 — its arc lemmas did not use
it) and adapted, never weakening a statement:
* U3 `u3_tail_not_mem_arc`: `have h1 := StrandKind.seg_arc_subset_ball … hm; rw [Metric.mem_ball] at h1` →
  `seg_arc_subset_closedBall … hm; rw [Metric.mem_closedBall] at h1`; the existing strict bound
  `h3 : max … < r₁` still closes the `linarith` (r₁ ≤ dist ≤ max < r₁).
* U3 `u3_arc_disjoint_old`: same change (with `hq`).
* U4 `eval_arc_mem_ball`: `Metric.ball_subset_ball (arc_lt_discRadius D x ε hε).le (seg_arc_subset_ball …)` →
  `Metric.closedBall_subset_ball (arc_lt_discRadius D x ε hε) (seg_arc_subset_closedBall …)`.
* U4 `kind_ne_arc_of_mem`: inner `Metric.ball_subset_ball (…).le (seg_arc_subset_ball …)` →
  `Metric.closedBall_subset_ball (arc_lt_discRadius D x ε hε) (seg_arc_subset_closedBall …)`.
* U6b `kind_ne_arc_of_mem`: removed as an exact duplicate of U4's (item 2 above), so its use disappears.
`grep seg_arc_subset_ball` on the assembled file now hits only the two explanatory docstrings.

## Other edits
Module docstring only: title `Skeleton FINAL` → `Smoothing (assembled)`, and the "Status" paragraph
rewritten (was "every lemma of the chain is `sorry`"; now records the assembly and the false-lemma
replacement, plan pointer → PLAN_FINAL.md).  Nothing else outside the unit hunks was modified.

## Left unproved
Nothing.  Written under work/drafts/smoothing only (this file and Smoothing_Assembled.lean); nothing under
work/lean was touched; scripts and logs are in /tmp.
