# W2_U8R — the representation leaf `represent` (unit U8R): plan, infrastructure, status

2026-09-14, prover for unit U8R (PLAN_FINAL.md §4 "L-smooth", §5 "U8 smooth": the leaf `represent`, the second
sentence of ng:commutation, sm-3:1924-1925 "Every supplied finite front can be represented by a finite elementary
front word", printed proof 1938-1947).  File: `work/drafts/frontrows/W2_U8R.lean` = `Skeleton_W1.lean` + ONE
inserted block (`diff Skeleton_W1.lean W2_U8R.lean` = the single hunk `3685a3686,4836`; zero lines removed or
changed), the delimited section `/-! ### U8R infrastructure … -/ section U8RInfra … end U8RInfra` (lines
3700-4835, 1,151 lines, everything in `namespace SM.FrontRows.U8R`), placed immediately before the leaf's
docstring.  **The leaf `represent` is NOT closed**: its `sorry` is untouched, `grep -c sorry` 13 before, 13
after; no placeholder anywhere in the inserted block.  Compile: `cd work/lean && lake env lean
../drafts/frontrows/W2_U8R.lean` — **0 errors**, 13 `declaration uses sorry` warnings (the wave-1 leaves of U3, U5,
U6, U8), ~16 s.  `#print axioms` (on a temporary copy) of `U8R.represent_of_sweepStatement`,
`represent_of_slotRecordIso`, `markingRecordIso`, `frontRecord_writhe`, `frontRecord_crossingCount`,
`cycNext_eq_of`, `exists_xvel_sign_of_isLeftCusp`, `isRightCusp_nextCusp_of_isLeftCusp`,
`strictMonoOn_x_of_isLeftCusp`, `exists_arc_mem`, `fibre_finite`, `exists_two_cusps`, `totalFibre_finite`,
`snd_injOn_totalFibre`: `[propext, Classical.choice, Quot.sound]` only.  No import added, no statement touched, no other unit's sorry
touched.

## 0. Verdict in one paragraph

The leaf is a 7.5-11k-line project (PLAN_FINAL §5; the "rock" of the block).  This unit (i) fixed the route and
wrote the plan (§1-§3), (ii) PROVED the whole record-theoretic half of the reduction — every rounding `S(F)`
carries the named record of the front itself (`frontRecord F`, `markingRecordIso`), that record already has the
writhe and the crossing count of `F`, and U2's `realizeRecordIso` closes the diagram side — so that `represent`
now follows from ONE remaining statement, `U8R.SweepStatement F` (§2, a `def … : Prop`, no placeholder), by the
proved `U8R.represent_of_sweepStatement`; and (iii) PROVED the first analytic layer of the sweep (§4 F-H: the
x-velocity along a circle, its sign between cusps and its sign change at a cusp, the cusp arcs — consecutive cusps
alternate left/right, `x` is strictly monotone on each arc, the arcs cover the circle, every circle has ≥ 2
cusps, the fibre over any `x₀` is finite and, off the singular x-values, totally ordered by height).  What
remains (§3) is the sweep proper: the local models at a cusp
and at a crossing, the constancy of the cut between singular x-values, the word and its closedness, and the
first-return induction identifying the two records — estimated 5.5-8k lines; the largest single sub-lemma is the
cusp local model (Taylor, ~1-1.5k).  Rows 76 and 83 still wait for it (FR-8 fallback unchanged).

## 1. Plan of record for `represent` (what the leaf says, and the route)

**Statement (frozen).**  `∀ F : SmoothFront, ∃ W : OWord, F.downCount = (realize W).downCount ∧ F.writhe =
(realize W).writhe ∧ F.sCount = (realize W).sCount ∧ ∀ S, F.IsRounding S → Nonempty (RecordIso S.record
(realize W).diagram.record)` (R76-3 / FR-10: "represented by" = equal `D`, `w`, `s` and a named-record isomorphism
of every rounding with the realization's diagram).

**Route (three layers).**

1. *Record layer (PROVED here).*  A rounding `S(F)` is `⟨G, geom, marking : F.Marking S⟩` (FrontSmooth §8): the
   polygonal diagram carries the front's own named record (FR-1).  Define that record once and for all as a
   `Record` (`U8R.frontRecord F`: circles `Fin F.c`, occurrences `F.Occ`, successor = the cyclic successor of
   the parameters on each circle, pairing = the partner of the double point, over = smaller slope, sign = the
   over-first tangent-determinant sign) and prove `Marking F S → RecordIso S.record (frontRecord F)`
   (`U8R.markingRecordIso`; the successor clause is the accepted "successor preservation = cyclic-order
   preservation", LinkDiagramRecord §G, run through the generic characterisation `cycNext_eq_of`).  Then
   `RecordIso S.record (realize W).diagram.record = (markingRecordIso m).trans ι` for any `ι : RecordIso
   (frontRecord F) (realize W).diagram.record`, and `ι` in turn is `ι'.trans (U2.realizeRecordIso W hne).symm`
   for `ι' : RecordIso (frontRecord F) (U2.slotRecord W.closed IsσSlot _)`.  Moreover `frontRecord F` has
   `F.writhe` and `F.crossingPairs.card` (`frontRecord_writhe`, `frontRecord_crossingCount`: the over
   occurrences are the over-first pairs), so `w` and the crossing count of the leaf are CARRIED BY THE RECORD
   (`RecordIso.writhe_eq`, `Diagram.record_writhe`; `RecordIso.crossingCount_eq`, `Diagram.record_crossingCount`):
   only `D` and the cusp count remain to be read syntactically (`realize_downCount`, `realize_cuspCount`).
   Result: `U8R.represent_of_sweepStatement : SweepStatement F → (∃ W, …leaf conclusion…)`.

2. *Combinatorial layer (the sweep's reading; NOT done).*  Given the analytic data of layer 3, define the word
   `W`: the singularities of `F` (cusps and double points) sorted by `x`, ties broken by height bottom-to-top;
   each read as a letter at the position `1 + #(strands of the cut just before its x-value passing above it)`
   — a crossing as `σ m` (the branch with the smaller slope is the one above before and below after, hence the
   descending strand `σSlotA`, which is over in the realization: `U2.isDesc_σSlotA`), a left cusp as `l m d`
   with `d` = "the upper new arm travels rightward", a right cusp as `r m`.  Prove `W.Closed` (the cut after all
   events of one x-value is the cut of `F` just after it; `Letter.step` at each event), `D(F) =
   downCountFrom W []` (the down bit of a cusp letter is `IsDownCusp` of the cusp — needs the geometric
   reading of `cuspDisc`, layer 3(c)), `#cusps = W.cuspCount` (one cusp letter per cusp), and the record
   isomorphism `frontRecord F ≅ U2.slotRecord W IsσSlot`: `Φ p := (k_e, m)` for the over branch and `(k_e, m+1)`
   for the under branch of the crossing `e` of `p`; `pair` ↔ `σtwin` (same column), `isOver` ↔ `isDesc`, `sgn`
   ↔ `σsgn` (`coe_σsgn_eq_signBit`: positive iff the two bits agree iff the branches travel the same x-direction
   iff `crossSign = 1`, `crossSign_eq_one_iff_of_isOverUnder`), `comp` through the circle ↔ orbit bijection, and
   `succ` ↔ `firstReturn (nextPerm) IsσSlot` — the heart: follow the strand from an occurrence to the next
   occurrence along its circle and show `next` on slots follows it column by column (`U2.firstReturn_eq_of_path`,
   `U2.firstReturn_factor`: first returns to the "full cuts" `k_j` factor the first return to `σ` slots).

3. *Analytic layer (partly done).*  (a) [DONE, §4 F-H] the circle structure: `x'` vanishes exactly at the cusps
   (`isCusp_iff_xvel_eq_zero`), has constant sign on every cusp-free preconnected parameter set, changes sign
   at a cusp (left cusp: `−` before, `+` after; right cusp: the reverse), so the cusps of a circle, in cyclic
   order (`nextCusp`, from the generic `cycNext`), alternate left/right, `x` is strictly monotone on each closed
   arc `[c, arcEnd c]` (Rolle + `ContinuousOn.strictMonoOn_of_injOn_Icc'`), the arcs cover the circle
   (`exists_arc_mem`), every circle has ≥ 2 cusps, and the fibre over any `x₀` is finite (at most one parameter
   per arc, `fibre_finite`); the singular x-values form a `Finset` (`singX`).  (b) [TODO] the cut at a
   non-singular `x₀`: the fibre points are regular, pairwise distinct in `z` (no double point), so ordered by
   height, and carry the direction bit `0 < x'`; on an interval of non-singular `x` the fibres are
   order-isomorphic ("no crossing between singular values": the strands are continuous graphs — inverse of the
   strictly monotone `x` on each arc — whose differences never vanish, IVT).  (c) [TODO, the largest] the local
   models: at a cusp `t₀` the two arms `t < t₀ < t'` with equal `x` satisfy `sign (z(t') − z(t)) = sign
   (cuspDisc)` (the Taylor lemma FrontSmooth's docstring calls "an optional ~500-line Taylor lemma"; here it is
   not optional: it gives the direction bit `d` and the down bit of the cusp letter), and near `x(t₀)` the fibre
   changes by exactly the two arms of that cusp (`cusp_alone`, `exists_no_cusp_near`); at a double point the two
   branches swap their height order (`slope` comparison; transversality) and no other strand changes.

**Why this factoring.**  (i) The sweep unit never sees `Marking`, `cycBetween` or `visitCoord`: it produces a
`RecordIso` with U2's `slotRecord`, whose fields are first returns of `next`, exactly the vocabulary of U2's
tools (`firstReturn_eq_of_path`, `firstReturn_factor`, `nextPerm_pow_apply`, `next_cases`).  (ii) `w` and the
crossing count never have to be traced letter by letter: they are properties of the record.  (iii) Every
rounding is handled at once (`markingRecordIso`), and the leaf's `∀ S` is discharged by the record layer.

## 2. The remaining obligation, exactly (W2_U8R.lean L4235)

```
def U8R.SweepStatement (F : SmoothFront) : Prop :=
  ∃ W : OWord, W.letters ≠ [] ∧ F.downCount = W.downCountSyn ∧ F.cuspSet.card = W.letters.cuspCount ∧
    Nonempty (RecordIso (frontRecord F) (U2.slotRecord W.closed U2.IsσSlot (U2.allActive W.closed)))

theorem U8R.represent_of_sweepStatement (F) (h : SweepStatement F) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)   -- PROVED
```
Once a unit proves `theorem u8s_sweep (F : SmoothFront) : U8R.SweepStatement F`, the leaf is
`represent F := U8R.represent_of_sweepStatement F (u8s_sweep F)`.  Two weaker entry points are also proved,
for a sweep that prefers to deliver a `Marking` of the realization or the syntactic `w`:
`represent_of_marking` (hypotheses: `hne`, the three syntactic counts, `Nonempty (F.Marking (realize W).diagram)`),
`represent_of_frontRecordIso` (syntactic counts + `RecordIso (frontRecord F) (realize W).diagram.record`),
`represent_of_frontRecordIso_counts` (geometric `D` and cusp count + the record isomorphism).

## 3. What remains, decomposed, with estimates (Lean lines; calibration β2 ×1.5-2 for geometric units)

| # | sub-lemma (all TRUE, standard) | tools | est. |
|---|---|---|---|
| R1 | **cusp local model**: for a cusp `(i,t₀)` there is `δ` such that for `t₀ − δ < t < t₀ < t' < t₀ + δ` with `x(t) = x(t')`: `sign (z(t') − z(t)) = sign (F.cuspDisc (i,t₀))`; and `x` on `(t₀−δ, t₀+δ)` is a strict local min (left cusp) / max (right cusp) with the two arms bijective onto `(x₀, x₀+η)` resp. `(x₀−η, x₀)` | Taylor with remainder to order 3 for `x`, `z` (`taylor_mean_remainder_lagrange` on components, or `HasDerivAt` little-o three times), `strictMonoOn_x_of_isLeftCusp`, IVT for the matched arm | 1-1.5k |
| R2 | **crossing local model**: at a double point the two branches are graphs over an `x`-interval with `z_over − z_under` changing sign from `+` (before) to `−` (after) (`slope` order), and the fibre changes by nothing else (`no_triple`, finiteness) | inverse of the strictly monotone `x` on the arc (§4 G), `slope_ne_of_isDouble`, `det_pos_iff_of_slope_lt` | 0.6-0.9k |
| R3 | **cuts**: for `x₀ ∉ singX` the fibre (§4 H, `totalFibre`, ordered by `snd_injOn_totalFibre`) sorted by `z` gives the cut `c(x₀) : Cuts` (bits `0 < x'`, top to bottom); local constancy of the ordered fibre in `x₀` on intervals avoiding `singX` (strands = continuous graphs, IVT on differences) | `fibre_finite`, `regular_of_notMem_singX`, `xvel_pos_on_arc_of_isLeftCusp`, `Finset.sort` on `z` | 0.9-1.3k |
| R4 | **the word**: events sorted by `(x, z)` (bottom first at equal `x`), positions, `W.Closed` by induction over events (`Letter.step` at each event; the cut invariant "current cut = cut of `F` just after the processed events") | R1-R3, `Word.run_append`, `Letter.step_eq_some_iff`, β1's `act_*` | 0.8-1.2k |
| R5 | **counts**: `downCountFrom W [] = D(F)` (per cusp letter: `downBit = 1 ↔ IsDownCusp`, from R1's sign reading), `W.cuspCount = F.cuspSet.card` | `downCountFrom_nil_eq_sum`-style splitting (FrontRealizeCorrespondence), R1 | 0.4-0.6k |
| R6 | **the record isomorphism** `frontRecord F ≅ U2.slotRecord W IsσSlot`: `Φ`, `pair`/`isOver`/`sgn` (local, R2), `comp` (circles ↔ orbits through the strand-piece correspondence), `succ` ↔ `firstReturn` by induction along the traversal between consecutive occurrences (each cut passage = one `next` step per intervening column, `posR`/`posL`; each cusp = two `next` steps through the cusp vertex) | `cycNext_eq_of` is NOT needed here (frontRecord's `succ` is already a cyclic successor; the F-side successor of an occurrence is characterised by `cycNext_no_between` = "no occurrence of the circle strictly between"), U2 §A/§F first-return tools, `next_cases`, `U2.nextVisit_eq` pattern | 1.8-2.5k |
| | **total for `SweepStatement`** | | **5.5-8k** |

Risks.  R1 is analysis on a `C^∞` germ given only by `det(γ'', γ''') ≠ 0`, `x'' ≠ 0` — a real Taylor argument
with error control (the chain of the design record's "~500-line Taylor lemma" is optimistic; budget 1-1.5k).
R6's induction is the same shape as U2's `nextVisit_eq` (1085-1213) but over the analytic path; keep the
invariant "the F-strand at position `p` of the cut before column `k` is the slot `(k, p)`" as a `def` and prove
one step lemma per `next_cases` shape.  Ties at equal `x` are handled combinatorially (positions read on the cut
BEFORE the x-value, events processed bottom-to-top), so NO perturbation of `F` and none of the `deform_*` leaves
are needed — this differs from the printed proof ("separate them by small local x translations") only as a proof
device.  If R1 stalls, everything else can still be proved with R1 as the single named assumption.

## 4. What is proved (the inserted block, by sub-section; all in `SM.FrontRows.U8R`)

**A. Cyclic successor on a finite type with real keys (L3708-3899).**  For `[Fintype α] [DecidableEq α]
[LinearOrder ι]`, `comp : α → ι`, `key : α → ℝ` injective on fibres (`hkey`): `lexKey`, `keyOrder`
(`LinearOrder.lift'`), `fib`, `fibList` (the fibre sorted by key), `cycNext`/`cycPrev` (`List.next`/`prev`),
`cycSucc : Perm α`, `comp_cycNext`, `cycSucc_sameCycle` (one cycle per fibre), `cycNext_no_between` (via the
accepted `sorted_next_no_cyclic_between`), `cycNext_ne_self`, `cycNext_eq_self`, and **`cycNext_eq_of`**: an
element of the fibre, different from `a` whenever the fibre has another element, with nothing of the fibre
strictly `cycBetween` `a` and it, IS the cyclic successor (via the accepted `cycNext_unique_on`).  This is
`Diagram.nextVisit` (LinkDiagramRecord §B) made generic; reused twice below (occurrences, cusps).

**B. `frontRecord F : Record` (L3901-4014).**  `partner` (the other branch, `Classical.choose` of the accepted
`Marking.exists_partner`), `partner_spec/ne`, `eval_partner`, `isDouble_partner`, **`eq_partner_of`** (uniqueness
by `no_triple`), `partner_partner`, `partnerPerm`; `occComp`, `occKey`, `occKey_inj`; `frontOver` (`decide
(slope p < slope (partner p))`), `frontSgn` (the over-first `SignType.sign (det (vel over) (vel under))`),
`frontOver_partner` (`= !`), `frontSgn_partner`, `frontSgn_ne_zero` (transversality); the record with all seven
axioms discharged; rfl-lemmas `frontRecord_comp/succ/pair/isOver/sgn`.

**B'. Its counts (L4016-4088).**  `sum_over_eq_sum_crossingPairs` (the over occurrences `p ↦ (p, partner p)` are
exactly `F.crossingPairs`, a `Finset.sum_bij'`), **`frontRecord_writhe : (frontRecord F).writhe = F.writhe`**,
**`frontRecord_crossingCount : (frontRecord F).crossingCount = F.crossingPairs.card`**.

**C. `markingRecordIso (m : F.Marking S) : RecordIso S.record (frontRecord F)` (L4090-4167).**  `e := m.e.symm`,
`Φ := m.Φ.symm`; `comp_eq` from `Marking.compOf_eq_e`; `succ_eq` = `cycNext_eq_of` fed with `nextVisit_ne_self`
and `not_visitBetween_nextVisit` transported by `m.between_iff`; `pair_eq` from `partner_of_Φ_eq_twin` +
`eq_partner_of`; `bit_eq` from `m.over_iff`; `sgn_eq` from `m.sgn_eq` in both slope orders with
`crossSign_eq_sign`, `twin_fst`, `signType_intCast_injective`.  Corollary `IsRounding.recordIso_frontRecord`.

**D-E. The reductions (L4169-4247).**  `represent_of_frontRecordIso`, `represent_of_marking`,
`represent_of_frontRecordIso_counts`, `represent_of_slotRecordIso` (through `U2.realizeRecordIso`),
`SweepStatement`, `represent_of_sweepStatement` (§2).

**F. The x-velocity (L4249-4408).**  `xvel`, `continuous_xvel`, **`isCusp_iff_xvel_eq_zero`** (`no_vertical`),
`xvel_mul_pos_of_cuspFree` (IVT, `IsPreconnected.intermediate_value`) with `xvel_pos/neg_of_cuspFree`,
`hasDerivAt_xvel` (`x'` has derivative `x''`, `iteratedDeriv_succ`), `sign_near_simple_zero` (a real function with
a simple zero: `−` before, `+` after; from `hasDerivAt_iff_isLittleO`), **`exists_xvel_sign_of_isLeftCusp /
_isRightCusp`** (a left cusp is entered leftward and left rightward; a right cusp the reverse),
`exists_no_cusp_near` (cusps are isolated), `singX : Finset ℝ` with `mem_singX_of_isCusp/isDouble`,
`rep_pair_mem_doubleSet`, `regular_of_notMem_singX`.

**G. The cusp arcs (L4410-4684).**  `nextCusp` (= `cycNext` on `F.Cusp`), `nextCusp_fst`, `nextCusp_no_between`,
`eq_of_nextCusp_eq_self`; `arcEnd` (the next cusp's parameter, lifted by one period when the arc wraps),
`lt_arcEnd`, `arcEnd_le`, `sameParam_arcEnd`, `isCusp_arcEnd`, `isLeftCusp/isRightCusp_iff_of_sameParam`;
**`not_isCusp_of_mem_arc`** (no cusp strictly inside the arc; the wrap-around and the alone-on-its-circle cases),
`xvel_mul_pos_on_arc`, `exists_mem_arc_near(_end)`, **`xvel_pos_on_arc_of_isLeftCusp`**,
**`xvel_neg_on_arc_of_isRightCusp`**, **`isRightCusp_nextCusp_of_isLeftCusp`**, **`isLeftCusp_nextCusp_of_isRightCusp`**
(consecutive cusps alternate), `nextCusp_ne`, **`exists_two_cusps`** (every circle has two distinct cusps),
`hasDerivAt_x`, `injOn_x_arc` (Rolle, `exists_hasDerivAt_eq_zero`), **`strictMonoOn_x_of_isLeftCusp`**,
**`strictAntiOn_x_of_isRightCusp`** (`ContinuousOn.strictMonoOn_of_injOn_Icc'` + the sign at an interior point;
`strictMonoOn_of_deriv_pos` is not in the import closure and no import was added).

**H. Cover and fibres (L4686-4833).**  `circleCusps`, `circleCusps_nonempty`, **`exists_arc_mem`** (every
parameter lies, modulo the period, on the closed arc of the last cusp before it, or of the last cusp of the
circle when it wraps), `fibre F i x₀` (the parameters in `[0,1)` over `x₀`), **`fibre_finite`** (injection
`t ↦ (arc, ⌊lift − t⌋ ∈ {0,1})` into a finite set, by `injOn_x_arc`); `totalFibre F x₀` (all circles),
`mem_totalFibre_iff`, **`totalFibre_finite`**, **`snd_injOn_totalFibre`** (over `x₀ ∉ singX` the fibre points
have pairwise distinct heights — the total order by `z` that IS the cut of the sweep, R3),
`xvel_ne_zero_of_mem_totalFibre` (each carries a direction bit `0 < x'`).

## 5. Gotchas recorded for the sweep unit

1. `List.next` carries a `DecidableEq` instance; `sorted_next_no_cyclic_between` uses the `LinearOrder`'s.  Bridge
   with `Subsingleton.elim` on the instance and `rw` on the goal only (`cycNext_no_between`), never `rw … at` a
   hypothesis mentioning both.
2. `Record` needs `[DecidableEq M]`; for `F.Occ` (a subtype of `Fin c × ℝ`) it is found by instance resolution
   (Real's noncomputable `DecidableEq`), so `open Classical` is NOT needed and would risk instance mismatches
   with `SmoothFront.crossingPairs`.
3. `F.IsLeftCusp c.1` and `F.IsLeftCusp (c.1.1, c.1.2)` are defeq (structure eta); `exact` crosses them, `rw`
   does not.
4. Not in the import closure (do not use without an import decision): `strictMonoOn_of_deriv_pos`, `slope`,
   `hasDerivAt_iff_tendsto_slope`.  Available: `exists_deriv_eq_zero`, `exists_hasDerivAt_eq_zero`,
   `hasDerivAt_iff_isLittleO`, `ContinuousOn.strictMonoOn_of_injOn_Icc'`, `IsPreconnected.intermediate_value`.
5. The whole block compiles in ~10 s on top of the 6 s import; the full file in ~16 s (the machine was lightly
   loaded).  Scratch files with the seven imports of the skeleton are the fast loop.

## 6. Decisions / notes for the assembler

* Merge: the block is a single hunk between `PLFront.IsStandardCircles.downCount_eq_c_general` and the
  `represent` docstring; it uses only `SM.FrontRows.U2` (namespace, wave 1) and the accepted library; nothing
  else in the file changed.
* The leaf's proof, when the sweep lands, is one line: `represent F := U8R.represent_of_sweepStatement F
  (u8s_sweep F)`.  The `hw`/`hs` clauses of the frozen statement are already discharged by the record layer.
* FR-8 fallback (drop `represent`, disclose the class change on 76/83/93) remains Mark's decision; this unit's
  estimate for the remainder is 5.5-8k lines (§3), about half of PLAN_FINAL's 7.5-11k for the whole leaf.

## Appendix — declarations of the inserted block (file order; L = line in W2_U8R.lean)
A: lexKey L3717, lexKey_injective 3720, keyOrder 3728, keyOrder_lt_iff 3730, fib 3739, mem_fib 3741, fibList 3744,
fibList_nodup 3748, mem_fibList 3752, self_mem_fibList 3756, cycNext 3760, cycPrev 3764, cycNext_eq 3767,
cycPrev_eq 3771, comp_cycNext 3775, comp_cycPrev 3778, cycPrev_cycNext 3781, cycNext_cycPrev 3785, cycSucc 3790,
comp_cycSucc 3798, cycNext_getElem 3800, cycSucc_sameCycle_getElem 3807, cycSucc_sameCycle 3821,
cycNext_no_between 3828, cycNext_ne_self 3848, cycNext_eq_self 3862, cycNext_eq_of 3885.
B: partner 3908, partner_spec 3910, partner_ne 3913, eval_partner 3915, isDouble_partner 3917, eq_partner_of 3921,
partner_partner 3927, partnerPerm 3931, occComp 3940, occKey 3942, occKey_inj 3944, frontOver 3948, frontSgn 3951,
slope_ne_partner 3955, frontOver_partner 3958, frontSgn_partner 3967, frontSgn_ne_zero 3976, frontRecord 3988,
frontRecord_comp/succ/pair/isOver/sgn 4006-4011.
B': fst_mem_occSet_of_mem_crossingPairs 4022, partner_val_of_mem_crossingPairs 4026, frontOver_of_mem_crossingPairs
4036, over_pair_mem_crossingPairs 4042, sum_over_eq_sum_crossingPairs 4050, frontRecord_writhe 4066,
frontRecord_crossingCount 4077.
C: markingRecordIso 4097, IsRounding.recordIso_frontRecord 4164.
D-E: represent_of_frontRecordIso 4178, represent_of_marking 4190, represent_of_frontRecordIso_counts 4200,
represent_of_slotRecordIso 4223, SweepStatement 4235, represent_of_sweepStatement 4240.
F: xvel 4259, xvel_def 4261, continuous_xvel 4263, isCusp_iff_xvel_eq_zero 4266, xvel_ne_zero_of_not_isCusp 4275,
xvel_mul_pos_of_cuspFree 4279, xvel_pos_of_cuspFree 4293, xvel_neg_of_cuspFree 4298, hasDerivAt_xvel 4304,
sign_near_simple_zero 4317, exists_xvel_sign_of_isLeftCusp 4340, exists_xvel_sign_of_isRightCusp 4345,
exists_no_cusp_near 4357, singX 4374, mem_singX_of_isCusp 4377, rep_pair_mem_doubleSet 4384, mem_singX_of_isDouble
4395, regular_of_notMem_singX 4404.
G: cuspComp 4418, cuspKey 4420, cuspKey_inj 4422, nextCusp 4426, nextCusp_fst 4428, nextCusp_no_between 4431,
eq_of_nextCusp_eq_self 4435, arcEnd 4441, lt_arcEnd 4444, arcEnd_le 4452, sameParam_arcEnd 4460, isCusp_arcEnd 4467,
isLeftCusp_iff_of_sameParam 4470, isRightCusp_iff_of_sameParam 4474, not_isCusp_of_mem_arc 4479,
xvel_mul_pos_on_arc 4523, exists_mem_arc_near 4528, exists_mem_arc_near_end 4541, xvel_pos_on_arc_of_isLeftCusp
4554, xvel_neg_on_arc_of_isRightCusp 4562, isRightCusp_nextCusp_of_isLeftCusp 4570,
isLeftCusp_nextCusp_of_isRightCusp 4583, left_right_absurd 4595, nextCusp_ne 4599, exists_two_cusps 4610,
hasDerivAt_x 4615, injOn_x_arc 4619, strictMonoOn_x_of_isLeftCusp 4635, strictAntiOn_x_of_isRightCusp 4660.
H: circleCusps 4693, mem_circleCusps 4695, circleCusps_nonempty 4698, exists_arc_mem 4703, fibre 4744,
fibre_finite 4748, totalFibre 4799, mem_totalFibre_iff 4801, totalFibre_finite 4805, snd_injOn_totalFibre 4814,
xvel_ne_zero_of_mem_totalFibre 4823.
