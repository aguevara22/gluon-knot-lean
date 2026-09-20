# W1_M4_REPORT — unit U-M4 of the moves toolkit (the arcs, the covers, the cleanness, the R-II site data)

U-M4 (subagent), 2026-09-15 ≈ 20:15 UTC / 4:15pm ET.  File: `work/drafts/moves/W1_M4.lean` (= `Skeleton_W1.lean` +
60 helpers `um4_…` + the eleven U-M4 bodies).  Inputs: W1_SKELETON_REPORT.md §1–§5, PLAN_FINAL.md §5–§6, the §1c API
of the skeleton, SM/Smoothing.lean §5 (`arc_mem_iff_of_same_edge`, `arcS/arcT`, `arcCover_D`, `clean_D`) and §6d
(`inner_arcST₀_iff`, `frontier_injOn_toDiagram`, `arcCover_toDiagram`), SM/LinkMoves.lean (`IsArc`, `ArcCover`,
`Clean`, `Separates`, `OverOn`, `Arc.inner_mk_iff`), SM/Traversal*.lean (`traversalBetween`, `traversalBetween_shift`).

## 0. Result

| check | result |
|---|---|
| compile `cd work/lean && lake env lean ../drafts/moves/W1_M4.lean` | exit 0, **0 errors**, ≈ 12 s; the only non-`sorry` warning is the pre-existing cosmetic `<;>` linter note at line 565 (skeleton) |
| `declaration uses sorry` | **22** (was 33): the 22 sub-leaves / frozen leaves of the OTHER units, untouched |
| `grep -c sorry W1_M4.lean` | **23** (was 34) = 22 bodies + the frozen header comment (line 17) |
| `python3 check_W1_identity.py Statements_FINAL.lean W1_M4.lean` | prefix identical; all 37 declarations byte-identical; suffix identical except the body of `exists_rii_deletion` (as in the skeleton) — **PASS** |
| every skeleton declaration keeps its statement | 267 / 267 declarations of `Skeleton_W1.lean` have byte-identical statements in `W1_M4.lean`; the 60 new declarations are all `um4_`-prefixed |
| **all eleven U-M4 sub-leaves PROVED** | `m4_arcIn_ne_arcS` (1601), `m4_arcIn'_ne_arcS'` (1608), `m4_arcCover` (1624), `m4_arcCover'` (1920), `m4_clean` (2082), `m4_clean'` (2142), `m4_inner_iff'` (2182), `m4_no_inner` (2212), `m4_sep_y` (2278), `m4_sep_z` (2291), `m4_same_over` (2305) — line numbers in `W1_M4.lean` |
| general `j` | the `mem_iff` classifications are proved for **general `j ≥ 1`** (no PLAN §6 R1 fallback to `j ∈ {1, 2}` was needed) |
| `#print axioms` (scratch copy with `#print axioms` appended) | 9 sub-leaves: `[propext, Classical.choice, Quot.sound]` (standard).  `m4_clean'` and `m4_no_inner`: `[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx` is INHERITED from the black boxes, not from U-M4 (see §3) |

Nothing under `work/lean` was written.  Scratch files (insertion scripts, logs, the `#print axioms` copy) live in the
session scratchpad only.

## 1. What was proved, and how (per sub-leaf)

* **`m4_arcIn_ne_arcS`** — the start points differ in strand: `(arcS).Mem (arcIn).startPt` would put `e_in = s`
  (`um4_arcS_mem_iff`, `s_ne_eIn`).
* **`m4_arcIn'_ne_arcS'`** — same on the reduced side: the start strand of `arcIn'` has kind `cutIn`
  (`kind_mk_i 0`), that of `arcS'` has kind `old s` (`kind_sStrand`).
* **`m4_arcCover`** (`D ∩ U` = the two arcs).  The traversal-order core is
  `um4_between_zero_nat` / `um4_between_shift`: with `1 ≤ j < n`,
  `traversalBetween (a, θ₁) r (a + j, θ₂) ↔ (r.1 − a).val ≤ j ∧ ((r.1 − a).val = 0 → θ₁ < r.2) ∧ ((r.1 − a).val = j → r.2 < θ₂)`
  (via `traversalBetween_shift` to the cut at `0`, then plain real arithmetic on `traversalKey`).  From it
  `um4_arcIn_inner_iff` / `um4_arcIn_mem_iff` (points `⟨i, (a + m, θ)⟩`, `m < k`) and `um4_arcIn_mem_strand`.
  `um4_pt_i` writes every point of component `i` as `⟨i, (a + m, θ)⟩` (`m := (b − a).val`).  `IsArc arcIn`: ends by
  `eval_arcIn_start/stop` + `Cut.p_frontier/q_frontier`; inner points by `Cut.in_int_iff` (`m = 0`),
  `Cut.out_int_iff` (`m = j`), and `um4_run_edge_mem_interior` (`1 ≤ m < j`: both ends in `interior U` by
  `Cut.run_mem_interior`, `Convex.interior.add_smul_sub_mem`).  `IsArc arcS`: `arc_inner_iff_of_same_edge` +
  `Cut.s_int_iff`.  `mem_iff` (→): the strand of `p` is foreign (`Cut.clear` + `eval_mem_seg`), or `s`
  (`Cut.s_iff`), or `strand m` (`um4_eval_local_mem_iff`: `in_iff` / convexity / `out_iff`); (←):
  `isArc_eval_mem_of_mem`.  `disjoint`: `s ≠ strand m` for `m ≤ j` (`um4_s_ne_strand`: `s_ne_eIn`, `run_free` with
  `y`, `s_ne_eOut`).
* **`m4_arcCover'`** (`D' ∩ U` = `[p → M' → q]` and `s ∩ U`).  Points by `strand_cases` and the kind laws:
  `um4_eval_cutIn` (`edgePt e_in (θ t_M)`), `um4_eval_mid` (`M' + θ (q − M')`), `um4_eval_cutOut`
  (`edgePt e_out (t_q + θ(1 − t_q))`), `um4_eval_old` (`edgePt e θ`).  `um4_arcIn'_inner_iff` /
  `um4_arcIn'_mem_iff` via `um4_between_zero_nat` with `j = 2` on the reduced modulus (`um4_k'_eq`,
  `ZMod.val_natCast_of_lt`); `um4_mk_i_eq_iff` replaces `Strand_mk_eq_mk_iff` (pitfall §4.2: `Fin C.shadow.c` vs
  `Fin D.Γ.c`).  `um4_mid_mem_interior`: `M' + θ(q − M') = q + (1 − θ)(M' − q)` (`module`) and
  `Convex.add_smul_sub_mem_interior` (`q ∈ U`, `M' ∈ interior U`).  Old strands: `um4_old_cases` (an occurring
  old strand is `s` or foreign, from `kind_occurs`), `um4_eq_sStrand_iff` (`u = sStrand ↔ kind u = old s`),
  `um4_mem_iff_old` (`∈ U ↔ arcS'.Mem`), `um4_not_arcIn'_mem_old`.  The classification `um4_mem_U_iff'` is by
  label `0 / 1 / 2 / ≥ 3` on component `i` and `old` elsewhere; label `2` in `U` forces `θ = 0` (the vertex `q`).
* **`m4_clean`**.  `um4_frontier_pt`: a frontier point of the trace is an arc end (`mem_iff` + `IsArc.inner_interior`
  + `frontier ∩ interior = ∅`).  The four ends are four DISTINCT plane points: `um4_p_ne_q` via
  `um4_seg_eIn_inter_eOut` (`seg e_in ∩ seg e_out ⊆ {M₁}`: `j = 1` by `Generic.seg_inter_succ`; `j ≥ 2` by
  non-adjacency + `no_io`, a common point would make `{e_in, e_out}` a crossing) and `t_p < 1`;
  `um4_p_ne_sIn/sOut` via `Generic.seg_inter_seg_eq y` (`t_p = t_y` impossible); `um4_q_ne_sIn/sOut` via `z`
  (`t_q = t_z` impossible); `um4_sIn_ne_sOut` by `edgePt_injective`.  `um4_eval_end_injOn` (16 cases).  `exits`:
  `M₀ ∉ U` on component `i`, and `um4_tail_not_mem_of_ne` (the tail of a strand of another component is `tail s ∉ U`
  or foreign) elsewhere.
* **`m4_clean'`**.  Same shape with `m4_arcCover'` and `eval_arcIn'_start/stop`, `eval_arcS'_start/stop` (the
  same four plane points); `exits` via `tail_mk_i` + `reducedTuple_zero` (`M₀`) and `tail_mk_of_ne`.
* **`m4_inner_iff'`**.  `um4_crossing_strand_mem_U`: a strand of a crossing with double point in `U` is `s`, `e_in`
  or `e_out` (foreign excluded by `Cut.clear`, run strands by `run_free`).  Nine cases on the two strands:
  `{s, e_in} → y`, `{s, e_out} → z` (`um4_crossing_eq`, `Finset.pair_comm`), `{e_in, e_out}` excluded by `no_io`.
  (←): `y, z ∈ K ⊆ interior U` (`in_iff`/`out_iff` at `t_y`/`t_z`, `Cut.K_sub`).
* **`m4_no_inner`**: `m3_crossingPoint_origCrossing` + `m4_inner_iff'` + `m3_origCrossing_ne_y/z` (as prescribed).
* **`m4_sep_y`, `m4_sep_z`, `m4_same_over`**.  `um4_visitPt_eq` (the traversal point of an occurrence from an
  `edgePt` equation, via `um4_crossingParam_eq`), `um4_arcS_mem_visit_s` (an occurrence of `y`/`z` on `s` lies on
  `arcS`: `t_in < t_sy, t_sz < t_out`), `um4_arcIn_mem_visit_eIn` (`t_p < t_y`), `um4_arcIn_mem_visit_eOut`
  (`t_z < t_q`), `um4_overStrand_y/z` (the over strand is `e_in`/`e_out` or `s`), then the case split on the over
  strand (`eq_under_of_mem_of_ne` for the under strand); `m4_same_over` is `B.same_over` read on the arcs.

## 2. Helpers added (60, all `um4_`, all in `section Construction`, each immediately before the first sub-leaf using it)

Before `m4_arcIn_ne_arcS`: `um4_between_zero_nat`, `um4_between_shift`, `um4_pt_i`, `um4_of_not_foreign`,
`um4_s_ne_strand`, `um4_strand_eq_eIn_iff`, `um4_strand_eq_eOut_iff`, `um4_dir_strand`, `um4_clampIco_eq_iff`,
`um4_tin_mem`, `um4_tout_mem`, `um4_arcIn_inner_iff`, `um4_arcIn_mem_iff`, `um4_arcIn_mem_strand`,
`um4_arcS_mem_iff`, `um4_arcS_inner_iff`, `um4_arcS'_mem_iff`, `um4_arcS'_inner_iff`,
`um4_run_edge_mem_interior`, `um4_eval_local_mem_iff`, `um4_isArc_arcIn`, `um4_isArc_arcS`.
Before `m4_arcCover'`: `um4_k'_eq`, `um4_pt_i'`, `um4_eval_old`, `um4_eval_cutIn`, `um4_eval_mid`, `um4_eval_cutOut`,
`um4_mid_mem_interior`, `um4_old_cases`, `um4_eq_sStrand_iff`, `um4_arcIn'_inner_iff`, `um4_mk_i_eq_iff`,
`um4_arcIn'_mem_iff`, `um4_isArc_arcIn'`, `um4_isArc_arcS'`, `um4_mem_iff_old`, `um4_not_arcIn'_mem_old`,
`um4_mem_U_iff'`.
Before `m4_clean`: `um4_seg_eIn_inter_eOut`, `um4_p_ne_q`, `um4_p_ne_sIn`, `um4_p_ne_sOut`, `um4_q_ne_sIn`,
`um4_q_ne_sOut`, `um4_sIn_ne_sOut`, `um4_frontier_pt`, `um4_eval_end_injOn`, `um4_tail_not_mem_of_ne`.
Before `m4_clean'`: `um4_frontier_pt'`, `um4_eval_end_injOn'`.
Before `m4_inner_iff'`: `um4_crossing_strand_mem_U`, `um4_crossing_eq`.
Before `m4_sep_y`: `um4_crossingParam_eq`, `um4_visitPt_eq`, `um4_arcS_mem_visit_s`, `um4_arcIn_mem_visit_eIn`,
`um4_arcIn_mem_visit_eOut`, `um4_overStrand_y`, `um4_overStrand_z`.

Reusable beyond U-M4 (U-M5/U-M6 may want them): `um4_between_zero_nat`/`um4_between_shift` (the general
traversal-order classification across a run of labels), `um4_pt_i`/`um4_pt_i'`, the four `um4_eval_*` kind
evaluations, `um4_mem_U_iff'`, `um4_old_cases`, `um4_eq_sStrand_iff`, `um4_seg_eIn_inter_eOut`,
`um4_crossing_strand_mem_U`, `um4_visitPt_eq`.

## 3. Axioms — where the two `sorryAx` come from (not from U-M4)

* `m4_clean' : Clean C.U (B.reducedDiagram C)` — the STATEMENT contains `reducedDiagram C`, whose definition uses
  `m2_generic C` (U-M2 sub-leaves) and `overStrand'` → `origCrossing` → `m3_isCrossing_orig` (U-M3).  The proof body
  uses only standard-axiom material (`m4_arcCover'`, the end evaluations, the tail laws).  When U-M2/U-M3 land, the
  axiom footprint becomes standard automatically.
* `m4_no_inner` — consumes `m3_crossingPoint_origCrossing`, `m3_origCrossing_ne_y`, `m3_origCrossing_ne_z` (U-M3
  black boxes), exactly as W1_SKELETON_REPORT §2 prescribes ("M4 needs M3's `m3_crossingPoint_origCrossing` for
  `m4_no_inner`").
The other nine sub-leaves depend on `[propext, Classical.choice, Quot.sound]` only.

## 4. Pitfalls met (additions to W1_SKELETON_REPORT §4)

1. `Strand_mk_eq_mk_iff` / `Sigma.mk.inj_iff` do NOT rewrite on `C.shadow.Strand` when the component is `B.i`
   (`Fin C.shadow.c` vs `Fin D.Γ.c`, pitfall §4.2 again): `um4_mk_i_eq_iff` (stated on `C.shadow.Strand`, proved by
   `Sigma.mk.inj` + `eq_of_heq`, i.e. term-mode, default transparency) is the drop-in.
2. `((0 : ℕ) : ZMod _)` inside a `show` needs the explicit modulus (`ZMod (C.shadow.comp B.i).k`), otherwise the
   coercion cannot be resolved.
3. `B.a + ((0 : ℕ) : ZMod B.k)` is only propositionally `B.a` (`Nat.cast_zero, add_zero`) — the modulus is a
   variable, so `Nat.cast 0` does not reduce; the same for `B.strand 0` versus `B.eIn` (use `strand_zero`).
4. `omega` on `B.j < (D.Γ.comp B.i).k` (the modulus as it appears in `ZMod`) needs `show B.j < B.k` first
   (pitfall §4.3 in a new disguise).
5. `variable (B) in` does not add `B` to a declaration whose statement does not mention `B`
   (`um4_crossingParam_eq`, `um4_visitPt_eq` are `D`-only).
6. `heq ▸ h` fails when the expected type has the abbrev unfolded (`⟨B.i, B.a⟩` vs `B.eIn`); state the intermediate
   `have h1 : B.eIn ∈ x.val := by rw [← hus]; exact hu`.
7. `traversalBetween_of_key_lt` lives in SM/ThreeEdgeArc.lean, which is NOT in the import closure of the skeleton;
   `um4_between_zero_nat` reproves the needed arithmetic directly on `traversalKey`.

## 5. Nothing remains for U-M4

All eleven sub-leaves are closed for general `j`; no sub-leaf was false or needed a stronger hypothesis; no
statement was changed.  U-M7's `m7_riiData` now has every U-M4 field discharged; what it still awaits is
`m5_moveMatch` (U-M5) for `out`, and the black boxes of U-M1/U-M2/U-M3/U-M6.
