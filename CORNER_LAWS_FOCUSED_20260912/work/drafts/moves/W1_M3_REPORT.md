# W1_M3_REPORT — unit U-M3 of the moves toolkit (Wave 1)

U-M3 (subagent), 2026-09-15 19:39 UTC / 3:39pm ET.  File: `work/drafts/moves/W1_M3.lean` (= `Skeleton_W1.lean` with the nine U-M3
sub-leaves PROVED and 28 helper lemmas `um3_*` inserted; every other declaration byte-identical).
Template followed: SM/Smoothing.lean §6b (`isCrossing_orig` :3171, `u3_meet_classify` :2966,
`origCrossing_injective` :3262, `liftStrand`/`isCrossing_lift` :3285–3424, `crossingParam_toDiagram` :3664)
with the kinds `old / cutIn / cutOut` (+ the excluded `mid`) in place of Smoothing's seven.

## 0. Deliverables and checks

| item | result |
|---|---|
| compile `cd work/lean && lake env lean ../drafts/moves/W1_M3.lean` | exit 0, **0 errors**, 1 pre-existing cosmetic linter warning (line 565, inherited from the skeleton); no new warnings |
| `grep -c sorry` before / after | **34 → 25** (the nine U-M3 bodies removed; the frozen header comment and the 24 other-unit leaves untouched) |
| `python3 check_W1_identity.py Statements_FINAL.lean W1_M3.lean` | prefix identical, 37/37 statements identical, suffix identical except the body of `exists_rii_deletion` (as in the skeleton) |
| every skeleton declaration keeps its statement | checked with the same statement extractor on Skeleton_W1 vs W1_M3: **267/267** unchanged, the only new declarations are the 28 `um3_*` helpers |
| `#print axioms` (scratch copy) | 8 sub-leaves: `[propext, Classical.choice, Quot.sound]`; `m3_crossingParam`: `+ sorryAx` **inherited through its frozen statement** (`(B.reducedDiagram C).crossingParam`; `reducedDiagram` is built on `m2_generic`, i.e. the four U-M2 black boxes — `#print axioms reducedDiagram`/`m2_generic` show the same `sorryAx`).  All 28 helpers and the assembled `crossingEquiv` are standard only |
| `work/lean` | nothing written |

## 1. The nine sub-leaves (W1_M3.lean line; all PROVED)

| sub-leaf | line | proof |
|---|---|---|
| `m3_isCrossing_orig` | 1455 | `crossing_pair_spec` on `y'.fst, y'.snd`; non-adjacency read on kinds (`adjacent_iff_kind`), segments read on kinds (`seg_eq`); then `um3_meet_classify` gives non-adjacent originals that meet; `isCrossing_pair` |
| `m3_kind_ne_mid` | 1477 | `um3_meet_classify` applied to `u` and `other y' u`, first component |
| `m3_orig_injOn_crossing` | 1487 | `orig` is injective on occurring non-middle kinds (`um3_orig_inj`), then `kind_injective` — no equal-double-point argument needed (unlike Smoothing, where one strand has two cut pieces) |
| `m3_origCrossing_ne_y` | 1503 | if `origCrossing y' = y` some `u ∈ y'` has `orig u = e_in`, so `kind u = cutIn` (`um3_orig_inj`); the double point of `y'` is then `edgePt e_in t` with `t ≤ t_M` (`um3_cutIn_param`) and lies on `s` (`um3_seg_subset_seg_orig`), hence equals `crossingPoint y = edgePt e_in t_y` (`Generic.seg_inter_seg_eq`), so `t = t_y` (`edgePt_injective`), contradicting `t_M < t_y` |
| `m3_origCrossing_ne_z` | 1527 | mirror image with `cutOut`, `t ≥ t_q > t_z` |
| `m3_crossingPoint_origCrossing` | 1552 | `Generic.common_point_unique`: the double point of `y'` lies on `seg (kind u) ⊆ seg (orig u)` for both strands |
| `m3_origCrossing_injective` | 1561 | `y₁.val ⊆ y₂.val`: `orig u ∈ {orig y₂.fst, orig y₂.snd}`, and `orig` injective on occurring non-middle kinds |
| `m3_exists_lift` | 1687 | `um3_exists_lift_strand` for `x.fst`, `x.snd` (non-middle lifts through the double point, over the right originals); non-adjacency by `um3_not_adj_of_not_adjacent_orig`; `isCrossing_pair`; `um3_origCrossing_mk` identifies the crossing |
| `m3_crossingParam` | 1773 | template `crossingParam_toDiagram`: `Kind.tail_add_smul_dir`, `tail_eq/dir_eq`, `m3_crossingPoint_origCrossing`, `edgePt_injective`, `Kind.liftParam_origParam` |

## 2. Helpers added (all `um3_`, in `section Construction`, before the first sub-leaf that uses them)

Block A (lines 1129–1447, before `m3_isCrossing_orig`):
* `um3_adjacent_iff` (1129) — `Adjacent e f ↔ f ∈ {e, e+1, e−1}`; `um3_eq_mk_add_one_iff`, `um3_eq_mk_sub_one_iff` (1250, 1255) —
  decoding `⟨i, a⟩ = ⟨f.1, f.2 ± 1⟩`; `um3_strand_succ_j`, `um3_strand_pred_j` (1259, 1262).
* `um3_j_eq_one_of_adjacent` (1147) — `Adjacent e_in e_out → j = 1` (ZMod: `j ∈ {−1, 0, 1}` with `1 ≤ j ≤ k − 3`).
* `um3_seg_subset_seg_orig` (1166) — `κ ≠ mid → κ.seg ⊆ D.Γ.seg κ.orig`; `um3_cutIn_param` (1181) — a point of `cutIn` is
  `edgePt e_in t`, `0 ≤ t ≤ t_M`; `um3_cutOut_param` (1190) — `t_q ≤ t ≤ 1` on `e_out`.
* `um3_mid_seg_subset_U` (1199, convexity of `U`, `M' ∈ interior U`, `q ∈ U`), `um3_mid_disjoint_s` (1209, `Cut.mid_side` +
  `det_smul_self`), `um3_mid_disjoint_old` (1218, foreign edges by `Cut.clear`, `s` by the previous) — **the middle edge meets
  no occurring old strand**.
* `um3_cutIn_disjoint_cutOut` (1229) — the two cut pieces never meet: `j ≥ 2` via `no_io` (a common point would make
  `{e_in, e_out}` a crossing), `j = 1` via `Generic.seg_inter_succ` (`e_in ∩ e_out = {M₁}`, and `M₁ ∉ cutIn` since `t_M < 1`).
* `um3_ne_eIn_of_occurs`, `um3_ne_eOut_of_occurs`, `um3_ne_first_of_occurs`, `um3_ne_last_of_occurs` (1268–1281) — an occurring
  `old e` has `e ∉ {e_in, e_out, ⟨i, a+1⟩, ⟨i, a+j−1⟩}`.
* `um3_adj_of_adjacent_orig` (1287) — **adjacency transport**: occurring non-middle kinds that meet, with adjacent originals,
  are adjacent kinds (16-case table; the `(cutIn, cutOut)` cells are killed by `um3_cutIn_disjoint_cutOut`).
* `um3_meet_classify` (1375) — the analogue of Smoothing's `u3_meet_classify`: non-adjacent occurring kinds that meet are
  both non-middle, have non-adjacent originals, and the originals meet.
* `um3_orig_inj` (1399) — `orig` is injective on occurring non-middle kinds.
* `um3_not_adj_of_not_adjacent_orig` (1415) — converse transport for the lift (no `Occurs` needed).

Block B (before `m3_origCrossing_ne_y`): `um3_exists_orig_eq` (1493) — `e ∈ (origCrossing y').val → ∃ u ∈ y', orig u = e`.

Block C (before `m3_exists_lift`, lines 1575–1685): `um3_foreign_of_mem_in/out` (the other strand of `e_in` at `x ≠ y` is
foreign: `s` would force `x = y`, `e_out` is excluded by `no_io`, the run edges by `run_free`), `um3_crossingParam_in_lt`
(`x ≠ y` ⇒ the crossing parameter on `e_in` is `< t_p`: the foreign other strand misses `U`, `Cut.in_iff`),
`um3_crossingParam_out_gt` (`> t_q`), `um3_exists_lift_strand` (the lifted strand as an existential — no `def`, no
`split_ifs`), `um3_origCrossing_mk` (`origCrossing ⟨{u, u'}, _⟩ = x` from `orig u = x.fst`, `orig u' = x.snd`).

## 3. Observations for the other units

* **U-M2** may reuse `um3_meet_classify` + `Kind.dir_eq_smul_orig` + `Smoothing.det_smul_smul` for `m2_transverse` (it is
  literally the content the docstring describes; the M2 prover may copy the helper block — it only uses `Cut` fields and
  §1c laws).  `um3_mid_disjoint_old`, `um3_cutIn_disjoint_cutOut`, `um3_mid_seg_subset_U` are the disjointness inputs of
  `m2_tail_off` / `m2_no_triple`.
* **U-M4 / U-M5 / U-M6**: `um3_crossingParam_in_lt` / `um3_crossingParam_out_gt` are the "retained occurrences of `e_in`
  have `t < t_p`, of `e_out` `t > t_q`" facts of §5 U-M6 (proved here for crossings `≠ y, z`); `um3_seg_subset_seg_orig`,
  `um3_cutIn_param`, `um3_cutOut_param` are the parameter bookkeeping for `m4_no_inner` / `over_eq`.
* No sub-leaf was false or needed a stronger hypothesis.  The frozen `hk : j + 3 ≤ k` is used only through
  `um3_j_eq_one_of_adjacent` (needs `j + 2 ≤ k`) and the skeleton's own laws.

## 4. Pitfalls met (additions to W1_SKELETON_REPORT §4)

1. **`simp only [Kind.orig] at hA` leaves stale instances.**  After `cases κ`, rewriting `(Kind.old e).orig` to `e` inside
   `⟨κ.orig.1, κ.orig.2 + 1⟩` keeps the `HAdd` instance at the type `ZMod (D.Γ.comp (Kind.old e).orig.1).k`; every later `rw`
   fails ("not type-correct under implicit transparency") and `rw`'s closing `rfl` does not fire.  Fix: `replace hA :
   D.Γ.Adjacent e e' := hA` (defeq restatement) BEFORE decoding with `um3_adjacent_iff`.
2. **`split_ifs` auto-discharges** a branch when the condition's proof is in context, leaving one goal; use `subst h; simp
   [Kind.succ]` for the true branch instead of a two-bullet script.
3. **`h ▸ he` against an abbrev** (`B.eOut` vs the expected `⟨B.i, B.a + ↑B.j⟩ ∈ x.val`) needs a type ascription
   `(h ▸ he : B.eOut ∈ x.val)` (same as the skeleton's `kind_sStrand`).
4. `Set.Nonempty` has no `.symm`; flip the `Disjoint` (`(um3_… C).symm`) instead.
5. `rw [← Kind.tail_add_smul_dir …]` needs the goal to say `D.Γ.edgePt …`, not the unfolded `edgePoint …` (do not `show`
   the unfolding first, as the Smoothing template does with its own `edgePoint`-stated lemma).
