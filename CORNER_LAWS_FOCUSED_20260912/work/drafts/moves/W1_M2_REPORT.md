# W1_M2_REPORT — unit U-M2 of the moves toolkit (Wave 1): `Generic` of the reduced shadow

U-M2 (subagent), 2026-09-15 19:35 UTC / 3:35pm ET.  Inputs: W1_SKELETON_REPORT.md (§1 API, §2 sub-leaves, §4 pitfalls,
§5 U-M2 prompt), PLAN_FINAL.md §5–§6, Skeleton_W1.lean (frozen; `Cut` = the M1↔M2–M6 interface), SM/Smoothing.lean §0'
(toolbox: `edgePt`, `Generic.seg_inter_succ`, `Generic.edgePt_injective`, `mk_add_one_eq_iff`, `mk_sub_one_eq_iff`,
`det_smul_smul`, `regularPair_smul_pos`, `regularPair_of_det_ne_zero`) and §6a (the template `regular` :2701,
`u3_kind_tail_off` :2785, `u3_meet_classify`/`transverse` :2959/3017, `u3_kind_no_triple`/`no_triple` :3134/3152),
SM/LinkDiagram.lean (`Generic`, `Adjacent`, `IncidentTail`), SM/RegularLocus.lean (`Regular`), SM/LinkMoves.lean (`IsDisc`).

## 0. Result

| item | result |
|---|---|
| file | `work/drafts/moves/W1_M2.lean` (2406 lines = Skeleton_W1.lean with the four U-M2 `sorry` bodies replaced and 33 helpers `um2_…` inserted before their sub-leaves, all inside `section Construction`) |
| compile (`cd work/lean && lake env lean ../drafts/moves/W1_M2.lean`) | exit 0, **0 errors**, 29 `declaration uses sorry` (was 33), 1 cosmetic linter warning (line 565, inherited from the skeleton), ≈ 13 s |
| `grep -c sorry` | Skeleton_W1.lean **34** → W1_M2.lean **30** (the four bodies; the frozen header comment still counts 1) |
| statement identity | `python3 check_W1_identity.py Statements_FINAL.lean W1_M2.lean` → prefix identical, 37/37 declarations byte-identical, suffix identical except the body of `exists_rii_deletion` (as in the skeleton).  `diff Skeleton_W1.lean W1_M2.lean` removes exactly four lines, each `  sorry`, and adds 544 — so every skeleton declaration (docstring, name, statement) is unchanged |
| **proved** | `m2_regular` (:1350), `m2_tail_off` (:1455), `m2_transverse` (:1577), `m2_no_triple` (:1651); hence `m2_generic` (:1660) is now sorry-free |
| unproved (of U-M2) | none |
| `#print axioms` (scratch copy = W1_M2.lean + `#print axioms`) | `m2_regular`, `m2_tail_off`, `m2_transverse`, `m2_no_triple`, `m2_generic`: `[propext, Classical.choice, Quot.sound]` — standard only |
| nothing written under `work/lean` | yes (scratch files under the session scratchpad only) |

No sub-leaf was found false or under-hypothesised; the `Cut` fields used are exactly `disc` (convexity), `K_sub` (via
`M'_mem_interior`), `in_iff`/`out_iff` (via the proved `M_zero_not_mem`, `tail_s_not_mem`, `M'_mem_interior`, `q_mem`),
`clear`, `q_off_in`, `mid_off_out`, `mid_side`, plus `tp_lt_tM`, `tM_lt_ty`, `tz_lt_tq`, `tq_lt_one`.  Unused `Cut`
fields (for M2): `in_int_iff`, `out_int_iff`, `s_iff`, `s_int_iff`, `tin*`, `tout*`.  `Generic.seg_inter_seg_eq` (the
`e_in ∩ s = {y}` argument of the docstring) turned out unnecessary: `Cut.mid_side` at `θ = 0` and `θ = 1` already puts
`M'` and `q` off `line(s)`.

## 1. Proof architecture (imitates Smoothing §6a: one kind-level lemma per `Generic` field, then the strand-level
sub-leaf is `rw [<index law>]; exact <kind lemma> (kind_occurs u) …`)

* `m2_regular`: `intro n; have h := um2_regularPair_pred_dir C (kind ⟨i', n⟩) (kind_occurs _); rw [← kind_pred, ← dir_eq,
  ← dir_eq] at h; exact h` — literally Smoothing's `regular` :2701.  `um2_regularPair_pred_dir κ (hκ : κ.Occurs) :
  RegularPair κ.pred.dir κ.dir`: `old (strand (j+1))` ↦ `D.generic.regular i (a + j + 1)` rescaled by `1 − t_q`;
  other `old e` ↦ `D.generic.regular e.1 e.2`; `cutIn` ↦ `D.generic.regular i a` rescaled by `t_M`; `mid` ↦
  `regularPair_of_det_ne_zero` from `q_off_in` (`det (t_M • dir e_in) (q − M') = t_M · det …`); `cutOut` ↦ from `mid_off_out`.
* `m2_tail_off`: `rw [incidentTail_iff_kind] at h; rw [tail_eq, seg_eq]; exact um2_kind_tail_off …`.  The 16-entry
  table of `um2_kind_tail_off κ κ' (h : ¬(κ' = κ ∨ κ' = κ.pred))`:
  | κ.tail ∈ κ'.seg? | old e' | cutIn | mid | cutOut |
  |---|---|---|---|---|
  | old e | `D.generic.tail_off` through `um2_eq_or_eq_succ_of_tail_mem_seg`; `e = ⟨e'.1, e'.2+1⟩` is `κ' = κ.pred` unless `e = strand (j+1)`, when `e' = strand j` is not occurring | `cutIn.seg ⊆ seg e_in`, so `e = e_in` or `e = strand 1` — both non-occurring (`1 ≤ j`) | `tail e ∉ U` (`um2_tail_old_not_mem_U`: occurring old = foreign or `s`), `[M', q] ⊆ U` | `cutOut.seg ⊆ seg e_out`: `e = e_out` non-occurring, `e = strand (j+1)` gives `κ' = κ.pred` |
  | cutIn (`M₀`) | `e' = e_in` non-occurring; `e_in = ⟨e'.1, e'.2+1⟩` gives `κ' = old ⟨i, a−1⟩ = κ.pred` | excluded | `M₀ ∉ U` | `M₀ ∈ seg e_out` forces `e_in = e_out` or `e_in = strand (j+1)`, i.e. `0 = j+1` (`strand_inj`) |
  | mid (`M'`) | `um2_mid_disj_old` (foreign: `clear` + `[M', q] ⊆ U`; `s`: `mid_side`) | excluded (`κ.pred`) | excluded | `M' = M' + 0•(q−M')` on `line(e_out)` ⇒ `0 = 1` (`um2_mid_pt_line_out`) |
  | cutOut (`q`) | `um2_mid_disj_old` with `q ∈ [M', q]` | `q = M' + 1•(q−M')` on `line(e_in)` ⇒ `1 = 0` (`um2_mid_pt_line_in`) | excluded (`κ.pred`) | excluded |
* `m2_transverse`: `rw [adjacent_iff_kind] at h; rw [seg_eq, seg_eq] at hmeet; rw [dir_eq, dir_eq]; exact
  um2_kind_transverse …`.  `um2_kind_transverse`: (i) neither kind is `mid` (`mid` vs `old e'`: `um2_mid_disj_old`
  contradicts `hmeet`; `mid` vs `cutIn`/`cutOut`: these are `mid.pred`/`mid.succ`, excluded by `h`); (ii) the originals are
  non-adjacent — a 3-way `um2_adjacent_iff` case split per pair, each adjacent alternative being either a non-occurring
  strand (`e_in = strand 0`, `strand 1`, `strand (j−1)`, `strand j`) or exactly `κ' = κ.succ` / `κ' = κ.pred`
  (`succ (old ⟨i, a−1⟩) = cutIn`, `pred (old (strand (j+1))) = cutOut`, `succ cutOut = old (strand (j+1))`, `pred cutIn =
  old ⟨i, a−1⟩`); the pair `cutIn`/`cutOut` is dismissed by **`um2_cutIn_disj_cutOut`** instead (for `j = 1` the
  originals ARE adjacent); (iii) `det κ.dir κ'.dir = l l' det (dir orig) (dir orig')` (`Kind.dir_eq_smul_orig`,
  `det_smul_smul`) and `D.generic.transverse`, the meeting point transported by `um2_seg_subset_seg_orig`.
* `um2_cutIn_disj_cutOut`: a common point `x = edgePt e_in (θ t_M) = edgePt e_out (t_q + θ'(1 − t_q))`.  `θ' = 0`: `x = q`
  on `line(e_in)`, contradicting `q_off_in`.  `θ' > 0`: `x ∈ seg e_in ∩ seg e_out`; `j = 1`: `Generic.seg_inter_succ`
  gives `x = M₁ = edgePt e_in 1`, so `θ t_M = 1` (`edgePt_injective`) against `θ t_M ≤ t_M < 1`; `j ≥ 2`:
  `um2_not_adjacent_eIn_eOut` (labels `j ∉ {0, 1, k−1}` by `strand_inj`) makes `{e_in, e_out}` a crossing of `D`, excluded
  by the frozen field `no_io` — this is the one place `no_io` is used in M2.
* `m2_no_triple`: `rw [interior_eq] at hx hx' hx''; exact um2_kind_no_triple … (kind_injective …)`.  `um2_kind_no_triple`:
  if one kind is `mid`, `um2_mid_interior_not_mem` (an interior point `M' + θ(q − M')`, `0 < θ < 1`, is off every old
  strand by `um2_mid_disj_old`, off `cutIn` because it would force `θ = 0`, off `cutOut` because `θ = 1`); otherwise
  `um2_orig_ne` (orig is injective on occurring non-middle kinds) and `um2_interior_subset_interior_orig` give a triple
  point of `D`.

## 2. Helpers added (33, prefix `um2_`, all in `section Construction` before the sub-leaf that uses them)

Index bookkeeping on `D` (:1093–1153): `um2_adjacent_iff` (`Adjacent e f ↔ f = e ∨ f = ⟨e.1, e.2+1⟩ ∨ f = ⟨e.1, e.2−1⟩`),
`um2_eq_or_eq_succ_of_tail_mem_seg` (copy of Smoothing's `u3_eq_or_eq_succ_of_tail_mem_seg`, which is section-bound there),
`um2_old_ne` (occurring old strand ≠ `strand m`, `m ≤ j`), `um2_strand_one`, `um2_strand_succ_j`, `um2_strand_j_sub_one`,
`um2_strand_k_sub_one` (`strand (k−1) = ⟨i, a−1⟩`), `um2_strand_succ_sub_one`, `um2_foreign_or_s`, `um2_not_adjacent_eIn_eOut`.
Segments of kinds (:1156–1204): `um2_tail_mem_seg`, `um2_interior_subset_seg`, `um2_seg_subset_seg_orig`,
`um2_interior_subset_interior_orig` (non-middle kinds; `origParam ∈ [0,1]` / `(0,1)` by `nlinarith`), `um2_mem_seg_mid_iff`,
`um2_mem_interior_mid_iff` (`Iff.rfl`), `um2_M'_mem_seg_mid`, `um2_q_mem_seg_mid`.
Geometry of the middle edge (:1208–1266): `um2_seg_mid_subset_U` (`Convex.add_smul_sub_mem`), `um2_det_self`,
`um2_det_smul_left` (local: `det_self`/`det_smul_left` live in SM files not imported here), `um2_mid_pt_line_in` (`M' + θ(q−M')
= edgePt e_in t → θ = 0`), `um2_mid_pt_line_out` (`… = edgePt e_out t → θ = 1`), `um2_mid_not_mem_seg_s`,
`um2_tail_old_not_mem_U`, `um2_mid_disj_old`, `um2_cutIn_disj_cutOut`.
Kind-level forms (:1313, 1360, 1466, 1588–1630): `um2_regularPair_pred_dir`, `um2_kind_tail_off`, `um2_kind_transverse`,
`um2_mid_interior_not_mem`, `um2_orig_ne`, `um2_kind_no_triple`.

## 3. Notes for the other units / the executor

1. `linear_combination (norm := module) h` works for vector identities in `Plane` (used in `um2_mid_pt_line_in/out`);
   `module` alone also works (as in the skeleton's `dir_eq`).
2. In `section Construction` the variable `C : B.Cut` is included only when it appears in the statement, so helpers about
   `D` alone need no `omit`; `B` is implicit there (`variable {B}`), so call them as `B.um2_strand_one` / `um2_old_ne hκ hm`.
3. `Kind.tail C.tM C.tq Kind.mid` and `C.M'` (resp. `Kind.dir … mid` and `C.q − C.M'`, `Kind.cutOut.orig` and `B.eOut`) are
   defeq, and `exact` sees it; but a `have` whose statement mentions `Kind.cutOut.orig` needs the ascription
   `(Kind.cutOut : B.Kind)` — write `B.eOut` instead.
4. `rw [Kind.tail_add_smul_dir …] at hx` rewrites one kind at a time; name the kind (`Kind.cutIn`, `Kind.cutOut`) when
   both pieces appear in `hx`.
5. For U-M3: `um2_mid_disj_old`, `um2_mid_interior_not_mem`, `um2_cutIn_disj_cutOut`, `um2_seg_subset_seg_orig`,
   `um2_orig_ne` and `um2_adjacent_iff` are exactly the ingredients of `m3_kind_ne_mid` / `m3_isCrossing_orig`
   (M3 may copy them under its own prefix; they sit before `m2_regular`, i.e. before the M3 sub-leaves, so they are
   also directly usable in a merged file).
6. Timing: ≈ 11–13 s per compile at load ≈ 10.5; three compile iterations were needed (errors: a `rfl`-pattern
   substituting the wrong variable, `det_smul_self` firing after `det_smul_right`, and the implicit-`B` issue of note 3).
