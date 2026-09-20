# W1_M1_REPORT — unit U-M1 (`m1_exists_cut`), Wave 1 of the moves toolkit

U-M1 (subagent), 2026-09-15 19:40 UTC / 3:40pm ET.  File: `work/drafts/moves/W1_M1.lean` (= `Skeleton_W1.lean` +
688 inserted lines + the body of `m1_exists_cut`).  Inputs: W1_SKELETON_REPORT.md (§1c.0–1c.1, §4, §5 U-M1),
PLAN_FINAL.md §5–§6, SM/Smoothing.lean §0' (`edgePt`, `mem_seg_iff`, `Generic.seg_inter_succ`,
`Generic.crossingPoint_injective`), SM/LinkDiagram.lean (`Generic`, `IsCrossing`, `Adjacent`, `IncidentTail`),
SM/LinkMoves.lean (`IsDisc`, `edge_ne_zero`), SM/EuclideanPlane.lean (`scalar_of_det_zero`), Mathlib
(`Disjoint.exists_cthickenings`, `Convex.cthickening`, `IsCompact.cthickening`,
`Metric.thickening_subset_interior_cthickening`, `Convex.add_smul_sub_mem(_interior)`, `IsClosed.csInf_mem`).

## 0. Result

| item | result |
|---|---|
| **`m1_exists_cut : Nonempty B.Cut`** (the only sub-leaf of U-M1) | **PROVED** (body 81 lines + 42 helpers `um1_*`) |
| compile `cd work/lean && lake env lean ../drafts/moves/W1_M1.lean` | exit 0, **0 errors**, 1 pre-existing cosmetic linter warning (`<;>`, skeleton line 565 → now 1253), ≈ 12 s |
| `declaration uses sorry` | **32** (skeleton: 33) — the 28 other sub-leaves `m2_…m6_` + the 4 frozen leaves |
| `grep -c sorry` | 34 → **33** (the header comment line 17 still counts) |
| `python3 check_W1_identity.py Statements_FINAL.lean W1_M1.lean` | prefix identical; 37 declarations unchanged; suffix identical except the body of `exists_rii_deletion` |
| `diff Skeleton_W1.lean W1_M1.lean` | exactly ONE deleted line (`  sorry`, the body of `m1_exists_cut`); 689 added lines (688 helpers/header + the body's last line); every skeleton statement, name and docstring kept |
| `#print axioms m1_exists_cut` (scratch copy `S4.lean` = skeleton lines 1–455 + the same helpers + the same body) | `[propext, Classical.choice, Quot.sound]` — standard only |
| other units' sorries | untouched |

Nothing under `work/lean` was written.  Scratch files: `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-…/scratchpad/S1–S4.lean`.

## 1. The construction as proved (helpers in file order, all between `end Cut` and the sub-leaf, namespace `BigonData`)

### 1a. Pure toolbox (no `B`)
* `um1_edgePt_combo` — `edgePt e t = edgePt e t₀ + ((t−t₀)/(t₁−t₀)) • (edgePt e t₁ − edgePt e t₀)` (coordinates + `field_simp; ring`).
* `um1_mem_of_convex` — a convex set containing `edgePt e t₀`, `edgePt e t₁` contains every `edgePt e t`, `t₀ ≤ t ≤ t₁` (`Convex.add_smul_sub_mem`).
* `um1_mem_interior_of_convex`, `um1_mem_interior_of_convex'` — one end in `V`, the other in `interior V` ⇒ the half-open segment is interior (`Convex.add_smul_sub_mem_interior`), both orientations.
* `um1_not_mem_interior_of_min` / `_of_max` — the frontier argument WITHOUT a frontier formula: if `f t₀ ∈ interior V` for continuous `f` then some `f t`, `t < t₀` (resp. `> t₀`) lies in `V` (`Metric.isOpen_iff` on the preimage).
* `um1_exists_affine_ne_zero` — an affine `A − t·Bc` that is nonzero somewhere is nonzero at some `t ∈ (lo, hi)` (constant case / at most one root among two candidates).
* `um1_mul_pos_trans` — `0 < A·B`, `0 < A·C`, `A ≠ 0` ⇒ `0 < B·C` (the sign-transport step of the run induction).
* `um1_exists_zero_combo` — `A·B < 0` ⇒ `∃ θ ∈ (0,1)`, `A + θ(B − A) = 0` (discrete IVT along an edge).
* `um1_continuous_edgePt`, `um1_isClosed_paramSet` — `t ↦ edgePt e t` continuous; `{t ∈ [0,1] | edgePt e t ∈ V}` closed for closed `V`.
* **`um1_entry`** (tail ∉ V, head ∈ interior V ⇒ `∃ tp ∈ (0,1)` with the closed law `∈ V ↔ tp ≤ t` and the interior law `∈ interior V ↔ tp < t`), **`um1_exit`** (mirror, `sSup`), **`um1_through`** (both ends ∉ V, an interior point at `t₁` ⇒ `tin < t₁ < tout` with `∈ V ↔ tin ≤ t ≤ tout`, `∈ interior V ↔ tin < t < tout`).  Proof pattern: `tp := sInf S`, `IsClosed.csInf_mem`, `csInf_le`, convexity for `⇐`, `um1_not_mem_interior_of_min` for the strict interior law.  These are stated for an arbitrary shadow/closed convex `V` and are reusable.

### 1b. Site facts
* `um1_s_ne_strand (m ≤ j)` — `s ≠ ⟨i, a+m⟩` (`s_ne_eIn`, `s_ne_eOut`, `run_free` + `s_mem_y`).
* `um1_det_ne_zero_of_crossing` — the two strands of any crossing have `det (dir u) (dir v) ≠ 0` (from `Generic.transverse`); `um1_det_s_in_ne_zero`, `um1_det_s_out_ne_zero`.
* `um1_side_combo` — the side function `P ↦ det w (P − o)` is affine along `[P, Q]`.
* **`um1_side_edgePt_in` / `_out`** — `det (dir s) (edgePt e_in t − tail s) = (t − ty)·det (dir s) (dir e_in)` and the `e_out`/`tz` twin (coordinates of `hty, htsy` / `htz, htsz`, one `linear_combination`).
* `um1_M_one` (`M 1 = edgePt e_in 1`), `um1_M_j` (`M j = edgePt e_out 0`), `um1_y_mem_K`, `um1_z_mem_K`, `um1_tail_s_not_mem_K`, `um1_head_s_not_mem_K` (`s_iff` at `0`, `1`).
* **`um1_mem_seg_s_of_side_zero`** — `K ∩ line(s) ⊆ seg s`: a point of `K` on `line(s)` is `edgePt s c` (`scalar_of_det_zero`); `c < 0` would put `tail s` between it and `y` (convexity) and `c > 1` would put `head s` between `y` and it.
* `um1_not_incidentTail_s (1 ≤ m ≤ j)`, `um1_not_adjacent_s (1 ≤ m < j)` — index bookkeeping (`incident`/`adjacent` unfolded, `Nat.cast_sub`, `linear_combination` in `ZMod`).
* `um1_seg_run_sub_K` (run edges ⊆ `K` by convexity), **`um1_run_edge_off_line`** (a run-edge point on `line(s)` is on `seg s`, giving a crossing `{⟨i,a+m⟩, s}` against `run_free`), **`um1_side_M_ne_zero`** (a run vertex on `line(s)` is a vertex on `seg s`, against `tail_off`).
* **`um1_side_step`** (consecutive run vertices strictly on the same side: else `um1_exists_zero_combo` produces a run-edge point on `line(s)`), **`um1_side_run`** (`Nat.le_induction`: every `M_m`, `1 ≤ m ≤ j`, has the sign of `M₁`), **`um1_signs`** — THE SIDE LEMMA in the form used downstream: `det (dir s) (dir e_in) · det (dir s) (dir e_out) < 0` (evaluate `um1_side_run` at `m = j` with `M₁ = edgePt e_in 1`, `M_j = edgePt e_out 0`; `nlinarith`).
* **`um1_y_off_out`** — `y ∉ line(e_out)`: else `det (y − z) (dir e_out) = 0` with `y − z = (tsy − tsz)·dir s`, so `tsy = tsz`, `crossingPoint y = crossingPoint z`, `y = z` (`Generic.crossingPoint_injective`) against `y_ne_z`.
* `um1_affine_out`, `um1_affine_out_ty` — `det (q − edgePt e_in t) (dir e_out) = A − t·Bc` with `A − ty·Bc = −det (y − tail e_out) (dir e_out) ≠ 0`.
* **`um1_mid_side`** — for `tM < ty`, `tz < tq`: `det (dir s) (M' + θ(q − M') − tail s) ≠ 0` on `[0,1]` (after `um1_side_combo` and the two side formulas, multiply by `det (dir s) (dir e_out)`: both summands are `≥ 0`, not both `0`).
* `um1_not_adjacent_in_out (2 ≤ j)` — `(j : ZMod k) ∉ {−1, 0, 1}` via `Smoothing.nat_eq_of_zcast_eq`.
* **`um1_q_off_in`** — `q ∉ line(e_in)` (stated with the exact `Cut` hypotheses: `q ∈ V`, `q ∉ interior V`, `M₀ ∉ V`, `y ∈ V`, `M₁ ∈ interior V`).  If `q = edgePt e_in c`: comparing the two side formulas with `um1_signs` gives `c < ty`; `c < 0` puts `M₀` between `q` and `y` (convexity) against `M₀ ∉ V`; `0 ≤ c` puts `q ∈ seg e_in ∩ seg e_out`, which for `j ≥ 2` is a crossing containing both `e_in, e_out` (`no_io`) and for `j = 1` is `{M₁}` (`Generic.seg_inter_succ`) against `q ∉ interior V`.

### 1c. The body of `m1_exists_cut`
`F := (⋃_{Foreign u} seg u) ∪ {M₀, M_{j+1}, tail s, head s}` compact (`Set.Finite.isCompact_biUnion`, finite set),
disjoint from `K` (`clear_of_foreign`, `M_zero_not_mem_K`, `M_succ_j_not_mem_K`, the two `s_iff` end facts);
`Disjoint.exists_cthickenings` gives `δ > 0` with `cthickening δ F ∩ cthickening δ K = ∅`; **`U := Metric.cthickening δ K`**
(`Convex.cthickening`, `IsCompact.cthickening`, `K ⊆ thickening δ K ⊆ interior U`); `Cut.clear` and the four
"outside" facts from `F ⊆ cthickening δ F`; `tp` from `um1_entry` on `e_in` (`M₀ ∉ U`, `M₁ ∈ interior U`), `tq`
from `um1_exit` on `e_out`, `tin, tout` from `um1_through` on `s` at `tsy` (then `tsz` through the interior law:
`tin < min tsy tsz`, `max tsy tsz < tout`); `tp < ty`, `tz < tq` from the interior laws at `y, z ∈ K ⊆ interior U`;
`tM ∈ (tp, ty)` from `um1_exists_affine_ne_zero` seeded at `t = ty` by `um1_y_off_out`; the three `det` fields
from `um1_q_off_in`, `um1_affine_out`, `um1_mid_side`.  (The docstring's `ρ₀/2` is realised as the `δ` of
`Disjoint.exists_cthickenings`, which is the same construction with the gap computed by Mathlib.)

## 2. Deviations from the recommended prompt (none affect statements)

* `ρ₀ := infDist` replaced by `Disjoint.exists_cthickenings` (compact ∩ closed = ∅ ⇒ disjoint closed thickenings): shorter and avoids the `infDist` API.
* The interior laws use `Convex.add_smul_sub_mem_interior` on `edgePt`-parametrised segments instead of `openSegment_closure_interior_subset_interior` (same lemma family, no `openSegment` bookkeeping).
* The side lemma is packaged as one inequality `um1_signs : det (dir s) (dir e_in) · det (dir s) (dir e_out) < 0` plus the two affine formulas `um1_side_edgePt_in/out`; `M₀`, `M_{j+1}`, `p`, `M'`, `q` "on the other side" are instances of those formulas (not stated separately since nothing downstream in U-M1 needs them).  U-M2 may want them: `det (dir s) (edgePt e_in t − tail s) = (t − ty)·D_in` with `D_in·D_out < 0` gives every sign statement in one line.
* `tM` is chosen by `um1_exists_affine_ne_zero` seeded at `t_y` (`y ∉ line(e_out)`, `um1_y_off_out`) rather than by the "line contains `e_in` ⇒ `y = z`" case split; the `y = z` argument is inside `um1_y_off_out`.

## 3. Reusable for other units

`um1_entry/um1_exit/um1_through` (any strand against any closed convex set), `um1_mem_of_convex`,
`um1_mem_interior_of_convex(')`, `um1_side_edgePt_in/out` + `um1_signs` (U-M2's `m2_transverse`/`m2_no_triple` at
`M'`, `q`; U-M3's `m3_kind_ne_mid`), `um1_mem_seg_s_of_side_zero`, `um1_det_ne_zero_of_crossing`,
`um1_not_adjacent_in_out`, `um1_y_off_out`.  All are `theorem`s in namespace `SM.Link.BigonData` (those not
mentioning `B` take the shadow implicitly — call them without dot notation, e.g. `um1_entry hconv hcl e h0 h1`).

## 4. Pitfalls met (additions to W1_SKELETON_REPORT §4)

* `le_or_lt`, `lt_or_le` are gone in this Mathlib: use `le_or_gt`, `lt_or_ge`.
* `Shadow.edgePt_eq` takes the shadow explicitly: `D.Γ.edgePt_eq e`, not `Shadow.edgePt_eq e`.
* `run_free`'s statement is in raw form `⟨i, a + m⟩ ∉ x.val`; `rw` with `strand` fails — use `show B.strand m ∈ _` first.
* A lemma that does not mention `B` gets no `B` argument from `variable (B)`, so `B.um1_…` dot notation fails on it.
* `simp only [...]` on `congrArg Prod.fst B.htz` rewrites `B.eOut` to `⟨B.i, B.a + ↑B.j⟩`; `linear_combination`/`ring` still identify the atoms (abbrev), so coefficient bookkeeping is the only work.
* `(Nat.succ_le_iff.mp B.hj).lt_or_eq` does not elaborate; use `(show 1 ≤ B.j from B.hj).lt_or_eq`.
