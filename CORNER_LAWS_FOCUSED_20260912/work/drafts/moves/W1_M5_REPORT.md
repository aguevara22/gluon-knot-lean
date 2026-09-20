# W1_M5_REPORT — unit U-M5 (`m5_moveMatch`) of the moves toolkit (Wave 1)

U-M5 (subagent), 2026-09-15 ≈ 19:40 UTC / 3:40pm ET.  File: `work/drafts/moves/W1_M5.lean`
(= `Skeleton_W1.lean` + 360 inserted lines of `um5_` helpers immediately before the sub-leaf + the body
of `m5_moveMatch`).  Nothing under `work/lean` was written; no `lake build`.

## 0. Result

| item | result |
|---|---|
| sub-leaf `m5_moveMatch : Nonempty (MoveMatch C.U (B.reducedDiagram C) D)` | **PROVED**: `⟨um5_moveMatch C⟩` |
| compile `cd work/lean && lake env lean ../drafts/moves/W1_M5.lean` | exit 0, **0 errors**, 32 `declaration uses sorry` warnings (skeleton: 33) + the pre-existing cosmetic `<;>` linter warning at line 565; ≈ 10 s |
| `grep -c sorry` | Skeleton_W1.lean 34 → W1_M5.lean **33** (33 = 32 bodies + the frozen header comment) |
| `python3 check_W1_identity.py Statements_FINAL.lean W1_M5.lean` | prefix identical; 37/37 declarations byte-identical; suffix identical except the body of `exists_rii_deletion` |
| `diff Skeleton_W1.lean W1_M5.lean` | only `>` additions (1409a1410,1768) and the one body change `1415,1416c1774` (`:= by sorry` → `:= ⟨um5_moveMatch C⟩`); every skeleton statement/name/docstring unchanged |
| `#print axioms` (scratch copy `M5_ax.lean`) | `m5_moveMatch` / `um5_moveMatch`: `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` enters ONLY through the other units' black boxes (§2); the whole `φ` side is standard-only: `um5_origPt_bijective`, `um5_outsideEquiv`, `um5_eval_eq`, `um5_dir_pos`, `um5_dir_pos_before` → `[propext, Classical.choice, Quot.sound]` |

## 1. The construction (Smoothing §6e transposed; `MoveMatch U D₁ D₂` with `D₁ := reducedDiagram C`, `D₂ := D`)

* `φ := um5_outsideEquiv : C.shadow.Outside C.U ≃ D.Γ.Outside C.U` — `Equiv.ofBijective` of `origPt` restricted to the
  outside points (`um5_origPt_bijective`).  The direction is `D' → D` directly (no `.symm`), as the skeleton's
  `origPt` goes `C.shadow.Pt → D.Γ.Pt`.
  - `um5_mid_mem_interior` / `um5_kind_ne_mid`: a point of the middle edge at `θ ∈ [0,1)` is `(1−θ)•M' + θ•q ∈ interior U`
    (`Convex.combo_interior_self_mem_interior`, `M'_mem_interior`, `q_mem`), so an outside point never has kind `mid`.
  - `um5_origParam_mem_Ico`, `um5_origPt_param`: the clamp in `origPt` is inactive off `mid`.
  - `um5_eval_eq_edgePt_orig`, `um5_eval_origPt`, `um5_origPt_outside`: same traced point (`eval_eq` + `Kind.tail_add_smul_dir`).
  - injectivity `um5_origPt_inj`: `um5_kind_eq_of_orig_eq` (two occurring non-middle kinds with equal `orig` are equal —
    `old e_in`, `old e_out` do not occur, `e_in ≠ e_out`), then `kind_injective` and `Kind.liftParam_origParam`.
  - surjectivity `um5_exists_origPt_eq`: `um5_strand_dichotomy` (a strand of `D` is `⟨i, a+m⟩` with `m ≤ j`, or gives an
    occurring `old`); `e_in` at `t ≤ t_p < t_M` lifts to `cutIn` at `t / t_M` (`Cut.in_int_iff`), `e_out` at `t ≥ t_q` to
    `cutOut` at `(t−t_q)/(1−t_q)` (`Cut.out_int_iff`), a run edge is impossible (`um5_run_edge_mem_interior`: both ends
    in `interior U` by `Cut.run_mem_interior`, `Convex.interior`), everything else lifts by `strandOf (old e)`
    (`um5_exists_lift` = Smoothing's `exists_lift`).
* `eval_eq := um5_eval_eq`; `dir_pos := um5_dir_pos` (`um5_dir_orig`: `Kind.dir_eq_smul_orig` inverted by
  `um5_smul_inv`, since the structure wants `D.dir = l • D'.dir`); `dir_pos_before := um5_dir_pos_before`
  (`um5_dir_strandBefore_origPt`: at `θ = 0` the kind is not `cutOut` — its tail is `q ∈ U` —, `um5_origParam_zero`
  puts `origPt` at parameter `0` too, `kind_pred` turns `strandBefore` into `(kind u).pred`, and `um5_dir_pred` gives the
  positive factor: `1` for `old`/`cutIn`, `(1−t_q)⁻¹` when `pred = cutOut`, i.e. `e = strand (j+1)` and
  `⟨i, a+(j+1)−1⟩ = e_out`; at `θ ≠ 0`, `um5_origParam_ne_zero` and the forward case).
* `ψ := um5_outerEquiv := (Equiv.subtypeUnivEquiv (m4_no_inner C)).trans ((crossingEquiv C).trans
  (Equiv.subtypeEquivRight (m4_inner_iff' + not_or)))`; `(ψ x').1 = origCrossing C x'.1` by `rfl`.
* `over_eq`, `under_eq`: `um5_origPt_visitPt` — `origPt (D'.visitPt ⟨x', u⟩) = D.visitPt ⟨origCrossing x', orig u⟩`
  (`m3_kind_ne_mid`, `m3_crossingParam`, `Kind.origParam_liftParam`, `Shadow.mk_eq_mk_iff`), then the visit equalities from
  `orig_overStrand'` / `reducedDiagram_underStrand_orig`.
* `e := Equiv.refl _` (`C.shadow.c = D.Γ.c` is `rfl`), `comp_eq p := orig_fst C ⟨p.1.1, p.1.2.1⟩`.

## 2. Black boxes consumed (other units' sub-leaves, used as hypotheses, unchanged)

`m3_kind_ne_mid` (1×), `m3_crossingParam` (2×), `m4_no_inner` (ψ), `m4_inner_iff'` (ψ); indirectly `m2_generic`
(through `reducedDiagram`), the `m3_*` behind `crossingEquiv`, `origCrossing`, `overStrand'`.  These are the only
sources of `sorryAx` in `m5_moveMatch`.  No statement outside U-M5 was touched.

## 3. Helpers added (35, prefix `um5_`, all in `section Construction`, before the sub-leaf; lines 1410–1768)

`um5_mid_mem_interior, um5_kind_ne_mid, um5_origParam_mem_Ico, um5_origPt_param, um5_origPt_fst, um5_origPt_edge,
um5_strandOf_origPt, um5_eval_eq_edgePt_orig, um5_eval_origPt, um5_origPt_outside, um5_kind_eq_of_orig_eq,
um5_origPt_inj, um5_run_edge_mem_interior, um5_exists_lift, um5_strand_dichotomy, um5_exists_origPt_eq,
um5_origPt_bijective, um5_outsideEquiv (def), um5_outsideEquiv_val, um5_eval_eq, um5_smul_inv, um5_dir_orig,
um5_dir_pos, um5_origParam_zero, um5_origParam_ne_zero, um5_dir_pred, um5_kind_ne_cutOut_of_zero,
um5_dir_strandBefore_origPt, um5_dir_pos_before, um5_outerEquiv (def), um5_outerEquiv_val, um5_origPt_visitPt,
um5_over_eq, um5_under_eq, um5_moveMatch (def)`.

## 4. Notes for the executor / other units

* No sub-leaf of U-M5 was false or needed a stronger hypothesis; the `Cut` interface sufficed as frozen (used:
  `in_int_iff`, `out_int_iff`, `M'_mem_interior`, `q_mem`, `run_mem_interior`, `disc.convex`, `tM_pos`, `tq_lt_one`,
  `tp_lt_tM`, `tq_pos`, `tM_lt_one`).
* Pitfalls met (all §4 of W1_SKELETON_REPORT): `rw` fails under the dependent `Pt` types
  (`⟨(origPt C q).fst, (origPt C q).snd.1 − 1⟩`, `(reducedDiagram C).Γ.Outside` vs `C.shadow.Outside`) — restating the
  goal with `show` (everything is `rfl`-defeq: `um5_outsideEquiv_val`, `um5_outerEquiv_val`, `um5_strandOf_origPt`)
  is the reliable move; `Kind.old.inj_iff` does not exist (use `have h' : e = e' := h`, iota-reduction of `orig`).
* `um5_origPt_visitPt` is exactly U-M6's `origPt (visitPt v) = visitPt (origVisit v)` (stated without `origVisit`,
  which is defined after the sub-leaf); U-M6 may reuse it.
* Scratch harness: `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/`
  (`mk.sh` builds skeleton lines 1–1408 + `m5_body.lean` + closers; `M5_ax.lean` = the `#print axioms` copy).
