# W6_CC_REPORT — wave-6 unit CC (prefix `w6x_`): closing `w6r_box_centreCorners`, 2026-09-19 (D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W6_CC.lean`** (27,005 lines) = `W5_Assembled.lean` (25,237) + W6-COR's two changes + W6-ROT's
inserted block (applied mechanically, `<scratchpad>/w6cc/build_cc.py`, assert-guarded: the merge base has
`diff W6_ROT.lean <base> | grep "^[0-9]"` = COR's `25067a25068,25503`, `25073c25509,25517` and `diff W6_COR.lean <base>` =
ROT's `25540a25541,26071`) + **ONE `w6x_` block (784 lines, `section W6CC … end W6CC`, 33 declarations) inserted inside
`section W6Rot` immediately before the docstring of `w6r_box_centreCorners`** + **the `sorry` body of `w6r_box_centreCorners`
replaced by a 9-line proof**.  `diff W6_ROT.lean W6_CC.lean | grep "^[0-9]"` = **`25067a25068,25503`, `25073c25509,25517`
(COR's two changes), `25590a26035,26819` (this unit's insertion), `25597c26826,26834` (this unit's body replacement)** —
nothing else differs.  No statement, name or docstring touched; no import/`open`/`attribute`/top-level `variable` added.

**Compile** (`cd work/lean && lake env lean ../drafts/corner/W6_CC.lean`, 60 s): **0 errors, 0 warnings other than exactly 9
`declaration uses sorry`** = W5's 10 minus `w5r_box_corners` (closed by COR): 4439 `s7q_box_ret`, 18055 `s7z_F_exists`,
18496 `s7z_returned_of_FSector`, 23881 `w5b_box_returnedData`, 24278/24287/24304 BR's three turn/curl boxes, 25534
`w5r_box_branch`, 26953 `s7_bigon_law_at` (the leaf's own sorry).  **ROT's `w6r_box_centreCorners` (26824) no longer warns.**
`grep -c sorry`: W5 22 / COR 21 / ROT 23 / **CC 21** (= COR's count: ROT's one new sorry body removed; the block contains no
`sorry` token, not even in prose, and no `#print`/`#check`).  `tools/stmt_check.py W6_CC.lean --base W3_Skeleton.lean`: **5/5
PASS**; `tail -n 43` identical to `W3_Skeleton.lean`; `tools/clash_scan.py`: `duplicates_in_assembled: []`,
`full_name_clashes: {}` (1431 new decls; the 33 `w6x_*` names listed as `UNPREFIXED:w6x_*` like every unit prefix).
Nothing written under `work/lean`; `lake build` never run.

**`#print axioms`** (scratch copy `<scratchpad>/w6cc/W6_CC_axioms.lean` = the file + 14 `#print axioms` lines after `end SM`,
log `axioms.log`):

| declaration | axioms |
|---|---|
| **`w6r_box_centreCorners`** (CLOSED), **`w6r_exists_rotation`** (ROT's radius form — was `sorryAx` through the two boxes), `w6x_centreCornerData`, `w6x_glued_order`, `w6x_hcol`, `w6x_point_mark_first/second`, `w6x_hμ`, `w6x_cornerMark_succ_of_chain`, `w6r_rotation_interlacing`, `w6r_rotation_noninterlacing`, `w5r_box_corners` | **`[propext, Classical.choice, Quot.sound]`** — no `sorryAx` |
| `w4_box_returnedRows` | standard + `sorryAx` + `lit_homfly, lp_lm, lp_lm_uniqueness` (unchanged: `sorryAx` enters only through `w5_box_branch` ← BR's three boxes 24278/24287/24304; the GLUE re-threads them with ROT's/CURL's results) |
| `thm_C_S7` | `sorryAx` exactly as in W5 (the leaf's own sorry; not wired, merge rule) |

## 0. In one paragraph

`w6r_CentreCornerData` is TRUE as stated (rule 3 not triggered) and **PROVED**, in exactly ROT's form, below the radius `min` of F's
split radius (`s7f_exists_bigonSplit`) and A2's interval-local radius (`s7a2_exists_intervalLocal`) — the same radius as
`w5r_box_corners`.  Route (W6_ROT_REPORT §4's programme): ROT's splice lemma `w6r_centreCornerData_of_splice` needs, on top of
W6-COR's SET-level bijection `e` (`w6c_glued_corners_wall`: `ccpCornerMark q_H (e x) = w5t_mark (inl/inr (ccpCornerMark L_i y))`,
contact marks `inl M`, `inl 0`, `inl 0`), (i) the CYCLIC ORDER (`hsucc₁ hsucc₂ hfirst₁ hlast₂ hsplice`), (ii) the POINTS (`hpt`), (iii)
the COLLINEARITY on `E_a` (`hcol`).  (i) is read off RT's first-return law `w5t_transport … .ret : s7b_ReturnTransport f (w5t_glued
g₁ g₂ (inl 0) (inl 0)) w5t_mark` by the chain device of RT's `w5t_ct_cornerMark_succ` generalised to the glued cycle: the only
off-image TRUE corner of `q_H` is `μ_M = f(x_ℓ)` (`w6x_hμ`, `s7fb_nextMark_xl`), so the interior of every other first-return gap
is corner-free (`w6x_gap_not_corner`), `g₁`/`g₂`-chains between consecutive half corners lift to corner-free `f`-chains
(`w6x_chain_inl/inr`), the two glue steps are corner-free chains (`w6x_step_p₁`: `y_a → ι(inr (g₂ 0))`; `w6x_chain_μ`:
`μ_M → ι(inl (g₁ 0))`), and a corner-free chain of positive length from `c_i` to a true corner `z` forces `z = c_{i+1}`
(`w6x_cornerMark_succ_of_chain`, `ccp_corner_chain` on `q_H`); the five clauses are the abstract `w6x_glued_order`.  (ii): the
centre point of an image vertex is the half vertex by definition of `firstHalf`/`secondHalf`; of an image visit, Cramer uniqueness
on the common transverse lines (`w6x_cramer_of_line`, `intersection_parameters_unique`), each half edge lying on the line of its
centre edge (`w6x_firstHalf_line`: the last edge is `r • E_a`; `w6x_secondHalf_line`: edge `0` is `(1 − r) • E_a`).  (iii): the
corner-polygon edges into/out of the contact are positive multiples of the halves' last/first edges (`ccpCornerPolygon_edge`,
`ccpCornerPolygon_outEdge_eq_inEdge`), i.e. of `r • E_a` and `(1 − r) • E_a` (`w6x_hcol`).  No new black box; nothing consumed
with `sorry`; everything used is a proved theorem of the file or the library.

## 1. The block (26035-26818, `section W6CC … end W6CC`, variables of `W4Bigon`; 33 declarations)

| lines | section / declaration | content |
|---|---|---|
| 26055-26093 | `W6CCChain`: `def w6x_Chain f C w w' K := (f^K) w = w' ∧ ∀ j, 0 < j → j < K → ¬ C ((f^j) w)`; `w6x_Chain.trans` (junction interior only when both pieces are nonempty: `(0 < K → 0 < K' → ¬ C w')`); `w6x_chain_one`, `w6x_chain_zero` | pure combinatorics on `Equiv.Perm α` |
| 26096-26276 | `W6CCAbstract` (variables: carriers `q q₁ q₂`, `ι : Mark L₁ ⊕ Mark L₂ → Mark Q`, glue marks `p₁ p₂`, `μ`, `hret : s7b_ReturnTransport f (w5t_glued g₁ g₂ p₁ p₂) ι`, `hμ : f (ι (inr p₂)) = μ`, `hμr : μ ∉ range ι`, `hown₁/₂`, `hcorner₁/₂` (off `p_i`), `hoff` — W6-COR's `w6c_glued_corners` hypotheses plus the step law) | `w6x_gap_not_corner` (26122); `w6x_step` (26139); `w6x_chain_inl` (26148) / `w6x_chain_inr` (26183): `m` `g_i`-steps from `c` avoiding `p_i` with corner-free interior ⇒ `∃ K, (1 ≤ m → 1 ≤ K) ∧ (m = 0 → K = 0) ∧ w6x_Chain f (IsTrueCorner T) (ι (inl c)) (ι (inl (g₁^m c))) K` (induction on `m`, `w5t_glued_apply_inl/inr`); `w6x_step_p₁` (26218, `w5t_glued_apply_inl_p`); `w6x_chain_μ` (26228: from `hret.step (inr p₂)` of length `k ≥ 2`, the chain from `μ = f^1(ι (inr p₂))` of length `k − 1`); **`w6x_cornerMark_succ_of_chain`** (26257) |
| 26279-26411 | `W6CCOrder`: `w6x_chain_corner_inl/inr` (consecutive corners of `q_i` off `p_i` ⇒ chain of positive length between the images), `w6x_chain_after_p₁/p₂` (from `ι(inl (g₁ p₁))` to the image of the first corner of `q₁` after `p₁`; the start is a true corner of `T` only when the chain is empty) | `ccp_corner_chain` on the halves, `ccpCornerMark_add_one`, `s7fb_cycle_next_congr` |
| 26436 | **`w6x_glued_order hS hS₁ hS₂ hnot₁ hnot₂ hμt e he hj₁ hj₂ hj`** | the FIVE order clauses of the splice lemma, in its exact shapes: `hsucc₁` = `chain_corner_inl` + `succ_of_chain` + `ccpCornerMark_injective`; `hsucc₂` likewise; `hfirst₁` = `chain_μ ⬝ chain_after_p₁`; `hlast₂` = `chain_corner_inr ⬝ w6x_chain_one hμ` (junction `x_ℓ` not a corner, `hnot₂`); `hsplice` = `chain_corner_inl ⬝ step_p₁ ⬝ chain_after_p₂` (junction `y_a`, `hnot₁`) |
| 26514-26635 | `W6CCPoints`: **`w6x_cramer_of_line`** (26526; `P' e' = edgePoint P E s₁`, `edge P' e' = c₁ • edge P E`, same for `f'/F`, transverse ⇒ `edgePoint P' e' (edgeParameter P' e' f') = edgePoint P E (edgeParameter P E F)`: `s7a2_cramer_symm` on both, `intersection_parameters_unique`); `w6x_firstHalf_line`, `w6x_secondHalf_line`; `w6x_point_first/second` (`s7a2_point Pc (inr (s7b_firstVisitQ v)) = s7a2_point (firstHalf Pc M a) (inr v)`; `s7b_firstVisitQ_visitTwin`, `s7a2_det_ne_zero_generic`); **`w6x_point_mark_first/second`** (`s7a2_point Pc (w5t_mark (inl c)) = s7a2_point (firstHalf) c` for `c ≠ inl 0`) | the `hpt` ingredients |
| 26649 | **`w6x_hcol`** | `∃ v α β, 0 < α ∧ 0 < β ∧ g.center M − ccp L₁ (j₁ − 1) = α • v ∧ ccp L₂ (j₂ + 1) − g.center M = β • v` with `v = edge g.center a`, `α = c₁ r`, `β = c₂ (1 − r)` |
| 26686-26762 | `w6x_hnot₁/₂` (`y_a`, `x_ℓ` not true corners: `hRT.y_not/x_not`), `w6x_hcorner₁/₂`, `w6x_hoff` (W6-COR's `?_` goals of `w6c_glued_corners_wall`, restated), **`w6x_hμ`** (`f(x_ℓ) = inl M`: `smoothingSuccessor_visit_of_not_mem`, `s7fb_nextMark_xl hn hQ hsep hη hw`) | the wall data |
| 26776 | **`w6x_centreCornerData hloc ht hr hr0 hr1 hη hE hT hT₁ hT₂ : w6r_CentreCornerData hn g h h₁ h₂ t T₀`** | `w6c_glued_corners_wall` → `w6x_glued_order` on `hRT.ret` → `w6r_centreCornerData_of_splice` with `hpt` (from `he`, `s7a2_point_eq_evaluation`, `w6x_point_mark_*`) and `w6x_hcol` |
| 26826-26834 | **body of `w6r_box_centreCorners`** | radius `min δ₁ δ₂` (`s7f_exists_bigonSplit`, `s7a2_exists_intervalLocal`); `hE, hT` from `w4_mem_EligDec`; `hT₁, hT₂` from `w4_eligibleEquiv … (hsplit t ht₁) ⟨T₀, hmem⟩` — byte-for-byte the shape of `w5r_box_corners`' body |

## 2. Honest state

- **CLOSED:** `w6r_box_centreCorners` (standard axioms).  Consequently `w6r_exists_rotation` (ROT's radius form of BOTH rotation
  identities) is now sorry-free: `[propext, Classical.choice, Quot.sound]`.
- **Exact remaining sorries of the file (9, none this unit's):** the dead boxes 4439, 18055, 18496, 23881, 25534; BR's LIVE
  `w5b_box_interlacingTurnData` (24278), `w5b_box_noninterlacingTurnData` (24287), `w5b_box_curlData` (24304) — the GLUE fills them
  from `w6r_exists_rotation`/COR's patterns and CURL; the leaf `s7_bigon_law_at` (26953, merge rule).
- **Black boxes consumed:** none.  Rule 3 not triggered (the Prop is true as stated; no corrected form).
- **Not done:** wiring `w6r_exists_rotation` into BR's boxes (GLUE's job, by the task).

## 3. Method audit (D-AUTH-20260919 §2)

Not triggered: no lemma took two failed attempts.  Plan fixed before writing (after reading ROT §4/§6, COR §1, RT's `w5t_ct_*` and
`w5t_step_second_zero`): (i) a generic chain predicate + the glued analogue of `w5t_ct_cornerMark_succ`, with `μ_M` located as
`f(x_ℓ)` (the `h1` of `w5t_step_second_zero`, re-derived from the exported `s7fb_nextMark_xl`) so that gap interiors are corner-free
by COR's `hoff`; (ii) points by Cramer uniqueness on reparametrised lines instead of any parameter transport; (iii) `hcol` from
`ccpCornerPolygon_edge`.  Probe record (`<scratchpad>/w6cc/`, prefix olean `pfx/W6Prefix.olean` = `W6_CC[1..26034]` + closing
`end`s, 2 m 47 s to build; 25-32 s per probe): Probe0 (signatures) 0 errors; P1 (chains + abstract) 1 error (`rw [hjK']` direction →
`← hjK'`); P2 (+ corner chains) 6 errors in `w6x_chain_after_p₁/₂` only — `rw [← hj₁]` rewrote `p₁` everywhere (dropped; the
`s7fb_cycle_next_congr` step suffices) and `h ▸ hp₁t` direction (→ `by rw [h]; exact hp₁t`); P3 (+ `w6x_glued_order`) 0 errors on
the first attempt; P4 (points) 3 error classes — an `omit [NeZero n]` on a lemma that needs it, missing `include hn hsep`, two unused
`c ≠ 0` hypotheses (dropped) — then one unused-variable warning (`hr0` in `w6x_secondHalf_line`, dropped); P5 (wall + test box)
1 error: `rw [hr] at hE₁` "motive is not type correct" (`g.center M` occurs in the TYPE of `h.1.2.2.2.1` inside `w5r_T₁`) → rewrite
the differences `g.center M − g.center a`, `g.center (a+1) − g.center M` first (`hEa`, `hEa'`); then 0 errors, standard axioms.

## 4. Verification record

```
cd work/lean && lake env lean ../drafts/corner/W6_CC.lean          # 0 errors; 9 × "declaration uses sorry" (4439 18055 18496 23881 24278 24287 24304 25534 26953); 60 s
cd work/lean && lake env lean <scratchpad>/w6cc/W6_CC_axioms.lean   # table above (log axioms.log)
grep -c sorry work/drafts/corner/{W5_Assembled,W6_COR,W6_ROT,W6_CC}.lean   # 22 / 21 / 23 / 21
diff work/drafts/corner/W6_ROT.lean work/drafts/corner/W6_CC.lean | grep "^[0-9]"   # 25067a25068,25503  25073c25509,25517  25590a26035,26819  25597c26826,26834
python3 work/drafts/corner/tools/stmt_check.py work/drafts/corner/W6_CC.lean --base work/drafts/corner/W3_Skeleton.lean   # 5/5 PASS
python3 work/drafts/corner/tools/clash_scan.py work/drafts/corner/W6_CC.lean   # duplicates [] / full_name_clashes {} / 1431 new decls
tail -n 43 work/drafts/corner/W6_CC.lean | diff - <(tail -n 43 work/drafts/corner/W3_Skeleton.lean)   # identical
grep -n "#print\|#check" work/drafts/corner/W6_CC.lean   # none
```
Reproduce: `<scratchpad>/w6cc/build_cc.py` (the mechanical COR+ROT merge, assert-guarded), then `assemble.py` (block =
`pieces/00_head 01_abstract 02_order 03_main 04_points 05_wall` + `end W6CC`, body replacement); probes `P1-P5.lean` via
`lean.sh` against `pfx/W6Prefix.olean` (`build_pfx.sh`); `06_test.lean` = the box body as `w6x_box_test` with `#print axioms`.
