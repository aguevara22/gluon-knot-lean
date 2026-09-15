# W3S_S3S5_REPORT — unit S3S5 of the U8R sweep (crossing local model + `Φ` and the local record clauses)

2026-09-14, prover for unit S3S5 (plan `W3_U8R_PLAN.md` §3 S3 + S5, §4).  File:
**`work/drafts/frontrows/W3S_S3S5.lean`** (15,945 lines) = `W3_U8R_Skeleton.lean` (15,587) + ONE helper block
(196 lines, inserted before the S3 leaf docstring: `diff` hunk `14983a14984,15179`) + the five leaf bodies
(hunks `14993c15189,15220`, `15106c15333,15383`, `15113c15390,15414`, `15116c15417,15421`, `15122c15427,15481`).
Nothing else differs from the skeleton; every statement, definition and docstring is byte-identical (checked with
`diff`, and the five leaf header lines compared separately).  The four L-geo leaves (`typeIII_site`, `typeII_move`,
`typeI_move`, `crossedCusp_move`, lines 11100-11126) are untouched.

**Compile** (`cd work/lean && lake env lean ../drafts/frontrows/W3S_S3S5.lean`, ~50-57 s): exit 0, **0 errors**,
53 `declaration uses sorry` warnings (= the 53 remaining leaves of the other units; none in my region), 0
deprecation warnings, no warning of any kind in lines 14984-15481.  `grep -c sorry`: **58 before → 53 after**.
Log: `/tmp/s3s5/full.log`.

## 1. Leaves — all five PROVED, none left

| leaf | line | axioms (`#print axioms` on a probe) | notes |
|---|---|---|---|
| `cross_height_order` (S3) | 15186 | `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** | statement TRUE as frozen (over above for `x < x₀`, below for `x > x₀`) |
| `ΦSub_bijective` (S5) | 15333 | `sorryAx` only through `word_closed` (inside the type of `ΦFun`) | injective + surjective, both branches |
| `ΦFun_partner` (S5) | 15390 | idem (`word_closed`) | via `U2.σslot_ext` |
| `isDesc_ΦFun` (S5) | 15417 | idem (`word_closed`) | 4 lines |
| `σsgn_ΦFun` (S5) | 15427 | `word_closed` + the black box **`run_take_eq_hybrid`** (S4) | `step_hybrid` was NOT needed |

`regular_local_graph` (S1) was NOT needed for `cross_height_order` (the plan allowed inlining it): the direct
`hasDerivAt_iff_isLittleO` argument on `z − s·x` along each branch, with the inverse bound `|x − x₀| ≥ |x'|/2·|t − t₀|`
from the same lemma on `x`, suffices.  No S2/S6 statement is used.  No `deform_*`, no new import.

## 2. The helper block `/-! ### S3S5 helpers -/ section S3S5Helpers … end S3S5Helpers` (lines 14984-15179)

Placed immediately before the S3 leaf docstring, inside `section SweepLeaves` (so `F : SmoothFront` is the section
variable), inside `namespace U8R`.  All names prefixed `s3s5_`.  Because the block precedes the S4 leaves and
`section SlotMap`, NO helper mentions `crossOf`, `ΦFun` or `run_take_eq_hybrid`; the Φ-specific facts are local
`have`s inside the leaf bodies (see §3.7).

| helper | statement (words) | tools |
|---|---|---|
| `s3s5_graph_bound (r) (ha : xvel F r.1 r.2 ≠ 0) (hε : 0 < ε)` | `∃ δ > 0, ∀ t, |t − r.2| < δ → |(z t − s·x t) − (z₀ − s·x₀)| ≤ ε·|x t − x₀|`, `s = F.slope r` | `hasDerivAt_x`, `((F.comp r.1).hasDerivAt r.2).snd`, `HasDerivAt.sub/const_mul`, `div_mul_cancel₀`, `hasDerivAt_iff_isLittleO`, `IsLittleO.def`, `Metric.eventually_nhds_iff`, `abs_sub` |
| `s3s5_filter_split (f : α → ℝ) z L (hL : Pairwise (f q ≤ f p))` | `filter (z ≤ f) L = filter (z < f) L ++ filter (f = z) L` for a nonincreasing key | induction, `List.filter_cons_of_pos/neg`, `decide_eq_true_eq` |
| `s3s5_eq_pair (hab : a ≠ b) (hR : ¬ R b a) L hnd hmem hpw` | a nodup list with members exactly `{a, b}`, `Pairwise R`, is `[a, b]` | `match` on `L`, `List.nodup_cons` |
| `s3s5_mem_fibre_at_height (q : Cross F) p` | `p ∈ totalFibre (evX (inr q)) ∧ ht p = evZ (inr q) ↔ p = q.1.1 ∨ p = q.1.2` | `F.no_triple`, `SameParam.eq_of_mem_Ico`, `mem_crossingPairs'` |
| `s3s5_filter_height_eq (q)` | `filter (ht · = evZ (inr q)) (fibreListBefore (evX (inr q))) = [over, under]` | the two above, `fibreListBefore_nodup/_pairwise`, `Prod.Lex.toLex_le_toLex` (`¬ beforeLE under over`: equal heights, larger slope) |
| `s3s5_beforeBits_of_not_isCusp` | regular point ⇒ `beforeBits p = [dirBit p]` | `ite_eq_right` |
| `s3s5_hybridCut_cross (q)` | `∃ A B, hybridCut (evX (inr q)) (evZ (inr q)) = A ++ dirBit over :: dirBit under :: B ∧ A.length + 1 = posOf (inr q)` (`A` is definitionally the `posOf` list, so the length clause is `rfl`) | heights antitone along `fibreListBefore` (`Pairwise.imp`), `s3s5_filter_split`, `s3s5_filter_height_eq`, `not_isCusp_of_isDouble`, `List.flatMap_append/cons/nil` |
| `s3s5_dirBit_eq_iff (ho hu : (F.vel ·).1 ≠ 0)` | `dirBit o = dirBit u ↔ 0 < (vel o).1 * (vel u).1` | `show` (eta: `xvel F o.1 o.2 ≡ (F.vel o).1`), `mul_pos_iff`, case split |
| `s3s5_evIdx_injective` | `evIdx e = evIdx e' → e = e'` | `eventAt_evIdx` |
| `s3s5_eventAt_eq_inr (hk) (hℓ : letterAt (word F) k = σ m)` | `∃ q : Cross F, eventAt F k = inr q` | `letterAt_word`, `letterOf` of a cusp is `l`/`r` (`split_ifs` closes it) |

## 3. Proof sketches actually used, and pitfalls for the merger / other units

1. **`cross_height_order`.**  `ε := (slope q − slope p)/4`; `s3s5_graph_bound` on both branches; at equal `x`
   (`hx`, plus `eval q = eval p` for `x₀`, `z₀`), `z_p − z_q = D_p − D_q + (s_q − s_p)(x₀ − x)` with `|D_·| ≤ ε|x − x₀|`;
   closed by `nlinarith` after supplying `hpos : 0 < (s_q − s_p)·(x₀ − x)` (resp. `(x − x₀)`) explicitly.
2. **`σsgn_ΦFun`.**  `cut (word F) k = hybridCut …` from `run_take_eq_hybrid` (then `unfold colX colZ; rw [eventAt_evIdx]`
   — the black box is stated with `colX/colZ`, not `evX/evZ`); `bit W k m = dirBit over`, `bit W k (m+1) = dirBit under`
   via `s3s5_hybridCut_cross` + `List.getD_append_right` (for `m+1`: `show (_ :: _ :: B).getD (A.length + 1 − A.length) false = _`
   then `Nat.add_sub_cancel_left` — after `Nat.add_sub_cancel` the index displays as `.succ`, so `show` is the robust
   step); `frontSgn p = sign (det (vel over) (vel under))` in both `frontOver` cases (`hpair`); then
   `signType_intCast_injective`, `crossSign_eq_sign`, `coe_σsgnCol`, `crossSign_eq_one_iff(_of_isOverUnder)`.
   **Pitfall:** `simp only [Letter.idx]` followed by `rw [hb1, hb2]` fails with "motive is not type correct" (the
   `Decidable` instance of the `if` still mentions `(σ m).idx`); use `simp only [Letter.idx, hb1, hb2]` in one call.
3. **`ΦSub_bijective`.**  Injective: `colOf (ΦFun r) = evIdx (inr (crossOf r))` (`σSlotA_spec/σSlotB_spec .1`) ⇒ equal
   crossings (`s3s5_evIdx_injective`, `Sum.inr_injective`); `isDesc (ΦFun r) = frontOver r` ⇒ equal bits; then
   `(crossOf r).1` is `(r.1, partner.1)` or `(partner.1, r.1)` by the bit (`hval`), so `r.1 = r'.1`.  Surjective:
   `U2.isσSlot_iff` ⇒ `u = σSlotA/B hW hk hℓ`; `s3s5_eventAt_eq_inr` ⇒ `eventAt k = inr q`; `po := ⟨q.1.1, _⟩` (over,
   `frontOver_of_mem_crossingPairs`, `partner_val_of_mem_crossingPairs`), `crossOf po = q`, `crossOf (partner po) = q`;
   equality of slots by `U2.σslot_ext` (column + `isDesc`), never by unfolding `σSlotA`.  **Pitfall:** in
   `show ΦFun F po = σSlotA (word_closed F) hk hℓ` the `hW` argument must be given explicitly (`_` is not synthesized).
4. **`ΦFun_partner`.**  `crossOf (partner p) = crossOf p` (both `dite` branches, `partner_partner`), then `U2.σslot_ext`
   with `U2.colOf_σtwin`, `U2.isDesc_σtwin`, `frontOver_partner`.  (`σtwin_σSlotA` was not needed.)
5. **`isDesc_ΦFun`.**  `unfold ΦFun; split_ifs` + `U2.isDesc_σSlotA/B`, `Bool.eq_false_iff`.
6. **Deprecations.**  This toolchain deprecates `if_pos/if_neg/dif_pos/dif_neg` in favour of
   `ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right` (same signatures — checked); my block uses the new names,
   so the region compiles warning-free.  Other units' code still uses the old names (warnings only).
7. **Duplication the merger may want to fold.**  Because the helper block must precede `cross_height_order` (before
   `crossOf`/`ΦFun` exist), the facts `colOf (ΦFun r) = evIdx (inr (crossOf r))`, `isDesc (ΦFun r) = frontOver r`,
   and `(crossOf r).1 = if frontOver r then … else …` are re-proved as 3-5-line `have`s inside `ΦSub_bijective`,
   `ΦFun_partner` and `σsgn_ΦFun`.  If the merger prefers, they can become lemmas placed right after `isσSlot_ΦFun`
   (15325) — but that would be a change outside a leaf body, so I did not do it.  `ΦFun_partner`/`isDesc_ΦFun` come
   AFTER `ΦSub_bijective` in the frozen order, so the bijectivity leaf cannot cite them.
8. **Statement checks.**  `cross_height_order` numerically and analytically confirmed as frozen (over = smaller slope
   is above for `x < x₀`); the letter conventions `σSlotA` = over = `isDesc = true` and `σsgn = +1 ↔ bits agree ↔
   x-velocities of the same sign` match `frontOver`/`frontSgn` exactly — no missing hypothesis in any of the five.
   None of the §6 doubts of the plan concerns this unit.

## 4. Fast loop used (recommended to the other provers and the merger)

The whole file takes ~50 s per compile.  Compile the prefix once into an `.olean` and iterate on a ~150-line tail:
```
{ head -n 14983 W3S_S3S5.lean; printf '\nend SweepLeaves\n\nend\n\nend U8R\n\nend Leaves\n\nend FrontRows\n\nend SM\n'; } > /tmp/s3s5/S3S5Prefix.lean
cd work/lean && lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/s3s5 lean --root=/tmp/s3s5 -o /tmp/s3s5/S3S5Prefix.olean /tmp/s3s5/S3S5Prefix.lean'   # ~45 s, once
# test file: `import S3S5Prefix`, reopen `namespace SM`, `open SM.FrontWord SM.Link`, `open scoped ContDiff`, `namespace FrontRows`,
# `section Leaves`, `namespace U8R`, `open SM.FrontWord SM.FrontWord.Letter SM.FrontRealize Equiv`, `noncomputable section`,
# `section SweepLeaves`, `variable (F : SmoothFront)`, then the block + the tail (lines 14984-15126 of the skeleton) + closers.
lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/s3s5 lean /tmp/s3s5/T.lean'   # ~8-10 s per iteration
```
Scripts: `/tmp/s3s5/build.sh` (assemble + compile), `/tmp/s3s5/apply.py <file> <leaf>…` (replaces the `:= sorry` of a
named leaf by `/tmp/s3s5/bodies/<leaf>.lean`; asserts the target is the first `sorry` after the header).
