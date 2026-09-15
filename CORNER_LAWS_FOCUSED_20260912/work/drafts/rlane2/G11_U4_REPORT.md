# G11_U4_REPORT — Unit U4 (C moved polygon + inner crossings D3–D4)

Written 2026-09-14 by the U4 prover (Claude, tmux `side`, Mark's RunPod home pod).
File: `work/drafts/rlane2/G11_U4.lean` (2899 lines; skeleton 1086 + 1813 lines of `gu4_` helpers/proofs).
Compile: `cd work/lean && lake env lean ../drafts/rlane2/G11_U4.lean` → **exit 0, 0 errors, 40 × `declaration uses sorry`
(the other units' leaves), no other warning**, ~12 s. `grep -c sorry`: 50 before → 41 after (40 leaves + the module docstring's
mention). `diff G11_Skeleton.lean G11_U4.lean`: the only removed lines are the nine `  sorry` bodies of U4's leaves; every
definition, statement, name and docstring is byte-identical (the two term-mode proofs were written as `by exact …` so the
`:= by` lines are unchanged too). Nothing under `work/lean` was written.

## 1. Leaves proved (9 of 9)

| leaf | status | depends on black boxes |
|---|---|---|
| `X₁_generic` | PROVED via `Shadow.single_generic_of` (regular / tail_off / transverse / no_triple) | `X₀_generic` (U3) |
| `X₁_cross_pC` | PROVED, **sorry-free** (`#print axioms`: propext, Classical.choice, Quot.sound) | — |
| `X₁_cross_qB` | PROVED, **sorry-free** | — |
| `X₁_cross_iff` | PROVED, **sorry-free** | — |
| `X₁_cross_pq` | PROVED | `X₀_cross_pq` (U3) via `X₁_cross_iff` |
| `X₁_sign_pC` | PROVED, **sorry-free** | — |
| `X₁_sign_qB` | PROVED, **sorry-free** | — |
| `inner_M₀` | PROVED | `X₀_generic`, `X₀_cross_mp/mq/pq`, `triangle_sub_interior` (U3) |
| `inner_M₁` | PROVED | `X₀_generic`, `X₀_cross_mp/mq/pq`, `triangle_sub_interior` (U3) |

`disc_isDisc` (U3) is **not used**: convexity of `U` is proved directly (`gu4_convex_U`, the image of the convex hull under
the homothety), and `Δ ⊆ U` likewise (`gu4_Δ_sub_U`, pre-image = convex combination of the point and the centroid), both
sorry-free. `triangle_sub_interior` is used only in the D3/D4 block (interior membership of `a, b, c`), which is placed after
that leaf in the file. All nine leaves are TRUE as stated; no counterexample, no missing hypothesis.

## 2. Method (so the assembler / U5 / U6 can reuse it)

Frame of the configuration (all `gu4_` defs take `π : G11_Params C`, used as `π.gu4_a` etc.):
`a = x_mp`, `b = x_mq`, `c = x_pq` (`gu4_a/b/c`), `tmp, tmq` their parameters on `m` (`gu4_tmp/tmq`), `dm = edge X m`,
`v = c − a` (`gu4_dm/v`), `E = det dm v ≠ 0` (`gu4_E`, `gu4_E_ne`). Three affine functionals
`α y = det (y − a) v` (vanishes on the line `p`), `β y = det dm (y − a)` (vanishes on `m`), `γ y = det (y − b) (c − b)`
(vanishes on `q`); every point is `a + (α/E) • dm + (β/E) • v` (`gu4_frame`, Cramer) and `γ = α + L (β − E)`, `L = tmq − tmp`
(`gu4_γ_eq`). Values: on `edgePoint X m t`: `(α, β, γ) = ((t − tmp) E, 0, (t − tmq) E)`; on the apex
`w = a + (1−λ)(t₂−tmp) • dm + λ • v`; on `[p_in, w]` at `σ`: `β = σ λ E`, `α = ((1−σ)(t₁−tmp) + σ(1−λ)(t₂−tmp)) E` with
the bracket `< 0` (`gu4_segB_coeff_neg`, so the edge never meets the line `p`), `γ = ((1−σ)(t₁−tmq) + σ(λ−1)(tmq−t₂)) E`;
on `[w, p_out]` at `σ`: `β = (1−σ) λ E`, `α = ((1−σ)(1−λ)(t₂−tmp) + σ(t₃−tmp)) E`,
`γ = ((1−σ)(λ−1)(tmq−t₂) + σ(t₃−tmq)) E` with the bracket `> 0` (`gu4_segC_coeff_pos`, never meets `q`).

New double points: `σ_p = (λ−1)(t₂−tmp) / ((λ−1)(t₂−tmp) + (t₃−tmp))`, `y_p = w + σ_p (p_out − w) = a + (1−σ_p) λ • v`
(`gu4_yp_eq`); `σ_q = (tmq−t₁) / ((tmq−t₁) + (λ−1)(tmq−t₂))`, `y_q = p_in + σ_q (w − p_in) = b + σ_q λ • (c − b)`
(`gu4_yq_eq`); `0 < σ_p, σ_q < 1`. That `y_p` lies on the closed edge `p` of `X` is the **convexity capture**
`gu4_mem_edgeSegment_of_convex`: `U` is convex, contains `a ∈ p` and `y_p ∈ Θ ⊆ U`, and contains neither endpoint of `p`
(`disc_clear_vertex`), so `y_p`, which is on the line of `p`, is on the segment. (For U6's D9: `(1−σ_p) λ > 1 ⟺ t₃ > t₂`
and `σ_q λ > 1 ⟺ t₂ > t₁`, i.e. `x_pq` is strictly between `a` and `y_p` along `p`, between `b` and `y_q` along `q`; not
proved here since not a U4 leaf, but immediate from `gu4_yp_eq`/`gu4_yq_eq` with `field_simp`.)

Signs: `det (d_p) (p_out − w) = ((t₃ − t₂) + λ (t₂ − tmp)) · det d_p d_m` (`gu4_det_p_segC`, `gu4_Kp_pos`) and
`det (d_q) (w − p_in) = ((t₂ − t₁) + λ (tmq − t₂)) · det d_q d_m` (`gu4_det_q_segB`, `gu4_Kq_pos`) — coordinate-free,
valid for all `λ > 1`, exactly the plan's C4 in unnormalized parameters.

Labels of `X₀`: `gu4_X₀_mA/mB/mC/mD/mD_succ` (values of the four `m`-pieces), `gu4_lab_spec` (`X₀ (G11_lab m i) = X i`,
`X₀ (G11_lab m i + 1) = X (i+1)` for `i ≠ m`), `gu4_label_cases` (every label of `ZMod (k+3)` is `mA, mB, mC, mD` or
`G11_lab m i`), `gu4_lab_ne_pieces`, `gu4_lab_injective`, `gu4_p'_ne`, `gu4_q'_ne`, `gu4_p'_ne_q'`, `gu4_seg/int/edge_X₀_lab`,
`gu4_mem_mA..mD` (`y ∈ edgeSegment X₀ mA ↔ ∃ t ∈ [0, t₁], y = edgePoint X m t`, etc.). `X₁`: `gu4_X₁_of_ne`, `gu4_X₁_mA..mD`,
`gu4_seg/int/edge_X₁_eq` (labels `∉ {mB, mC}`), `gu4_edge_X₁_mB/mC`, `gu4_mem_segB/intB/segC/intC` (parametrizations).

Master lemmas: `gu4_meet_B` (an edge `d ∉ {mB, mC}` of `X₀` meeting `p_in + σ (w − p_in)` is `q'`, or `mA` with `σ = 0`),
`gu4_meet_C` (… `[w, p_out]` … is `p'`, or `mD` with `σ = 1`), `gu4_corner` (the bent edges meet only at `w`),
`gu4_intB_partner`/`gu4_intC_partner` (an interior point of a bent edge is on no other edge of `X₁` except `q'`/`p'`),
`gu4_apex_not_mem_X₀`, `gu4_pout_not_mem_segB`, `gu4_pin_not_mem_segC`. Genericity clauses: `gu4_X₁_regular`,
`gu4_X₁_tail`, `gu4_X₁_trans` (+ `_bent`), `gu4_X₁_triple`. Inner crossings: `gu4_classify_X₀/X₁` (labels of edges meeting
`U`), `gu4_mpiece_param`, `gu4_mpieces_disjoint`, `gu4_mpiece_p'/q'`, `gu4_inner_pair_X₀`
(`{i,j} = {mB,p'} ∨ {mC,q'} ∨ {p',q'}`), `gu4_inner_pair_X₁` (`{p',mC} ∨ {q',mB} ∨ {p',q'}`, 25 cases), and the crossing-point
identities `gu4_cp_X₀_mp/mq/pq : crossingPoint (xPair X₀_cross_*) = a / b / c`, `gu4_cp_X₁_pC/qB/pq = y_p / y_q / c`
(these six are likely what U5/U6 want for `Clean`, `BeforeOn`, `exists_Ψ₁`). Interior: `gu4_a/b/c_mem_intU`,
`gu4_yp/yq_mem_intU`, `gu4_segB/segC_sub_theta`, `gu4_segB/segC_sub_U`.

## 3. Helpers added (242 declarations, all `gu4_`-prefixed, all inside `namespace G11_Params`)

* **18 `noncomputable def`s** (abbreviations, flagged for the assembler since the rules speak of helper *lemmas*):
  `gu4_a gu4_b gu4_c gu4_tmp gu4_tmq gu4_dm gu4_v gu4_E gu4_α gu4_β gu4_γ gu4_pin gu4_m0 gu4_pout gu4_σp gu4_σq gu4_yp gu4_yq`.
  They are pure notation (each unfolds to a skeleton expression) and could be inlined if defs are unwanted.
* 224 theorems. Placement: block 1 (`/-! ### U4 helpers …` sections, ~1360 lines) sits immediately before the Unit-C header
  `/-! ### Unit C leaves — the moved polygon -/`; block 2 (`/-! ### U4 helpers (D3–D4) …`, ~200 lines) sits immediately
  before the D3 docstring of `inner_M₀` (it needs `triangle_sub_interior`, declared after the C leaves); five helpers
  (`gu4_cp_X₁_pq`, `gu4_classify_X₁`, `gu4_ad_ne`, `gu4_ad_m`, `gu4_inner_pair_X₁`) sit between `X₁_cross_pq` and `inner_M₁`
  because they cite `X₁_cross_pq`. **Keep this order when merging units.**
* General (unit-independent, reusable by U5/U6): `gu4_det_*` (det linearity), `gu4_cramer`, `gu4_eq_of_det_eq`,
  `gu4_remote_of_isCrossing`, `gu4_ne_of_remote`, `gu4_gen_regular/tail/trans/triple` (label-level reading of
  `Shadow.Generic` for `single ⟨j, hj, Y⟩`), `gu4_crossingPoint_mem_interior`, `gu4_crossingPoint_mem_pair`,
  `gu4_mem_edgeSegment_iff`, `gu4_mem_edgeInterior_iff`, `gu4_mem_edgeSegment_of_convex`, `gu4_sub_of_mem_edge`.

## 4. Mathlib / library pitfalls met (pinned Mathlib, Lean v4.34.0-rc2)

* `div_add_div_same` does not exist → `← add_div`. `if_pos`/`if_neg` are deprecated → `ite_eq_left`/`ite_eq_right`.
  `Set.mem_setOf_eq` deprecated → `Set.mem_ofPred_eq`. `push_neg` deprecated (→ `push Not`); I used `simp only [not_or]`.
* `← Nat.cast_succ` produces the `.succ` form (blocks later `rw`); use `← Nat.cast_add_one`.
* `regularPair_of_det_ne_zero` exists both as `SM.regularPair_of_det_ne_zero` (SoftRotation) and
  `SM.Link.regularPair_of_det_ne_zero` (Smoothing) — qualify it. `Smoothing.zcast_sub_self` is `SM.Link.Smoothing.…`
  (reachable through the skeleton's `open SM.Link`).
* `∃ σ, 0 ≤ σ ∧ σ ≤ 1 ∧ y = p + σ • v` elaborates `σ : ℕ` (numeral default; `ℕ` acts on `Plane`) — always write `∃ σ : ℝ`.
* With `variable (π : G11_Params C)`, a lemma whose *statement* does not mention `π` does not get `π` in scope for its
  proof; bind `(π : G11_Params C)` explicitly (shadowing is accepted), or `(_π …)` if unused. Lemmas taking `π` first must
  be called `π.gu4_foo args` (writing `gu4_foo _ h` makes `_` the `π`).
* `Shadow.single_crossingPoint` takes the `PolyComp` explicitly (`Shadow.single_crossingPoint _ hΓ x`);
  `π.M₀.Γ.crossingPoint y` rewrites to `SM.crossingPoint (singleCrossingEquiv _ y)` through it by defeq.
* `SM.Generic X₀` (G1 ∧ G2) is FALSE for the subdivided polygons (collinear flat vertices); only the shadow-level
  `Shadow.Generic` (with `Regular`, zero turns allowed) is available for `X₀, X₁` — all uniqueness arguments here go through
  the frame functionals or `Generic.common_point_unique`, never `SM.crossingPoint_unique`.
* `field_simp` sometimes closes the goal, making a following `ring` an error ("no goals") — check each use.

## 5. Verification log

* `lake env lean ../drafts/rlane2/G11_U4.lean`: exit 0; 40 `declaration uses sorry` (exactly the 40 non-U4 leaves); no
  other message.
* `diff G11_Skeleton.lean G11_U4.lean | grep '^<'`: `9 <   sorry` and nothing else.
* `#print axioms` (scratch copy): `X₁_cross_pC`, `X₁_cross_qB`, `X₁_cross_iff`, `X₁_sign_pC`, `X₁_sign_qB`, `gu4_convex_U`,
  `gu4_Δ_sub_U` → `[propext, Classical.choice, Quot.sound]`; `X₁_generic`, `X₁_cross_pq`, `inner_M₀`, `inner_M₁` → additionally
  `sorryAx`, inherited only from the U3 black boxes listed in §1.
