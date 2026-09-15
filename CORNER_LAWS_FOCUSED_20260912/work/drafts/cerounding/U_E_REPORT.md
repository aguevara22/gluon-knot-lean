# U_E_REPORT — unit E (existence of the choices), ce:rounding (row 89)

File: `work/drafts/cerounding/U_E.lean` (1267 lines; was the byte-identical copy of `Skeleton_FINAL.lean`, 1103 lines).
Compile: `cd work/lean && lake env lean ../drafts/cerounding/U_E.lean` — exit 0, **0 errors**.
`grep -c sorry`: 37 → **33** (the 4 leaves of unit E; the 4 remaining docstring mentions are unchanged).
"declaration uses sorry" warnings: 33 (skeleton) → **29**.  Other warnings: only the pre-existing cosmetic ones
(2 unused simp args in `chart_add_disp` at 321-322; 5 `letI` style hints at 566-650), untouched.
`#print axioms SM.ce_rounding` = [propext, sorryAx, Classical.choice, Quot.sound] (unchanged; sorryAx from the other units).
Relative to `Skeleton_FINAL.lean` the diff REMOVES exactly four lines, each `  sorry`; no statement, name, docstring or
definition was changed (checked with `diff Skeleton_FINAL.lean U_E.lean | grep '^<'`).

## Leaves proved (4 of 4)

| leaf | line | axioms | proof |
|---|---|---|---|
| `cusp_image_injective` | 915 | no sorryAx | `k ≠ k'` with both parameters in `Ico 0 1` gives `¬ SameParam` (`SameParam.eq_of_mem_Ico` + `Subtype.ext`), so a common image is `IsDoubleOf L.projLoop k.1 k'.1`; `CuspedProjection.not_isCusp_of_isDouble L h` contradicts `k.2.2`. |
| `exists_gap` | 926 | no sorryAx | `Fintype L.cuspSet` from `h.cusps_finite.fintype`; `S := univ.filter (p.1 ≠ p.2)`; if `S` nonempty, `Finset.exists_min_image` on the pair-distance, positive by `dist_pos` + `cusp_image_injective`, `gap := min/4`; if `S` empty, `gap := 1` vacuously. |
| `exists_remote_clearance` | 979 | **no sorryAx** | The evaluation `q ↦ xzOf (L.T q.1) q.2` is continuous on `Param c = Fin c × ℝ` (`continuous_prod_of_discrete_left`, `(L.projLoop j).continuous`).  Compact parameter set `Kp := {i} ×ˢ (Icc (t₀−1/2) (t₀+1/2) ∩ {t ∣ ∀ n, t+n ∉ J}) ∪ {j ≠ i} ×ˢ Icc 0 1` (`isCompact_Icc.inter_right` of the closed `⋂ n, (·+n)⁻¹' Jᶜ`; `isCompact_singleton.prod`, `(Set.toFinite _).isCompact.prod`, `.union`, `.image`).  The cusp image is not in `F '' Kp`: a preimage `q` is `¬ SameParam k.1 q` (first piece: `q.2 = t₀ + n` would put `t₀ = q.2 + (−n) ∈ J`, `t₀_mem_J`; second piece: `q.1 ≠ i`), hence a double point at the cusp, excluded by `not_isCusp_of_isDouble`.  `Metric.isOpen_iff` on the open complement of the compact (closed) image gives a ball of radius `ε` missing it — no `Nonempty` side condition, unlike `infDist_pos_iff_notMem_closure`.  Every remote `q` has a representative in `Kp` (`round (t₀ − q.2)` + `abs_sub_round` for the own circle, `Int.fract` for the others; `L.xz_add_int`), so `ε ≤ ‖p − p₀‖ ≤ lip · ‖chart p‖` (`ue_norm_unchart_sub_le` with `unchart_chart`); `d := ε / (2 lip)`. |
| `exists_eta` | 1056 | sorryAx via `rect_subset_closedBall` (U-G black box) only | `ε₁ := min 1 (min (d/2) (ρ₀/(2 lip)))`; `Metric.continuousAt_iff` for `g.u` at `t₀` (`u_t₀`, `u_smooth`) gives `η₁`; `η := min (η₁/2) (δ/2)`.  Then `|u(t₀ ± η)| < ε₁`, so `M η < ε₁ ≤ 1` (`abs_min_le_max_abs_abs`, `abs_max_le_max_abs_abs`, `max_lt`), `M² ≤ M`, `M³ ≤ M`, `radius η ≤ 2M < 2ε₁ ≤ d`; for `w ∈ rect η`, `‖w‖ ≤ radius η` (`rect_subset_closedBall`) and `‖unchart w − p₀‖ ≤ lip · ‖w‖ ≤ lip · 2M < ρ₀`. |

## Helpers added (2, before `exists_remote_clearance`, namespace `SM.SpatialLink`, both sorry-free)

- `ue_lip_pos (g : L.GermData i t₀) : 0 < |g.A| * (2 + |g.y₀|)` (line 947).
- `ue_norm_unchart_sub_le (g : L.GermData i t₀) (w : Plane) : ‖g.unchart w - xzOf (L.T i) t₀‖ ≤ |g.A| * (2 + |g.y₀|) * ‖w‖`
  (line 952): the inverse chart is Lipschitz in the sup norm, measured from the cusp image `unchart 0 = xzOf (L.T i) t₀`
  (componentwise: `|A w₁|` and `|y₀ A w₁ + (2A/3) w₂|`, via `norm_prod_le_iff`, `norm_fst_le`, `norm_snd_le`, `abs_add_le`).
  Used by both `exists_remote_clearance` and `exists_eta`.

No new definitions (the Lipschitz constant is written out as `|g.A| * (2 + |g.y₀|)`), no changes outside the four bodies.

## Mathlib / Lean pitfalls met

- `₊` and `₋` are NOT identifier characters in Lean 4 (`hu₋` is a parse error that silently garbles the rest of the
  declaration; use `huL`/`huR`).  Subscript digits `₀…₉` are fine.
- `continuous_add_right` is deprecated in this Mathlib → `continuous_add_const`.
- `div_lt_iff`/`le_div_iff` → the `₀` versions `div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c`,
  `le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b`.
- `Metric.infDist_pos_iff_notMem_closure` needs `s.Nonempty`; the plan's route was replaced by
  `Metric.isOpen_iff.mp hK.isClosed.isOpen_compl` (no nonemptiness needed; `IsCompact.isClosed` needs `T2Space`, fine on `Plane`).
- `k.2` for `k : L.cuspSet` elaborates directly against `k.1.2 ∈ Ico 0 1 ∧ L.IsCusp k.1.1 k.1.2` (a `have` with that type
  ascription works; `Set.mem_setOf_eq` is definitional).
- `CuspedProjection.not_isCusp_of_isDouble` has `L` EXPLICIT (from `variable (L)`): call it as
  `CuspedProjection.not_isCusp_of_isDouble L h hd`, not `h.not_isCusp_of_isDouble hd`.
- After `simp only [GermData.unchart, …, GermData.z₀]` the field is unfolded to `(L.T i t₀).2.2`, so a `rw [show …]`
  must be phrased on the unfolded term.
- `Prod.norm_def`/`norm_prod_le_iff` (sup norm on `ℝ × ℝ`) are in `Mathlib.Analysis.Normed.Group.Constructions`;
  `norm_fst_le`/`norm_snd_le` there take the pair explicitly.
- The linter prefers `have` over `haveI` for the `Fintype` instance of a Prop goal (a warning only; `have` used).

## For the assembler / executor

- The four bodies are self-contained; the only cross-unit dependency is `exists_eta` → `GermData.rect_subset_closedBall`
  (U-G leaf, used as stated).  `exists_remote_clearance`, `exists_gap`, `cusp_image_injective` and both helpers are
  sorry-free already (`#print axioms` = [propext, Classical.choice, Quot.sound]).
- The proofs do NOT use `δ ≤ 1/3` (the plan's CE-R10 note on compactness of the remote set): compactness comes from
  the window `Icc (t₀−1/2) (t₀+1/2)` ∩ a closed set; the window's nonemptiness is never needed because the ball argument
  is on the open complement.  So the leaves hold verbatim even if `GermData.δ_le` were dropped.
- The helper block (2 lemmas) sits between `exists_gap` and `exists_remote_clearance`, inside `namespace SpatialLink`
  after `end Choices`, with the `variable (L : SpatialLink c)` of that namespace.  When merging with the other units'
  copies, take lines 912-1105 of `U_E.lean` (from the docstring of `cusp_image_injective` to the end of `exists_eta`).
- Scratch used for iteration: lines 1-397 of the file (header + §4.1-4.2) + the block + `end SpatialLink / end / end SM`
  (~7 s per compile); full compile of `U_E.lean` takes ~9 s here.
