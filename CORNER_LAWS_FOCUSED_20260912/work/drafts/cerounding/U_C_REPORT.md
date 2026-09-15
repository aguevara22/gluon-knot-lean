# U_C_REPORT — unit C "one cusp" (ce:rounding, row 89)

File: `work/drafts/cerounding/U_C.lean` (byte-identical copy of `Skeleton_FINAL.lean` + the 7 leaf bodies
of unit C + 5 helpers).  Compile: `cd work/lean && lake env lean ../drafts/cerounding/U_C.lean` — exit 0,
0 errors.  `grep -c sorry`: 37 before → 30 after (the 7 leaf `sorry`s; the other occurrences are the 4
mentions in the header comments + the 26 leaves of units P, G, L, E).  `declaration uses sorry` warnings
after: lines 221 225 230 (U-P), 260 313 326 365 369 372 379 384 389 393 (U-G), 715 761 789 795 802 808
814 838 846 (U-L), 1042 1047 1055 1064 (U-E) = 26 = 33 − 7; none in the unit-C region (462–668).
No new warnings (the remaining ones are the skeleton's: unused simp args at 321–322 in `chart_add_disp`,
`letI` style hints in `Choices`).  Statements, names, docstrings untouched.

## Leaves proved (7 / 7) — namespace `SM.SpatialLink.CuspChoice`

| leaf | line | proof |
|---|---|---|
| `chi_eq_zero_of_notMem` | 462 | `periodicBump_eq_zero ch.r_pos ch.r_lt_half`; a translate with `|t − t₀ − n| < r` would put `t + (−n)` in `(a, b)` since `r < η` (`abs_sub_lt_iff`, `unfold a b`, `push_cast`, `linarith`). |
| `isDisc_U` | 552 | `⟨uc_convex_U, (rect_isCompact η).image unchart_continuous, ⟨_, uc_center_mem_interior_U⟩⟩`. |
| `center_mem_interior_U` | 556 | `uc_center_mem_interior_U`. |
| `arc_in` | 573 | `mem_U_iff` + `chart_proj (Icc_subset_J ht)`; `u² ∈ [−M², 2M²]` from `abs_u_le_M` via `sq_le_sq'` + `nlinarith`; `u³ ∈ [u₋³, u₊³]` from `u_mem_Icc_of_mem` and `(Odd.strictMono_pow _).monotone`. |
| `clean` | 590 | `norm_chart_le_of_mem_U` contradicts `remote` unless `q.1 = k.1.1 ∧ ∃ n, q.2 + n ∈ J`; move to `q.2 + n` by `(L.projLoop _).eq_add_int`; `chart_proj` puts `u(q.2+n)³ ∈ [u₋³, u₊³]`, `StrictMono.le_iff_le` of the cube gives `u ∈ [u₋, u₊]`, then `mem_Icc_of_u_mem`. |
| `arc_simple` | 614 | equality ⇒ point in `U` (`arc_in`) ⇒ `clean` ⇒ both parameters in `Icc a b ⊆ J` with equal projections ⇒ `proj_injOn_J` ⇒ `q.2 + n = t` ⇒ `SameParam (k.1.1, t) q` with witness `−n`, contradiction. |
| `chi_eq_zero_on_collar` | 632 | `periodicBump_eq_zero`; `s = t − t₀ ∈ (−η, −r) ∪ (r, η)`; for `m ≤ −1`, `m = 0`, `1 ≤ m` separately `r ≤ |s − m|` by `le_abs` + `linarith` using `η < δ ≤ 1/3`, `r < η` (so `1 − η > r`); integers split by `lt_trichotomy n 0` + `omega` + `exact_mod_cast`. |

## Helpers added (all `theorem`, immediately before `isDisc_U`, same namespace)

- `uc_unchart_convex_comb (w w') (hab : a + b = 1) : unchart (a•w + b•w') = a•unchart w + b•unchart w'`
  (`subst b = 1 − a`; `ext <;> simp only [GermData.unchart, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
  Prod.smul_snd, smul_eq_mul] <;> ring`).
- `uc_convex_U : Convex ℝ ch.U` (direct from the definition of `Convex`, `rect_convex`, the helper above).
- `uc_U_eq_preimage : ch.U = ch.g.chart ⁻¹' ch.g.rect ch.η` (from `chart_unchart`/`unchart_chart`).
  NOTE: this duplicates `mem_U_iff`, which in the frozen order is declared AFTER `isDisc_U`; if the
  assembler may reorder, `Set.ext fun p => ch.mem_U_iff p` replaces the proof and the helper can go.
- `uc_mem_interior_U_of_chart : chart p ∈ Ioo (−M²) (2M²) ×ˢ Ioo (u₋³) (u₊³) → p ∈ interior U`
  (`preimage_interior_subset_interior_preimage chart_continuous`, `interior_prod_eq`, `interior_Icc`).
- `uc_center_mem_interior_U : xzOf (L.T k.1.1) k.1.2 ∈ interior ch.U` (`chart_proj t₀_mem_J`, `u_t₀`;
  `M_pos`, `uMin_neg`, `uMax_pos`; `zero_pow`, `Odd.pow_neg`, `pow_pos`).

## Black boxes used (other units' leaves, as statements)

U-P: `periodicBump_eq_zero`.  U-G: `chart_proj`, `uMin_neg`, `uMax_pos`, `u_mem_Icc_of_mem`,
`mem_Icc_of_u_mem`, `abs_u_le_M`.  Hence `#print axioms` of every unit-C leaf currently lists `sorryAx`
transitively; the unit-C bodies themselves contain no `sorry` (no `declaration uses sorry` at 462–668).
Also used (proved in skeleton/library): `M_pos`, `rect_convex`, `rect_isCompact`, `chart_unchart`,
`unchart_chart`, `chart_continuous`, `unchart_continuous`, `t₀_mem_J`, `u_t₀`, `proj_injOn_J`,
`Icc_subset_J`, `norm_chart_le_of_mem_U`, `mem_U_iff`, `remote`, `r_pos`, `r_lt`, `r_lt_half`, `η_pos`,
`η_lt`, `δ_le`, `SmoothLoop.eq_add_int` (via `projLoop`, `projLoop_γ` is `rfl`).

## Truth audit

All 7 leaves are TRUE as stated; no hypothesis is missing.  `chi_eq_zero_on_collar` needs
`1 − η > r`, which follows from `η < δ ≤ 1/3` and `r < η` (fields of `CuspChoice`/`GermData`), exactly as
PLAN_FINAL §4 says.  `clean` needs `remote` in the normalized sup-norm — matches `norm_chart_le_of_mem_U`.

## Mathlib / Lean pitfalls met (v4.34.0-rc2 pin)

- The negation-pushing tactic is `push Not at h` (the skeleton's convention), not `push_neg`.
- `Odd.pow_neg` is an `alias` of `Odd.pow_neg_iff` (Mathlib/Algebra/Order/Ring/Basic.lean:175); grepping
  for `theorem Odd.pow_neg` finds nothing.
- `interior_Icc` needs `[NoMinOrder] [NoMaxOrder]` — fine on `ℝ`; `interior_prod_eq` for the product.
- `CuspChoice.a`/`b` are plain `def`s: `t ∈ Set.Icc ch.a ch.b` is accepted where
  `t ∈ Set.Icc (k.1.2 − η) (k.1.2 + η)` is expected (type ascription on a `have`), and `unfold a b` works
  inside the namespace.
- `Set.mem_prod.mp hq` is the safe way to split membership in `s ×ˢ t` (defeq works too).
- Integer translates: split with `lt_trichotomy n 0`, `omega` for `n ≤ −1` / `1 ≤ n`, then
  `exact_mod_cast` to `ℝ`; `le_abs.mpr (Or.inl/inr _)` + `linarith` avoids case analysis on `abs`.
- Iteration tip: a copy of the file truncated after `end CuspChoice` (+ `end SpatialLink`, `end`, `end SM`)
  compiles in ~8 s versus ~60 s for the full file.
