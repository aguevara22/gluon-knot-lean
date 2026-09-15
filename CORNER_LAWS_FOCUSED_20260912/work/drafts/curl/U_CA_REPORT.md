# U_CA_REPORT — Unit CA (U7: record assembly + window bookkeeping) of cf:lem-curl

Prover subagent, 2026-09-14. File: `work/drafts/curl/U_CA.lean` (copy of `Skeleton_FINAL.lean`; the diff
against the skeleton removes exactly the eight `  sorry` lines of this unit and adds 585 lines of proofs and
`ca_`-helpers — no definition, structure, statement, name or docstring touched; every `theorem`/`def`/`structure`
head of the skeleton is byte-identical, including the `:= by` lines).

Check: `cd work/lean && lake env lean ../drafts/curl/U_CA.lean` → **0 errors**, ≈9 s. The only non-`sorry` warning
is the skeleton's inherited `<;>` linter note (line 567, `cModel_one`). `grep -c sorry`: **56 → 48** (8 leaves closed;
the 48 = 46 leaf sorries of the other units + the two prose mentions in the header and the §7 banner).
`#print axioms` of each of the eight leaves: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
`#print axioms SM.cf_lem_curl` = `[propext, sorryAx, Classical.choice, Quot.sound, SM.lp_lm]` (the `sorryAx` is the
other units'), `SM.CurlData` = `[propext, Classical.choice, Quot.sound, SM.lp_lm]` as in the skeleton.

## Leaves proved (8 / 8)

| leaf | line | proof idea |
|---|---|---|
| `cycBetween_ext_of_insert_pair` | 950 | triples with a repetition: both sides false (`not_cycBetween_self_*`). Distinct triples: at least one entry is old (only two inserted elements); rotate it to the front (`ca_cycBetween_rot`, an unconditional iff) and apply the `core` case split: (old, old, old) `hold`; (old, old, k) rotate to `(b, c, a)` and `hgap`; (old, k, old) `hgap`; (old, k₁, k₂) `hpair`; (old, k₂, k₁) both false by `ca_cycBetween_swap` (for distinct reals exactly one of the two cyclic orders holds) + `hpair`. All-inserted distinct triple: pigeonhole contradiction |
| `cycBetween_fract_gap` | 1086 | every `τ ∈ [0,1)` off the closed window has a representative `σ ∈ (s₂ − 1, s₁)` with `fract σ = τ` (`ca_exists_rep`: `σ := s₂ − 1 + fract(τ − (s₂ − 1))`); `σ, σ', x, y` all lie in the unit interval `[s₂ − 1, s₂)`, on which `fract` is a rotation preserving cyclic betweenness (`ca_cycBetween_fract`); then `σ, σ' < s₁ < x, y` and `ca_cycBetween_congr_mid` (moving the middle entry without crossing the ends). Works when the window wraps past an integer — the rotation lemma absorbs it |
| `cycBetween_fract_pair` | 1101 | same representative and rotation; `σ < s₁ < x < y` is the first disjunct |
| `exists_carriedAssembly` | 1455 | `τ' := ca_τ'` (old parameter on `(oldVisit w).1`, `fract q₁` on `underVisit kink`, `fract q₂` on `overVisit kink`); the eight `RecordCarried` clauses are the helpers `ca_τ'_mem`, `ca_τ'_inj`, `ca_twin_eval`, `ca_doubles`, `ca_transverse`, `ca_order`, `ca_sign_eq` (below); `one` from `K.c_eq` + `carried.one`; the three `CarriedAssembly` clauses are `ca_τ'_old/under/over` by unfolding the `dite`/`ite` |
| `deriv_eq_of_offWindow` | 1475 | `ca_deriv_eq_of_offWindow`: shift `t` by an integer into `[s₂ − 1, s₂)` (`ca_exists_shift_Ico`); off the open window it lands in `[s₂ − 1, s₁]`, a nondegenerate closed interval (`ca_window_short`: `s₂ − 1 < s₁` from `β − α < 1`) every point of which is `OffWindow` (`ca_offWindow_of_mem_Icc`), so `F' = F` on it; equal derivatives there by `UniqueDiffWithinAt.eq_deriv` + `uniqueDiffOn_Icc` + `HasDerivWithinAt.congr` (`ca_deriv_eq_of_eqOn_Icc`, endpoints included); back to `t` by `deriv_eq_add_int` |
| `doublePoints_diff_eq` | 1485 | a parameter with a shift in the closed window puts the point in `Δ` (`new_in_disc` / `old_in_disc`), so for `q ∉ Δ` both parameters are `OffClosedWindow` and `F' = F` at both (`unchanged`) — both inclusions |
| `one_neg_u_of` | 1517 | existence: `fract t₀` of the window tangency `new_one_neg_u` (`ca_loop_fract`, `ca_deriv_loop_fract`); uniqueness: a parameter with a shift in the closed window is `t₀` by the `∃!`, hence equal to `fract t₀` (`ca_fract_add_int_eq`); a parameter off the closed window has `F' t = F t ∈ Δ` and `deriv F' t = deriv F t`, contradicting `tails_no_neg_u` |
| `one_double_of` | 1551 | both parameters with shifts in the closed window: distinct shifts (`ca_eq_of_add_int_eq`), `only_double` gives `{q₁, q₂}`, and `F'(q₁) = F'(q₂)` (`double`); one parameter off the closed window: `ca_no_double_off` — the other is on the open window (`arc_off_rest`) or off it too, giving a double point of `F` in `Δ`, hence on the arc (`meets_arc`), which carries no occurrence (`no_double`) |

All eight statements are true as written; no hypothesis is missing. (The sanity probes were the cyclic-order ones,
checked on the wrap-around example of PLAN_FINAL §3 — `x = 0.9, y = 1.1`, `τ ∈ [0.2, 0.8]` — before choosing the
"representative in `(s₂ − 1, s₁)` + rotation" route, which needs no case split on `⌊x⌋` vs `⌊y⌋`.)

## Leaves left

None in this unit.

## Helpers added (45, all `ca_`-prefixed, lowercase; each before the first leaf that uses it, in `namespace Curl` §7)

Before `cycBetween_ext_of_insert_pair` (lines 928-948): `ca_cycBetween_rot` (`cycBetween a b c ↔ cycBetween b c a`,
unconditional), `ca_cycBetween_swap` (distinct `a b c`: `cycBetween a c b ↔ ¬ cycBetween a b c`), `ca_old_or_inserted`
(`(a ≠ k₁ ∧ a ≠ k₂) ∨ (a = k₁ ∨ a = k₂)`).

Before `cycBetween_fract_gap` (lines 1003-1084): `ca_cycBetween_congr_mid` (middle entry moves without crossing the
ends), `ca_cycBetween_fract` (`a b c ∈ Ico C (C+1)` ⇒ `cycBetween (fract a) (fract b) (fract c) ↔ cycBetween a b c`;
8-case `linarith` sweep), `ca_exists_rep` (`s₁ < s₂`, `τ ∈ [0,1)`, `OffClosedWindow` ⇒ `∃ σ ∈ Ioo (s₂−1) s₁, fract σ = τ`;
note it does **not** need `s₂ − s₁ < 1`), `ca_mem_unit_of_window`, `ca_mem_unit_of_gap` (memberships in
`Ico (s₂−1) (s₂−1+1)`).

Before `exists_carriedAssembly` (lines 1111-1453) — the window/period bookkeeping, shared with Unit A:
- periodicity through `Int.fract`: `ca_fract_eq_add_int`, `ca_loop_fract (L : SmoothLoop)`, `ca_deriv_loop_fract`,
  `ca_fract_add_int_eq` (`t ∈ [0,1)` ⇒ `fract (t + n) = t`), `ca_eq_of_add_int_eq`, `ca_fract_ne_of_lt`;
- windows: `ca_window_or_off`, `ca_open_or_off` (excluded-middle splits), `ca_offWindow_of_offClosed`,
  `ca_offWindow_add_int`, `ca_exists_shift_Ico`, `ca_offWindow_of_mem_Icc` (`t ∈ [s₂−1, s₁]` ⇒ `OffWindow`);
- derivatives: `ca_deriv_eq_of_eqOn_Icc` (general), `ca_det_swap`, `ca_window_short (S) (sc)`,
  **`ca_deriv_eq_of_offWindow (S) (sc)`** (the content of the leaf `deriv_eq_of_offWindow`, needed here first for
  `transverse`/`sign_eq`);
- the old occurrences: `ca_τ_offClosedWindow`, `ca_F'_τ`, `ca_deriv_F'_τ`, `ca_τ_ne_fract`, `ca_fract_q_ne`;
- the record: `def ca_τ' (S) (sc) (K) : K.D'.Γ.Visit → ℝ` (the only `def`), `ca_τ'_old`, `ca_τ'_under`, `ca_τ'_over`,
  `ca_visit_cases` (old / under-kink / over-kink trichotomy, from `visit_eq_over_or_under`), `ca_old_of_ne`,
  `ca_τ'_mem`, `ca_τ'_inj`, `ca_twin_eval`, `ca_doubles_off`, `ca_doubles`, `ca_transverse`, `ca_visitCoord_inj`
  (`c = 1` ⇒ `compOf v = compOf w` by `Fin.ext` + `omega`, then `visitCoord_injOn`), `ca_order`
  (`cycBetween_ext_of_insert_pair` with `κ₁ = ca_τ'`, `κ₂ = D'.visitCoord`, `k₁ = underVisit kink`,
  `k₂ = overVisit kink`; `hold` = `carried.order` + `order_old`, `hgap` = `cycBetween_fract_gap` (`x = qᵢ`, `y = t₀`)
  + `KinkLocation.gap` + `order_gap`, `hpair` = `cycBetween_fract_pair` + `order_pair`), `ca_sign_eq`.

Before `one_double_of` (line 1538): `ca_no_double_off`.

Duplicates the assembler may dedupe with Unit HT: `ca_deriv_eq_of_eqOn_Icc` = HT's `ht_deriv_eq_of_eqOn_Icc`
(same statement); `ca_offWindow_of_mem_Icc` is the `[s₂ − 1, s₁]` twin of HT's `ht_offWindow_of_mem_Icc`
(`[s₂, s₁ + 1]`). The §8 skeleton lemmas `τ_offClosedWindow`, `OffClosedWindow.offWindow`, `F'_τ`, `F'_fract` come
*after* §7, so this unit carries its own copies (`ca_τ_offClosedWindow`, `ca_offWindow_of_offClosed`, `ca_F'_τ`,
`ca_loop_fract`); the assembler may hoist either way.

## Mathlib pitfalls (pin 85e3a25e, Lean v4.34.0-rc2)

1. `h.not_lt` for `h : a < b` on `ℝ` fails after `unfold cycBetween` ("environment does not contain `Real.lt.not_lt`":
   dot notation resolves through `Real.lt`); use `lt_asymm h` (or `not_lt.mpr h.le`).
2. `Int.fract_add_int` and `Int.floor_add_int` are **not** available under these imports; use `Int.fract_eq_iff`
   (`fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z, a − b = z`), `Int.fract_eq_fract` (`↔ ∃ z, a − b = z`), `Int.self_sub_floor`,
   `Int.floor_add_one`, `Int.floor_le_floor`, `Int.lt_floor_add_one`. `rw [Int.fract]` unfolds to `x − ⌊x⌋` (as the
   skeleton's `F'_fract`).
3. Deprecations (warnings only, but avoided): `dif_pos/dif_neg/if_pos/if_neg` → `dite_eq_left/dite_eq_right/
   ite_eq_left/ite_eq_right` (same shapes); `push_neg` → `push Not`; `Set.mem_diff` → `Set.mem_sdiff`;
   `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`. For `q ∈ doublePoints γ \ Δ` (and `∩ Δ`) no simp is needed:
   `rintro ⟨⟨s, t, hs, ht, hst, rfl, hq⟩, hΔ⟩` and `refine ⟨⟨s, t, …⟩, hΔ⟩` work by defeq.
4. `linarith` does not read `x ∈ Ico a b` / `Ioo` memberships; destructure (`obtain ⟨h1, h2⟩ := hx`) or pass `hx.1, hx.2`.
   Casts: keep one form (`(⌊x⌋ : ℝ)` vs `((-⌊x⌋ : ℤ) : ℝ)`) or `push_cast` in the hypothesis too, otherwise `linarith`
   treats them as different atoms.
5. `rcases … with rfl` on `v = K.D'.underVisit K.ri.kink` (local `v`) substitutes fine; after it, `rw [ca_τ'_under]`
   matches syntactically. For the kink crossing `x = K.ri.kink`, `subst hx` then `K.kink_neg` rewrites.
6. `K.oldVisit.symm_apply_apply v` closes `K.oldVisit.symm ⟨(K.oldVisit v).1, (K.oldVisit v).2⟩ = v` directly
   (Subtype eta is definitional); `(K.oldVisit v).2 : (K.oldVisit v).1.1 ≠ K.ri.kink` is the `dite_eq_right` proof.
7. `SmoothRegularLoop` dot-notation (`sc.F'.eq_add_int`, `.deriv_eq_add_int`, `.differentiable`) reaches the
   `SmoothLoop` lemmas; a lemma stated for `L : SmoothLoop` rewrites `sc.F'.γ (Int.fract x)` (unifies `L := sc.F'.toSmoothLoop`).

## For the assembler / executor

- Unit CA's text is lines 925-1565 of `U_CA.lean` (`/-! ### Unit C …` through the end of `one_double_of`); the
  statements inside are the skeleton's. Splicing into the assembled file: copy the whole span (helpers + leaf bodies);
  it references only Mathlib, the accepted `cycBetween`/`Diagram`/`SmoothLoop` API, the skeleton's §5-§6 definitions
  and the package fields — no other unit's leaf.
- The leaf `deriv_eq_of_offWindow` is `by exact ca_deriv_eq_of_offWindow S sc ht`; the real proof sits before
  `exists_carriedAssembly` because `RecordCarried.transverse`/`sign_eq` for the old occurrences need the velocities of
  `F'` at `τ v` (off the closed window) to be those of `F`.
- `ca_τ'` reads the under occurrence of the kink at `fract q₁` (earlier parameter, met first) and the over occurrence at
  `fract q₂`, matching `SmoothCurl.double_neg : det (F'' q₂) (F'' q₁) < 0`, `KinkInsertion.kink_neg`, `order_pair`
  (under first) and `Diagram.sign` — `ca_sign_eq` at the kink is `sign_neg double_neg` = `kink_neg` with no sign flip.
- The record's `doubles` clause at a window endpoint (`s + n = s₁`) is handled by the `OffClosedWindow` split: a
  parameter with a shift in the *closed* window goes to `only_double`; one without goes to `ca_doubles_off`, which
  needs only `unchanged` (open-window hypothesis) at the other parameter — no separate endpoint case.
