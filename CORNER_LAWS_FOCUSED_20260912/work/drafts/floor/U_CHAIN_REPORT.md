# U_CHAIN_REPORT — unit U-CHAIN (`ucurl_`), rows 99/100 floor lane

Prover: Claude (subagent), 2026-09-15.  File: `work/drafts/floor/U_CHAIN.lean` (copy of
`Statements_FINAL.lean` + helpers + the proof of the unit's one leaf).

Check: `cd work/lean && lake env lean ../drafts/floor/U_CHAIN.lean` — **0 errors**, ~11 s warm.
Warnings: 22 `declaration uses sorry` (the other units' leaves, unchanged) and one
`unusedVariables` warning on the frozen binder `hu` of `ucurl_exists_curled` (the unit-length
hypothesis is not needed: `CurlSite.tangent_at` supplies `u = normalize (deriv F.γ t₀)`; the
statement is frozen, so the warning stays).

`grep -c sorry`: Statements_FINAL.lean 25 lines (23 declarations + 2 comment mentions) →
U_CHAIN.lean 24 lines (22 declarations + 2 comment mentions).  `diff Statements_FINAL.lean
U_CHAIN.lean` has exactly two hunks: the inserted helper block (after the §8.6 header, before the
leaf's docstring) and the leaf's `sorry` body replaced by the proof.  No definition, structure,
statement, name or docstring changed.

`#print axioms SM.ucurl_exists_curled` = `[propext, Classical.choice, Quot.sound, SM.lp_lm]`
(`lp_lm` enters only through `P`, as in the rest of the lane).

## 1. Leaves

| leaf | status |
|---|---|
| `ucurl_exists_curled` | **PROVED** |

Nothing left in this unit.  No leaf is false as stated; no hypothesis had to be strengthened.

## 2. Helpers added (all prefixed `ucurl_`, placed immediately before the leaf in the same section)

Explicit binders `{C : PolyComp} {D : PolygonDiagram C} {ε : ℝ}` are written on every helper (no
`section`/`variable`), so the block can be merged verbatim.

Subdivision facts on an arbitrary `RoundingWitness` (from `a_zero`, `a_last`, `a_lt_b`, `b_lt_a`):
- `ucurl_a_mono` — `i ≤ j ≤ k → a i ≤ a j` (`Nat.le_induction`).
- `ucurl_a_nonneg`, `ucurl_b_lt_one` — `0 ≤ a j`, `b j < 1`.
- `ucurl_Icc_subset_Ico` — `Icc (a j) (b j) ⊆ Ico 0 1`.
- `ucurl_junction_disjoint` — a point of the closed junction `i` is not in the open junction `j ≠ i`.
- `ucurl_int_eq_zero` — `t, t + n ∈ Ico 0 1 → n = 0` (pure arithmetic; the "mod 1" reductions).

Analysis:
- `ucurl_antitone_of_pieces` — constant left of `a`, constant right of `b`, `AntitoneOn` on `[a,b]`
  ⇒ `Antitone` on `ℝ` (clamping `t ↦ max a (min t b)`).
- `ucurl_turn_pos` — `0 < deriv (θ j) t₀` ⇒ `0 < principalTurn C.P j`: a negative turn gives
  `StrictAntiOn (θ j)` on the junction (`θ_strict.2`), globally antitone with `θ_const_left/right`,
  hence `deriv ≤ 0` by Mathlib's `Antitone.deriv_nonpos`.  (Avoids the `AccPt` bookkeeping of
  `HasDerivWithinAt.nonpos_of_antitoneOn`.)
- `ucurl_mem_interior_cornerDisc` — `eucDist p (C.P i) < ε → p ∈ interior (cornerDisc C ε i)`
  (`isOpen_lt (E_continuous_eucDist _) continuous_const`, `mem_interior_iff_mem_nhds`).
- `ucurl_junction_mem_interior` — for `Round C D ε h` (= `roundedWitness h` definitionally: `Lε.γ =
  curveMap C ε`, `a = CornerRounding.a C ε`, `b = CornerRounding.b C ε`, all by `show`), every
  interior junction parameter `t ∈ Ioo (a j) (b j)` has `Lε.γ t ∈ interior (cornerDisc C ε j)`:
  `curveMap_on_junction` (1668) + `juncArc_mem_open_disc` (1104) with `s = (t − a j)Λ/ℓ_j ∈ (0,1)`
  (`b_sub_a`, `ℓ_pos`, `Λ_pos`) and `A0 j + ε • dirOf (θu j) = C.P j` (`dirOf_θu D.regular j`).
  This is the ONLY place the construction is opened; everything else reads `RoundingWitness` fields.

The chain:
- `structure ucurl_ChainState (W) (u) (s : Finset ℝ)` — the frozen invariant after the curls at the
  tangencies `s`: `F : SmoothRegularLoop`, `X : Diagram`, `carried : RecordCarried F X`,
  `poly : P X = P D.toDiagram`, `writhe : X.writhe = D.toDiagram.writhe − s.card`,
  `neg : ∀ x, X.sign x = −1`,
  `agree : ∀ t, (F.γ t = L_ε t ∧ deriv F.γ t = deriv L_ε t) ∨ ∃ t₁ ∈ s, ∃ j < k, t₁ ∈ Ioo (a j) (b j) ∧
  (∃ n : ℤ, t + n ∈ Ioo (a j) (b j)) ∧ F.γ t ∈ cornerDisc C ε j` ("`F = L_ε` WITH VELOCITY off the used
  windows, and a point in a used window lies in the used corner disc"),
  `no_u : ∀ t, normalize (deriv F.γ t) = u → ∃ t₁ ∈ tangencySet W u, t₁ ∉ s ∧ ∃ n : ℤ, t = t₁ + n`
  (the `u`-tangencies of `F` are unused tangencies of `L_ε`, mod 1 — the direction the conclusion needs).
- `ucurl_chainState_zero` — the record itself at `s = ∅` (`W.carried.toRecordCarried`; `no_u` by
  `Int.fract` and `SmoothLoop.deriv_eq_add_int`).
- `ucurl_step` — the one-step lemma (stated for ANY `RoundingWitness W` with `hturn` and the interior
  hypothesis `hint`, so it is independent of the construction): `Nonempty (ucurl_ChainState W u s) →
  Nonempty (ucurl_ChainState W u (insert t₀ s))` for an unused tangency `t₀` with
  `CrossesPositively W t₀`.

## 3. The one-step lemma: how each `CurlSite` field is discharged (probe result: all satisfiable)

Site `S` at `t₀ ∈ Ioo (a j) (b j)`, `α := a j`, `β := b j`, `θ := W.θ j`, `carried := st.carried`.
Two preliminary facts: `hnone` — no used tangency lies in `Icc (a j) (b j)` (two `u`-tangencies of
`L_ε` in one closed junction coincide by `direction_once`); `hunch` — `F = L_ε` with velocity on
`Icc (a j) (b j)` (the second alternative of `agree` would put `t` in a used open junction `j' ≠ j`
(`ucurl_int_eq_zero`, `ucurl_junction_disjoint`), forcing `j = j'` and a used tangency in junction `j`).

| field | proof |
|---|---|
| `tangent_at` | `hunch` at `t₀` + `ht₀.2` |
| `α_lt`, `lt_β` | `t₀ ∈ Ioo` |
| `short` | `0 ≤ a j`, `b j < 1` |
| `embedded` | `junction_embedded` transported by `Set.InjOn.congr` along `hunch` |
| `no_double` | THE delicate field (B's analysis, confirmed): an occurrence parameter `τ v + n ∈ Icc (a j) (b j)` has `n = 0`; `q := F.γ (τ v) = L_ε (τ v) ∈ cornerDisc j` (`disc_contains_modification`); the twin parameter `τ (twin v) ≠ τ v` traces `q` (`twin_eval`, `τ_inj`, `twin_ne`).  By `agree` at the twin: either unchanged — then `q` is a double point of `L_ε`, so a crossing point of `L` (`same_double_points`), excluded from the disc by `disc_no_double`; or in a used window of junction `j' ≠ j` (`j' = j` contradicts `hnone`) — then `q ∈ cornerDisc j'`, contradicting `disc_disjoint` (`ZMod.val_natCast_of_lt` for `(j : ZMod k) ≠ j'`) |
| `lift` | `θ_lift` with `hunch` (after `show normalize (deriv st.F.γ t) = _`) |
| `turns_pos` | `θ_strict.1` with `ucurl_turn_pos` (the printed "the junction is positive because the crossing is positive") |
| `isolated` | `direction_once` with `hunch` |

`S.p ∈ interior (cornerDisc C ε j)` by `hint`; `cf_lem_curl.exists_curl S (cornerDisc C ε j) hp`
gives `Δ ⊆ cornerDisc C ε j` and `Wc : CurlWitness S Δ`.  New state `(Wc.F', Wc.D', Wc.carried')`:
`poly` = `poly_eq`; `writhe` = `writhe_eq` + `Finset.card_insert_of_notMem`; `neg`: `kink_neg` for the
kink, `old_sign` on `old.symm ⟨y, hy⟩` (`Equiv.apply_symm_apply`) otherwise; `agree`: off the window
(mod 1) by `unchanged`/`unchanged_deriv` (previous alternative carried over), in the window the new
alternative with `t₀`, `Wc.α_le`/`le_β` (`S.α = a j` by `rfl`), `new_in_disc` + periodicity
(`SmoothLoop.eq_add_int`) + `Δ ⊆ cornerDisc`; `no_u`: off the window by `unchanged_deriv` and the old
`no_u` (the witness `t₁ ≠ t₀` since `t₀ ∈ Ioo s₁ s₂`), in the window `Wc.no_u` on `t + n ∈ Δ` with
`SmoothLoop.deriv_eq_add_int`.

## 4. The leaf

`Finset.induction_on` on `s ⊆ hfin.toFinset` (`hfin := hcount.1`), predicate `Nonempty (ucurl_ChainState
(Round C D ε h) u s)`; base `ucurl_chainState_zero`, step `ucurl_step _ h.turn_ne hint …` with
`hint := ucurl_junction_mem_interior`, `Set.Finite.mem_toFinset`.  At `s = hfin.toFinset`: the
`no_u` clause gives `∀ t, normalize (deriv F.γ t) ≠ u` (an unused tangency would be a member of
`toFinset`); `writhe` with `hfin.toFinset.card = R` from `hcount.2.1` by `Set.ncard_eq_toFinset_card`
and `Nat.cast` injectivity; `poly`, `neg`, `⟨carried⟩` are projections.  `hu` is unused.

## 5. Mathlib / toolchain pitfalls met

- `le_or_lt` no longer exists: use `le_or_gt`.
- `push_neg` is deprecated in this Mathlib: `push Not at h` works.
- `Finset.card_insert_of_notMem`, `Finset.notMem_empty` (the `notMem` spellings).
- Structure-instance fields continued on a following line must be at a column ≥ the first field's
  column (`sepByIndent`); I used the anonymous constructor `⟨Wc.F', Wc.D', Wc.carried', ?_, …⟩` for the
  new state to avoid the layout constraint.
- `IsLiftOn`'s second clause is stated on the unapplied function; `rw` on `deriv st.F.γ t` needs a
  preceding `show normalize (deriv st.F.γ t) = _` (beta).
- `Antitone.deriv_nonpos` takes the point implicitly; `HasDerivWithinAt.nonpos_of_antitoneOn` needs an
  `AccPt` hypothesis — avoided by the clamping lemma.
- `Round C D ε h` unfolds to `roundedWitness h` by `show` (plain `def`), so `curveMap_on_junction`
  applies directly; `cornerDisc C ε j` with `j : ℕ` is `cornerDisc C ε (↑j : ZMod C.k)` and
  `disc_disjoint` needs `(↑j : ZMod C.k) ≠ ↑j'`, obtained via `ZMod.val_natCast_of_lt` as in
  Rounding.lean's `disc_only_modification`.

## 6. Notes for the assembler / executor

- The helper block is self-contained (uses only `RoundingWitness`/`CurlWitness` fields, `cf_lem_curl`,
  `Carried.toRecordCarried`, `RecordCarried` fields, and the Rounding internals `curveMap_on_junction`,
  `juncArc_mem_open_disc`, `dirOf_θu`, `turn_bounds`, `ℓ_pos`, `Λ_pos`, `b_sub_a`,
  `E_continuous_eucDist`).  It depends on the frozen defs `Round`, `tangencySet`, `CrossesPositively`,
  `TangencyCount` only.
- `ucurl_ChainState` is a `Type`-valued structure (it carries `F`, `X`, `carried`), consumed through
  `Nonempty`; it is the plan's `CurlChainState`, named with the unit prefix.  `ucurl_step` is stated for
  an arbitrary `RoundingWitness` plus the interior hypothesis `hint`, so it survives any change of the
  construction; only `ucurl_junction_mem_interior` reads `roundedWitness` internals.
- Nothing in the leaf needs `hu : euclideanLength u = 1` (the site's `u_unit` is derived from
  `tangent_at`); the frozen statement keeps it, hence the one linter warning.  If the assembler wants a
  warning-free file, `set_option linter.unusedVariables false in` before the leaf is the only option
  that leaves the statement byte-identical (not applied here).
- No leaf of this unit is believed false.  The two facts the plan flagged as delicate — `no_double` for
  later sites and the disjointness of the windows — are exactly the two alternatives of `agree` plus
  `direction_once` ("distinct tangencies lie in distinct junctions"); both went through without extra
  hypotheses.
