# W3S_S6b_REPORT — unit S6b of the U8R sweep (wave 3)

2026-09-14, prover for unit **S6b** = the last five leaves of PLAN §3 / Unit S6: `path_cusps`,
`exists_cuspVertex_sameCycle`, `circleComp_bijective`, `slotComp_ΦFun`, `ΦFun_cycNext`.
File: `work/drafts/frontrows/W3S_S6b.lean` (17,258 lines; skeleton 15,586 + 1,672 inserted).
Compile: `cd work/lean && lake env lean ../drafts/frontrows/W3S_S6b.lean` — **0 errors, exit 0, 61 s**.
`grep -c sorry`: **58 → 53** (the 5 leaves of S6b; the 4 L-geo leaves and the 49 leaves of S1/S2/S3/S4/S5/S6a untouched).

## 1. Result

| leaf | line (my file) | status |
|---|---|---|
| `path_cusps` | 16745 | **PROVED** (clauses 1-2 from the path induction `s6b_path`; clause 3 from the per-step circle invariant `s6b_circ_next`) |
| `exists_cuspVertex_sameCycle` | 16760 | **PROVED** (combinatorial: a cycle of cut slots keeps `xsign`, `xcoord2` strictly monotone, contradiction with `iterate_period`) |
| `slotComp_ΦFun` | 16808 | **PROVED** (`jump_cross` puts `Φ p` on the cycle of `slotAt`; `jump_cusp` puts the cusp vertex there; `s6b_path` connects any two `slotAt` of one circle) |
| `ΦFun_cycNext` (THE HEART) | 16822 | **PROVED** (`jump_cross p` ++ `s6b_path` on `(t_p+ε', t'−ε')` ++ shifted `jump_cross p'`; `U2.firstReturn_eq_of_path` with `M = (m₁−a₁)+m₂+a₃`; no `cycBetween` occurrence between `p` and `cycNext p` via `cycNext_no_between`, alone case via `cycNext_ne_self`) |
| `circleComp_bijective` | 16889 (**relocated**, see §3) | **PROVED** (surjective: `exists_cuspVertex_sameCycle` + `rep`/`orbitOf_rep`; injective: the circle invariant `s6b_circ`) |

All five statements, names and docstrings are byte-identical to the skeleton (checked by a multiset diff of lines:
the only skeleton lines absent from my file are the five `… := sorry` statement tails).  The Assembly section
(`recordIso`, `sweep_proof`) and `represent` compile unchanged on top of the proved leaves.

## 2. Helpers (one block, `/-! ### S6b helpers -/ section S6bHelpers … end S6bHelpers`, lines 15200-16741, 1,542 lines)

All names prefixed `s6b_`; no new imports; no `open Classical`.

* **Periodicity / lifting** (15202-15300): `s6b_xOf_add_int`, `s6b_slotAt_add_int`, `s6b_slotAt_eq_of_eq_add`,
  `s6b_notMem_singX_of_eq_add` (`slotAt` is 1-periodic in the parameter: `Int.fract_add_intCast`, `eq_add_int`);
  `s6b_singParams_finite` / `s6b_singParams` (the singular parameters of a circle in a bounded open interval form a
  `Finset`: injection `s ↦ (fract s, ⌊s⌋)` into `fibre × Icc ⌊a⌋ ⌊b⌋`); occurrence/cusp bookkeeping at lifted
  parameters (`s6b_occ_of_isDouble`, `s6b_occ_eq_of_sameParam`, `s6b_cusp_eq_of_sameParam`, …).
* **`s6b_jump`** (the jump at ANY singular parameter `s`, lifted from `jump_cusp`/`jump_cross`/`jump_regular` by
  periodicity, with a uniform σ-clause "every σ slot on the way is `Φ` of an occurrence at `s`" and the cusp clause).
* **`s6b_path_aux` / `s6b_path`** (THE PATH INDUCTION, strong induction on `(s6b_singParams i t₀ t₁).card`:
  `slotAt_const` up to the smallest singular parameter, `s6b_jump` across it with `ε'` below the gap to the next one,
  IH from `s₁ + ε'`): `slotAt t₀ → slotAt t₁` in `m` steps; every σ slot on the way is `Φ p` for an occurrence `p` at
  a parameter strictly inside; the cusp vertex of every cusp strictly inside is on the way.  (This also implies S6a's
  `path_no_occ` in five lines — not used, not touched.)
* **Cycles**: `s6b_sameCycle_slotAt`, `s6b_slotAt_fst_eq` (transport across `c.1.1 = i`), `s6b_sameCycle_cuspVertex`,
  `s6b_sameCycle_ΦFun`, `s6b_exists_regular`, `s6b_slotComp_cuspVertex`, `s6b_cuspVertex_of_snd_eq_zero`
  (a slot at position 0 IS `cuspVertex c` of the event of its column).
* **`cycNext`**: `s6b_jump_cross_shift` (`jump_cross` at `p.1.2 + n`), `s6b_no_occ_between` (no occurrence strictly
  between `p` and `cycNext p` read in `(p.1.2, p.1.2 + 1]`; `cycBetween` arithmetic with `Int.fract`).
* **CORE — the circle of a slot is preserved by `next`** (15660-16741, ≈1,080 lines; needed for `path_cusps`
  clause 3 and the injectivity of `circleComp`, see §4):
  - Stage 1 list lemmas: `s6b_filter_split` (splitting a filter of an antitone list, Bool predicates `P = Q || R`
    with `R`-values below `Q`-values), `s6b_entriesOf_append/_congr/_singleton/_eq_map`, `s6b_eq_singleton_of_nodup`,
    `s6b_eq_pair_of_nodup_sorted`, `s6b_sorted_eq` (`List.Pairwise.eq_of_mem_iff` with local `Std.Irrefl/Antisymm`).
  - Stage 2 events: `s6b_key_lt_of_idx_lt`, `s6b_idx_lt_of_key_lt`, `s6b_no_event_between`, `s6b_top`, `s6b_bot`
    (from `events_pairwise_lt`), `s6b_regular_of_no_event` (from `exists_event_of_singular`), regular bits,
    antitone fibre lists, `s6b_entries_regular_eq` (before/after entries agree on regular points).
  - Stage 3 the column structure: `s6b_entries k := hybridEntries (colX k) (colZ k)`,
    `s6b_entriesAfter k := hybridEntriesP (colX k) (colZ k < ht)`; `s6b_entries_eq : = A ++ E_b ++ B`,
    `s6b_entriesAfter_eq : = A ++ E_a ++ B`; `s6b_length_A : |A| + 1 = idx`; the mid lists at the event's height
    (`s6b_mid_cusp` by `cusp_alone`, `s6b_mid_cross` by `no_triple` + the slope keys) and their entries
    (`s6b_Eb_Ea_left/right/cross`); the letter of a column determines its event (`s6b_event_of_letter_l/r/σ`).
  - Stage 4 transitions: `s6b_entries_tie` (exact list equality `s6b_entries (k+1) = s6b_entriesAfter k` at a tie),
    `s6b_entriesAfter_top`, `s6b_entries_bot` (entry-level versions of S4's `hybridCutStrict_eq_cutAfter` /
    `hybridCut_eq_cutBefore`), `s6b_circ_gap` (the CIRCLE lists of `entriesAfter a` and `entriesBefore b` agree across
    a gap: `entriesBefore_left_limit`/`entriesAfter_right_limit` give local constancy, `IsPreconnected.constant` on
    `Ioo a b` with the discrete topology on `List (Fin F.c)`), `s6b_circ_trans`.
  - Stage 5: `s6b_circAt_step` (`posR` keeps the circle: above/middle(σ swap)/below), `s6b_circPair`, `s6b_circ`,
    `s6b_circAt_arms_l/r`, `s6b_posR_of_posL`, **`s6b_circ_next`** (by `next_cases`, six cases), `s6b_circ_iterate`,
    `s6b_circ_of_sameCycle`, `s6b_circ_cuspVertex`, `s6b_circ_slotAt`.

Black boxes consumed (statements only): S6a `slotAt_const`, `jump_regular`, `jump_cusp`, `jump_cross` (and
`isSlot_slotAt` through `slotAt`); S1 `fibreListAfter_eq_fibreListBefore`, `entriesBefore_eq_of_notMem_singX`,
**`entriesBefore_left_limit`, `entriesAfter_right_limit`**; S4 `events_pairwise_lt`, `colX_mono`,
`exists_event_of_singular`, `word_closed`.  Not used: S2, S3, S5 leaves, `path_no_occ`, `posAt_const_of_arc`,
`cut_word_colAt`, `run_take_eq_hybrid`, `step_hybrid`.

## 3. WHAT THE MERGER MUST KNOW

1. **`circleComp_bijective` and `circleEquiv` were RELOCATED** (docstring, statement and `circleEquiv`'s text
   byte-identical) from their skeleton position (between `circleComp` and `isSlot_slotAt`) to just before
   `end Traversal`, after `ΦFun_cycNext`.  Reason: the skeleton declares the leaf BEFORE `slotAt`, the jump leaves,
   `path_cusps` and `exists_cuspVertex_sameCycle`, on all of which its proof depends; Lean cannot prove it in place.
   Nothing between the two positions uses `circleComp_bijective`/`circleEquiv` (the only consumer is `recordIso` in the
   Assembly section, which follows).  A merge script that pastes leaf bodies at the skeleton positions must apply the
   same move (or move the leaf together with `circleEquiv`); otherwise "unknown identifier" errors.
2. The helper block sits immediately before the `path_cusps` docstring, i.e. AFTER S6a's last leaf `path_no_occ`.
   S6a's helper block (if placed before `isSlot_slotAt`) cannot clash: all my names carry the prefix `s6b_`.
3. **S1 entry-level limits are load-bearing.**  `s6b_circ_gap` consumes `entriesBefore_left_limit` and
   `entriesAfter_right_limit` as stated (the `Cont` clause at the level of entries).  PLAN §6 suggests S1 may prove only
   the bit-level limits (`cutBefore_left_limit`, `cutAfter_right_limit`) if it stalls; that would NOT suffice for
   S6b — the circle of each entry across a gap is exactly what the bit-level versions lose.
4. No `sorry` inside the S6b block; the 53 remaining `sorry`s are the other units' leaves.  No import added.

## 4. Pitfalls / findings

* **The jump leaves do not determine the intermediate slots.**  `path_cusps` clause 3 ("every cusp vertex on the path
  belongs to circle `i`") and the injectivity of `circleComp` for CROSSING-FREE circles are NOT derivable from
  `jump_regular`/`jump_cusp`/`jump_cross`/`slotAt_const` as black boxes: their statements only pin the endpoints
  (`slotAt (t ∓ ε')`) and the σ slots, so nothing excludes the path wandering through slots of another circle
  (for circles WITH occurrences injectivity does follow from the σ-structure — the loop of a circle covers its cycle and
  meets exactly `Φ` of its own occurrences — but crossing-free circles have no σ slots).  PLAN §3 anticipated this
  ("add to the jump leaves' proofs or derive from `next_cases`").  I resolved it by proving the per-step invariant
  `s6b_circ_next : s6b_circ (next u) = s6b_circ u`, where `s6b_circ` reads the circle of a cut slot `(k, p)` from the
  `p`-th entry of the hybrid cut of column `k` and the circle of a cusp vertex from its event.  This required
  re-deriving the ENTRY-level structure of the hybrid cuts (S4 proves only bit-level statements) — ≈1,080 lines.
* PLAN §6 doubt about the `¬ IsσSlot` clauses of the jump leaves (index `j = 0`, tie columns): irrelevant for S6b as
  long as the statements stay as they are; `ΦFun_cycNext` uses `jump_cross`'s clause exactly in the form
  `∀ j < m, j ≠ a → ¬σ`.  If S6a weakens it to `0 < j`, `ΦFun_cycNext`'s minimality argument at index `a₁ + j` with
  `j > 0` still works for piece A (the σ slot `Φ p` is at `a₁`, indices `> a₁` are what we use), and for piece C the
  index `j'' < a₃` — a weakened clause on `j'' = 0` would need `0 < a₃` or a separate argument; report if it happens.
* `slotAt F i t h` depends on the proof `h` only up to proof irrelevance: `slotAt_const`'s output (with proofs from
  `hreg`) is used directly as `slotAt … h₀ = slotAt … h₁'` — `exact` accepts it.
* `Prod.Lex.le_iff`/`lt_iff` leave `(ofLex (toLex _)).1` projections: `simp only [ofLex_toLex]` before `linarith`.
* `split_ifs at h` closes constructor-mismatch branches by itself; do not add a bullet for them (use `by_cases` +
  `if_pos/if_neg` + `cases h` for determinism).
* `rcases hℓ : letterAt W k with ⟨m, d⟩ | ⟨m⟩ | ⟨m⟩` for the three letters (not `m d | m | m`).
* The discrete topology on `List (Fin F.c)` is introduced locally (`let _ : TopologicalSpace _ := ⊥`,
  `have _ : DiscreteTopology _ := ⟨rfl⟩`) for `IsPreconnected.constant`; `ContinuousWithinAt` unfolds via
  `nhds_discrete` + `Filter.tendsto_pure`.
* Fast loop used: the skeleton prefix (everything before my leaves) compiled once to `/tmp/s6b/olean/S6bPre.olean`
  (`lean --root=/tmp/s6b -o …`, `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/s6b/olean`), the scratch file
  `import S6bPre` — 10-15 s per iteration instead of 45-60 s.

## 5. Logs

Full compile: `/tmp/s6b/final.log` (0 errors; warnings: 53 × "declaration uses sorry" for the other units, a few
unused-simp-argument / unused-variable linter notes, and two pre-existing "automatically included section variable"
notes at skeleton lines 13451/13472).  Scratch development: `/tmp/s6b/Work.lean` (= `head.lean` + `body.lean` + `tail.lean`).
