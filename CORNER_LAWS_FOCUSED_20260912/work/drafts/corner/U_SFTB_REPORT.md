# U_SFTB report — unit U112-B (`sftb_`), leaf `sft_mixed` (row 112 thm:C-soft, mixed sector)

Prover subagent, 2026-09-15 ~16:10 UTC / 12:10pm ET. File: `work/drafts/corner/U_SFTB.lean` (byte-identical copy of
`Statements_FINAL.lean` + this unit's proofs; 896 lines, was 764).
Check: `cd work/lean && lake env lean ../drafts/corner/U_SFTB.lean` → **0 errors**, 13 warnings `declaration uses sorry`
(= the 9 leaves of the other units + the 4 row theorems of §6; `sft_mixed` is not among them). `grep -c sorry`: 16 → 15
(the 16 = 14 sorry bodies + 2 comment lines at :24 and the §6 header). Nothing written under work/lean.

## Proved

- **`sft_mixed`** (PLAN §4 U112-B, §3.4 "Mixed", sm-4:1059-1065) — the statement is untouched; body ≈ 20 lines.
  Route exactly as PLAN §3.4: `soft_family_generic hn hP j q hq` `.2.2.2.2.2` gives `δ > 0` and, for `ε ∈ (0, δ)`,
  `∃ hQ hp hclass, (i) ∧ (ii) ∧ …`; `ε₁ := δ`. The leaf's own `hQ` is used directly (`Generic` is a Prop, so the
  existential's `hQ'` is irrelevant — the clauses consumed never mention it). From clause (i), last conjunct
  (`hI.2.2.2.2`): the soft edge `E_{softOldIndex j j}` is disjoint from every edge except its two neighbours ⇒
  `∀ c : Crossing P_ε, softOldIndex j j ∉ c.val` (`sftb_soft_edge_no_crossing`). From clause (ii)
  (`hII.2.2.2.2.1`, `hII.2.2.2.2.2.1`): `turn P_ε (softOldIndex j j) = −χ₋`, `turn P_ε (softNewIndex j) = −χ₊`;
  `χ₋, χ₊ ≠ 0` by `softAttachment_signs_nonzero hq` (SoftAttachmentSigns.lean:71) and `χ₋ ≠ χ₊` ⇒ `χ₊ = −χ₋`
  (`sftb_signType_eq_neg_of_ne`); with `softOldIndex_attachment_next : softOldIndex j j + 1 = softNewIndex j` the
  corners `M, M_ε` are consecutive with opposite turns; conclude by `sftb_cornerStateSum_eq_zero_of_consecutive_opposite`.
- `#print axioms SM.sft_mixed` (checked on a scratch copy, not left in the file):
  `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` — no `sorryAx`. `SM.lit_homfly` enters only through the
  definition of `cornerStateSum` (def:C's `cornerHomfly`), as for every C-row statement; the helpers not mentioning `C`
  (`sftb_soft_edge_no_crossing`, `sftb_markSuccessor_vertex_of_no_crossing`) are standard-axioms only.
- Unconditional (no floor, no `hCV`, no other unit's leaf): portable library material on its own after review, as PLAN §4
  says of the mixed sector.

## Helpers added (all `sftb_`, immediately before `sft_mixed` in `section Soft`, after `sft_same_sign`)

| name | statement | note |
|---|---|---|
| `sftb_markSuccessor_vertex_of_no_crossing` | `(∀ c : Crossing P, i ∉ c.val) → markSuccessor hn hP (inl i) = inl (i+1)` | **verbatim re-proof of `Carrier.markSuccessor_vertex_of_no_crossing` (SM/CS5.lean:30)** — `SM.CS5` is NOT in the import closure of Statements_FINAL (checked by `#check`), and adding an import was not in my remit. Assembler: if `SM.CS5` gets imported, this helper can be replaced by the accepted one (identical statement) |
| `sftb_not_uniformDecomposition_of_consecutive_opposite` | `hno, turn P (i+1) = −turn P i, S ∈ independentSupports → ¬ UniformDecomposition hn hP S` | the thm:C-S5 argument for one `S` (work/drafts/CS5B.lean:141): `owner (inl (i+1)) = owner (inl i)` via `smoothingSuccessor_vertex` + `owner_successor`; `ccpCornerMark_exists` + `isTrueCorner_vertex` + `ccpCornerPolygon_turn_vertex` (CarrierCornerPolygon.lean:598) give both turns on the carrier's corner polygon; `τ = −τ` is impossible for `τ ≠ 0` |
| `sftb_cornerStateSum_eq_zero_of_consecutive_opposite` | `hno, turn P (i+1) = −turn P i → cornerStateSum hn hP = 0` | the reusable lemma work/drafts/CS5B.lean:171, via `cornerStateSum_eq_sum_independentSupports` (CornerStateSum.lean:174) + `Finset.sum_eq_zero` + `ite_eq_right` |
| `sftb_signType_eq_neg_of_ne` | `σ ≠ 0 → τ ≠ 0 → σ ≠ τ → τ = −σ` | `cases <;> decide` |
| `sftb_sub_one_ne` | `3 ≤ n → j − 1 ≠ j` in `ZMod n` | `sub_eq_self`, `ZMod.one_eq_zero_iff`, `omega`; `omit [NeZero n] in` |
| `sftb_soft_edge_no_crossing` | disjointness hypothesis (the last clause of lem:soft-generic (i), stated verbatim) `→ ∀ c : Crossing (softInsertion P j q ε), softOldIndex j j ∉ c.val` | `IsCrossing = ∃ a b, s = {a,b} ∧ remote a b ∧ (seg a ∩ seg b).Nonempty` (Crossings.lean:12), `remote = ¬ adjacent`, `adjacent i j = (j−i = −1 ∨ j−i = 0 ∨ j−i = 1)` (Polygon.lean:61-66); the two neighbours are excluded by `softOldIndex_next j (j−1)` (SoftInsertionSuccessors.lean:28) and `softOldIndex_attachment_next` (SoftInsertionIndices.lean:74); `Set.Nonempty.not_disjoint` |

None of these statements is named by PLAN §3 for another unit (U112-B has no helper-unit obligations); U112-C/D may reuse
`sftb_soft_edge_no_crossing` (the same soft edge is crossing-free in all three sectors) and `sftb_sub_one_ne`.

## Left

Nothing in this unit. Other units' leaves untouched: `sg_isolated_undominated`, `sg_daughters_products`,
`sg_daughters_rotation`, `s7_sliding_law_at`, `s7_bigon_law_at`, `s7_universal_extraction`, `s7_corner_product`,
`sft_same_sign`, `sft_loop`, and the §6 row theorems.

## Mathlib / Lean pitfalls met

- `if_neg` is deprecated in this Mathlib pin ("Use `ite_eq_right` instead") — used `ite_eq_right`, which is what the
  CS5B draft already used (so that draft's use was not a typo).
- `(s ∩ t).Nonempty` is an `∃`; it has no `.symm` — swap with `rwa [Set.inter_comm]`.
- In the `rw` chain for the opposite turns, do NOT insert `neg_neg`: after `rw [softOldIndex_attachment_next, hτ₂, hτ₁,
  sftb_signType_eq_neg_of_ne …]` the goal is `−(−χ₋) = −(−χ₋)` and closes by `rfl`; an extra `neg_neg` rewrites only one
  side and leaves `−(−χ₋) = χ₋` open.
- Destructuring `hgen ε hε hlt : ∃ hQ hp hclass, A ∧ B ∧ C ∧ D ∧ E ∧ F` with `obtain ⟨_hQ', _hp, _hclass, hI, hII, -⟩`
  works (the trailing `-` takes the remainder `C ∧ D ∧ E ∧ F`); name the three witnesses with underscores rather than
  `-` since the later clauses depend on them.
- `Carrier.markSuccessor_position_cases` unfolds definitionally at vertex/visit marks exactly as in CS5.lean
  (`change (0 : ℝ) < 0 at hlt`, `change v.2.val = i at hedge`) — copied verbatim, compiles.

## For the assembler / executor

- Statement/name/docstring diff vs `Statements_FINAL.lean`: only the six `sftb_` declarations (with docstrings and one
  `/-! … -/` header) inserted before `sft_mixed`, and the leaf body. Clash scan: `sftb_*` is unique to this unit; no `^def`
  of mine (one docstring line that began with `def:crossings` was reflowed to avoid a false positive).
- If the assembler imports `SM.CS5` for any reason, `sftb_markSuccessor_vertex_of_no_crossing` duplicates
  `Carrier.markSuccessor_vertex_of_no_crossing` (same statement, different name — no clash, but redundant).
- The three CS5-pattern helpers are the natural home for a future library lemma `cornerStateSum_eq_zero_of_consecutive_
  opposite` (promised by the CS5B draft); thm:C-S5 itself could be re-derived from it in two lines.
- No leaf of this unit is false or needs a stronger hypothesis. The printed mixed-sector argument (sm-4:1059-1065) is
  fully covered by lem:soft-generic (i) (soft edge crossing-free) + (ii) (the two new turns); no rotation, coefficient or
  transport step is needed, as PLAN §3.4 predicted (~200 lines estimated; 132 lines used incl. docstrings).
