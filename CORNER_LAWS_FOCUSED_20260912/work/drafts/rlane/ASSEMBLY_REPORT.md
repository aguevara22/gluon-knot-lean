# R lane — assembly report: `RLaneCores_Assembled.lean` (2026-09-14, 03:25 UTC / 11:25pm ET)

Assembler: Claude Fable 5.1 subagent, Lean v4.34.0-rc2 (Mathlib pin), checked with
`cd work/lean && lake env lean <file>` only. Nothing was written under `work/lean`.

**Result:** `work/drafts/rlane/RLaneCores_Assembled.lean` — 4051 lines, ZERO `sorry`, compiles with
no errors and no warnings in 14.0 s (real; user 16.1 s), and the four row theorems
`RProof.localization / parity / fibre_partition / generic_table` (and the engine `RProof.indep_partition`)
depend on exactly `[propext, Classical.choice, Quot.sound]`. Intended home
`work/lean/RProof/Cores.lean` (module `RProof.Cores`); the copy there is for the owner of `work/lean`
to make. Reproducible build: `work/drafts/rlane/assemble_rlane.sh` (pure `sed` line ranges + the three
closing terms).

## 1. Inputs and their hunks against the FIXED file `work/drafts/RLaneCores_statement.lean` (1073 lines)

Each unit was re-diffed (`diff RLaneCores_statement.lean rlane/U_*.lean`); every hunk is an insertion
(`a`) or a one-line `c` whose only deleted line is `  sorry`. No statement or definition changed.

| unit | diff hunks (statement → unit) | deleted lines | content |
|---|---|---|---|
| `U_L.lean` (1422) | `1a2`; `620a622,951`; `630c961,979` | one `  sorry` | line 2 `import CV.TripleEvents`; block `/-! ## Unit L … namespace L … end L` (330 lines) before the row-164 docstring; proof of `localization` (19 lines, `δ := E.radius`, fields from `hE.tripleEventData` + `L.interlace_toggle_of_exact`, `L.xor_iff_not_of_right`) |
| `U_P1.lean` (1746) | `721a722,1394` | none | block `/-! ### Unit P1 … namespace P1 … end P1` (673 lines) before the row-167 docstring; `P1.parityData (hL : LocalizationData E e f g δ) : ParityData E e f g δ` (E e f g δ implicit via `variable`) |
| `U_F1.lean` (1476) | `6a7,13`; `120c127,191`; `823a895,1226` | one `  sorry` | `6a7,13` is a unit header docstring (NOT used); `127-191` = proof of the engine `indep_partition` (65 lines, in place); block `/-! ### Unit F1 … namespace F1 … end F1` (332 lines) before the row-171 docstring, with `F1.fibrePartitionData`, `F1.punctured_mono / localizationData_mono / parityData_mono`, `F1.fibre_partition_of_rows (hLoc : ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ LocalizationData …) (hPar : ∃ δ, … ParityData …) : ∃ δ, … FibrePartitionData …` |
| `U_G2.lean` (2619) | `1061a1062,2607` | none | block (1546 lines) before the row-172 docstring: `/-! ## Unit G1 … namespace G1 … end G1` (807 lines, lines 1062–1868) then `/-! ## Unit G2 … namespace G2 … end G2` (1062-relative 819–1479) then `/-! ### Test assembly … namespace G2 … end G2` (to 2607) with `G2.goodRadius_of_le`, `G2.parityData_of_le`, `G2.genericTableData h3 hδ hPar`, `G2.generic_table_of_parity {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) (hpar : ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ ParityData E e f g δ) : ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTableData E e f g δ` |
| `U_G1.lean` (1880) | `1061a1062,1868` | none | superseded: its G1 block is byte-identical (md5) to `U_G2.lean` lines 1062–1868; not used separately |

The four insertion regions are pairwise disjoint in the statement file (after lines 620, 721, 823, 1061)
and the three replaced `sorry` lines are 120 (engine), 630 (localization); the remaining `sorry` lines
730, 833, 1071 are the three rows closed in §3.

## 2. Assembly (line map of `RLaneCores_Assembled.lean`)

Built by `assemble_rlane.sh` from the statement file `S` and the units, by exact line ranges:

| assembled lines | source | note |
|---|---|---|
| 1 | `S` 1 | `import Bridge.B3` |
| 2 | (U_L 2) | `import CV.TripleEvents` |
| 3–7 | `S` 2–6 | remaining imports + blank |
| 8–15 | new | 7-line module docstring `/-! **RProof.Cores — assembled** … -/` + blank (prose only) |
| 16–128 | `S` 7–119 | through `indep_partition … := by` |
| 129–193 | `U_F1` 127–191 | engine proof (replaces `S` 120 `sorry`) |
| 194–693 | `S` 121–620 | |
| 694–1023 | `U_L` 622–951 | unit L block |
| 1024–1032 | `S` 621–629 | row-164 docstring + statement |
| 1033–1051 | `U_L` 961–979 | `localization` proof (replaces `S` 630 `sorry`) |
| 1052–1142 | `S` 631–721 | |
| 1143–1815 | `U_P1` 722–1394 | unit P1 block |
| 1816–1823 | `S` 722–729 | row-167 docstring + statement |
| 1824–1826 | new | closing of `parity` (replaces `S` 730 `sorry`) |
| 1827–1919 | `S` 731–823 | |
| 1920–2251 | `U_F1` 895–1226 | unit F1 block |
| 2252–2260 | `S` 824–832 | row-171 docstring + statement |
| 2261–2263 | new | closing of `fibre_partition` (replaces `S` 833 `sorry`) |
| 2264–2491 | `S` 834–1061 | |
| 2492–4037 | `U_G2` 1062–2607 | units G1 + G2 block |
| 4038 | new | one blank line after `end G2` (cosmetic; the unit had none) |
| 4039–4047 | `S` 1062–1070 | row-172 docstring + statement |
| 4048–4049 | new | closing of `generic_table` (replaces `S` 1071 `sorry`) |
| 4050–4051 | `S` 1072–1073 | blank, `end RProof` |

Verified: `diff RLaneCores_statement.lean RLaneCores_Assembled.lean` has hunks
`1a2 6a8,15 120c129,193 620a694,1023 630c1033,1051 721a1143,1815 730c1824,1826 824a1921,2252
833c2261,2263 1061a2492,4038 1071c4048,4049` and its ONLY deleted lines are the five `  sorry`
(the `824a…` numbering is diff aligning the F1 block's leading blank line with `S` 824). Each spliced
region is md5-identical to its source range in the unit file (six checks: engine proof, L block,
localization proof, P1 block, F1 block at 1920–2251, G1+G2 block).

## 3. De-duplication and scoping

- Inserted helpers live in disjoint sub-namespaces of `RProof`: `L` (18 decls), `P1` (43), `F1` (26),
  `G1` (57), `G2` (35); the fixed file contributes `RProof` (54), `RProof.LocalTable` (20+1). A
  namespace-aware scan of all 255 column-0 declarations found NO duplicate fully-qualified name (the
  only repeats are the statement file's own anonymous `instance … : Decidable …`, which are auto-named).
  Lean confirms: a duplicate would be a compile error and there is none.
- A stack-aware scan (namespaces and sections) of the four inserted blocks shows no `variable`, `open`,
  `set_option` or declaration at `RProof` level outside the sub-namespaces — the fixed statements after
  each block see exactly the context they had in the statement file.
- Name shadowing checked: `RProof.P1.parity` (field lemma) vs the row `RProof.parity`; the closing
  terms are written after `end P1`, so bare `parity` resolves to the row (compile + axioms confirm).
- Nothing was dropped except `U_F1`'s unit-header docstring (`6a7,13`, prose) and the redundant
  standalone `U_G1.lean`.

## 4. Closing terms (the only new proof text)

```lean
theorem parity … := by
  -- Assembly: the radius of row 164 carries `ParityData` (unit P1).
  obtain ⟨δ, h1, h2, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  exact ⟨δ, h1, h2, P1.parityData hL⟩

theorem fibre_partition … := by
  -- Assembly: rows 164 and 167 at the common radius (unit F1).
  exact F1.fibre_partition_of_rows (localization E e f g h3 h4e h4f h4g hE)
    (parity E e f g h3 h4e h4f h4g hE)

theorem generic_table … := by
  -- Assembly: the good radius of unit G1 and the parity radius (unit G2).
  exact G2.generic_table_of_parity hE (parity E e f g h3 h4e h4f h4g hE)
```

`localization` is unit L's proof verbatim (`δ := E.radius`). `parity` inherits that radius; `fibre_partition`
gets `min δ₁ δ₂` inside `F1.fibre_partition_of_rows`; `generic_table` gets `min` of G1's good radius and
the parity radius inside `G2.generic_table_of_parity`.

## 5. Checks

| check | result |
|---|---|
| `grep -n sorry` | none in code; two prose mentions (line 14 header, line 36 = statement file's own docstring) |
| `cd work/lean && lake env lean …/RLaneCores_Assembled.lean` | exit 0, no output (0 errors, 0 warnings); `real 14.0 s, user 16.1 s, sys 3.6 s` |
| `#print axioms` on `/tmp/RLaneCores_Assembled_axioms.lean` (copy + 5 `#print axioms`, 12.2 s) | `RProof.localization`, `RProof.parity`, `RProof.fibre_partition`, `RProof.generic_table`, `RProof.indep_partition`: each `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no literature axioms |
| bundles byte-identical to statement file (md5 of `structure … ` through last field) | `LocalizationData` (84 lines), `ParityData` (32), `FibrePartitionData` (66), `GenericTableData` (212): IDENTICAL |
| row signatures byte-identical (`theorem <row> (E : CV.Event n) (e f g : ZMod n)` through `:= by`, 7 lines each; exactly one match each) | `localization`, `parity`, `fibre_partition`, `generic_table`: IDENTICAL |
| line count | 4051 |

Files: `work/drafts/rlane/RLaneCores_Assembled.lean`, `work/drafts/rlane/assemble_rlane.sh`,
this report. Scratch: `/tmp/RLaneCores_Assembled_axioms.lean`, `/tmp/rlane_assembled_compile.log`.
