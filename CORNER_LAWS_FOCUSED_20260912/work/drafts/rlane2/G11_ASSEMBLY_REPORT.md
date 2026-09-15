# G11_ASSEMBLY_REPORT — row 173 (`RProof.generic_transport`), G11 lane

Written 2026-09-14 14:13 UTC / 10:13am ET by the G11 assembler on Mark's RunPod home pod.
Lane: `work/drafts/rlane2/`. Output: **`G11_Assembled.lean`** (11 175 lines), built by **`G11_assemble.py --post`**
(reproducible; `python3 G11_assemble.py --post` regenerates the file from the skeleton and the six unit files).

## 0. Result in one paragraph

`G11_Assembled.lean` compiles with **0 errors and 0 `sorry`** (`cd work/lean && lake env lean ../drafts/rlane2/G11_Assembled.lean`:
exit 0, 28 s, 18 linter warnings, no `declaration uses sorry`); `grep -c sorry` = **0**; no `#print`/`#eval` lines.
`#print axioms RProof.generic_transport` (on a /tmp copy) = `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
SM.lp_lm_uniqueness]` — exactly the set of the accepted sibling rows, no `sorryAx`. The statement of `generic_transport` is
byte-identical to the skeleton's and has the sibling-row shape (`exterior`, `availability_zero_one` in `RProof/X1Rows2.lean`:
same six binders, conclusion `∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ <RowData> hn E e f g δ`). No declaration name clashes with
`work/lean`. **Two assembler-level edits were necessary and are flagged in §3** (the skeleton's leaves `G11_clear` and
`G11_cfg_hpq` were missing section hypotheses; fixed with `include … in`, statement text unchanged, signatures changed).
The flagged branch leaf X2 (`G11_two_crossings_absurd`) and the two declarations marked `-- NOT ON THE ROW'S PATH`
(`GT_G11_proof`, `generic_transport_of_GT_G11`) were removed as instructed; the row is derived through `GT_G11_strong` only.

## 1. Unit diffs against the skeleton (task item 1)

`diff G11_Skeleton.lean G11_U<i>.lean` parsed hunk by hunk (`G11_assemble.py` aborts on anything not in the table).

| unit | removed skeleton lines | added lines | hunks | leaves proved | verdict |
|---|---|---|---|---|---|
| U1 | 7 × `  sorry` | 260 | 9 | 7 (A2–A6, A7, F0) | clean |
| U2 | 12 × `  sorry` | 1024 (+2 imports) | 17 | 12 of 14 (A9–A15 except `G11_cfg_hpq`, X1, X3; `G11_clear` open) | clean |
| U3 | 9 × `  sorry` | 1496 (+1 import) | 15 | 9 (B1–B4, D1, D2, `G11_exists_params`) | clean |
| U4 | 9 × `  sorry` | 1822 | 11 | 9 (C1–C4, D3, D4, `X₁_cross_pq`) | clean |
| U5 | 4 × `  sorry`, 3 headers `:= by` → `:=` | 1313 | 5 | 4 (D5, D6, D7) | clean (see note) |
| U6 | 5 × `  sorry` | 4256 | 8 | 5 (D8, E1, F1, F2, F3) | clean |

* No unit changed any statement, definition, name or docstring; no deletion hunk; no two units touch the same leaf.
* **U5 note:** `clean_M₀`, `clean_M₁`, `exists_moveMatch` were given as one-line terms with the header changed from
  `… := by` to `… :=`. The statement is unchanged; the assembler restored the frozen header and wrote the body as
  `  exact <term>` (normalisation only, no adoption of a statement change).
* **Imports added by units and kept** (both needed, oleans present): U2 `import Mathlib.Analysis.Normed.Affine.AddTorsorBases`,
  `import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`; U3 `import SM.CS3` (not in the import closure of `RProof.X1Rows3`).
  **The port must carry these three imports.**
* Helper names: all `gu<i>_`-prefixed, 1 116 helpers (gu1 5, gu2 68, gu3 151, gu4 242, gu5 144, gu6 506); zero duplicate
  full names inside the file, so no de-duplication or renaming was required. Different units re-prove similar facts under
  different names (e.g. `gu3_/gu4_remote_of_isCrossing`, the `X₀` label arithmetic in gu3/gu4/gu5/gu6); left as is
  (merging them is a port-time clean-up, not an assembly step).

## 2. Assembly (task item 2)

Skeleton line by line; each proved leaf's `  sorry` replaced by the unit's body; each helper block inserted after the
skeleton line the unit put it after (unit order U1…U6 when two units insert at the same place — never happened);
imports de-duplicated after line 1. Verification inside the script: every non-`sorry` skeleton line survives verbatim
and in order (pre-post-processing); every inserted block occurs contiguously. Final-file check: 63 unit blocks,
59 byte-identical and contiguous, 4 (all U2) contiguous after the substitutions of §3 (the `hcfg` argument and the
relocated `gu2_cfg_hpq` block). Placement constraints from the reports (U4 blocks before Unit C / before D3 /
between `X₁_cross_pq` and `inner_M₁`; U6 D8 → E1 → F blocks) are satisfied automatically because the skeleton positions
are kept.

Declarations in the file: 1 241 (125 skeleton = 54 defs, 69 theorems, 2 structures — 128 minus the 3 removed; 1 116 helpers).

## 3. Assembler-level edits — READ THIS (task items 3, 4)

**3a. `G11_cfg_hpq` (leaf A12, ON the row's path) — missing hypotheses.** The frozen statement mentions neither `hfg` nor
`hcfg`, so (Lean 4 inclusion rule) they were not in scope; its conclusion implies `f ≠ g ∧ IsCrossing P {f, g}`
(`gu2_hcfg_of_hpq`, proved), so the leaf as frozen is a Gauss-parity statement (X2-type), not provable from `work/lean`
and presumably false for degenerate `P'` (U2 report). Fix adopted, as U2 recommended: the line `include hfg hcfg in`
before the theorem; theorem text byte-identical; body `exact gu2_cfg_hpq hn hG hs hT q hcef hceg htri hfg hcfg hX`.
Consequences: signature `G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX` (10 call sites updated by textual
substitution); the statements of `G11_cfg_clear_frontier`/`G11_cfg_clear_vertex` now mention `hcfg`, so their
signatures gain it too (`… hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX`), and `G11_configOf`'s three field lines pass
`_hcfg` (its frozen binder name); `gu2_cfg_clear_vertex` likewise (2 call sites). U2's block containing `gu2_cfg_hpq`
(+ docstring) was relocated from after the leaf to after `G11_cfg_hmq` (it must precede the leaf that now uses it);
one word of its docstring changed (`above does not have` → `below did not have`). `G11_configOf`'s own explicit signature
is unchanged, so U6's `G11_liftVisit_σD` / `G11_recordIsoData` and the assembly are unaffected.

**3b. `G11_clear` (leaf A8, NOT on the row's path — nothing calls it) — missing `hG`.** Without `hG : CarrierGeometry P` the
statement is FALSE (U2's counterexample `G11_U2_probe.py`: four edges through one point). Fix adopted: `include hG in`
before its docstring; theorem text byte-identical; body `exact gu2_clear hG hs hef heg hfg hcef hceg hcfg hX`.
Signature becomes `G11_clear hG hs hef heg hfg hcef hceg hcfg hX`. (Alternative if the reviewer prefers no signature
change: drop the leaf — `gu2_clear`/`gu2_clear_closed` carry the content used by A15.)

**3c. Removed (task item 4):** the X2 docstring, the two `-- NOT ON THE ROW'S PATH` comment lines and `theorem
G11_two_crossings_absurd` (17 lines); `GT_G11_proof` with its docstring (9 lines); `generic_transport_of_GT_G11` with its
comment and docstring (12 lines). Kept: X1 `G11_le_one_crossing` and X3 `G11_card_cases` (proved; now unused).
Removed text is saved at `/tmp/g11asm/removed.lean` (pod-local scratch).

**3d. Module docstring rewritten (task item 8)** to describe the assembled state; the "Statement finding" paragraph now
says the literal `GT_G11` branch is omitted. The word `sorry` occurs nowhere in the file.

No own proving was needed beyond 3a/3b (the only open leaves were the two under-hypothesised ones, whose provable forms
U2 had already closed).

**Unproved leaves remaining in the file: none.** Leaves of the skeleton not in the file: `G11_two_crossings_absurd` (X2,
removed, unproved by design — Gauss parity not in the library).

## 4. Compile / axioms / statement / clashes (task items 5–7)

* Official compile: `cd work/lean && lake env lean ../drafts/rlane2/G11_Assembled.lean` → exit 0, 0 errors,
  0 `declaration uses sorry`, real 28 s. 18 warnings, all linter: "automatically included section variable(s) unused
  `[NeZero n]`" for 12 theorems (frozen statements `G11_no_visit_between`, `G11_alt_swap`, `G11_exact_swap`,
  `G11_alt_crossingSign`, `G11_param_ne`; U2 helpers `gu2_exact_of_eq`, `gu2_tail_not_mem_segment`,
  `gu2_param_ne_of_xPair_ne`, `gu2_visitTwin_vef/veg/vfg`, `gu2_pair_mem_triangleSupports`) and 3 unused binders
  `hef heg hfg` in the frozen `G11_card_cases`. Silencing them needs `omit [NeZero n] in` / `_`-binders (signature-level
  edits to frozen statements) — NOT done; harmless.
* `grep -c sorry G11_Assembled.lean` = 0. `#print`/`#eval`/`#check` lines: 0.
* `#print axioms` on `/tmp/g11asm/G11_Axioms.lean` (the file + `#print axioms` lines; compiled from `work/lean`):
  `RProof.generic_transport`, `RProof.GT_G11_strong_proof`, `RProof.G11_le_one_crossing`:
  `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`;
  `RProof.G11_core`: `[propext, Classical.choice, Quot.sound, SM.lit_homfly]`;
  `G11_configOf`, `G11_recordIsoData`, `G11_card_cases`, `G11_clear`, `G11_cfg_hpq`: `[propext, Classical.choice, Quot.sound]`.
  No `sorryAx` anywhere in the output.
* `generic_transport` statement: byte-identical to the skeleton (checked programmatically, header through `:= by`);
  sibling-row shape confirmed against `RProof.exterior` (X1Rows2:1966) and `RProof.availability_zero_one` (X1Rows2:3619).
  `work/lean` has no `RProof.generic_transport` yet (only `GT_generic_transport_of_G11 (hG11 : GT_G11)`).
* Name-clash scan: all 1 241 full names of the file (namespace-aware: `RProof.*`, `RProof.G11_Config.*`,
  `RProof.G11_Params.*`, `RProof.gu5_Side.*`, …) against the 15 764 declarations parsed from the 660 `.lean` sources
  under `work/lean` (excluding `.lake`): **0 exact clashes**; also 0 short-name coincidences with the opened namespaces
  `SM`, `SM.GeoCarrier`, `SM.Link`, `SM.Carrier`, `RProof` (which could otherwise cause ambiguity at port time).
* Skeleton footprint of the final file (`diff G11_Skeleton.lean G11_Assembled.lean | grep '^<'`): the 49 `  sorry` lines,
  the module docstring lines, the removed X2/`GT_G11_proof`/`generic_transport_of_GT_G11` text, the 2 statement lines of
  `G11_cfg_clear_frontier`/`G11_cfg_clear_vertex` and the 3 field lines of `G11_configOf` (the `hcfg` fix), 5 blank lines.
  Nothing else.

## 5. For the port / reviewer

1. Carry the three extra imports (§1). 2. The signature changes of §3a/3b are the only deviations from the frozen
skeleton; they are forced (the frozen forms are unprovable/false), and `G11_configOf`, `GT_G11_strong`, `GT_G11_strong_proof`
and `generic_transport` are untouched. 3. `GT_G11` itself (X1Rows3) remains unproved in this lane; the row does not need it.
4. Reports of the units: `G11_U{1..6}_REPORT.md`; the U4 report lists 18 `noncomputable def` abbreviations and U3 one
`def` (`gu3_IsVisitIso`) among the helpers — kept as delivered. 5. Nothing was written under `work/lean`.
