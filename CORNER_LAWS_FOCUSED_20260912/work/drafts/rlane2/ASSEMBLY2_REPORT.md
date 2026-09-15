# ASSEMBLY2_REPORT — R-lane X₁ rows, wave 2 (units W2_EXT, W2_AV)

Written 2026-09-14 by the wave-2 assembler. Directory: `work/drafts/rlane2/`. Compile command throughout:
`cd work/lean && lake env lean ../drafts/rlane2/<file>.lean` (nothing under `work/lean` was written; no `lake build`).
Inputs: `RLaneX1_Assembled.lean` (wave 1, 3079 lines), `W2_EXT.lean` (5015 lines, `W2_EXT_REPORT.md`),
`W2_AV.lean` (4734 lines, `W2_AV_REPORT.md`); portable wave-1 module `work/lean/RProof/X1Rows.lean` (built).

## 1. Unit diffs against the wave-1 assembled file

| unit | `diff RLaneX1_Assembled.lean W2_x.lean` hunks | lines removed (`grep '^<'`) | verdict |
|---|---|---|---|
| `W2_EXT.lean` | `3a4` (import `CV.PieceHomflyTransport`), `513a515,2441` (doc comment + `section EXT … end EXT`, 96 `EXT_` declarations), `522c2450,2458` (row-168 body) | exactly one: the `sorry` of `exterior` | allowed edits only |
| `W2_AV.lean` | `5a6` (the same import, after `SM.CornerStateSum`), `659a661,2295` (doc comment + `section AV … end AV` + six top-level `AV_` lemmas), `668c2304,2323` (row-170 body) | exactly one: the `sorry` of `availability_zero_one` | allowed edits only |

Both hunks are self-scoped (`section EXT` with a local `open SM.Carrier`; `section AV` with a local
`open SM.Carrier SM.Link` and an inner `namespace AV_Wall`), placed between the frozen bundle
(`ExteriorData` / `AvailabilityZeroOneData`) and its row theorem, inside `namespace RProof` under the file's
`open SM SM.GeoCarrier` and `variable {n : ℕ} [NeZero n]`. The eight lines of each row theorem's docstring and
statement are unchanged (`W2_EXT` 2442–2449 = base 514–521; `W2_AV` 2296–2303 = base 660–667). Declaration
inventory: EXT 96 names, all `EXT_`-prefixed; AV 120 names, all `AV_`-prefixed except the five members of
`namespace AV_Wall` (`mono`, `not_dom_of_mem`, `dom_transport`, `indep'`, `mark_key_lt` = `RProof.AV_Wall.*`);
no duplicate within a unit, EXT ∩ AV = ∅, (EXT ∪ AV) ∩ X1Rows names = ∅. No statement, definition, structure,
name, docstring or existing import of the wave-1 file was changed by either unit; the other six row theorems
keep their placeholders in both unit files.

## 2. `RLaneX1_Assembled2.lean` (6684 lines)

Construction: line-based merge on the wave-1 skeleton — base 1–3, `import CV.PieceHomflyTransport`, base 4–103
(through the wave-1 assembler note), an inserted wave-2 assembler note, base 104–513, `W2_EXT` 515–2441,
base 514–521 + `W2_EXT` 2450–2458 (row 168), base 523–659, `W2_AV` 661–2295, base 660–667 + `W2_AV` 2304–2323
(row 170), base 669–3079. Resulting positions: `section EXT` 566–2455, `theorem exterior` 2458,
`section AV` 2619–4157, top-level `AV_rowTerm_eq_of_summandTransport … AV_ne_of_remote` 4164–4242,
`theorem availability_zero_one` 4247.
Checks:
* `diff RLaneX1_Assembled.lean RLaneX1_Assembled2.lean | grep '^<'` → exactly two lines, both `  sorry`
  (hunks `3a4`, `104a106,120` (the note), `513a530,2456`, `522c2465,2473`, `659a2611,4245`, `668c4254,4273`).
* Each unit is contained: `diff W2_EXT.lean RLaneX1_Assembled2.lean | grep '^<'` → only `  sorry` (row 170's
  placeholder); `diff W2_AV.lean … | grep '^<'` → only the import line (it sits at line 4 here instead of 6)
  and `  sorry` (row 168's placeholder).
* Compile: exit 0, 0 errors, exactly six `declaration uses \`sorry\`` warnings at lines
  5041, 5102, 5253, 5393, 5479, 5559 = `generic_transport`, `generic_selected`, `extreme_pair_zero`,
  `extreme_transport`, `extreme_selected`, `cv_R` (the six still-open rows); no other warning; 14.7 s wall.
* Rows 168 `RProof.exterior` and 170 `RProof.availability_zero_one` are PROVED.

## 3. `RLaneX1Rows2.lean` — the PORTABLE wave-2 module (3645 lines)

`import RProof.X1Rows` + `import CV.PieceHomflyTransport` + a module docstring, then `namespace RProof`,
`open SM SM.GeoCarrier`, `variable {n : ℕ} [NeZero n]` (the same context X1Rows opened, so the unit text is
verbatim), then ONLY the new material: `W2_EXT` 515–2441 (`section EXT` 72–1961), the row-168
theorem (frozen docstring + statement from base 514–521, proof from `W2_EXT` 2450–2458; `theorem exterior` at
1964), `W2_AV` 661–2295 (`section AV` 1989–3527, top-level `AV_` lemmas 3534–3612), the row-170
theorem (base 660–667 + `W2_AV` 2304–2323; `theorem availability_zero_one` at 3617), `end RProof`.
Declarations: 218 = 96 `EXT_` + 120 `AV_`/`AV_Wall.*` + the two row theorems. Every one of the 218 qualified
names was checked absent from `work/lean/RProof/X1Rows.lean` (name-list intersection ∅; the clean compile with
X1Rows imported is the definitive redeclaration check). The two theorem statements are byte-identical to
`Statements_FINAL.lean` (md5 of `theorem … := by` block: exterior `1a54375a23de`, availability_zero_one
`30b85dd9e1c3`, same in all three files).
Checks: `grep -c sorry RLaneX1Rows2.lean` → **0**; compile exit 0 with **no output at all** (no warnings);
12.4 s wall.

## 4. `#print axioms` (scratch `/tmp/asm2/RLaneX1Rows2_axioms.lean` = portable module + one `#print axioms`
per declaration; output `/tmp/asm2/axioms.out`, 218 entries, **no `sorryAx` anywhere**, no `SM.hyp_R`)

* `RProof.exterior` → `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`.
* `RProof.availability_zero_one` → `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`.
* All three non-standard axioms are on the accepted `literature` list of `work/lean/axiom-policy.json`
  (`lit:homfly → SM.lit_homfly`, `lp:lm → SM.lp_lm`, `lp:lm-uniqueness → SM.lp_lm_uniqueness`; declared in
  `SM/LinkInterfaces.lean` 127/181/241). Both unit reports had already recorded exactly this set. The `lp_lm`
  pair enters through the HOMFLY-of-lifts / piece-polynomial transport (`CV.PieceHomflyTransport`), which
  wave 1 did not use — hence the difference from wave 1's `[…, SM.lit_homfly]`.
* Histogram: 189 declarations `[propext, Classical.choice, Quot.sound]`; 18 `[…, SM.lit_homfly, SM.lp_lm,
  SM.lp_lm_uniqueness]` (`EXT_pieceHomfly_eq_of_labels`, `EXT_exteriorFactor_eq_base`, `EXT_168_independent_of_A`,
  `EXT_homfly_wall`, `EXT_pieceHomfly_wall`, `EXT_exteriorFactor_wall`, `EXT_168_wall_invariant`,
  `EXT_168_factorization`, `exterior`, `AV_homfly_lift_eq`, `AV_pieceHomfly_eq`, `AV_groupedPoly_eq`, `AV_Omega1_eq`,
  `AV_summandTransport`, `AV_170_summand_transport`, `AV_170_summands_agree`, `AV_170_fibre_identity`,
  `availability_zero_one`); 4 `[…, SM.lit_homfly]` only; 2 `[propext, Quot.sound]` (`EXT_walk_transfer`,
  `AV_ne_of_remote`).

## 5. Name-clash scan against `work/lean` (sources, `.lake` excluded; 12,888 qualified declaration names)

* No `EXT_*` or `AV_*` identifier and no `AV_Wall` occurs anywhere in `work/lean` (0 grep hits).
* No declaration named `exterior` or `availability_zero_one` in any namespace of `work/lean`; in particular
  `RProof/Cores.lean` and `RProof/X1Rows.lean` do not declare them. `lean-declarations.json` lists
  `R:exterior → RProof.exterior` and `R:availability_0_1 → RProof.availability_zero_one` with `status: pending`,
  `module: ""` — the declarations in the portable module are the intended ones and must be placed exactly once.
* Exact qualified-name clashes: **none**. Near-miss (base name only): `RProof.AV_Wall.mono` vs. unrelated `mono`
  lemmas in other namespaces (`SM/Curl.lean`, `SM/GeoPositiveLift.lean`, `SM/LinkPositiveLift.lean`) — different
  namespaces, no clash.
* Result: **no clash**.

## 6. Available for the next wave (portable-module line numbers)

Row 168 field lemmas `EXT_168_independent_of_A`, `EXT_168_wall_invariant hL hguard hE`, `EXT_168_factorization
hL hguard hE`; guard radius `EXT_exists_guardRadius hE`; wall transport `EXT_homfly_wall`, `EXT_pieceHomfly_wall`,
`EXT_rotation_wall`, `EXT_exteriorFactor_wall`. Row 170: `AV_170_summand_transport hn hL hR hef heg hfg`,
`AV_170_summands_agree`, `AV_170_fibre_identity hn hL hF hR …`, radius `AV_exists_eventRadius hE`, wall data
`AV_wall_of_event`, transport `AV_summandTransport`, `AV_homfly_lift_eq`, `AV_rotationNumber_tcp`. Both row theorems
now feed `A2_cvRNear_of_rows` (X1Rows) directly: `availability_zero_one` is its first argument.

## 7. Open items

* Still open (placeholders only in `RLaneX1_Assembled2.lean`): `generic_transport` (173), `generic_selected` (174),
  `extreme_pair_zero` (175), `extreme_transport` (176), `extreme_selected` (177), `cv_R` (178).
* When `RLaneX1Rows2.lean` moves into `work/lean` (e.g. as `RProof/X1Rows2.lean`), only the header prose needs
  the path/date note; the import `CV.PieceHomflyTransport` must stay. Its axiom footprint adds `SM.lp_lm`,
  `SM.lp_lm_uniqueness` to the R lane (both accepted literature interfaces).
* The wave-2 assembler note in `RLaneX1_Assembled2.lean` (lines 106–120) is the only prose added to the assembled file.
