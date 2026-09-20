# Row 57 lem:gauss-two-discs — WAVE-2 ASSEMBLY REPORT (`W2_Assembled.lean`)

Written 2026-09-19 (14:50 UTC / 10:50am ET) by the wave-2 (U12) assembler.  Directory: `work/drafts/twodiscs/`.
Inputs: `W1_Assembled.lean` (13 815 lines, 62/92 leaves closed) and the wave-2 unit files `W2_U5, W2_U6, W2_U7,
W2_U8, W2_U9` (+ `W2_*_REPORT.md`).  Outputs: **`W2_Assembled.lean`** (20 912 lines, all 92 leaves closed) and the
port **`port/SM/GaussTwoDiscs*.lean`** (6 modules, `port/PORT_REPORT.md`, `port/check_57_identity_port.py`).
Scratch (private): `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/asm2/`
(`verify_units2.py`, `merge2.py`, `clash_scan2.py`, `port.py`, `compile_port.sh`, `W2_Assembled_axioms.lean`,
`axioms_port.lean`, `compile_main.log`, `compile_axioms.log`, `compile_port.log`, `port_*.log`).  Nothing was written
under `work/lean`; no `lake build`; the only compile command used is `cd work/lean && lake env lean …` (for the port
modules with `--root`/`-o` into the scratch object tree, §6).

## 0. Result

| check | result |
|---|---|
| `cd work/lean && lake env lean ../drafts/twodiscs/W2_Assembled.lean` | **0 errors, 0 `declaration uses sorry` warnings** (exit 0, 92 s wall); 80 linter/deprecation warnings (§7) |
| `python3 check_57_identity.py W2_Assembled.lean` | `IDENTITY OK` (DEFS, BUNDLE, THM byte-identical to `Statements_FINAL.lean`) |
| leaves | 92 declared (each exactly once); **92 closed, 0 open** (wave 2 closed the 30 that were open: U5 2, U6 8, U7 7, U8 8, U9 5) |
| `grep -c sorry` | 33 (`W1_Assembled`) → **3** (three prose mentions in the skeleton/header notes; no `sorry` token in any declaration) |
| `#print axioms` (scratch copy `W2_Assembled_axioms.lean` = the file + 96 `#print axioms` lines before `end SM`; 0 errors) | **all 96 = `[propext, Classical.choice, Quot.sound]`**: the 92 leaves, **`SM.lem_gauss_two_discs`** and the three bridges `SM.two_regions_plane`, `SM.isPLDisc_of_isPLDiscSphere`, `SM.isPLDisc_closure_interior`.  No `sorryAx`, no literature axiom, no `Lean.ofReduceBool`/`native_decide`, no unregistered axiom |
| corrected forms (rule 3) | 1 leaf statement changed in this wave: `U5_pushforward_edges` (false as stated, replaced by U5's proved corrected form; no consumer) — §2.2 |
| clash scan vs work/lean (namespace-aware) | **0 clashes** among the 1 467 declarations of `W2_Assembled.lean` vs the 25 325 of `work/lean` (the wave-1 clash `SM.polygonImage` was resolved by the rename to `embeddedPolygonImage`, D-TD-3; none remains) — §5 |
| port | 6 modules under `port/SM/`, each compiled to an olean in import order in a scratch object tree, **0 errors**; `#print axioms SM.lem_gauss_two_discs` through `import SM.GaussTwoDiscs` = `[propext, Classical.choice, Quot.sound]`; frozen blocks byte-identical (DEFS in `GaussTwoDiscsDefs`, BUNDLE+THM in `GaussTwoDiscs`); no `sorry`/`#print`/`#eval` string anywhere — §6 and `port/PORT_REPORT.md` |

## 1. Verification of the unit files (task step 1)

Method (`verify_units2.py`, the wave-1 `verify_units.py` re-pointed at `W1_Assembled.lean` as base): `difflib.SequenceMatcher`
(line-based, no junk heuristic) of each `W2_U<k>.lean` against `W1_Assembled.lean`.  Every base line removed or changed must be
a `  sorry` body of the unit's own leaves; every declaration in inserted text must carry the unit's prefix `u<k>h_` or sit in a
`u<k>h_`-prefixed namespace; scoping commands in inserted text are listed.  `check_57_identity.py` on the five unit files:
all `IDENTITY OK`.

| unit | lines | diff hunks | base lines removed | own leaves closed | new decls (all prefixed?) | imports added | scoping in inserted text |
|---|---|---|---|---|---|---|---|
| U5 | 15 676 | 1 insert (anchor 10670, 1 613 lines) + 1 replace | 1 `sorry` | 1/2 (`U5_exists_ear_homeo`; `U5_pushforward_edges` left open, false — §2.2) | 117 `u5h_` (102 thm, 15 def) + tactic macro `u5h_hull_perm` — yes | none | `section U5_block` (`open Filter`; 5 inner `section generic/concrete` with `variable`), `section U5_block2`; all closed |
| U6 | 14 150 | 1 insert (10734, 280 lines) + 8 replaces | 8 `sorry` | 8/8 | 20 `u6h_` (thm) — yes | none | none |
| U7 | 13 989 | 1 insert (10785, 51 lines) + 7 replaces | 7 `sorry` | 7/7 | 14 `u7h_` (thm) — yes | none | none |
| U8 | 17 167 | 1 insert (10826, 3 021 lines) + 8 replaces | 8 `sorry` | 8/8 | 317 `u8h_` (280 thm, 35 def, 2 structures; 66 short names live inside `namespace u8h_AnnCtx` / `namespace u8h_AnnData`, full names `SM.u8h_Ann….*`; `_root_.SM.u8h_s`) — yes (namespace-aware) | none | `namespace u8h_AnnCtx` (`variable … include C`, 2 `omit C in`), `namespace u8h_AnnData` ×2 (`variable … include D`); 4 `open Classical in`; all closed |
| U9 | 15 162 | 1 insert (10897, 1 347 lines) + 5 replaces | 5 `sorry` | 5/5 | 98 `u9h_` (94 thm, 4 def) — yes | none | none |

Conclusion: no unit touched a frozen block, a leaf statement, a leaf docstring or another unit's leaf; every removed base line is
a `  sorry` of the unit's own leaves (29 in all); every helper is prefixed; all scoping is closed or `in`-scoped; no imports were
added (the 14 of `W1_Assembled` suffice).  The five insert anchors are pairwise distinct and no insert falls inside another unit's
replaced range, so the merge needed no ordering choice and no renaming.

Black boxes declared by the units (all by name, statements untouched — verified by the diff):
* U5 ← U1 `U1_triangle_convex`, `U1_isPositiveAffineOn_mono`; U2 `U2_triangulation_square`, `U2_isCompact_of_triangulation`;
  U3 `U3_refine_along_lines`; U4 `U4_polygonImage_subset_interior_square`; helpers `u1h_`, `u2h_`, `u3h_`, `u4h_` (W2_U5_REPORT §5).
* U6 ← **U5 `U5_exists_ear_homeo`** (the corrected form with `hcut`, used once in the induction step of `u6h_ambient_induction`
  with `U' := u4h_regionOf (deleteVertex P j)`); U1 `U1_triangle_isCompact/_convex/_interior_nonempty`,
  `U1_interior_convex_isConnected`, `U1_compl_compact_convex_isConnected`; U2 `U2_triangulation_square/_triangle`;
  U3 `U3_isPositivePLOn_comp`; U4 `U4_triangle_base`, `U4_exists_insideModel` and the `u4h_regionOf*` family.
* U7 ← **U6 `U6_exists_ambientParam`, `U6_interiorRegion_eq`**; U1 (`_isDisc`, `IsHomeoOnto` toolkit), U2 (`U2_inverse_isPositivePLOn`,
  `U2_triangulation_empty`), U3 (`U3_isPositivePLFromPlane_inv` in its corrected form, `u3h_seam`, …), U4.
* U8 ← **U6 `U6_exists_ambientParam`, `U6_exteriorRegion_eq`**; U1, U2 (`U2_continuousOn_of_isPositivePLOn`,
  `U2_inverse_isPositivePLOn`, `U2_triangulation_square`), U3 (`U3_isPositivePLToPlane_comp`, `U3_refine_into`, 25 `u3h_`).
* U9 ← **U6 `U6_exists_ambientParam`, `U6_interiorRegion_eq`** (once, in `u9h_interiorRegion_eq`); U1, U2 (`U2_local_structure`,
  `U2_interior_face_subset_interior`), U4 (`U4_range_traversal`, `U4_exists_insideModel`, `u4h_Region` …).
* Wave 1 (already in `W1_Assembled`) ← the wave-2 leaves `U6_exists_ambientParam`, `U7_closure_interiorRegion_eq`,
  `U7_pl_discs_inner`, `U8_closure_exteriorRegion_eq`, `U8_pl_discs_outer`, `U9_traversalPositiveFor_iff_cyclicPos` (U10),
  `U7_pl_discs_inner`, `U8_pl_discs_outer` (U11), and the row/bridges ← `U6_two_regions`, `U6_exterior`, `U6_two_regions_plane`,
  `U7_isPLDisc_of_isPLDiscSphere`, `U7_isPLDisc_closure_interior`.

Every black box is now the same declaration as the producing unit's closed leaf (same name, same statement), so the dependency
chain U5 → U6 → {U7, U8, U9} → {U10, U11} → row closes without glue: `sorryAx` disappears from every declaration (§3).

## 2. Merge (task step 2)

### 2.1 Method
`merge2.py`: the difflib opcodes of each unit against `W1_Assembled.lean` are replayed onto `W1_Assembled.lean` — the one `insert`
hunk per unit (its helper block) is placed before the base line it precedes in the unit file, each `replace` hunk (a single
`  sorry` line → the leaf body, plus any helper the unit placed right after that leaf, e.g. U6's optional
`u6h_sphereCircle_subset_closure_regionOf`) replaces that line.  Assertions: every replaced range is exactly one `  sorry` line, no
two units replace the same line, no insert falls inside a replaced range, no import lines in hunks.  Anchors (1-indexed base
lines): U5 10670, U6 10734, U7 10785, U8 10826, U9 10897 — no shared anchor.  A `W2 assembly note` block after the W1 note records
the correction below.  File order: imports (14), notes, frozen §1-§4 (lines 77-276), §L: U1 (283), U2 (854), U3 (2544), U4
(5232), U5 (10677), U6 (12601), U7 (13007), U8 (13222), U9 (16629), U10 (18044), U11 (20291), frozen §5 (20838), row (20873),
bridges §6 (20893), `end SM` (20912).

### 2.2 Corrected form applied (rule 3) — marked `W2 ASSEMBLY (rule 3)` in the docstring
**`U5_pushforward_edges`** — false as stated (W2_U5_REPORT.md §3; kernel-checked counterexample
`u5h_pushforward_edges_false : ¬ u5h_pushforward_edges_stmt`, where `u5h_pushforward_edges_stmt` is the skeleton statement as
a `Prop`: `n = 3`, `P = (A, A, B, C)` with a repeated vertex at `j = 1`, `h = Homeomorph.refl`, `U' = conv {B, C, A}` with the
one-face triangulation; the conclusion demands a face edge equal to the point `edgeSegment P 0 = {A}`, impossible since face-edge
endpoints are distinct).  Applied exactly as in wave 1 §2.2: the leaf keeps its name and conclusion; its hypotheses are replaced by
those of U5's proved `u5h_pushforward_edges` — the clause `hC : h '' polygonImage (deleteVertex P j) = polygonImage P` is
dropped; `hedge'`/`huniq'` are required only for `i ≠ -1`; new hypotheses `m : Plane`, `hm : h m = P j`, `hfa`, `hfc` (the diagonal
ends are fixed), `hfix` (every non-diagonal edge of the cut polygon is fixed pointwise), `hedge1`, `hedge2`, `huniq1`, `huniq2`
(the two halves `[P (j-1), m]`, `[m, P (j+1)]` of the diagonal are face edges of exactly one face) — the shape produced by
`U5_exists_ear_homeo`.  Body: `u5h_pushforward_edges P j U' Kin h hh hU m hm hfa hfc hfix hedge' hedge1 hedge2 huniq' huniq1 huniq2`
— **closed**, sorry-free.  Consumers: **none** (checked by grep over `W1_Assembled`, all five unit files and `Statements_FINAL`;
U6 uses only `U5_exists_ear_homeo`), so nothing was re-threaded.  The leaf is not in a frozen block; `Statements_FINAL.lean`
is unchanged (identity check OK).

No other rule-3 case arose in wave 2: U6, U7, U8, U9 proved every leaf as frozen, including `U9_lift_preserves_cyclicPos` (true as
stated, not only vacuous — W2_U9_REPORT §2.6), so the wave-1 note on it is closed without a replacement.

## 3. Axioms (task step 3)

`W2_Assembled_axioms.lean` (scratch) = `W2_Assembled.lean` + `#print axioms` for the 92 leaves, `lem_gauss_two_discs` and the 3
bridges, compiled with `lake env lean` from `work/lean` (a temporary copy in `drafts/twodiscs`, deleted afterwards): 0 errors,
98 s wall, 96 lines printed, **every one `[propext, Classical.choice, Quot.sound]`**.  In particular
```
'SM.lem_gauss_two_discs' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.two_regions_plane' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.isPLDisc_of_isPLDiscSphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.isPLDisc_closure_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The four wave-1 leaves that carried `sorryAx` through the open wave-2 leaves (`U10_boundary_map_of_lift`, `U10_pl_extension`,
`U11_boundary_homeo_of_lift`, `U11_top_extension`) and the 30 wave-2 leaves are now sorry-free with no change to their bodies.

## 4. Remaining `sorry` leaves

**None.**  `grep -n sorry W2_Assembled.lean` finds only the three prose mentions of the skeleton/header notes (lines 39, 49, 277:
"every leaf is `sorry`" describing the skeleton stage); the compile emits no `declaration uses sorry` warning.  (In the port these
three mentions are reworded, §6.)

## 5. Namespace-aware clash scan against work/lean (task step 3, last item)

`clash_scan2.py` (= wave-1 `clash_scan.py` re-pointed): 1 467 declarations in `W2_Assembled.lean` (48 frozen/skeleton vocabulary,
92 `U<k>_` leaves, 1 327 `u<k>h_` helpers: u1h 33, u2h 111, u3h 158, u4h 280, u5h 117, u6h 20, u7h 14, u8h 317, u9h 98, u10h 148,
u11h 31) vs 25 325 declarations in `work/lean` (excluding `.lake`).  **0 exact clashes.**  The wave-1 clash `SM.polygonImage` vs
`SM.Rounding.polygonImage (C : PolyComp)` no longer exists: the frozen definition is `SM.embeddedPolygonImage` since D-TD-3 (the
rename is in `Statements_FINAL.lean`, the skeleton, `W1_Assembled` and every unit file; the identity check enforces it).  Same short
name in a different namespace (harmless, as in wave 1): `SM.Triangle.map` ~ `SM/PolynomialBlock.lean:267`, `SM/LinkRecordExtras.lean:478`;
`SM.u4h_SplitCtx.hne` ~ `SM/FrontRealizeGeometry.lean:1058`; `SM.u4h_SplitCtx.side` ~ `SM/GermSides.lean:18`.  New in wave 2 and
clash-free: `SM.u8h_AnnCtx.*`, `SM.u8h_AnnData.*` (66 short names, only reachable with their prefix).

## 6. Port (task step 4) — `work/drafts/twodiscs/port/SM/`

Generator `asm2/port.py`; recipe and every detail in **`port/PORT_REPORT.md`**.  Summary:

| module | W2_Assembled lines | lines | decls | leaves | `-o` compile | warnings |
|---|---|---|---|---|---|---|
| `SM/GaussTwoDiscsDefs.lean` | imports; header prose (reworded) + provenance note; **frozen DEFS** (77-276) | 274 | 32 | 0 | 19 s | 0 |
| `SM/GaussTwoDiscsPL.lean` | U1-U3 (277-5231) | 4 972 | 352 | 46 | 35 s | 2 |
| `SM/GaussTwoDiscsEars.lean` | U4 (5232-10676) | 5 462 | 290 | 9 | 31 s | 0 |
| `SM/GaussTwoDiscsAmbient.lean` | U5-U9 (10677-18043) | 7 385 | 600 | 30 | 35 s | 11 |
| `SM/GaussTwoDiscsExtension.lean` | U10-U11 (18044-20837) | 2 811 | 188 | 7 | 23 s | 2 |
| `SM/GaussTwoDiscs.lean` | **frozen BUNDLE**, row (**frozen THM** header), §6 bridges (20838-20912) | 92 | 5 | 0 | 20 s | 0 |

* Each file starts with `-- Ported <HH:MM>Z 2026-09-19 from work/drafts/twodiscs/W2_Assembled.lean by the pod executor (files
  prepared by the U12 assembler)` (literal placeholder), imports in chain order (`Defs` carries the 14 imports; each later module
  imports only its predecessor), a module docstring, `namespace SM` / `open Set OnePoint` / `variable {n : ℕ}`, body, `end SM`.
* Compiled in import order to oleans in the scratch object tree `asm2/porttree/O` (symlinks to `work/lean/.lake/build/lib/lean/SM`)
  with `cd work/lean && lake env sh -c "LEAN_PATH=\"$O:\$LEAN_PATH\" lean --root=work/drafts/twodiscs/port -o $O/SM/<m>.olean
  ../drafts/twodiscs/port/SM/<m>.lean"`: **all six 0 errors**, chain 2 min 43 s; `asm2/axioms_port.lean` (`import SM.GaussTwoDiscs`,
  96 `#print axioms`): **96 × `[propext, Classical.choice, Quot.sound]`**, including `SM.lem_gauss_two_discs` and the 3 bridges.
* No `sorry` / `#print` / `#eval` string in any module (code or prose): the three prose mentions and the `W1 ASSEMBLY` / `W2 ASSEMBLY`
  notes are reworded (PORT_REPORT.md §3).  No declaration renamed; 9 binder renames for unused helper variables.
* Frozen blocks byte-identical: DEFS in `SM/GaussTwoDiscsDefs.lean`, BUNDLE and THM in `SM/GaussTwoDiscs.lean` —
  `python3 port/check_57_identity_port.py` → `IDENTITY OK` (re-point `check_57_identity.py` at those two files).
* Warnings: 80 → 15 (10 leaf-header unused variables kept as printed, 5 `<;>` style notes), §7 and PORT_REPORT.md §4.

## 7. Warnings in the merged file (0 errors) — and what the port does with them

80 non-`sorry` warnings in `W2_Assembled.lean` (`compile_main.log`): 25 deprecations under the pin (`Set.mem_setOf_eq` ×10,
`Set.setOf_true`, `dif_pos` ×7, `if_pos` ×2, `if_neg` ×2, `continuousOn_iff_continuous_restrict` ×2, `ContinuousOn.restrict`),
21 unused-variable (10 in leaf headers kept as printed: `U2_local_structure` `hx`; `U5_exists_ear_homeo` `hn`, `hP`, `hedge`;
`U6_exteriorRegion_eq` and `U6_interiorRegion_eq` `hn`, `hP`; `U10_boundary_map_of_lift` / `U11_boundary_homeo_of_lift` `hD'`; 11 in
helpers), 18 unused-`simp`-argument (6 in `u4h_`, 6 in the `u8h_f_` fan-toolkit copy, 6 in the `u10h_` original), 5 `haveI → have`
"Try this", 5 `<;>`-style notes, 6 unused/never-executed tactic notes (3 tactics, each reported twice).  The port (§6,
PORT_REPORT.md §4) removes 65 of them by 56 within-line edits (all 25 deprecations — the replacements are exact aliases, checked
with `#check` —, the 5 `haveI`s, the 18 unused simp arguments, the 3 never-executed tactics, the 11 helper-level unused variables by
`_`-prefix or anonymous binders); it keeps the 10 leaf-header unused variables (statements as printed) and the 5 `<;>` style notes
(rewriting `… <;> ring_nf <;> linarith` as a sequence would obscure the intent; listed), i.e. 15 warnings remain in the port.

## 8. Notes for the executor (registration)

* The port files are ready to copy to `work/lean/SM/` (same relative paths); the header line's `<HH:MM>` placeholder is to be filled
  at port time.  Compile order and times: PORT_REPORT.md §2.  No file under `work/lean` was touched by this assembler.
* Registration: `lem:gauss-two-discs` (row 57) → declaration `SM.lem_gauss_two_discs`, module `SM.GaussTwoDiscs`, in
  `lean-declarations.json`; then `python3 tools/check_lean.py work/lean`.  The bridges `SM.two_regions_plane`,
  `SM.isPLDisc_of_isPLDiscSphere`, `SM.isPLDisc_closure_interior` live in the same module for consumers.
* Freeze check after the port: `python3 work/drafts/twodiscs/port/check_57_identity_port.py` (DEFS in `SM/GaussTwoDiscsDefs.lean`,
  BUNDLE and THM in `SM/GaussTwoDiscs.lean`), or re-point `check_57_identity.py` at those two files.
* Known duplication left in place (optional clean-up, no effect on correctness): U8's `u8h_f_` copy of U10's fan toolkit
  (73 declarations, byte-identical modulo prefix per W2_U8_REPORT §4) — U8 precedes U10 in the frozen order; deduplicating means
  moving U10's `u10h_D0 … u10h_fan_triangulation`, `u10h_gap … u10h_cover` before U8 (into `GaussTwoDiscsAmbient`) and
  renaming.  Likewise U9 re-proves `u10h_cyclicPos_total` as `u9h_cyclicPos_total` (W2_U9_REPORT §6).
