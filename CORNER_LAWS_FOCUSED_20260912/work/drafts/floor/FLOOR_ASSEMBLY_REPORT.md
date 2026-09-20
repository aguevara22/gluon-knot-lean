# Floor lane — wave 2 assembly report (2026-09-15, 17:12 UTC / 1:12pm ET, assembler)

Directory: `work/drafts/floor/`.  Output: **`Floor_Assembled.lean`** (3815 lines) = `Wave2_Skeleton.lean`
(3071 lines; = `Wave1_Assembled.lean` with the judge's D-FL-4 repair) with every proved hunk of the four
wave-2 unit files `W2_{B3,EQ,LIFT3,C}.lean` applied.  Compile: `cd work/lean && lake env lean
../drafts/floor/Floor_Assembled.lean` — exit 0, **0 errors**, 13 s warm, **no `declaration uses sorry`
warning**.  Nothing under `work/lean` was touched; no `lake build`.

**Every leaf of the floor lane is now proved.  `sorryAx` appears nowhere; rows 99 and 100 are proved
conditionally on `TransverseFrontBound`, and (port dry run, §7.4) unconditionally once the accepted
`SM.fd_contact` is imported.**

## 1. Per-unit diff verification (each `W2_<u>.lean` vs `Wave2_Skeleton.lean`)

Rule: a unit may only (a) replace the `sorry` body of ITS OWN leaf and (b) insert prefixed helper
declarations at declaration boundaries; no statement / definition / name / docstring / header may change.
Checker: `tools/wave2_assemble.py` (diff normal format; every `<` line must be `  sorry`; every `c` hunk
one base line = `  sorry`; every `a` hunk before a docstring/declaration/blank; added lines scanned for
`sorry|admit|native_decide|axiom|set_option|@[simp]|attribute|unsafe|implemented_by|extern`; every added
declaration name must carry the unit prefix, must not shadow a base name, must not repeat across units).

| unit | hunks (skeleton lines) | removed | leaf proved | helpers (prefix) | verdict |
|---|---|---|---|---|---|
| W2_B3 | `958a959,1059`, `967c1068,1088` | 1 × `  sorry` | `ub_tangencyCount_of_admissible` | 5 (`ub3_`) | OK |
| W2_EQ | `1713a1714,1741`, `1718c1746,1750` | 1 × `  sorry` | `usw_P_switchAll` | 1 (`ueq_`) | OK |
| W2_LIFT3 | `2922a2923,3406`, `2931c3415,3417` | 1 × `  sorry` | `ulift_exists_transverse_lift` | 51 (`ul3_`; 6 defs incl. `structure ul3_LiftData`, in two closed nested sections `ul3_knot`, `ul3_marking` with `variable {F} {X} {c}`) | OK |
| W2_C | `2934a2935,3033`, `2942c3041,3047` | 1 × `  sorry` | `cf_thm_carrierfloor_C_of_bound` | 4 (`uc_`) | OK |

No violations; all four units adopted in full.  Each leaf's `theorem … := by` header line is byte-identical
to the skeleton and occurs exactly once in the output.  61 new helper names, no duplicates
(`tools/wave2_new_names.txt`), none shadows a skeleton name, none is dotted (all plain names in `namespace SM`).
No `open`/`namespace`/`set_option` was added by B3, EQ, C; LIFT3 adds only the two nested sections above.

`tools/wave2_stmt_check.py Wave2_Skeleton.lean W2_<u>.lean` was also reported by each unit (242/242); re-run on
the assembled file below.

## 2. Assembly method

`python3 tools/wave2_assemble.py <floor dir> Wave2_Skeleton.lean B3,EQ,LIFT3,C Floor_Assembled.lean`
(same design as `tools/wave1_assemble.py`): records per skeleton line the replacement (must be a `sorry` body;
conflict = violation) and the insertions after it, walks the skeleton once, then verifies
(i) each of the 8 hunk blocks occurs verbatim and contiguously in the output — at assembled lines 959, 1068,
1835, 1867, 3076, 3568, 3574, 3680; (ii) all 3067 non-replaced skeleton lines are present in order;
(iii) leaf headers once each.  Authoritative post-check: `diff Wave2_Skeleton.lean Floor_Assembled.lean | grep
'^<'` prints exactly the 4 `  sorry` lines.  No hunk overlapped, so no de-duplication or renaming was needed.

Assembled positions: `ub3_*` l.959-1059, leaf `ub_tangencyCount_of_admissible` l.1063 (body l.1068-1088);
`ueq_iota_switchAll_rcompetitor` l.1835-1862, leaf `usw_P_switchAll` l.1866; `ul3_*` block l.3076-3559,
leaf `ulift_exists_transverse_lift` l.3564; `uc_*` l.3574-3672, leaf `cf_thm_carrierfloor_C_of_bound` l.3679;
`cf_thm_carrierfloor_of_bound` l.3691, `uf_z_parity` l.3789, `thm_floor_of_C` l.3804, `thm_floor_of_bound` l.3808.

## 3. Unproved leaves

**None.**  `grep -c sorry Floor_Assembled.lean` = **2**, both docstring mentions (l.30 in the module header,
l.418 in the §8 header) — no `sorry` term anywhere.  Skeleton: 6 (4 leaf bodies + the 2 mentions).  No
assembler proofs were needed in wave 2 (wave 1's two, `CarrierFloorCData.floor_support` and
`ub_exists_admissibleDirection`, are in the skeleton).

## 4. Compile, sorry count, axioms

- `lake env lean ../drafts/floor/Floor_Assembled.lean`: exit 0, 0 errors, 13 s.  Warnings: only the 2 inherited
  unused-variable lints on FROZEN binders (`hturn` in `ub_exists_direction` l.608, `hu` in `ucurl_exists_curled`
  l.2364).  Log: scratchpad `Floor_Assembled_compile.log`.
- `#print axioms` (scratch copy `…/scratchpad/Floor_axioms.lean` = the file + 13 print lines; exit 0):

| declaration | axioms |
|---|---|
| `SM.cf_thm_carrierfloor_R` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `SM.cf_thm_carrierfloor_A` | `[propext, Classical.choice, Quot.sound]` |
| `SM.cf_thm_carrierfloor_B` | `[propext, Classical.choice, Quot.sound]` (was `sorryAx` after wave 1) |
| `SM.cf_thm_carrierfloor_C_of_bound` | `[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `SM.cf_thm_carrierfloor_of_bound` | `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` |
| `SM.thm_floor_of_C` | same as `_of_bound` |
| `SM.thm_floor_of_bound` | same |
| `SM.uf_z_parity` | same |
| wave-2 leaves `ub_tangencyCount_of_admissible`, `ulift_exists_transverse_lift`, `ui_mirrorSubstitution`, `ub_BClaim` | `[propext, Classical.choice, Quot.sound]` |
| `usw_P_switchAll` | `[propext, Classical.choice, Quot.sound, SM.lp_lm, SM.lp_lm_uniqueness]` |

  **No `sorryAx` anywhere.**  `lit_homfly` (`lit:homfly`), `lp_lm` (`lp:lm`), `lp_lm_uniqueness`
  (`lp:lm-uniqueness`) are the registered literature interfaces of `work/lean/axiom-policy.json`; `lit_homfly` enters
  through `homfly_descent` (clause (R) `knot_reverse`, and `uf_a_floor_of_C`), `lp_lm*` through `P`.

## 5. Statement byte-identity (`tools/wave2_stmt_check.py <base> Floor_Assembled.lean`)

- vs `Statements_FINAL.lean`: **73 declarations checked, 72 byte-identical, 1 mismatch** — exactly the ONE intended
  difference: `structure MirrorSubstitutionData`, field `coeff : … = (-1) ^ k.toNat * coeffAt (-d) k f` in
  `Statements_FINAL.lean` vs `(-1) ^ k.natAbs` in the skeleton and the assembled file (judge's repair **D-FL-4**,
  after wave 1 refuted the `toNat` form by `ui_coeff_toNat_false`; the repaired field is proved by
  `ui_coeffAt_iotaHom`, so `ui_mirrorSubstitution` is a closed term with standard axioms).  Nothing else differs.
- vs `Wave2_Skeleton.lean`: **242 checked, 242 byte-identical, 0 mismatches**.
- vs `Wave1_Assembled.lean`: 241/242, the same single D-FL-4 field.

## 6. Name-clash scan against `work/lean` (674 `.lean` files outside `.lake`)

- The **61 new helpers**: grepped whole-word (any occurrence) and as a declaration `(theorem|def|…) (SM.)?NAME`:
  **0 hits**.
- **All 303 declarations** of the assembled file (namespace-aware: the file is `namespace SM`, sections are not
  namespaces; dotted names checked on their last component inside the corresponding namespace): 4 candidate hits,
  2 real —
  - `SM.TransverseKnot.spatial` = `work/lean/SM/SrcContact.lean` l.93 (`namespace TransverseKnot`, `def spatial`) and
    `SM.TransverseKnot.spatial_T` = SrcContact.lean l.100 (`@[simp] theorem spatial_T`).  These are exactly the §1
    "copied VERBATIM … deleted when the contact lane's module lands" declarations; the contact module landed today
    (ported 15:05Z, after the wave-1 scan).  Field bodies byte-identical (assembled l.66-70 = SrcContact l.94-98);
    header differs only by binder placement (`(K : TransverseKnot)` explicit vs `variable (K)`), same type
    `SM.TransverseKnot.spatial (K : TransverseKnot) : SpatialLink 1`.  **Must be deleted at port** (§7).
  - false positives: `PolygonDiagram.reverse` vs `ClosedC1Curve.reverse` (TurnLift.lean:237) and `Diagram.reverse`
    (LinkDiagram.lean:1213) — different namespaces.
- `SM.TransverseKnot.Reads`, `TransverseFrontBound`, `FdContactShape`, `transverseFrontBound_of_fdContactShape`: no
  declaration in `work/lean` (the accepted `FdContactData.representative_bound` spells the reading out as
  `Nonempty (K.spatial.HeightMarking K.spatial.projLoop X)` — no `Reads` name).

## 7. Port plan (for the porter; nothing ported by the assembler)

### 7.1 What becomes `SM/CarrierFloor.lean`

Everything from §1 through §8.9 (assembled l.45-3815: `namespace SM`, `open Link`, `open scoped ContDiff`,
`noncomputable section`, `open Classical`, the two `section Floor … end Floor` blocks with `open Carrier`,
`variable {n : ℕ} [NeZero n]`, the nested sections `ub2` (`open Set CornerRounding`), `ul3_knot`, `ul3_marking`, one
`open CornerRounding in`), EXCEPT the two §1 copies:

| §1 item (assembled lines) | action |
|---|---|
| module docstring paragraph l.55-61 ("copied VERBATIM … deleted here") | reword: `TransverseKnot.spatial` is the accepted `SM/SrcContact.lean` one; `Reads` is defined here |
| `/-- The transverse knot … -/ def TransverseKnot.spatial … where` l.63-70 | **delete** (accepted SrcContact.lean l.93, byte-identical body) |
| `@[simp] theorem TransverseKnot.spatial_T` l.72 | **delete** (accepted SrcContact.lean l.100) |
| `theorem TransverseKnot.spatial_projLoop_γ` l.74-76 | unused later (0 uses); keep (compiles by `rfl` against the accepted def — dry run) or drop; the accepted form is `SpatialLink.projLoop_γ` + `spatial_T` |
| `def TransverseKnot.Reads` l.78-83 | **keep verbatim** — `Nonempty (K.spatial.HeightMarking K.spatial.projLoop X)`, now in terms of the accepted `K.spatial`; it is definitionally the hypothesis of the accepted `FdContactData.representative_bound` |
| `TransverseFrontBound`, `FdContactShape`, `transverseFrontBound_of_fdContactShape` l.85-109 | keep verbatim |

Is §1 byte-identical to the accepted module?  `spatial`: field lines identical, header differs only by the
`variable (K)` convention; `spatial_T`: identical modulo the same binder; `Reads`: **not present** in `work/lean`
(neither `SrcContact.lean` nor `FdContactStatements.lean` names the reading) — it must be defined in the port,
verbatim as §1 has it.  `spatial_projLoop_γ` has no accepted counterpart (the accepted `spatial_projLoop : K.spatial.projLoop i = K.xz` is a different statement).

Imports: the six current ones (`SM.Curl`, `SM.TransverseFront`, `SM.CeSmoothingRecord`, `SM.CornerStateSum`,
`SM.LinkPositiveLift`, `SM.UniformRotation`) **plus `SM.SrcContact`** (for `TransverseKnot.spatial`), or
`SM.FdContactUnits` if the §7.4 bridge is included (it imports `FdContactStatements` → `SrcContact`).

Suggested split, mirroring the contact lane (`SrcContact` / `FdContactStatements` / `FdContactUnits`): §1-§7 (the
frozen statements, 52 base declarations) as `SM/CarrierFloorStatements.lean` and §8 (the 231 prefixed helpers and
unit leaves + the row theorems `cf_thm_carrierfloor_of_bound`, `thm_floor_of_C`, `thm_floor_of_bound`) as
`SM/CarrierFloorUnits.lean`; a single `SM/CarrierFloor.lean` is equally fine (3.8k lines, 13 s).

### 7.2 Header

Replace l.1-43 by the porter's standard header line ("Ported <time>Z 2026-09-15 from
work/drafts/floor/Floor_Assembled.lean lines 45-3815 … by the pod executor; body verbatim except this header, §1
(the two `TransverseKnot.spatial`/`spatial_T` copies removed — accepted in SM/SrcContact.lean) and the rewordings of
§7.3") followed by the imports and the module docstring l.8-43 with these edits: l.29-31 ("Check: `cd work/lean &&
lake env lean ../drafts/floor/Statements_FINAL.lean` — 0 errors; the only `sorry`s are the proof-route leaves … Nothing
here is to be ported without the statement review.") → state that every leaf is proved and the file is the port;
keep the accepted-inputs paragraph l.33-43 and add `SM/SrcContact.lean` (`TransverseKnot.spatial`) and, if §7.4 is
included, `SM/FdContactStatements.lean` / `SM/FdContactUnits.lean` (`FdContactData`, `fd_contact`).

### 7.3 Lines containing `sorry` / `#print` / `#eval` (must be reworded or removed)

Only **2** lines, both prose; no `#print`, `#eval`, `#check`, `#reduce`, `#synth`, `#guard` anywhere:
- l.30: "`sorry`s are the proof-route leaves of §8 (unit statements, frozen) and the two row theorems'" → reword
  (part of the §7.2 header edit).
- l.418: "/-! ## 8. The proof route: frozen unit statements (leaves `sorry`; prefixes per PLAN_FINAL.md §4)." →
  "(all leaves proved; prefixes …)".
Other prose that describes the draft state and should be adjusted (no forbidden strings): §1 docstring l.55-57
(the "copied VERBATIM … deleted here" sentence); the `TransverseFrontBound` docstring l.85-88 ("the EXPLICIT
HYPOTHESIS of the (C) route until row 94 lands") — row 94 HAS landed (`SM.fd_contact`, SM/FdContactUnits.lean l.1439,
registry status `implemented`).

### 7.4 Closing the hypothesis: rows 99 and 100 unconditionally (port dry run, compiled)

Scratch file `…/scratchpad/Floor_PortDryRun.lean` = the assembled file with `import SM.FdContactUnits`, the two §1
copies removed, and appended before the closing `end`:
```
theorem fdContactShape_sl : FdContactShape SM.sl where
  front_writhe := fd_contact.front_writhe
  representative_bound := fun K X hX => by
    have h := fd_contact.representative_bound K X hX
    exact_mod_cast h
theorem transverseFrontBound : TransverseFrontBound :=
  transverseFrontBound_of_fdContactShape fdContactShape_sl
theorem cf_thm_carrierfloor : CarrierFloorData := cf_thm_carrierfloor_of_bound transverseFrontBound
theorem thm_floor : FloorTheoremData := thm_floor_of_bound transverseFrontBound
```
`lake env lean` on it: **exit 0, 0 errors, 12 s** (so `Reads` unifies with the accepted `Nonempty (…HeightMarking…)`
hypothesis by delta, and `spatial_projLoop_γ`'s `rfl` survives against the accepted `spatial`).  `#print axioms
SM.cf_thm_carrierfloor` = `SM.thm_floor` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly,
SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` — every non-standard
axiom is in `axiom-policy.json` `literature`; no `sorryAx`.  Names: rows `cf:thm-carrierfloor` and `thm:floor` are
`status: pending` with empty `declaration` in `work/lean/lean-declarations.json` and are NOT in the policy's
fixed `targets`; the registry pattern (`fd:contact` → `SM.fd_contact`) and the file's §6 proposal give
`SM.cf_thm_carrierfloor` (module `SM.CarrierFloor…`) and `SM.thm_floor`.  Recommended: port these four
theorems as a §9 and register both rows.  (The bridge is the porter's/judge's to adopt — it is not in
`Floor_Assembled.lean`, whose statements stay frozen.)

### 7.5 Other porting notes

- `Diagram.switchAll` and its `usw_switchAll_*` facts, `iotaHom`, `MirrorSubstitutionData`, `rotPlane`/`downDir`,
  `liftY0`/`circBump`/`liftY`/`liftT`/`LiftAdmissible`, `Round`, `junctionTemplate`, `AllPosOrOneNeg`,
  `tangencySet`, `TangencyCount`: no declaration in `work/lean` (§6) — they port as new library material.
- Semantic (not textual) duplicates from wave 1 (`ul1_circBump_*` / `ul2_circBump_*` etc., WAVE1_ASSEMBLY_REPORT.md
  §1) remain; harmless, can be pruned later.
- The two unused-binder lints are on frozen statement binders (`hturn` in `ub_exists_direction`, `hu` in
  `ucurl_exists_curled`); leave, or rename to `_hturn`/`_hu` only with the reviewer's consent (statement text change).

## 8. Files

- `Floor_Assembled.lean` — the deliverable (compile as above; do not `lake build`; port per §7 only after review).
- `tools/wave2_assemble.py` (assembler + diff-rule checker), `tools/wave2_stmt_check.py` (parametrised
  `wave1_stmt_check.py`: `python3 tools/wave2_stmt_check.py <base.lean> <target.lean>`, run from this directory),
  `tools/wave2_new_names.txt` (the 61 helper names with their unit).
- Scratchpad (`/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/`):
  `Floor_Assembled_compile.log`, `Floor_axioms.lean/.log`, `Floor_PortDryRun.lean/.log`, `all_names.txt`,
  `clash_hits.txt`.
- Inputs unchanged: `Wave2_Skeleton.lean`, `W2_*.lean`, `W2_*_REPORT.md`, `Statements_FINAL.lean`, `Wave1_Assembled.lean`.
