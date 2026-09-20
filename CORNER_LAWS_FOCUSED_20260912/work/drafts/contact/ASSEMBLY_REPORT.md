# ASSEMBLY_REPORT.md — contact lane, assembly of the six prover units (2026-09-15)

Assembler for the contact lane.  Inputs: `Skeleton_FINAL.lean` (594 lines, statements frozen) and the six
unit files `U_CIRCLE / U_SL / U_READING / U_LEG / U_FAM / U_TRANS.lean` with their `U_*_REPORT.md`.
Outputs (this directory):

| file | lines | md5 | compile (`cd work/lean && lake env lean ../drafts/contact/<file>`) |
|---|---|---|---|
| `Contact_Assembled.lean` | 1983 | `5e307361dcc54a50346d9eb929da859d` | **0 errors, 0 warnings**, exit 0, ~15 s |
| `Contact_Units_Delta.lean` | 1462 | `9c66011281fd184e2c10984de9779653` | **0 errors, 0 warnings**, exit 0, ~10-13 s |

Scripts and logs: `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/`
(`assemble.py`, `stmt_identity.py`, `run_compiles.sh`, `compile_*.log`, `Contact_Assembled_axcheck.lean`,
`Delta_axcheck.lean`).  Nothing under `work/lean` was written; no `lake build`.

## 1. Diff audit of every unit against the skeleton (task 1)

`diff Skeleton_FINAL.lean U_<unit>.lean`, parsed hunk by hunk (`assemble.py`).  Every hunk lies inside
§5.4 (skeleton lines 549-572); every removed line is a `  sorry` body — with one benign exception, noted.

| unit | hunk (skeleton → unit) | removed | added | content |
|---|---|---|---|---|
| CIRCLE | `551,552c551,632` | `theorem u_circle : U_circle := by`, `  sorry` | 82 | 10 helpers `uc_*` + `theorem u_circle : U_circle := fun K => ⟨…⟩` (term body; statement `theorem u_circle : U_circle :=` retained byte-for-byte) |
| SL | `552a553,575` | — | 23 | helpers `usl_slCircle_eq`, `usl_contactForm_smul`, `usl_disjoint_of_uniform` |
| SL | `554c577,595` | `  sorry` | 19 | body of `u_sl_radius` |
| SL | `556c597,669` | `  sorry` | 73 | body of `u_sl_family` + `usl_reparam_*` helpers (5) |
| SL | `558c671,773` | `  sorry` | 103 | body of `u_sl_reparam` + `usl_embedding_of_circle`, `usl_transverseEmbedding_of_comp`, `usl_isotopy_family` |
| SL | `560c775,785` | `  sorry` | 11 | body of `u_sl_isotopy` |
| LEG | `560a561,1061` | — | 501 | 57 helpers `ulg_*` |
| LEG | `562c1063,1064` | `  sorry` | 2 | body of `u_legendrianFront` |
| LEG | `564c1066,1067` | `  sorry` | 2 | body of `u_spatialOf` |
| READING | `564a565,807` | — | 243 | `section urd_helpers … end urd_helpers` (23 helpers `urd_*`) |
| READING | `566c809,812` | `  sorry` | 4 | body of `u_reading` |
| TRANS | `566a567,690` | — | 124 | 10 helpers `utr_*` |
| TRANS | `568c692,714` | `  sorry` | 23 | body of `u_transport` |
| FAM | `570c570,732` | `  sorry` | 163 | body of `u_regular` + 16 helpers `ufm_*` |
| FAM | `572c734,761` | `  sorry` | 28 | body of `u_family` |

Findings:
* **No statement, definition, name or docstring of the skeleton was changed by any unit** (§5 below:
  all 74 skeleton declarations, docstring + statement, are byte-identical in the assembled file; the
  skeleton's lines 1-550 and 573-594 are byte-identical).  No violations; nothing rejected.
* Every added declaration carries its unit's prefix (`uc_ usl_ urd_ ulg_ ufm_ utr_`); 127 helpers in total
  (CIRCLE 10, SL 11, READING 23, LEG 57, FAM 16, TRANS 10); no name is declared twice within or across
  units, so **no de-duplication and no renaming was needed**.
* No unit added `import`, `open` at file level, `set_option`, `namespace`, `attribute`, `local notation`
  or docstrings above the leaf theorems.  U_READING's helpers are wrapped in
  `section urd_helpers` / `end urd_helpers` containing `open FrontRows FrontRows.U8R`, a nested
  `section fibList` with `variable`s, and `variable {F : SmoothFront} {S : Diagram}` — all scoped to
  the section, closed before `theorem u_reading`; the file-level header is untouched.
* The only non-`sorry` removed line is U_CIRCLE's `theorem u_circle : U_circle := by`, replaced by
  `theorem u_circle : U_circle := fun K =>` (term-mode body instead of `by`); the statement is identical.

## 2. Assembly (task 2)

`assemble.py` applies the 15 hunks to the skeleton: `c`-hunks replace the `sorry` line(s) of one leaf
(no two units replace the same line), `a`-hunks insert after the given skeleton line (no two units insert
after the same line).  Each added block was re-read from the unit file (lines `t1..t2` of the hunk header)
and cross-checked against the diff text.  Verified in the output:
* lines 1-550 and 573-594 of the skeleton appear byte-identical (as assembled lines 1-550 and 1964-1983);
* each of the 15 blocks occurs **contiguously** in `Contact_Assembled.lean` (start lines: CIRCLE 551;
  SL 633, 657, 677, 751, 855; LEG 866, 1368, 1371; READING 1373, 1617; TRANS 1621, 1746; FAM 1770, 1934);
* each of the 11 leaf statements occurs exactly once.

Layout of §5.4 in the assembled file: `uc_*` → `u_circle` (L631) → `usl_*` → `u_sl_radius` (L656) →
`u_sl_family` (L676) → `u_sl_reparam` (L750) → `u_sl_isotopy` (L854) → `ulg_*` → `u_legendrianFront` (L1367)
→ `u_spatialOf` (L1370) → `section urd_helpers` → `u_reading` (L1616) → `utr_*` → `u_transport` (L1745) →
`u_regular` (L1769) → `ufm_*` → `u_family` (L1933); §6 rows at L1966 (`fd_contact`), L1972 (`CV.ax_etnyre`),
L1977 (`CV.ax_slbound`).

## 3. Unproved leaves (task 3)

**None.**  All eleven unit theorems are proved: `u_circle, u_sl_radius, u_sl_family, u_sl_reparam,
u_sl_isotopy, u_legendrianFront, u_spatialOf, u_reading, u_transport, u_regular, u_family`.  No proving
by the assembler was necessary.

## 4. Compile, `sorry`, axioms (task 4)

* `Contact_Assembled.lean`: 0 errors, 0 warnings (the log is empty), exit 0, 15 s.
* `grep -c sorry Contact_Assembled.lean` = **1**: line 19, the frozen module docstring's sentence
  "`sorry` appears ONLY in the row theorems …" (commentary, now stale; left untouched because the module
  docstring is part of the frozen text — the executor's port of §0-§3, SM/SrcContact.lean, already
  rewrote that paragraph).  `grep -c sorry Contact_Units_Delta.lean` = 0.  No `sorryAx` anywhere.
* `#print axioms` on a scratch copy (`Contact_Assembled_axcheck.lean`, in the scratchpad rather than /tmp):

```
SM.fd_contact                : propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent,
                               SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact   (= expected set)
SM.CV.ax_slbound             : the same nine
SM.fd_contact_of_units       : the same nine
SM.CV.ax_etnyre              : propext, Classical.choice, Quot.sound, SM.src_contact
SM.src_contact_iff_consequence : propext, Classical.choice, Quot.sound
SM.u_circle … SM.u_family (all 11 leaves) : propext, Classical.choice, Quot.sound   (no sorryAx, no src_contact)
```

## 5. Byte-identity of the skeleton's declarations (task 5)

`stmt_identity.py` extracts every column-0 declaration of `Skeleton_FINAL.lean` (74: 19 `def`, 47 `theorem`,
7 `structure`, 1 `axiom`) together with its docstring, taking the statement up to and including `:=`
(structures: the whole `where` block), and searches for the block verbatim in `Contact_Assembled.lean`.
**74 / 74 found byte-identical** (leaves at assembled lines 631, 656, 676, 750, 854, 1367, 1370, 1616, 1745,
1769, 1933; rows at 1966, 1972, 1977).  The 11 leaf statements are also present byte-identical in the delta.

## 6. Name-clash scan (task 6) and the delta module

Scan of `work/lean/**/*.lean` (excluding `.lake`):
* whole-word grep of all 127 helper names: **0 hits**;
* prefix grep `\b(uc|usl|urd|ulg|ufm|utr)_`: the prefix `uc_` is already used in
  `SM/RegularPoleCount.lean` (`uc_abs_eq_sign_mul`, `uc_sign_mul_sign`, `uc_chartDensity_polar`,
  `uc_contDiff_bumpPhi`, `uc_hasDerivAt_bumpPhi`, `uc_hasDerivAt_radial`) and `SM/CeRounding.lean`
  (`uc_unchart_convex_comb`, `uc_convex_U`, `uc_U_eq_preimage`, `uc_mem_interior_U_of_chart`,
  `uc_center_mem_interior_U`) — different names, no clash; the other prefixes are unused;
* namespace: all helpers are declared inside `namespace SM` (full names `SM.uc_*`, …), the U_READING
  block inside `section urd_helpers` (sections do not change names).  `#check` on the delta confirms
  `SM.urd_markingOfRecordIso`, `SM.ulg_front`, `SM.u_reading`.
* **clashes: none.**  Confirmed by the compile of the delta against the ported library.

`Contact_Units_Delta.lean` = `import SM.FdContactStatements` + the skeleton's header (`namespace SM`,
`open SM.Link TransverseNeighborhood`, `open scoped ContDiff`, `open Set Function Real`,
`noncomputable section`, `open Classical`, `local notation "E3"`) + assembled lines 549-1963 verbatim
(the whole of §5.4: 127 helpers + 11 unit theorems) + §6:
* `theorem fd_contact : FdContactData := fd_contact_of_units …` in `namespace SM` (docstring verbatim);
* `CV.ax_slbound` declared at ROOT namespace `CV` (`namespace CV / open SM / theorem ax_slbound :
  AxSlboundData := ax_slbound_of SM.fd_contact`), because the port moved the CV bundles from the
  skeleton's `SM.CV` to root `CV` (SM/FdContactStatements.lean header, D-SC-5) and CV/AxEtnyre.lean uses
  the same shape; `#check @CV.ax_slbound : CV.AxSlboundData`;
* `CV.ax_etnyre` is **not redeclared**: it already exists as `CV/AxEtnyre.lean:12` (ported 15:05Z, imports
  SM.FdContactStatements, same one-line body); a second declaration would collide when both modules are
  imported.  A `/-! -/` note in the delta says so.
* Declaration set: delta = assembled §5.4+§6 minus `CV.ax_etnyre`, with `CV.ax_slbound` in root form
  (140 vs 141 declarations; no duplicates).
* Axioms in the delta: `SM.fd_contact` and `CV.ax_slbound` = the expected nine (log
  `compile_delta_axcheck.log`).

## 7. Notes for the executor

1. Registry: `lean-declarations.json` has `fd:contact` (line 1809) and `CV:ax:slbound` (status `pending`,
   empty declaration/module) — fill with `SM.fd_contact` / `CV.ax_slbound` and the new module's name;
   `CV:ax:etnyre` is already `CV.ax_etnyre` / `CV.AxEtnyre`.  `axiom-policy.json` fixes no name for rows
   94/161/162 (only `src:contact → SM.src_contact`).
2. Frozen commentary now stale (not changed here): the module docstring of the assembled file (lines
   18-21, "`sorry` appears ONLY in the row theorems …"), the docstring of `fd_contact` ("To be closed as …
   once the units … are proved") and of `CV.ax_slbound` ("waits on `fd_contact`").  Both §6 docstrings are
   copied verbatim into the delta; refresh them at port time if desired.
3. Pre-review non-blocking items RF-1…RF-5 (PREREVIEW.md) are documentation requests on the statements
   module, not on the units; nothing in the assembly touches them.
4. Compile budget: the whole assembled file elaborates in ~15 s against the built `.lake` (all imports are
   prebuilt); three concurrent `lake env lean` runs were fine on this 8-vCPU pod.
