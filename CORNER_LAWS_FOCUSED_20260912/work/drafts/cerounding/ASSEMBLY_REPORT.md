# ce:rounding lane — ASSEMBLY REPORT (2026-09-14)

Assembler output: `work/drafts/cerounding/CeRounding_Assembled.lean` (1825 lines), produced by
`work/drafts/cerounding/assemble_cerounding.py` from `Skeleton_FINAL.lean` and the five unit files
`U_{P,G,C,L,E}.lean`.  Port target (per work/port/review_prompt_ce-rounding.md): `SM/CeRounding.lean`.

## Headline

| check | result |
|---|---|
| leaves proved | **33 / 33** (P 3, G 10, C 7, L 9, E 4); unproved leaves: none |
| `grep -c sorry` | **0** (case-insensitive scan also 0; skeleton had 37 = 33 leaf bodies + 4 docstring mentions) |
| compile `cd work/lean && lake env lean ../drafts/cerounding/CeRounding_Assembled.lean` | exit 0, **0 errors**, 9 warnings (all pre-existing cosmetic, see §5), 9.6 s |
| `#print axioms SM.ce_rounding` (on a /tmp copy) | **[propext, Classical.choice, Quot.sound]** — no `sorryAx` |
| `#print axioms SM.SpatialLink.exists_cuspRoundingWitness`, `SM.SpatialLink.constWitness` | same three axioms |
| Statements_FINAL.lean byte identity | the region from `namespace SM` to `-- SKELETON-CUT` (135 lines, 18 blocks, 6 declarations) is a contiguous byte-identical substring of the assembled file |
| name clashes against work/lean | **none** (grep scan of all 153 declarations with namespace tracking: 0 exact full-name hits; compile test importing all 650 built modules + the assembled body: 0 errors) |
| `#print` / `#eval` / `#check` command lines | none in the file (the skeleton had none; the docstring mention of `#print axioms` was rewritten away) |
| module docstring | rewritten (the word "sorry" appears nowhere in the file) |

## 1. Unit-diff audit (task step 1)

For every unit file `diff Skeleton_FINAL.lean U_X.lean` was inspected in full, and the assembly script
re-derives the line diff (difflib, autojunk off) and aborts if any REMOVED skeleton line is not a leaf
`sorry`.  Findings:

| unit | removed skeleton lines | leaves filled (skeleton line of the `sorry`) | added lines | helpers added |
|---|---|---|---|---|
| U_P | 3 × `  sorry` | periodicBump_zero (222), periodicBump_eq_one (227), periodicBump_eq_zero (232) | 43 | `SM.SpatialLink.up_denom_pos`, `SM.SpatialLink.up_cos_eq_cos_abs` |
| U_G | 10 × `  sorry` | exists_germData (262), GermData.chart_proj (314), u_strictMonoOn_or_strictAntiOn (327), rect_subset_closedBall (366), uMin_neg (370), uMax_pos (373), u_mem_Icc_of_mem (381), mem_Icc_of_u_mem (386), u_mem_Ioo_of_mem (391), abs_u_le_M (395) | 160 | `SM.SpatialLink.GermData.ug_strictMonoOn_of_deriv_pos`, `…GermData.ug_strictAntiOn_of_deriv_neg` |
| U_C | 7 × `  sorry` (+ see note) | CuspChoice.chi_eq_zero_of_notMem (463), isDisc_U (495), center_mem_interior_U (498), arc_in (515), clean (521), arc_simple (526), chi_eq_zero_on_collar (534) | 134 (after normalisation) | `SM.SpatialLink.CuspChoice.uc_unchart_convex_comb`, `uc_convex_U`, `uc_U_eq_preimage`, `uc_mem_interior_U_of_chart`, `uc_center_mem_interior_U` |
| U_L | 9 × `  sorry` | Choices.core_joint_contDiff (590), arcs_disjoint_circle (636), chart_core (665), inside (670), arc_regular (677), arc_injOn (683), arc_no_crossing (690), core_eventuallyEq_of_notMem (714), deriv_xz_ne_zero_of_notMem (722) | 251 | `SM.SpatialLink.Choices.ul_hasDerivAt_u`, `…Choices.ul_chart_core_coords`, `…Choices.ul_chi_eq_zero_of_notMem_Icc` |
| U_E | 4 × `  sorry` | cusp_image_injective (917), exists_gap (923), exists_remote_clearance (932), exists_eta (941) | 168 | `SM.SpatialLink.ue_lip_pos`, `SM.SpatialLink.ue_norm_unchart_sub_le` |

Every unit filled exactly its own leaves (PLAN_FINAL.md §4 assignment); no unit touched another unit's
leaf, and no statement, definition, name, import or docstring was changed in any unit.

**Note on U_C (not adopted as written, normalised).**  U_C.lean wrote two leaves in term mode, dropping
the skeleton's `by`:
```
theorem isDisc_U : IsDisc ch.U :=                       -- skeleton: `:= by` / `sorry`
  ⟨ch.uc_convex_U, …⟩
theorem center_mem_interior_U : … ∈ interior ch.U :=    -- skeleton: `:= by` / `sorry`
  ch.uc_center_mem_interior_U
```
Name and type are unchanged, so this is a body change, not a statement change; still, so that every
skeleton statement line stays byte-identical, the assembler normalised both to `:= by` + `exact <term>`
(in memory only; U_C.lean itself is untouched).  With this normalisation the U_C diff removes exactly
seven `  sorry` lines.  No other deviation was found in any unit.

Helper de-duplication: the 14 helper names are pairwise distinct across units (prefixes `up_`, `ug_`,
`uc_`, `ul_`, `ue_`), none redeclares a skeleton name, so nothing was dropped or renamed.

## 2. Assembly (task step 2)

`assemble_cerounding.py`:
1. reads the skeleton and each unit; computes the line diff; asserts each removed line is `sorry`;
2. collects all hunks in skeleton coordinates (33 replacements + 4 pure insertions: U_P helpers after
   skeleton line 219, U_G helpers after 323, U_C helpers before 494, U_L helper after 706), checks them
   pairwise disjoint, applies them in one pass;
3. verifies every inserted block occurs contiguously in the output and that every non-`sorry` skeleton
   line survives in order (subsequence check);
4. since no leaf remained, replaces the module docstring (see §6) and strips any `#print/#eval/#check`
   command line (there were none).

`diff Skeleton_FINAL.lean CeRounding_Assembled.lean | grep '^<'` = the 33 `  sorry` lines + the 13 lines
of the old module docstring; nothing else was removed.

## 3. Unproved leaves (task step 3)

None.  No own proving was needed.

## 4. Compile, sorry count, axioms (task step 4)

```
cd work/lean && lake env lean ../drafts/cerounding/CeRounding_Assembled.lean   # exit 0, 0 errors, 9 warnings, 9.6 s
grep -c sorry ../drafts/cerounding/CeRounding_Assembled.lean                    # 0
# /tmp/CeRounding_axioms.lean = the file + `#print axioms …`:
'SM.ce_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.SpatialLink.exists_cuspRoundingWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.SpatialLink.constWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Warnings (all pre-existing in the skeleton; none introduced by the assembly)

| assembled line | warning |
|---|---|
| 376, 377 | `chart_add_disp`: unused simp args `Prod.fst_zero`, `Prod.snd_zero` |
| 882, 892, 906, 922, 938, 988, 1240 | linter.style.haveILetI: `letI : Fintype L.cuspSet := C.fin` in a Prop goal (skeleton idiom, also used by U_L's `core_joint_contDiff` and `core_eventuallyEq_of_notMem`) |

Cosmetic only; left as is so that no accepted-statement text moves.  If the port wants them silenced:
drop the two simp args, and write `have` for `letI` in the seven proofs (or `set_option
linter.style.haveILetI false in`).

## 6. Statements_FINAL.lean byte identity (task step 5)

The Statements file's own module docstring differs from the skeleton's by design (it is above
`namespace SM`).  From `namespace SM` down to the line before `-- SKELETON-CUT` (135 lines) the text is a
contiguous byte-identical substring of the assembled file; the six declarations `SpatialLink.ext'`,
`CuspedProjection.not_isCusp_of_isDouble`, `CuspRoundingFamily.deriv_eq_of_isDouble`,
`CuspRoundingWitness`, `CeRoundingData`, `CeRoundingData.exists_cuspRoundingFamily` are therefore
byte-identical including docstrings.  The row theorem below the cut marker has the identical statement
`theorem ce_rounding : CeRoundingData` (Statements: `:= by sorry`, docstring "The only `sorry` of this
file."; assembled: `where …` with the skeleton's docstring "Lemma ce:rounding (row 89), assembled from
the chain." — the docstring change is the skeleton's, made below the cut marker, and is required since
the word "sorry" is forbidden in the port).

## 7. Name-clash scan (task step 6)

* Grep scan: the assembled file declares 153 top-level declarations (namespaces `SM`, `SM.SpatialLink`,
  `SM.SpatialLink.GermData`, `SM.SpatialLink.CuspChoice`, `SM.SpatialLink.Choices`,
  `SM.CuspRoundingFamily`, `SM.CeRoundingData`, plus `_root_.SM.SmoothLoop.ext'`, `SM.deriv_space`,
  `SM.deriv_xzOf`).  Each was searched in every `work/lean/**/*.lean` (650 files) as a declaration with
  namespace tracking: **0 exact full-name clashes**.  13 same-short-name hits live in other namespaces
  (e.g. `SM.CornerRounding.a/b/M/M_pos` in SM/Rounding.lean vs `SM.SpatialLink.CuspChoice.a/b`,
  `SM.SpatialLink.GermData.M/M_pos`; `SM.Link.Record.exists_gap`, `SM.NoClosedHalfPlane.exists_gap` vs
  `SM.SpatialLink.exists_gap`; `CV.mem_U_iff` vs `SM.SpatialLink.CuspChoice.mem_U_iff`; `SM.Curl.J` vs
  `GermData.J`; `SM.FrontRealize.rect` vs `GermData.rect`; `SM.SmoothFront.not_isCusp_of_isDouble`,
  `SM.SmoothFront.GeomRounding.deriv_eq_of_isDouble`, `SM.SpatialLink.CleanCuspSmoothing.deriv_eq_of_isDouble`)
  — distinct constants, not clashes; all uses in the file are dot-notation or namespace-local and the
  file compiles with `open Link SmoothFront` in force.
* Compile test: `/tmp/CeRounding_clashtest.lean` = `import` of all 650 built modules (every `.lean` in
  work/lean has an `.olean`) + the assembled body without its imports: exit 0, 0 errors, the same 9
  warnings.  So no declaration of the assembled file is already declared anywhere in work/lean, and no
  name becomes ambiguous under the full library.

## 8. Module docstring rewrite (task step 7)

The sorry count is 0, so the skeleton's header docstring (which said "LEAF lemmas (`sorry`)", "every
`sorry` is a leaf", "= [propext, sorryAx, …]", "fill the `sorry`s") was replaced by a header describing
the assembled module (units, helper prefixes, sections, axioms, check command).  `grep -i sorry` on the
file returns nothing.  No `#print`/`#eval`/`#check` lines exist.  All declaration docstrings are the
skeleton's verbatim (the unit tags "**U-C leaf.**", "**U-L leaf.**" etc. remain; they mention no
forbidden string).

## 9. For the porter

* Copy `CeRounding_Assembled.lean` to `work/lean/SM/CeRounding.lean` unchanged (imports:
  `SM.CeSmoothingRecord`, `SM.Rounding`, `Mathlib.Analysis.SpecialFunctions.SmoothTransition`).
* Row 89 declaration: `SM.ce_rounding : SM.CeRoundingData`; the witness structure
  `SM.CuspRoundingWitness` extends the accepted `SM.CuspRoundingFamily`.
* Nothing in this file redeclares or modifies an accepted declaration.
