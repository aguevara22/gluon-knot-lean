# ASSEMBLY_REPORT — R-lane X₁ rows, wave 1 (units SEL, PRE, A2)

Written 2026-09-14 07:19 UTC / 3:19am ET by the assembler. Directory: `work/drafts/rlane2/`. Compile command
throughout: `cd work/lean && lake env lean ../drafts/rlane2/<file>.lean` (nothing under `work/lean` was
written; no `lake build`).

## 1. Unit diffs against the frozen statement file (`Statements_FINAL.lean`, 1178 lines)

| unit | `diff Statements_FINAL.lean U_x.lean` hunks | lines removed (`grep '^<'`) | verdict |
|---|---|---|---|
| `U_SEL.lean` (1699) | `572a573,1087` (insertion: `section SEL … end SEL`), `581c1096,1102` | exactly one: the `sorry` of `generic_selector` | allowed edits only |
| `U_PRE.lean` (1597) | `225a226,391` (`section PREHelpers`), `424a591,646`, `659a882,900`, `783a1025,1112`, `866a1196,1252`, `918a1305,1337` | none | pure insertions |
| `U_A2.lean` (2126) | `1109a1110,2057` (`section A2`, after `end Assembly`) | none | pure insertion |

Every hunk is self-scoped (sections `SEL` with a local `open SM.Carrier`, `PREHelpers`, `A2`; the twelve
`PRE_<row>_<field>` lemmas sit at the `RProof` top level directly before their row theorems). No hunk
consumes any of the eight still-open row theorems at the term level (the only mentions are in docstrings);
`A2_cvRNear_of_rows` takes the seven row theorems 170, 172–177 as hypotheses in their fixed shapes and
consumes the accepted cores `localization`, `fibre_partition`, `generic_table` directly. No statement,
definition, structure, name, docstring or import of the frozen file was changed by any unit.

## 2. `RLaneX1_Assembled.lean` (3080 lines)

Construction: line-based merge of `Statements_FINAL.lean` with the unit ranges above (PRE after base
lines 225, 424, 659, 783, 866, 918; SEL after 572 and replacing base line 581 by `U_SEL` 1096–1102; A2
after 1109) plus one inserted assembler note (`/-! ### Assembler note … -/`) before `namespace CV`.
Checks:
* `diff Statements_FINAL.lean RLaneX1_Assembled.lean | grep '^<'` → exactly `<   sorry` (the row-172 body).
* Each unit is contained in the assembled file: `diff U_SEL.lean RLaneX1_Assembled.lean | grep '^<'` is
  empty; for `U_PRE`/`U_A2` the single missing line is their still-open `generic_selector` body
  (`  sorry` / `  sorry`).
* Compile: exit 0, 0 errors, exactly eight `declaration uses \`sorry\`` warnings at lines 515 `exterior`,
  661 `availability_zero_one`, 1436 `generic_transport`, 1497 `generic_selected`, 1648 `extreme_pair_zero`,
  1788 `extreme_transport`, 1874 `extreme_selected`, 1954 `cv_R`; no other warning; ~12 s.
* Row 172 `RProof.generic_selector` is PROVED (radius `min δ_L δ_G` of the accepted rows 164 and 172-table,
  all five fields by `SEL_genericSelectorData`).

## 3. `RLaneX1_Statements.lean` — the PORTABLE library file (3003 lines)

= the assembled file minus exactly the eight still-open row theorems, each removed together with its
`/-- **Row … -/` docstring and proof body (assembled-file ranges 514–523 `exterior`, 660–669
`availability_zero_one`, 1435–1444 `generic_transport`, 1496–1505 `generic_selected`, 1647–1656
`extreme_pair_zero`, 1787–1796 `extreme_transport`, 1873–1882 `extreme_selected`, 1947–1956 `cv_R`).
Kept: every definition, structure/bundle, auxiliary, helper, field lemma, `CV.hyp_R`, `CvRNear`,
`ChamberInvII`, `hyp_R_of_near_of_chamberinv`, `smR_shape_of_hyp_R`, the whole A2 assembly and the proved
`RProof.generic_selector`. Declaration count 126 = 134 − 8 (name-list difference is exactly the eight rows).
Prose edits (the only text changes): the module docstring's compile sentence (statement-file lines 12–13)
was reworded so that the placeholder word no longer occurs, and the assembler note describes the omission.
Checks: `grep -c sorry RLaneX1_Statements.lean` → **0**; compile exit 0 with **no output at all** (no
warnings); ~11 s.

## 4. `#print axioms` (scratch `/tmp/rl2ax/RLaneX1_Statements_axioms.lean` = portable file + one
`#print axioms` per declaration; output `/tmp/rl2ax/axioms.out`, 126 entries, **no `sorryAx` anywhere**)

* `RProof.generic_selector` → `[propext, Classical.choice, Quot.sound, SM.lit_homfly]`.
* `CV.hyp_R` → `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` (the Prop mentions `CV.X1`).
* `CV.hyp_R`-related auxiliaries: `RProof.hyp_R_of_near_of_chamberinv`, `smR_shape_of_hyp_R`, `CvRNear`,
  `ChamberInvII`, `CvTheoremData`, `CvTheoremData.of_fibre_identities`, `near_of_fibre_identities`,
  `X1_eq_sum_fibreTerm`, `X1_eq_sum_rowTerm`, `A2_fibre_identities`, `A2_cvTheoremData`,
  `A2_cvTheoremData_of_rows`, `A2_cvRNear_of_rows` → all `[propext, Classical.choice, Quot.sound, SM.lit_homfly]`;
  `outsideSupports_transport`, `mem_outsideSupports_transport`, `transportSupport_transportSupport_symm`,
  `OppositeSides.symm` → `[propext, Classical.choice, Quot.sound]`.
* Field lemmas: all twelve `PRE_*` field lemmas and `SEL_selected_pair_unique`, `SEL_corner_signs_opposite`,
  `SEL_mixed_carrier`, `SEL_selector_zero` → `[propext, Classical.choice, Quot.sound]`; `SEL_row_zero`,
  `SEL_genericSelectorData`, `SEL_rowTerm_eq_zero` → `+ SM.lit_homfly` (they mention `rowTerm = CV.X1Summand`).
* Totals: 54 declarations `[propext, Classical.choice, Quot.sound, SM.lit_homfly]` (exactly those whose
  statement involves `X₁` through `rowTerm`/`fibreTerm`/`CV.X1`/the bundles), 70 `[propext, Classical.choice,
  Quot.sound]`, `three_le_of_h3` `[propext, Quot.sound]`, `PRE_eq_of_reachable_of_isolated` no axioms.
  `SM.lit_homfly` is the accepted literature interface reached through `CV.X1` (NOTES_FINAL §12 item 12).

## 5. Name-clash scan against `work/lean`

* `CV.hyp_R`: **no declaration** — `grep -rn hyp_R work/lean --include=*.lean` → 0 hits. `lean-declarations.json`
  lists `CV.hyp_R` as the target of row `CV:ax:R` with `status: pending`, `module: ""` (planned, not yet
  declared), so the declaration in the portable file is the intended one and must be placed exactly once
  (here or in the CV row module) when the file moves into `work/lean`. (`SM.hyp_R`, row `hyp:R`, likewise
  pending — a different name.)
* `RProof.*`: the 246 declaration names of `work/lean/RProof/Cores.lean` (the only `RProof` module) ∩ the
  134 names of the assembled file = ∅. No `SEL_`/`PRE_`/`A2_` identifier anywhere in `work/lean`.
* Whole-word grep of every unprefixed name across `work/lean` sources: no declaration of the same base
  name in any namespace (the `.symm` hits are unrelated `IsCommStep.symm` etc.). Near-misses, not clashes:
  `ChamberInvII` occurs only as the MODULE name `CV.ChamberInvII` (imports/prose in CV/*.lean,
  SM/GeoPathTransport.lean) — our `RProof.ChamberInvII : Prop` is a def in another namespace;
  `smR_shape_of_hyp_R` is mentioned in a comment of `Bridge/B4.lean` referring to this drafts file.
* Result: **no clash**.

## 6. Field lemmas available for the next wave (portable-file line numbers)

Row 170: `PRE_170_fibre_zero` (603), `PRE_170_fibre_one` (613), `PRE_170_fibre_correspond hF` (628).
Row 172: `SEL_selected_pair_unique hG` (1138), `SEL_corner_signs_opposite hG` (1160), `SEL_mixed_carrier hn hL hG`
(1194), `SEL_selector_zero hn hL hG` (1251), `SEL_row_zero hn hL hG` (1275), bundle `SEL_genericSelectorData hn hL hG`
(1294); row theorem `generic_selector` (1307).
Row 173: `PRE_173_canonical_branch hG` (1404). Row 175: `PRE_175_pair_absent_on_complete` (1527),
`PRE_175_pair_present_on_empty` (1546), `PRE_175_third_singleton_piece hPar` (1564). Row 176:
`PRE_176_singleton_rows_present` (1688), `PRE_176_graphs_complementary hL` (1703), `PRE_176_sign_branch hG` (1730).
Row 177: `PRE_177_full_present_on_empty` (1788), `PRE_177_full_absent_on_complete` (1801).
Assembly: `A2_fibre_identities` (2686), `A2_cvTheoremData` (2706), `A2_cvTheoremData_of_rows` (2823),
`A2_cvRNear_of_rows` (2874). Hypotheses `hL/hF/hPar/hG` are the accepted core bundles at the same radius.

## 7. Open items / notes for the next waves

* Still open (placeholder proofs only in `RLaneX1_Assembled.lean`): `exterior` (168), `availability_zero_one`
  (170: X₁ fields `summand_transport`, `summands_agree`, `fibre_identity`), `generic_transport` (173: `empty_row`,
  `endpoint_rows_*`), `generic_selected` (174), `extreme_pair_zero` (175: `pair_row_zero`), `extreme_transport`
  (176: `transport_x/y/z`), `extreme_selected` (177: `couple`), `cv_R` (178).
* Closing one-liners once rows 170, 173–177 are proved: `cv_R_near : CvRNear := A2_cvRNear_of_rows
  availability_zero_one generic_selector generic_transport generic_selected extreme_pair_zero extreme_transport
  extreme_selected` and `cv_R := hyp_R_of_near_of_chamberinv cv_R_near chamberinv_ii` with `chamberinv_ii :
  ChamberInvII` from CV row 147 (ii).
* `SEL_sorted_next_of_no_cyclic_between` is a verbatim port of `SM.sorted_next_of_no_cyclic_between`
  (SM/GaussNextFromEmptyArc.lean), which is not in the import closure; imports were deliberately left untouched
  here. When the library file is placed, either add that import and use the library lemma, or keep the port.
* Portable-file prose still describes the printed statements of all nine rows in the `/-! ## Row … -/` section
  comments; only the eight theorem declarations are absent.
