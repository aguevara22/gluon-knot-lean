# ER_ASSEMBLY_REPORT — row 104 cb:embedded-rotation, assembly of units U-A, U-B, U-C

Date: 2026-09-14. Assembler for the cb:embedded-rotation lane.
Output: `work/drafts/pldiscs/EmbeddedRotation_Assembled.lean` (1102 lines,
sha256 `c1555765e3adf90c22daaf163ced6039c469225b477c84c1cab28669c04288ca`).
Inputs: `EmbeddedRotation_Skeleton.lean` (414 lines), `ER_UA.lean` (599), `ER_UB.lean` (618), `ER_UC.lean` (712),
reports `ER_UA_REPORT.md`, `ER_UB_REPORT.md`, `ER_UC_REPORT.md`.
Compile: `cd work/lean && lake env lean ../drafts/pldiscs/EmbeddedRotation_Assembled.lean` — **0 errors**, exit 0, ~7.5 s.

## Result in one line

`grep -c sorry` = **0**; `#print axioms SM.cb_embedded_rotation` = **[propext, Classical.choice, Quot.sound]**
(no `sorryAx`); unproved leaves: **none**; name clashes against `work/lean`: **none**; statement part
byte-identical to `EmbeddedRotation_Statement.lean` lines 22-50 and 52-54.

## (1) Diff audit of each unit file against the skeleton

Method: `diff EmbeddedRotation_Skeleton.lean ER_U?.lean` (normal format), then check every removed line and
every hunk header; independently, split every file at the `§2/§3/§4/§5/§6` headers and compare the frozen
sections byte for byte.

| unit | hunks | removed lines (left side) | added lines | frozen sections identical to skeleton |
|---|---|---|---|---|
| U-A | 11 (`116c`, `120c`, `125c`, `131c`, `139c`, `145c`, `149c`, `154c`, `159c`, `164c`, `171c`) | exactly 11 × `  sorry` | 11 proof bodies + 3 helpers `ea_traversal_eq_on_Icc`, `ea_continuous_of_continuousOn_Icc`, `ea_param_eq_one_of_edgePoint_eq_next` | prefix, §4, §5, §6: yes |
| U-B | 7 (`177c`, `181c`, `185c`, `198c`, `207c`, `212c`, `221c`) | exactly 7 × `  sorry` | 7 proof bodies + 7 helpers `eb_regularPair_cone`, `eb_principalAngle_smul_right`, `eb_arg_planeComplex_normalize`, `eb_coe_angle_eq_arg`, `eb_exists_cos_neg_of_gt_pi`, `eb_abs_sub_le_pi_of_cos_nonneg`, `eb_planeDot_cos_sin` | prefix, §3, §5, §6: yes |
| U-C | 6 (`245a` helper block, `254c`, `261c`, `269c`, `281c`, `289c`) | exactly 5 × `  sorry` | 5 proof bodies + 6 helpers `ec_isLiftOn_congr`, `ec_diag_lift`, `ec_diag_const_step`, `ec_diag_cone_step`, `ec_planeDot_add_right`, `ec_planeDot_traversal_sub_nonneg` | prefix, §3, §4, §6: yes |

Every `c` hunk replaces one `  sorry` line; the single `a` hunk (U-C, after the §5 header) only inserts
helpers. No statement, definition, name or docstring of any leaf or of §1/§2/§6 was changed in any unit.
**Violations found: none; nothing was rejected.** All 16 helper names are distinct (prefixes `ea_`/`eb_`/`ec_`),
so no de-duplication or renaming was needed.

## (2) Assembly procedure

Scripted: `cp` skeleton → apply the three normal diffs with `patch` in reverse order (U-C, then U-B, then
U-A; each later patch touches only lines above the previous one, so skeleton line numbers stay valid).
Verified with a Python check that the result equals, byte for byte,
`skeleton[:§3] + ER_UA[§3:§4] + ER_UB[§4:§5] + ER_UC[§5:§6] + skeleton[§6:]`, and that each of the 24 hunk
right-hand sides occurs contiguously in the assembled file. After the step-(7) rewrite (below) the check was
repeated: all 24 hunks still contiguous; §1 (below the module docstring), §2 and §6 (minus the `#print` line)
identical to the skeleton; §3/§4/§5 bodies identical to the unit files apart from the one header line each.

Final layout (line numbers in the assembled file): module docstring 6-24; §1 statement part 26-56;
§2 route definitions 58-112; §3 U-A 114-359; §4 U-B 361-634; §5 U-C 636-979; §6 assembly 981-1100; `end SM` 1102.
63 top-level declarations, all distinct: 3 statement-part definitions, 12 §2/§6 definitions and theorems,
23 leaves, 16 helpers, `cb_embedded_rotation` plus the §6 lemmas.

## (3) Unproved leaves

None. 23 of 23 leaves (A1-A11, B1-B7, C1-C5) carry proofs; no `sorry` body remains, and no proving by the
assembler was needed.

## (4) Compile, sorry count, axioms

* `cd work/lean && lake env lean ../drafts/pldiscs/EmbeddedRotation_Assembled.lean`: exit 0, 0 errors,
  0 `declaration uses sorry`. The only output is 8 `linter.unusedVariables` warnings on binders of *frozen*
  statements (kept unchanged on purpose): `hk` in `traversal_diag_const` (l.179) and `traversal_diag_cone`
  (l.192); `hn` in `Embedded.regular` (l.223) and `Embedded.traversal_injective` (l.265); `h : Embedded P` in
  `diag_increment` (l.709), `cut_increment` (l.751), `top_increment_eq_left` (l.801); `hn` in
  `exists_supporting_vertex_turn_ne_zero` (l.922). Dropping them is a statement change — decide at accept time.
* `grep -c sorry EmbeddedRotation_Assembled.lean` = **0** (also case-insensitive: 0).
* `/tmp/er_asm/Axioms.lean` = the assembled file + `#print axioms` lines, compiled with `lake env lean` from
  `work/lean`:
  `'SM.cb_embedded_rotation' depends on axioms: [propext, Classical.choice, Quot.sound]` — no `sorryAx`.
  Also `SM.EmbeddedRotationData`, `SM.Embedded`, `SM.IsSupportingVertex`: same three axioms.
  (The skeleton's own `#print axioms` line, compiled before removal, printed the same list.)

## (5) Statement part byte-identity

`EmbeddedRotation_Statement.lean` lines 22-50 (docstrings + `structure Embedded`, `def IsSupportingVertex`,
`structure EmbeddedRotationData`) occur as one contiguous block in the assembled file (lines 28-56), and lines
52-54 (docstring + the two-line header of `theorem cb_embedded_rotation ... := by`) occur as one contiguous
block (lines 1077-1079), followed by the §6 body instead of the statement file's `  sorry` (its line 55).
The two blocks are separated by §2-§6 as the skeleton layout prescribes, so the 33-line span 22-54 is not
one contiguous block — this is intended and unchanged from the skeleton.

## (6) Name-clash scan against `work/lean`

Namespace-aware Python scan over all 659 `.lean` files under `work/lean` (excluding `.lake`), tracking
`namespace`/`section`/`end` to compute the full name of every `theorem/lemma/def/abbrev/structure/inductive/
instance/class/opaque/axiom` head, compared with the 63 assembled names prefixed `SM.` (the file is inside
`namespace SM`, so e.g. `Embedded.regular` is `SM.Embedded.regular`). **0 hits.** A coarser check for the same
bare name as a declaration head in *any* namespace: also 0 hits. Scanner sanity: it finds `SM.IsLiftOn`
(TurnLift.lean:40), `SM.IsLiftOn.increment_eq` (:55), `SM.exists_lift_of_unit` (:83), `SM.Regular`,
`SM.principalTurn`, `SM.rotationNumber`, `SM.normalize` at their known locations.
`work/lean/lean-declarations.json`: row `cb:embedded-rotation` is `status: pending` with empty `declaration`;
none of the 63 names is registered there yet.

## (7) Final cleanup (sorry count 0)

* Module docstring rewritten (no occurrence of the word "sorry"; describes the assembled state and the axiom set).
* The three unit section headers `§3/§4/§5` said "(all `sorry`)" / "(all `sorry` except the two one-liners)";
  replaced by "(all proved; helpers `ea_`/`eb_`/`ec_`)". These are `/-! -/` section comments, not leaf docstrings.
* The skeleton's `#print axioms cb_embedded_rotation` line removed. No `#print`/`#eval` line remains
  (no line of the file starts with `#`).
* Nothing else changed; recompiled after the rewrite (0 errors) and all identity checks re-run.

## Notes for the executor / port to `work/lean/SM/EmbeddedRotation.lean`

* The file is self-contained on the four imports `SM.RotationTheorem`, `SM.Crossings`, `SM.Generic`, `SM.TurnLift`.
* Helper names are prefixed `ea_`/`eb_`/`ec_`; the port may rename them but no clash forces it.
* The `[NeZero n]` on A6 (`traversal_cut_cone`) and the eight unused binders listed under (4) are the only
  loose ends in the frozen statements; all are harmless.
* Nothing under `work/lean` was written or built (`lake env lean` only).
