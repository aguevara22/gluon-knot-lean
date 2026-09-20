# Floor lane — wave 1 assembly report (2026-09-15, assembler)

Directory: `work/drafts/floor/`.  Output: **`Wave1_Assembled.lean`** (3075 lines) = `Statements_FINAL.lean`
(730 lines, frozen statements) with every proved hunk of the eleven wave-1 unit files applied, plus two
small assembler proofs (§4).  Compile: `cd work/lean && lake env lean ../drafts/floor/Wave1_Assembled.lean`
— exit 0, **0 errors**, ~11 s warm.  Nothing under `work/lean` was touched.

## 1. Per-unit diff verification (each unit file vs `Statements_FINAL.lean`)

Rule checked: a unit may only (a) replace the `sorry` body of ITS OWN leaves and (b) insert
prefixed helper declarations at declaration boundaries.  No statement, definition, name, docstring or
header may change.  Method: `diff` normal format; every `<` (removed) line must be a bare `sorry` (or, for
U_R, the leaf header re-emitted with the statement text unchanged); every added declaration name must carry
the unit prefix; added lines scanned for `sorry|admit|native_decide|axiom|set_option|@[simp]|attribute`.

| unit | hunks | removed lines | leaves proved (sorry -> proof) | helpers added (prefix) | verdict |
|---|---|---|---|---|---|
| U_R | 391a, 395-396c | header + 1 sorry | `ur_P_reverse_all` | 2 (`ur_`) | OK — header `:= by` re-emitted as `:=` (term-mode proof); statement text byte-identical |
| U_A | 185a, 197c, 411a, 419c, 427c | 3 sorry | `CarrierFloorAData.junction_local`, `ua_junction_determined`, `ua_length_determined` | 7 (`ua_`) | OK |
| U_B1 | 461c, 472c | 2 sorry | `ub_globalLift`, `ub_exists_direction` | 2 (`ub1_`) | OK |
| U_B2 | 473a, 486c | 1 sorry | `ub_levelCount` | 10 (`ub2_`), inside a nested `section ub2 … end ub2` with `open Set CornerRounding` (closed; no leak) | OK |
| U_IOTA | 575a, 576a | 0 | none (leaf FALSE as frozen) | 13 (`ui_`), incl. the refutation `ui_coeff_toNat_false` | OK — leaf body is `refine ⟨…, ?_, …⟩` with 5/6 fields proved, `sorry` line kept for the false `coeff` field |
| U_SW | 531a, 535c, 538c, 542c, 556a, 558c | 4 sorry | `usw_switchAll_sign`, `usw_switchAll_writhe`, `usw_carried_switchAll`, `usw_switchAllCarries` | 31 (`usw_`) | OK |
| U_CHAIN | 606a, 619c | 1 sorry | `ucurl_exists_curled` | 13 (`ucurl_`), incl. `structure ucurl_ChainState`; one `open CornerRounding in` (scoped) | OK |
| U_ROT | 595a, 603c | 1 sorry | `urot_exists_rotated` | 22 (`urot_`) | OK |
| U_LIFT1 | 649a | 0 (helpers only, by design) | none | 44 (`ul1_`) | OK |
| U_LIFT2 | 649a, 658c | 1 sorry | `ul_exists_constants` | 21 (`ul2_`) | OK |
| U_F | 697a, 709c, 716c | 2 sorry | `uf_a_floor_of_C`, `uf_z_parity` | 4 (`uf_`) | OK |

No violations found; every unit was adopted in full.  Total helpers: 170 new declarations, all prefixed,
no duplicate names among them (`sort | uniq -d` empty).

Semantic (not textual) overlap, kept as is because names differ and each unit's proofs reference its own
copies: `ul1_circBump_nonneg`/`ul2_circBump_nonneg`, `ul1_circBump_le_one`/`ul2_circBump_le_one`,
`ul1_circBump_periodic`/`ul2_circBump_periodic`, and the `cos_two_pi_mul_lt_one` / `circBump_self` /
`circBump_eq_zero` / `exists_int_of_circBump_ne_zero` / `liftY_periodic` pairs (different hypothesis
shapes: `ul1` uses `δ < 1/2`, `ul2` uses `δ < 1` or `δ ≤ 1/2`).  A porting pass can drop the `ul2_` copies.

## 2. Assembly method

`tools/wave1_assemble.py <floor dir> R,A,B1,B2,IOTA,SW,CHAIN,ROT,LIFT1,LIFT2,F <out>`: computes each unit's
diff against the base, records per base line the replacement (must be a `sorry` body; conflict = abort) and
the insertions after it (emitted in the unit order given; LIFT1 before LIFT2 at the shared anchor 649a),
walks the base once, then checks that each of the 29 inserted/replacement blocks occurs verbatim and
contiguously in the output.  Authoritative post-check: `diff Statements_FINAL.lean Wave1_Assembled.lean |
grep '^<'` lists exactly the 18 `sorry` lines + the U_R header (19 lines); every other base line is present
in order.  `tools/wave1_stmt_check.py` (run from this directory) extracts every declaration statement of the
base (header through the first `:=`/`where`; whole block for structures) and finds each verbatim in the
assembled file: **73 declarations checked, 73 byte-identical, 0 mismatches**.

## 3. Compile, sorry count, axioms

- `lake env lean ../drafts/floor/Wave1_Assembled.lean`: exit 0, 0 errors.  Warnings: 5 × `declaration uses
  'sorry'` (the wave-2 leaves, §5) and 2 × unused variable on FROZEN binders (`hturn` in
  `ub_exists_direction` l.604, `hu` in `ucurl_exists_curled` l.2211) — statements frozen, left as is.
- `grep -c sorry Wave1_Assembled.lean` = **7** = 5 leaf bodies + 2 docstring mentions (l.30 header, l.418
  §8 header).  Base file: 25 (23 leaves + 2 mentions).  Declarations with sorry: 23 -> 5.
- `#print axioms` (scratch copy `…/scratchpad/Wave1_axioms2.lean`, same file + `#print axioms` lines):
  - `SM.cf_thm_carrierfloor_R`: `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`
    (`lit_homfly` enters through `homfly_descent` in the `knot_reverse` field, `lp_lm*` through `P`)
  - `SM.cf_thm_carrierfloor_A`: `[propext, Classical.choice, Quot.sound]`
  - `SM.uf_z_parity`: `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`
  - also fully proved, no `sorryAx`: `ur_P_reverse_all` (+`lp_lm`, `lp_lm_uniqueness`),
    `CarrierFloorAData.junction_local`, `ua_junction_determined`, `ua_length_determined`, `ub_globalLift`,
    `ub_exists_direction`, `ub_levelCount`, `ub_exists_admissibleDirection`, `usw_switchAll_sign`,
    `usw_switchAll_writhe`, `usw_carried_switchAll`, `usw_switchAllCarries`, `urot_exists_rotated`,
    `ucurl_exists_curled` (+`lp_lm`), `ul_exists_constants`, `uf_a_floor_of_C` (+`lit_homfly`, `lp_lm*`),
    `thm_floor_of_C` (same), `CarrierFloorCData.floor_support` (+`lp_lm`),
    `transverseFrontBound_of_fdContactShape` (+`lp_lm`) — all standard axioms only.
  - still on `sorryAx`: `ub_BClaim`, `cf_thm_carrierfloor_B` (via `ub_tangencyCount_of_admissible`),
    `ui_mirrorSubstitution`, `cf_thm_carrierfloor_C_of_bound`, `cf_thm_carrierfloor_of_bound`,
    `thm_floor_of_bound`.
  All non-standard axioms are registered interfaces in `work/lean/axiom-policy.json` (`lit:homfly`,
  `lp:lm`, `lp:lm-uniqueness`).

## 4. Assembler's own proofs (task item 3, "small gaps"; both marked `-- (assembler, wave 1)` in the file)

1. `CarrierFloorCData.floor_support` (was U-C's stated corollary): `hC.floor C X h` + `(mindegAZ_spec
   (P_ne_zero X)).2 d k hdk` + cast + `linarith` (4 lines).
2. `ub_exists_admissibleDirection` (U-B3 library leaf): `u := dirOf φ` for the `φ` of
   `ub_exists_direction`; `dirOf_unit`; `−dirOf φ = dirOf (φ + π)` (`Real.cos_add_pi/sin_add_pi`); the edge
   clause via `dirOf (θu C (i+1).val) = uDir C (i+1) = normalize (edge C.P i)` (`dirOf_θu`,
   `ZMod.natCast_zmod_val`) and `ub2_dirOf_eq_iff` against `hφ`; the negative-arc clause via
   `ua_dirOf_arg_uDir` (arg of `uDir j` ≡ `θu C j.val` mod 2π), the point `θu + s ϑ ∈ [θu + ϑ, θu]`
   (`nlinarith`) and `harc` at `2(n − m)` resp. `2(n − m) + 1` (≈ 70 lines).
Neither changes any statement (§2 check re-run after both: 73/73).

## 5. Remaining leaves for wave 2 (exact list; all `sorry` bodies, statements frozen)

| leaf (assembled line of `theorem`) | wave-2 unit | status / notes |
|---|---|---|
| `ub_tangencyCount_of_admissible` (l.962) | **B3** | TRUE.  Route: from `hu : AdmissibleDirection C u` take `φ := (planeComplex u).arg` (`G1_smul_dirOf_arg` + `hu.1` gives `dirOf φ = u`); derive `hφ` (for `j : ℕ`, `dirOf (θu C j) = uDir C ↑j = normalize (edge C.P (↑j − 1))`, so `θu C j = φ + nπ` would make an edge direction `±u`, against `hu.2.1 (↑j − 1)`) and `harc` (for `turn C j < 0` and `φ + nπ ∈ [θu + ϑ, θu]`, `s := (φ + nπ − θu)/ϑ ∈ [0,1]` violates `hu.2.2 j`); `0 < rotationNumber C.P` from `hpos` through `principalTurn_sign` + `uniform_rotation` (UniformRotation.lean:64: all-left or one-right ⇒ `1 ≤ rot`; needs `3 ≤ C.k` = `C.hk` and `Regular` = `D.regular`); then `ub_levelCount` at `φ` and at `φ + π` (`dirOf (φ + π) = −dirOf φ`, `hφ`/`harc` shift by one `π`), and `|rot| = rot`.  The other B3 leaf, `ub_exists_admissibleDirection`, is DONE (§4). |
| `ui_mirrorSubstitution` (l.1711) | **ι (statement repair needed)** | **FALSE AS FROZEN** (one field).  5 of 6 fields are proved in the leaf body (`ι_a`, `ι_aInv`, `ι_z`, `degAZ_eq`, `ne_zero`); `coeff : coeffAt d k (ι f) = (-1) ^ k.toNat * coeffAt (-d) k f` is refuted by the kernel-checked `ui_coeff_toNat_false` (`f = z⁻¹`, `d = 0`, `k = −1`: LHS `−1`, RHS `1`).  Correct law with `(-1) ^ k.natAbs` is PROVED as `ui_coeffAt_iotaHom`; the stated form for `0 ≤ k` is `ui_coeffAt_iotaHom_of_nonneg`.  Judge's decision required: change the field to `(-1) ^ k.natAbs` (or `Int.negOnePow k`, or drop it — the (C) assembly consumes only `degAZ_eq`/`ne_zero`). |
| `usw_P_switchAll` (l.1721) | **EQ** | TRUE.  Inputs all in place: `usw_switchAllCarries` (proved), `iotaHom` a ring hom, `ui_iotaHom_z`/`ui_iotaHom_a`/`ui_iotaHom_aInv` (proved), `ui_iotaHom_iotaHom` (`ι ∘ ι = id`, proved).  Route: `D ↦ ι (P D.switchAll)` is an `RCompetitor` (`coefficient_transport` as in `ur_reverse_rcompetitor`; skein: `P_skein` on the switched triple with `Dp`, `Dm` exchanged gives `a⁻¹ ι P₊ − a ι P₋ = −z ι P₀`, i.e. the campaign skein multiplied by `−1`), hence `ι (P X.switchAll) = P X`, then apply `ι` once more. |
| `ulift_exists_transverse_lift` (l.2931) | **LIFT-3** | TRUE.  Inputs: `ul1_*` (L1-L4: `liftY0`/`liftT` smooth, periodic, `z′ − y₀x′ = v`), `ul2_*` (L5-L8: `ul2_exists_delta`, `ul2_liftY_tau`, `ul2_liftY_admissible`, `ul_exists_constants`).  Remaining: build `K : TransverseKnot` from `liftT F.γ τ c δ` (embeddedness from `RecordCarried.doubles` + `c_O < c_U` at the twin pairs, `y (τ v) = c v`), the `HeightMarking` of `K.spatial.projLoop` realising `X`'s over data (over = smaller `y`: `c_O < c_U`), and `K.front.writhe = X.writhe` (front = `xzOf (liftT …) = F.γ`, `ul1_xzOf_liftT`). |
| `cf_thm_carrierfloor_C_of_bound` (l.2945) | **C** | Conditional on ι's repair (uses `degAZ_eq`, `ne_zero` only) and on B3/EQ/LIFT-3.  Route per its docstring; `floor_zZero` by `supp (zZeroPart f) ⊆ supp f` (`coeffAt_zZeroPart_zero/of_ne`) and `mindegAZ_spec`.  `floor_support` is DONE (§4). |

Leaf reported false: **`ui_mirrorSubstitution`** (field `coeff`, `(-1)^k.toNat`) — the pre-review's blocking
issue, confirmed by the unit with a compiled counterexample; the statement was NOT changed anywhere.

## 6. Name-clash scan

Every one of the 170 new helper names (list: scratchpad `new_names.txt`; regenerate with
`diff Statements_FINAL.lean Wave1_Assembled.lean | grep '^>' | grep -oE '(theorem|def|structure|…)\s+\S+'`)
was grepped whole-word across `work/lean/**/*.lean` (any occurrence) and as `(theorem|def|…)\s+(SM\.)?NAME`:
**zero hits**.  The base file's own names (`Round`, `junctionTemplate`, `AllPosOrOneNeg`, `tangencySet`,
`iotaHom`, `rotPlane`, `downDir`, `liftY0`, `circBump`, `liftY`, `liftT`, `LiftAdmissible`, `Link.Diagram.switchAll`, …)
also have no declaration in `work/lean`.  All helpers live in `namespace SM` (the `Floor` sections are
sections, not namespaces); nothing shadows an accepted name.

## 7. Files

- `Wave1_Assembled.lean` — the deliverable (compile as above; do not `lake build`, do not port without review).
- `tools/wave1_assemble.py`, `tools/wave1_stmt_check.py` — the assembly and byte-identity scripts.
- Inputs unchanged: `Statements_FINAL.lean`, `U_*.lean`, `U_*_REPORT.md`, `PREREVIEW.md`, `PLAN_FINAL.md`.
