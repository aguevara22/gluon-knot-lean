# Unit U-LIFT-3 (`ul3_`) — wave 2 report (2026-09-15, prover)

File: `work/drafts/floor/W2_LIFT3.lean` (3558 lines) = `Wave2_Skeleton.lean` (3072 lines, the frozen
wave-2 skeleton) with the leaf `ulift_exists_transverse_lift` PROVED and 51 prefixed helpers inserted
immediately before it.  Nothing under `work/lean` was touched; no other unit's `sorry` was touched.

## 1. Result

| leaf | status | axioms |
|---|---|---|
| `ulift_exists_transverse_lift` (skeleton l.2931 → file l.3411-3417) | **PROVED** | `[propext, Classical.choice, Quot.sound]` |

Statement (frozen, unchanged):
```
theorem ulift_exists_transverse_lift (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X)
    (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (hneg : ∀ x, X.sign x = -1) :
    ∃ K : TransverseKnot, xzOf K.T = F.γ ∧ K.Reads X ∧ K.front.writhe = X.writhe
```
Body (3 lines): `obtain ⟨d⟩ := ul3_exists_liftData F X c hdown hneg` then
`⟨ul3_knot hdown d, ul3_knot_xzOf hdown d, ul3_reads hdown hneg d, ul3_front_writhe hdown hneg d⟩`.

Nothing remains for U-LIFT-3.  The leaf is TRUE as frozen; no hypothesis had to be strengthened
(`hneg` is used, for the sign clauses; see §4).

## 2. Compile, sorry count, statement freeze

- `cd work/lean && lake env lean ../drafts/floor/W2_LIFT3.lean`: **exit 0, 0 errors**, 13 s wall (load ≈ 14
  on 8 cores).  Warnings: 3 × `declaration uses 'sorry'` — the other wave-2 leaves
  `ub_tangencyCount_of_admissible` (l.962), `ui_mirrorSubstitution` (l.1717), `cf_thm_carrierfloor_C_of_bound`
  (l.3427) — and the 2 pre-existing unused-variable warnings on FROZEN binders (`hturn` l.608, `hu` l.2211),
  exactly as in `WAVE1_ASSEMBLY_REPORT.md` §3.  No new warning from the `ul3_` block.
- `grep -c sorry`: **6 before → 5 after** (before: 2 docstring mentions l.30/l.418 + 4 leaves; after: the 2
  mentions + the 3 leaves of units B3, ι, C at l.967, l.1718, l.3428).
- `diff Wave2_Skeleton.lean W2_LIFT3.lean`: exactly two hunks, `2922a2923,3406` (the inserted `ul3_` block,
  484 lines) and `2931c3415,3417` (the leaf body); `diff … | grep '^<'` prints exactly one line, `<   sorry`.
- `tools/wave1_stmt_check.py` re-pointed at base = `Wave2_Skeleton.lean`, target = `W2_LIFT3.lean`:
  **242 declarations checked, 242 byte-identical, 0 mismatches**.  (Against `Statements_FINAL.lean` it reports
  72/73 — the single mismatch is the skeleton's own D-FL-4 repair `MirrorSubstitutionData.coeff`
  (`k.toNat` → `k.natAbs`), present identically in `Wave2_Skeleton.lean`; not this unit's business.)
- Added lines scanned for `sorry|admit|native_decide|axiom|set_option|@[simp]|attribute`: none.
- `#print axioms` (scratch copy of the file + 4 `#print axioms` lines, same compile, exit 0):
  `SM.ulift_exists_transverse_lift`, `SM.ul3_knot`, `SM.ul3_marking`, `SM.ul3_front_writhe` all
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `lp_lm`/`lit_homfly` (the lift never touches `P`).
- Name-clash scan: each of the 51 new names grepped whole-word across `work/lean/SM`, `CV`, `Bridge`: zero hits.

## 3. The route as proved (PLAN_FINAL.md §3 (C) step 6, L5-L10; §2.1)

Inputs used from wave 1 (all proved there): `ul_exists_constants` (L5), `ul2_exists_delta` (L6),
`ul2_liftY_tau` (L8), `ul2_liftY_admissible` (L7), `ul1_liftY0_admissible` (L3), `ul1_liftT_contDiff_loop`,
`ul1_liftT_periodic_loop`, `ul1_deriv_xOf_liftT`, `ul1_deriv_zOf_liftT`, `ul1_xzOf_liftT`.

1. **Constants on occurrences.** `ul3_cst X cO cU v := if X.isOver v then cO v.1 else cU v.1`
   (`ul3_cst_overVisit/underVisit`); `ul3_cst_lt_twin_iff : cst v < cst (twin v) ↔ X.overBit v = true`
   and `ul3_cst_ne_twin` (from `visit_eq_over_or_under`, `twin_overVisit/underVisit`, `overBit_*`).
   `ul3_det_neg`: `det(γ′(τ over), γ′(τ under)) < 0` from `RecordCarried.sign_eq` + `hneg` +
   `sign_eq_neg_one_iff`; `ul3_exists_cst`: `ul_exists_constants` at every crossing, `choose`.
2. **The data bundle** `structure ul3_LiftData F X c` (`cO cU lt δ δ_pos δ_lt gap adm`) — the L5/L6 output
   frozen as a record, like `ucurl_ChainState`; `ul3_exists_liftData : Nonempty (ul3_LiftData F X c)` from
   `ul3_exists_cst` and `ul2_exists_delta` (continuity/periodicity of `deriv F.γ` from `SmoothLoop`).
3. **L9, the knot** `ul3_knot hdown d : TransverseKnot` on `ul3_T d := liftT F.γ c.τ (ul3_cstOf d) d.δ`:
   `smooth`/`periodic` (ul1 loop forms); `positive` = `ul3_T_positive` (`ul1_deriv_xOf/zOf_liftT`, then
   `ul2_liftY_admissible` with `ul1_liftY0_admissible`); `immersion` (`xzOf (liftT …) = F.γ`, `F.regular`);
   `embedded` = `ul3_T_embedded`: reduce both parameters to the fundamental period by `Int.fract`
   (`ul3_fract_mem`, `ul3_sameT_fract`, `ul3_fract_ne_of_not_sameT`, periodicity via the accepted
   `eq_of_sameT_of_periodic`), equal points ⇒ equal projections ⇒ a twin pair by `RecordCarried.doubles`
   ⇒ heights `cst v ≠ cst (twin v)` (L8 `ul3_yOf_T_tau`) contradict the equal `y`; `doubles_finite` =
   subset of `Set.range (v ↦ (τ v, τ (twin v)))` by `doubles`; `transverse` from `RecordCarried.transverse`
   after the same reduction (velocities via `SmoothLoop.deriv_periodic`); `no_triple` from
   `RecordCarried.no_triple`.
4. **L10a, the reading** `ul3_marking hdown hneg d : K.spatial.HeightMarking K.spatial.projLoop X`
   (`K.Reads X` is its `Nonempty`, `ul3_reads`): `ul3_occ v := ⟨(0, τ v), _⟩` is an occurrence of the
   projection (partner `(0, τ (twin v))`: `τ_mem`, `τ_inj` + `twin_ne`, `twin_eval`); injective by `τ_inj`,
   surjective by `doubles` (`Fin 1` is a subsingleton); `ul3_Φ := (Equiv.ofBijective ul3_occ _).symm`, with
   `ul3_Φ_param : p.1.2 = τ (Φ p)`.  Fields: `e := ul3_e c` (`Fintype.equivOfCardEq`, `c.one`); `comp_eq` by
   `Fin.ext`/`omega` from `X.Γ.c = 1`; `between_iff` = `RecordCarried.order` after `ul3_Φ_param`;
   `pair_eq` = `ul3_Φ_twin` (`doubles` + `τ_inj`); `over_iff`: `L.height p.1 = yOf T (τ (Φ p)) = cst (Φ p)`
   (`ul3_height`, L8) and `ul3_cstOf_lt_twin_iff` — over = smaller `y` because `c_O < c_U`; `sgn_eq`:
   `ul3_over_of_lt` (the smaller height is the over occurrence: `∃ x, Φ p = overVisit x ∧ Φ q = underVisit x`),
   then `crossSignOf` unfolds to `if 0 < det … then 1 else −1` = `−1` by `ul3_det_neg` (`ite_eq_right`) and
   `(X.sign x : ℤ) = −1` (`ul3_sign_cast`).
5. **L10b, the front writhe** `ul3_front_writhe : K.front.writhe = X.writhe` by `Finset.sum_nbij` with
   `x ↦ (τ (overVisit x), τ (underVisit x))` from `univ : Finset X.Γ.Crossing` onto `K.front.crossingPairs`:
   `ul3_pair_mem` (membership in `doubleSet` + `front_isOver`: `IsDouble` from `τ_mem`/`SameT.eq_of_mem_Ico`,
   `y (τ over) = c_O < c_U = y (τ under)`), injective by `τ_inj`, surjective `ul3_crossingPairs_surj`
   (`doubles` gives the twin pair, the over rule forces the over occurrence first), values
   `ul3_front_crossSign : crossSign (τ over) (τ under) = (X.sign x : ℤ)` (both `−1`).

## 4. Notes for the reviewer / porter

- `hneg` is genuinely used (`ul3_det_neg`, hence `sgn_eq` and the writhe values).  Without it the same
  marking exists by a case split on the sign of the determinant (`(X.sign x : ℤ) = (sign det : ℤ)` vs the
  `if` in `crossSignOf`), but the frozen leaf has `hneg`, so the shorter route was taken.
- FR-FL-C8 is realised literally: the reading is the record-level `SpatialLink.HeightMarking` of the
  accepted `CeSmoothingRecord.lean`; no point coincidence between the polygon `X` and the smooth front is
  asserted or needed (FR-FL-C6: the rotation of U-ROT is applied to the smooth curve only).
- `xzOf K.T = F.γ` is `funext; rfl` (`ul1_xzOf_liftT`); the marking's `(G i).γ = F.γ` (`ul3_projLoop_γ`) is
  the same identity through `TransverseKnot.spatial`/`projLoop` (both `rfl`-level).
- Only `Fin 1`/`X.Γ.c = 1` bookkeeping is needed for `e`/`comp_eq`; `ul3_e` is any equivalence
  (`Fintype.equivOfCardEq`), since `comp_eq` is decided by cardinality.
- Deprecated `if_neg` avoided (`ite_eq_right`, Lean core), so the block adds no warning.
- The helpers live in two nested sections (`section ul3_knot`, `section ul3_marking`, each with
  `variable {F} {X} {c}`), closed before the leaf; the leaf itself is outside them, as frozen.  Semantic
  overlap with wave 1: none (`ul3_fract_*` are new; `ul2_`/`ul1_` are consumed, not copied).
- Porting: the block (l.2923-3406) depends only on the U-LIFT definitions (`liftY0`, `circBump`, `liftY`,
  `liftT`, `LiftAdmissible`, `downDir`), the `ul1_`/`ul2_` helpers, §1 (`TransverseKnot.spatial`, `Reads`) and
  the accepted modules `SM.Curl`, `SM.TransverseFront`, `SM.CeSmoothingRecord` (+ `FrontRecordBridge`,
  `FrontGeomModel`, `LinkDiagramRecord` through them).

## 5. Helpers added (51, all `ul3_`, file l.2923-3406)

Fundamental period: `ul3_fract_mem`, `ul3_sameT_fract`, `ul3_fract_ne_of_not_sameT`.
Constants: `ul3_cst` (def), `ul3_cst_overVisit`, `ul3_cst_underVisit`, `ul3_cst_lt_twin_iff`, `ul3_cst_ne_twin`,
`ul3_det_neg`, `ul3_sign_cast`, `ul3_exists_cst`.
Data: `ul3_LiftData` (structure), `ul3_exists_liftData`, `ul3_cstOf` (def), `ul3_T` (def).
Knot (section `ul3_knot`): `ul3_xzOf_T`, `ul3_yOf_T`, `ul3_yOf_T_tau`, `ul3_T_smooth`, `ul3_T_periodic`,
`ul3_deriv_xOf_T`, `ul3_deriv_zOf_T`, `ul3_T_positive`, `ul3_T_embedded`, `ul3_T_doubles_finite`,
`ul3_T_transverse`, `ul3_T_no_triple`, `ul3_knot` (def), `ul3_knot_T`, `ul3_knot_xzOf`.
Marking and writhe (section `ul3_marking`): `ul3_projLoop_γ`, `ul3_occ_mem`, `ul3_occ` (def), `ul3_occ_injective`,
`ul3_occ_surjective`, `ul3_Φ` (def), `ul3_occ_Φ`, `ul3_Φ_param`, `ul3_Φ_twin`, `ul3_height`, `ul3_cstOf_lt_twin_iff`,
`ul3_over_of_lt`, `ul3_e` (def), `ul3_marking` (def), `ul3_reads`, `ul3_front_eval`, `ul3_front_vel`,
`ul3_front_crossSign`, `ul3_pair_mem`, `ul3_crossingPairs_surj`, `ul3_front_writhe`.

## 6. Method

Scratch iteration (`/workspace/scratch/…/scratchpad/L3_test.lean`): the file's header + §1 + `rotPlane`/`downDir`
+ the whole U-LIFT section (l.2245-2922) compiles in ~11 s, so the block was developed against it in two parts
(knot, then marking + writhe) and spliced into `W2_LIFT3.lean` by a script that inserts before the leaf's
docstring and replaces its `sorry` line; then the full official compile, the diff audit, the statement check
and the axiom print above.
