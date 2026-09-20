# WAVE 1 ASSEMBLY REPORT — CV/R tail, `Wave1_Assembled.lean`

Assembler, 2026-09-15 ≈ 20:10 UTC / 4:10pm ET.
Inputs: `work/drafts/cvtail/Statements_FINAL.lean` (992 lines, the judge's frozen statements) and the six
unit files `U_SLOT`, `U_SPLIT`, `U_R175`, `U_R174`, `U_R176`, `U_R177` (`.lean` + `_REPORT.md`).
Output: **`work/drafts/cvtail/Wave1_Assembled.lean`** (4386 lines, md5 `c196cbf67217716e47101ffda2cea974`).
Nothing written under `work/lean`; nothing ported or mapped. Scripts and scratch copies live in the session
scratchpad (`/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-…/scratchpad/`: `assemble.py`,
`stmtcheck.py`, `newnames.json`, `Wave1_axioms.lean`, `axioms.log`, `compile*.log`).

## 0. Result in one paragraph

All six unit diffs are clean (each deletes at most its own leaf's `  sorry` line and otherwise only inserts
prefixed material); the assembled file compiles with **0 errors** and exactly **7** `declaration uses sorry`
warnings = the 4 sibling-lane placeholders + the 3 RA rows 174/176/177 (**`grep -c sorry` = 8**, the extra hit
is the FINAL's own header prose at line 61). Three leaves are now closed unconditionally on their accepted
inputs — `CV.carrier_slot_floor_of_C`, `CV.cvt_singleton_split`, `RProof.cvt_pair_row_zero_of_singleton` —
so rows 155, 165 and 175 are proved modulo the row-99 (C) placeholder alone. Rows 174, 176, 177 stay
`sorry`, each reduced to one explicit, never-asserted interface Prop (`gsc_moves`, `est_port_relation`,
`esc_interface`) by a PROVED ledger of the fixed `RowShape` type. Every fully proved declaration depends on
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` (or a subset) —
exactly the standard + literature set registered in `work/lean/axiom-policy.json`. 177 new declarations, all
prefixed, zero name clashes against work/lean (675 files), the sibling draft lanes, and
`lean-declarations.json`.

## 1. Task (1): unit diffs against `Statements_FINAL.lean`

`diff Statements_FINAL.lean U_x.lean` (normal format), hunk headers and every deleted (`<`) line:

| unit | hunks | deleted lines | FINAL line of the deleted `sorry` | leaf | verdict |
|---|---|---|---|---|---|
| U_SLOT | `592a593,645` `601c654,672` | 1 × `  sorry` | 601 | `CV.carrier_slot_floor_of_C` | clean |
| U_SPLIT | `691a692,1649` `694c1652,1659` | 1 × `  sorry` | 694 | `CV.cvt_singleton_split` | clean |
| U_R175 | `751a752,762` `766c777,797` | 1 × `  sorry` | 766 | `RProof.cvt_pair_row_zero_of_singleton` | clean |
| U_R174 | `9a10,11` `731a734,1474` | none | — (leaf `generic_selected` untouched) | — | clean; adds 2 imports |
| U_R176 | `9a10,11` `784a787,1636` | none | — (leaf `extreme_transport` untouched) | — | clean; adds the same 2 imports |
| U_R177 | `798a799,1506` `810c1518` | 1 × `  sorry` | 810 | `RProof.extreme_selected` | clean (see §3.3) |

Checks performed per unit: (i) no `d` hunk; (ii) every `c` hunk is a single FINAL line whose text is `  sorry`
and whose enclosing declaration is that unit's own leaf; (iii) every `a` hunk is a pure insertion; (iv) every
declaration introduced in the insertions carries the unit's prefix (`cvtS_`, `cvt165s_`, `cvt175_`, `gsc_`,
`est_`, `esc_`; 0 exceptions among 177); (v) no `set_option`, `axiom`, `instance`, `macro`/`notation`, or
file-level `attribute` in the insertions — the only scoped commands are `attribute [local instance high]
Classical.propDecidable` inside `section Cvt165s` (assembled 916–1746; needed because the FINAL's `RProof.*`
imports bring a global `DecidableEq (Crossing P)` instance that differs from the CV/SM library's classical
one, see U_SPLIT_REPORT pitfall 1) and three section-local `open`s (`SM.Carrier SM.Link` in GSC and EST,
`SM.Link AddMonoidAlgebra` in ESC). Placeholders `cf_thm_carrierfloor`, `thm_C_S7`, `thm_C_soft`,
`cor_C_inherits` untouched in all six. **No violations; every hunk adopted.**

The two `import CV.FullTwist` / `import CV.HomflyRows` lines (U-174, U-176, byte-identical) are header
additions, not statement changes; kept once (de-duplicated by the script).

## 2. Task (2): the assembly

`assemble.py` parses the six normal-format diffs, records insertions keyed by FINAL line and the four
single-line replacements, refuses any `d` hunk / non-leaf `c` hunk / doubly-replaced line (none occurred),
de-duplicates identical insertions at the same position (the import pair), and emits FINAL with the hunks
applied in FINAL order. A provenance banner (lines 20–46, a `/-! … -/` block) was then inserted after the
imports — pure insertion, no declaration touched.

Contiguity / provenance of the assembled file (`diff Statements_FINAL.lean Wave1_Assembled.lean`):

```
9a10,11        imports CV.FullTwist, CV.HomflyRows          (U-174 = U-176)
18a21,46       assembler's banner
592a621,673    U-SLOT helpers (3)                            namespace CV, before the leaf docstring
601c682,700    U-SLOT leaf body
691a791,1748   U-SPLIT helpers (71), sections Cvt165sPattern, Cvt165s (with 9 sub-sections)
694c1751,1758  U-SPLIT leaf body
732a1797,2537  U-174 section GSC + GSCEvent (33 decls)      namespace RProof, before row-174 docstring
751a2557,2567  U-175 helper (1)
766c2582,2602  U-175 leaf body
785a2622,3471  U-176 section EST (5 sub-sections, 38 decls)  before row-176 docstring
798a3485,4192  U-177 section ESC (31 decls)                  before row-177 docstring
810c4204       U-177 leaf body  (`exact esc_ledger (by sorry) …`)
```
Deleted lines: exactly `4 <   sorry`. Insertion positions are pairwise distinct and non-overlapping, so no
hunk straddles another; each block sits inside the namespace/`noncomputable section` its unit compiled it in.

## 3. Task (3): unproved leaves and the interface Props their ledgers consume

Line numbers refer to `Wave1_Assembled.lean`.

### 3.1 Row 174 — `RProof.generic_selected` (2543; `sorry` at 2550) — OPEN
Ledger (PROVED, no `sorryAx`): `gsc_ledger (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) : RowShape
@GenericSelectedData` (2510) and `gsc_generic_selected_of_moves` (2528, the leaf's exact signature).
Closing line once the interface is realised:
`gsc_generic_selected_of_moves <proof of gsc_moves> (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) hn E e f g h3 h4e h4f h4g hE`.

Interface Props (all `RProof.`, never asserted):
* **`gsc_moves : Prop`** (2327) — for every `GT_Endpoint` configuration with `crossingSign P ℓ₁ ℓ₂ =
  crossingSign P ℓ₁ ℓ₃` and the three memberships `hSm hSxw hSm'`,
  `Nonempty (gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' (gsc_wallData_of_endpoint hn hG hG' D hSm hSm'))`.
* **`gsc_Ledger … (W : gsc_WallData …)`** (structure, 2100) — fields: `σ hσ`; carriers `qC qAB hCAB` (on `Q∪{m}`),
  `qC' qA qB hC'A hC'B hAB` (on `Q∪{x,w}`); `omega_wall`, `writhe_wall`; the bijection `ρ` with `ρ_AB ρ_C
  spectator_weight spectator_omega`; `omega_C`, `weight_C`, `weight_AB`, `carrierR_add`; `D₀ qx fulltwist :
  gsc_fulltwist_triple …`; `i j ℓ smoothing : gsc_smoothing_split …`; `writhe_count`.
* **`gsc_fulltwist_triple D_L D_H D₀ q : Prop`** (1988) — `D_H.IsPositive q ∧ IsOrientedSmoothing D_H q D₀ ∧
  ∃ D_L', Relation.ReflTransGen RII (D_H.switch q) D_L' ∧ homfly D_L' = homfly D_L` (the G10 RII deletion; (T2)
  read through ax:gausscode, U_R174_REPORT §5).
* **`gsc_smoothing_split D₀ i j QA QB ℓ : Prop`** (2000) — `componentCount = 2 ∧ i ≠ j ∧ homfly (knotRestrict i)
  = QA ∧ homfly (knotRestrict j) = QB ∧ CV.IsLinkingNumber D₀ i j ℓ`.
* **`gsc_WallData`** (2020) — REALISED: `gsc_wallData_of_endpoint` (τ = `GT_carrierEquiv`, `GT_weight_eq`,
  `GT_carrierR_eq`; standard axioms only). Also realised: the canonical sign (`gsc_sigma_of_endpoint`).

Estimated realisation cost (U_R174_REPORT §4, against the G11 precedent of 11k lines for one RIII site):
| item | content | est. lines |
|---|---|---|
| 4.1 | carrier structure (2): `qC qAB qC' qA qB`, distinctness, bijection `ρ` with `ρ_AB ρ_C` (geo insert/remove layer, twice) | 1500–2500 |
| 4.2 | pieces/reads across the wall: `omega_wall`, `writhe_wall` | 800–1200 |
| 4.3 | selector ledger (4)–(5) and rotation (7)–(8): `weight_C weight_AB omega_C carrierR_add` | 600–1000 |
| 4.4 | **the G10 move `fulltwist`**: an actual `SM.Link.RIIData` site on the E-side lift (no `RIIData` is constructed anywhere in work/lean) + `OrientedSmoothingData` for `D₀` + record identification `homfly D_L' = homfly D_L` | 8000–12000 |
| 4.5 | smoothing identification `smoothing`: two components ≅ the `P-ac` lifts of `A, B`, linking number | 1500–2500 |
| 4.6 | writhe count (10) | 400–600 |
| | **total** | **≈ 13–19k** |

### 3.2 Row 176 — `RProof.extreme_transport` (3476; `sorry` at 3483) — OPEN
Ledger (PROVED): `est_ledger (hF : CV.CarrierSlotFloor) (hport : est_port_relation) : RowShape
@ExtremeTransportData` (3432) and `est_extreme_transport_of hF hport …` (3448, the leaf's signature).
Closing line: `est_extreme_transport_of (CV.carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) <proof of est_port_relation> hn E e f g h3 h4e h4f h4g hE`.

Interface Props (never asserted):
* **`est_port_relation : Prop`** (3287) — for every simple-RIII event datum (`LocalizationData`,
  `AV_EventRadius`, `K3` side `t` with `CompleteLocal`, opposite `t'`, `hs`, outside `Q` with `FullAvail`,
  selected `j ∈ T`, carrier `q` of `Q ∪ {j}` whose wall copy retains some unselected `u' ∈ T'`): `∃ u …,
  Nonempty (est_PortData hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind …) (est_S'_ind …) q
  (GT_carrierEquiv (est_wall …) q) (est_liftCrossing … hu'))`.
* **`est_PortData hn hG hG' hS hS' q q' y`** (structure, Type, 2706) — fields: `port : ReflTransGen RII
  ((carrierDiagram q').switch y) (carrierDiagram q)` (T2); `DA`, `smooth : IsOrientedSmoothing … y DA` (T1);
  `two : DA.componentCount = 2`, `i j ij`; `Sf hSf Λ₁ Λ₂` (the independent full support and its two clean
  outer carriers); `poly₁ poly₂ : homfly (DA.knotRestrict i/j) = groupedPoly Λ₁/Λ₂`; `ℓ link :
  CV.IsLinkingNumber DA i j ℓ`; `writhe` (14) `w_0 = w_1 + w_2 + 2ℓ`; `rot` (13) `R = R_1 + R_2 + 1`;
  `alt₁ alt₂ : UniformOrOneDissentCV (geoCornerPolygon … Λᵢ)` (12).
  Realised instead of assumed: `y` positive, `w_+ = w_0 + 2` (`est_groupedWrithe_affected`), `R(D_+) = R(D_0)`,
  `d(D(W)) = slot`, `Ω(D(W)) = Ω₁`, all Laurent algebra, the event configuration and retained-set bookkeeping
  (`est_retained_*`, `est_owner_shared_eq`), the unaffected carriers (`EXT_homfly_wall`).

Estimated realisation cost (U_R176_REPORT §5 gives the item list as "G10-scale"; the line figures below are
the assembler's, scaled from U-174's per-item numbers):
| item | content | est. lines |
|---|---|---|
| 5.1 | **(T2) the RII port relation** as an actual `SM.Link.RIIData U (carrierDiagram q₀) ((carrierDiagram q₀').switch y)` across the wall (the outside match is the wall transport, i.e. an isotopy through the wall — G11-type) | 6000–10000 |
| 5.2 | (T1) an actual oriented smoothing `D_A` with `IsOrientedSmoothing` and `componentCount = 2` (no existence theorem for oriented smoothings of a polygonal diagram in the library) | 1000–2000 |
| 5.3 | the owner map (9)/(9a): `S_full ∈ Ind`, `Λ₁ Λ₂`, record isomorphism of each component restriction with the outer carrier's lift after removing the kink `r` (lc:single-crossing) | 1500–2500 |
| 5.4 | (14) writhe `w_0 = w_1 + w_2 + 2ℓ` (retained set of `q₀` = self-crossings ∪ mixed crossings, all positive) | 400–600 |
| 5.5 | (13) `R = R_1 + R_2 + 1` and (12) `UniformOrOneDissentCV` of `Λ₁ Λ₂` (turnlift (ii), corner-sign ledger, `selector_A`, `uniformrot`) | 600–1000 |
| | **total** | **≈ 10–16k** |
Items 5.1–5.2 share their machinery with U-174's 4.4 and U-177's (6) (a single `RIIData`-construction toolkit
à la `G11_Config` would serve all three).

### 3.3 Row 177 — `RProof.extreme_selected` (4197) — OPEN
Body adopted from U-177: `exact esc_ledger (by sorry) (CV.carrier_slot_floor_of_C
SM.cf_thm_carrierfloor.clauseC) n hn E e f g h3 h4e h4f h4g hE` (4204) — the single `sorry` is the interface
hole `esc_interface`; the term records the dependency structure explicitly (equivalent to a plain `sorry`
for the sorry census and `#print axioms`; keep or flatten at the executor's discretion).
Ledger (PROVED): `esc_ledger (hI : esc_interface) (hF : CV.CarrierSlotFloor) : RowShape @ExtremeSelectedData`
(4177), through `esc_couple` (4098), `esc_contact_identity`, `esc_coefficient_identity`,
`esc_three_component_row` ((12) PROVED from mp:lowest `SM.lowest.lowest_value`).

Interface Props (never asserted):
* **`esc_interface : Prop`** (3874) — at every configuration of the `couple` field (`t` the `K3` side with
  `CompleteLocal`, `t'` opposite, `Q` outside at `FullAvail`, `hQi hQi' hS'`, `q₀ q₀'` the triangle-touching
  carriers of the empty row on the two sides): `∃ A B C Z Λ, esc_FullSplitData hn (genericAt E t' ht'.1) e f g
  hQi' hS' q₀' A B C Z Λ ∧ esc_MoveData (carrierDiagram q₀) (carrierDiagram q₀') (points of x, y on both
  sides) Λ (groupedPoly A) (groupedPoly B) (groupedPoly C)`.
* **`esc_MoveData D_H D_L pxH pyH pxL pyL Λ fA fB fC`** (structure, Prop, 3804) — fields `switch_riii` ((4), via
  **`esc_switch_riii D_H D_L x_H x_L := homfly (D_H.switch x_H) = homfly (D_L.switch x_L)`**, 3744),
  `rii_after_smoothing` ((6), via **`esc_rii_after_smoothing D_H0 D_L0 y_H y_L := homfly (D_H0.switch y_H) =
  homfly (D_L0.switch y_L)`**, 3751, quantified over every oriented smoothing site), `knot_after_two`
  (`D_H^{xy}.componentCount = 1`), `three_components` (via **`esc_three_components J Λ fA fB fC :=
  J.componentCount = 3 ∧ twoLambda J = 2Λ ∧ ∃ σ : Fin 3 ≃ Fin J.Γ.c, homfly (knotRestrict (σ 0/1/2)) =
  fA/fB/fC`**, 3763). Crossings are identified by their double points.
* **`esc_FullSplitData hn hG e f g hQ hS q₀ A B C Z Λ`** (structure, Prop, 3832) — fields `touching_iff`,
  `distinct`, `central_no_piece`, `central_rot : carrierR Z = 1`, `writhe` (17), `mixed` (`CarrierMixed q₀ →
  wt(A)wt(B)wt(C)wt(Z) = 0`), `outer_alternative` (`CarrierUniform q₀ → UniformOrOneDissentCV` of `A B C`),
  `uniform` (live: `R_A+R_B+R_C = R+1 ∧ W_full = −W`; dead: `R_A+R_B+R_C+1 = R ∧ W_full = 0`).

Estimated realisation cost (U_R177_REPORT "What remains"):
| item | content | est. lines |
|---|---|---|
| (4) | `switch_riii`: matched switch + RIII through the wall on the grouped contact knot diagrams (G11 toolkit nearly verbatim; RIII site on `D_H.switch x_H`; record isomorphism as in G11 Unit F) | 8000–11000 |
| (6) | `rii_after_smoothing`: an actual `RIIData` for the empty bigon `y, z` after smoothing `x`, plus the ambient isotopy through the wall of the two-component remainders | 5000–8000 |
| — | `knot_after_two` / `three_components`: record interlacement ↔ `GeometricInterlaces` bridge for retained crossings, then `componentCount_smooth_of_self/mixed` (component identification itself is part of the split) | 300–600 |
| — | `esc_FullSplitData`: the carrier split of `Q' ∪ T'` (U-SPLIT's (a)–(e) three times over; turnlift (ii), uniformrot (i)(ii), `selector_A`, sign table (1c), writhe count (17)) | 3000–5000 |
| | **total** | **≈ 16–25k** |

**Gross open cost ≈ 39–60k lines; with the shared RII/RIII-site toolkit counted once, realistically ≈ 30–45k.**
Nothing else in the lane is open: rows 155, 165, 175, 178, 183, 184 are proved modulo the RA rows and the four
sibling placeholders.

### 3.4 Row status table

| row | declaration | line | status in `Wave1_Assembled.lean` |
|---|---|---|---|
| 155 | `CV.carrierfloor` | 576 | PROVED modulo `SM.cf_thm_carrierfloor` (placeholder, row 99); `carrierfloor_D` unconditional |
| — | `CV.carrier_slot_floor_of_C` (U-SLOT) | 681 | **PROVED** |
| 165 | `CV.singleton_D_i` | 1762 | PROVED modulo row 99 (C) — both leaves closed |
| — | `CV.cvt_singleton_split` (U-SPLIT) | 1750 | **PROVED** |
| 174 | `RProof.generic_selected` | 2543 | OPEN — `gsc_moves`; ledger `gsc_ledger` PROVED |
| 175 | `RProof.extreme_pair_zero` | 2613 | PROVED modulo row 99 (C) (via `singleton_D_i`) |
| — | `RProof.cvt_pair_row_zero_of_singleton` (U-175) | 2573 | **PROVED** |
| 176 | `RProof.extreme_transport` | 3476 | OPEN — `est_port_relation`; ledger `est_ledger` PROVED |
| 177 | `RProof.extreme_selected` | 4197 | OPEN — `esc_interface`; ledger `esc_ledger` PROVED |
| 178 | `RProof.cv_R` | 4221 | PROVED modulo 174/176/177 and row 99 (C) (`cv_R_of_rows` unconditional) |
| 183 | `Bridge.sm_R` | 4237 | same (`sm_R_of_rows` unconditional) |
| 184 | `SM.corner_laws_and_soft` | 4383 | PROVED modulo `Bridge.sm_R`, placeholders `thm_C_S7`, `thm_C_soft`, `cor_C_inherits` (`corner_laws_and_soft_of` unconditional) |

## 4. Task (4): compile, sorry census, axioms

`cd work/lean && lake env lean ../drafts/cvtail/Wave1_Assembled.lean` → **exit 0, 0 errors**, ≈ 25 s warm,
warnings exactly:
```
188  SM.cf_thm_carrierfloor     (placeholder, row 99)
222  SM.thm_C_S7                (placeholder, row 110)
226  SM.thm_C_soft              (placeholder, row 112)
2543 RProof.generic_selected    (row 174, interface gsc_moves)
3476 RProof.extreme_transport   (row 176, interface est_port_relation)
4197 RProof.extreme_selected    (row 177, interface esc_interface)
4331 SM.cor_C_inherits          (placeholder, row 128)
```
`grep -c sorry Wave1_Assembled.lean` = **8**: the 7 bodies above (lines 189, 223, 227, 2550, 3483, 4204, 4332)
plus the FINAL's header prose at line 61. (FINAL: 11 = 10 bodies + the same prose line; the three closed
leaves account for the difference.)

`#print axioms` on a scratch copy (`scratchpad/Wave1_axioms.lean` = the assembled file + 26 `#print axioms`
lines; the task said "/tmp copy" — the session scratchpad was used instead, same effect):

| declaration | axioms |
|---|---|
| `CV.carrier_slot_floor_of_C`, `CV.cvt_singleton_split`, `CV.singleton_D_i_of`, `CV.carrierfloor_of_sm`, `RProof.gsc_ledger`, `RProof.gsc_generic_selected_of_moves`, `RProof.est_ledger`, `RProof.est_extreme_transport_of`, `RProof.esc_ledger`, `RProof.esc_couple`, `RProof.cv_R_of_rows`, `Bridge.sm_R_of_rows` | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |
| `CV.carrierfloor_D`, `RProof.cvt_pair_row_zero_of_singleton`, `RProof.extreme_pair_zero_of_singleton`, `SM.corner_laws_and_soft_of` | `propext, Classical.choice, Quot.sound, SM.lit_homfly` |
| `RProof.gsc_wallData_of_endpoint` | `propext, Classical.choice, Quot.sound` |
| `CV.carrierfloor`, `CV.singleton_D_i`, `RProof.extreme_pair_zero`, `RProof.extreme_selected`, `RProof.cv_R`, `Bridge.sm_R`, `SM.corner_laws_and_soft` | the six above **+ `sorryAx`** (through the placeholders / RA rows) |
| `RProof.generic_selected`, `RProof.extreme_transport` | `propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly` |

No `sorryAx` in any fully proved declaration; no axiom outside `axiom-policy.json`'s `standard` +
`literature` sets (`SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness`); `SM.lit_homfly_descent` /
`SM.src_contact` do not yet appear (they will enter through row 99 (C) when the placeholder is replaced,
PREREVIEW FR-R-178-2).

## 5. Task (5): byte-identity of the FINAL's declaration statements

`stmtcheck.py` extracts from `Statements_FINAL.lean` every `theorem/def/abbrev/structure` header (keyword line
through the `:=`/`where`/`by` terminator; whole body for structures) together with its docstring, and counts
verbatim occurrences in `Wave1_Assembled.lean`: **85 declarations, each statement text present exactly once,
each docstring present exactly once**. One parser artefact: SM's `CarrierFloorData` (4 fields) is a textual
prefix of CV's `CarrierFloorData` (5 fields), so its text counts twice — both `structure CarrierFloorData :
Prop where` lines (154, 419) are the FINAL's own. Independently, `diff Statements_FINAL.lean
Wave1_Assembled.lean | grep '^<'` prints exactly four `  sorry` lines, i.e. every other byte of the FINAL,
statements and docstrings included, is present in order.

## 6. Task (6): name-clash scan

New declarations: **177** (U-SLOT 3 thm; U-SPLIT 64 thm + 7 def; U-175 1 thm; U-174 27 thm + 4 def (incl.
`noncomputable def gsc_wallData_of_endpoint`) + 2 structures; U-176 35 thm + 2 def + 1 structure; U-177 24 thm
+ 5 def + 2 structures), namespaces `CV` (SLOT, SPLIT) and `RProof` (R174–R177).
* Within the assembly: no duplicate `(namespace, name)` (and the compile would have rejected one).
* Against `work/lean` (675 `.lean` files, single-pass `grep -rEnow`): **0** occurrences of any new name and
  **0** identifiers bearing any of the six prefixes — no declaration clash and no bare mention.
* Against the other draft lanes under `work/drafts/` (excluding `cvtail`): 0 prefix hits.
* `work/lean/lean-declarations.json`: none of the 177 names present.
**Clashes: none.** No renaming was necessary.

## 7. Notes for the executor / next wave

1. **Closing lines** (when `SM.cf_thm_carrierfloor` lands, `SM.cf_thm_carrierfloor.clauseC` is the floor
   argument everywhere): row 174 `gsc_generic_selected_of_moves <gsc_moves> …`; row 176
   `est_extreme_transport_of <floor> <est_port_relation> …`; row 177 replace `(by sorry)` by the proof of
   `esc_interface`. The `RowShape` forms `gsc_ledger`, `est_ledger`, `esc_ledger` feed `cv_R_of_rows` directly.
2. **Shared realisation machinery.** Items 174/4.4, 176/5.1–5.2, 177/(6) all need an `SM.Link.RIIData`
   construction on a positive lift with an outside match through the wall (`G11_Config`-style), plus an
   existence theorem for oriented smoothings (`OrientedSmoothingData`) of a polygonal diagram; neither exists in
   work/lean. Build once, use three times. U-177's `esc_contact_*` / `esc_touchingFactor_eq_of_*` and U-176's
   `est_retained_*` are reusable by the other two rows (rename prefix).
3. **Port map.** U-SLOT + `CarrierSlotFloor` → with row 155 (`CV/CarrierFloor.lean`); U-SPLIT (958 lines) →
   `CV/…` next to row 165 — there the `RProof` `DecidableEq` instance is absent, so `cvt165s_insert_eq` and the
   `attribute [local instance high]` become unnecessary; U-175 → `RProof/` with row 175 once `CV.SingletonDiData`
   is ported; the three ledgers → `RProof/GenericSelected.lean`, `RProof/ExtremeTransport.lean`,
   `RProof/ExtremeSelected.lean` (they import `CV.FullTwist`, `CV.HomflyRows`, and depend on
   `CV.CarrierSlotFloor`, so they port together with or after row 155).
4. **Pitfall inherited for any later unit in this lane:** the FINAL's `RProof.*` imports make
   `RProof.instDecidableEqCrossing` win over `Classical.propDecidable`; library `insert`/`∪` lemmas are stated
   with the classical instance — wrap helpers in a section with `attribute [local instance high]
   Classical.propDecidable` and bridge once via `Subsingleton.elim` (U_SPLIT_REPORT pitfall 1).
5. The U-177 leaf body (`exact esc_ledger (by sorry) …`) is the only leaf whose `sorry` is not a bare body;
   this is intentional (the hole IS the interface). If the sorry census tooling wants bare bodies, flatten it
   to `sorry` — the statement is unchanged either way.
6. PREREVIEW's non-blocking items are unaffected by the assembly (no statement changed).
