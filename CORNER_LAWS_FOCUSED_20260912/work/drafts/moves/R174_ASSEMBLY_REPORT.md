# R174_ASSEMBLY_REPORT — assembly of the row-174 consumer wave (Site 174 + units HREC, CARRIERS, SITEIN, WALL, SMOOTH)

Assembler (subagent), 2026-09-15 22:30 UTC / 6:30pm ET.  Inputs: `Site_174.lean` (2941 lines), the unit files
`R174_HREC.lean`, `R174_CARRIERS.lean`, `R174_SITEIN.lean`, `R174_WALL.lean`, `R174_SMOOTH.lean` with their
reports, `Statements_FINAL.lean` (frozen), `check_W1_identity.py`, `RProof/RALedgers.lean` (`gsc_Ledger`,
`gsc_moves`, `gsc_generic_selected_of_moves`), the fixed statement of `RProof.generic_selected`
(work/drafts/cvtail/Statements_FINAL.lean:738).  Compile command throughout:
`cd work/lean && lake env lean ../drafts/moves/<file>.lean` (toolchain of `work/lean`).  Nothing under `work/lean`
was written; scratch copies (union, axiom probes) live in the session scratchpad.

## 0. Deliverables and checks

| item | result |
|---|---|
| **`work/drafts/moves/R174_Assembled.lean`** | **8703 lines, 765 declarations**: `Site_174.lean` (2941, byte-identical) + the five unit appendices verbatim (435 declarations after de-duplication) + the composition block `r174_` (6 declarations, lines 8548–8703) |
| compile | **exit 0, 0 errors**, 38 s; warnings: the skeleton's **33** `declaration uses sorry` (all at lines ≤ 1819, the frozen Wave-1/Wave-3 leaves of `Skeleton_W1`) + its one cosmetic `<;>` note (line 566).  No new warning of any kind |
| `grep -c sorry` | **34** = the skeleton's 33 leaf bodies + its header prose (line 17); identical to `Site_174.lean` and to every unit file — **no `sorry` was added by any unit or by the assembler** |
| append-only verification (§1) | every unit file is byte-identical to `Site_174.lean` on lines 1–2941 (`cmp`); `R174_SITEIN.lean` is byte-identical to `R174_CARRIERS.lean` on lines 1–4439; `check_W1_identity.py`: **37/37** declarations of `Statements_FINAL.lean` byte-identical in every unit file and in the assembled file |
| **closed?** | **NO — one Prop remains**: `r174s_arc_rec_prop` (SMOOTH's black box; the two arcs of `x'` on the `E`-side lift carry the `P-ac` records of `A`, `B`), packaged as `r174_arc_rec` / `r174_arc_rec_moves` (§3).  Everything else in `gsc_Ledger` is PROVED |
| composition (§3) | `r174_ledger_nonempty : r174_arc_rec → Nonempty (gsc_Ledger …)`, **`r174_gsc_moves_of_arc_rec : r174_arc_rec_moves → gsc_moves`**, **`r174_generic_selected_of_arc_rec`** = the row leaf in the FIXED signature of `RProof.generic_selected` from `r174_arc_rec_moves` (`gsc_generic_selected_of_moves … CV.carrierSlotFloor`) |
| `#print axioms` (§4) | on the skeleton base: `r174_gsc_moves_of_arc_rec` = `propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — `sorryAx` ONLY through the frozen skeleton leaves (`exists_bigonData_of_triangle` inside `s174_core`; the Wave-1 sub-leaves behind `gsc_fulltwist_of_bigon`).  **On the ported library base (`SM.BigonDeletion`, port draft below): no `sorryAx`** — `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |
| **`R174_Port_GenericSelectedUnits_draft.lean`** (§7) | 6847 lines = `import SM.BigonDeletion` + `import RProof.RALedgers` + Site_174 lines 1868–2941 + the five appendices + the composition, verbatim: **exit 0, 0 errors, 0 `sorry` warnings, 0 other warnings** (37 s).  Proves the row-174 material needs nothing from the skeleton beyond what `SM/BigonDeletion.lean` (ported 20:20Z today) provides, and that it never touches `G11_core_sw` |
| name clashes (§6) | **0** fully-qualified clashes and 0 short-name coincidences among the new `s174_`/`r174*` names against `work/lean/**/*.lean`.  (The scan also reports 251 clashes of the FROZEN skeleton prefix, lines 49–1857, against `SM/BigonDeletion.lean` — the Wave-1 port; expected, not new names, and the reason the port draft drops the skeleton copy) |
| scripts | `assemble_R174.py` (append-only checks + concatenation + de-duplication + byte-for-byte comparison with the deliverable: prints `True`; `--write` regenerates) |

## 1. Verification that every unit only APPENDED prefixed material

Method: `head -n 2941 <unit> | cmp - Site_174.lean` (byte identity of the frozen prefix), `check_W1_identity.py
Statements_FINAL.lean <unit>` (statement byte-identity of the 37 frozen declarations), a declaration scan of the
appended range (every declaration carries the unit prefix; structural lines are `namespace SM.Link` / `open SM
SM.GeoCarrier SM.Carrier RProof` / `noncomputable section` / sections / `end`, each appendix a self-contained
block), and the unit's own compile as recorded in its report.

| unit | file (lines) | appended range | prefix, declarations | `cmp` prefix | `check_W1_identity` | compile (report) | black boxes stated |
|---|---|---|---|---|---|---|---|
| Site 174 | `Site_174.lean` (2941) | 1868–2941 (skeleton = 1–1867 incl. the added `import RProof.RALedgers`) | `s174_`, 55 | = `Skeleton_W1` + import | 37/37 | 0 errors | `s174_hrec_prop` (a `def : Prop`, no `sorry`) |
| HREC | `R174_HREC.lean` (3390) | 2942–3390 (449) | `r174h_`, 30 | identical | 37/37 | 0 errors, ≈ 23 s | none |
| CARRIERS | `R174_CARRIERS.lean` (4439) | 2942–4439 (1498; two `namespace SM.Link` blocks) | `r174c_`, 149 | identical | 37/37 | 0 errors, ≈ 19 s | none |
| SITEIN | `R174_SITEIN.lean` (4630) | 4440–4630 (191); lines 1–4439 = `R174_CARRIERS.lean` byte-identical | `r174x_`, 17 | identical | 37/37 | 0 errors, ≈ 17 s | none (not in the task's input list but present on disk and needed: it supplies the site inputs `hx'`, `hw'` at exactly the ledger's binding) |
| WALL | `R174_WALL.lean` (5399) | 2942–5399 (2458) | `r174w_`, 200 (+1 global `@[instance_reducible] def r174w_decEqCrossing`, used only as a `local instance` inside its own sections) | identical | 37/37 | 0 errors, ≈ 29 s | none |
| SMOOTH | `R174_SMOOTH.lean` (3947) | 2942–3947 (1006) | `r174s_`, 42 (incl. `Record.r174s_*`) | identical | 37/37 | 0 errors, ≈ 17 s | `r174s_arc_rec_prop` (a `def : Prop`, no `sorry`) |

`check_W1_identity.py`'s range checks 1 and 3 report `False` on every file for the two reasons Site_174_REPORT §0
records (the skeleton's added import line shifts the 136-line prefix; appended material after the FINAL's suffix);
check 2 — the byte-identity of all 37 frozen statements — passes everywhere.  **Verdict: all five units are
append-only; no frozen declaration, docstring or statement changed; no unit added a `sorry`.**

## 2. Assembly

`R174_Assembled.lean` = `Site_174.lean` + HREC[2942:3390] + CARRIERS[2942:4439] + SITEIN[4440:4630] +
WALL[2942:5399] + SMOOTH[2942:3947] (one blank line between blocks; CARRIERS before SITEIN, which uses `r174c_`),
then de-duplication, then the composition block.  Layout (line numbers of the deliverable): skeleton 1–1867 ·
Site 174 (`s174_`) 1870–2941 · HREC 2944–3391 · CARRIERS 3394–4890 (its §6 block 4463–4890) · SITEIN 4893–5082 ·
WALL 5086–7538 · SMOOTH 7542–8545 · composition 8548–8703.

**De-duplication.**  By name nothing clashes (the prefixes are disjoint; 765 distinct fully-qualified names).  A
statement scan of the appended material found 13 statement-identical groups; only pairs with the SAME binder
structure at every use site were merged (W1's rule):

| dropped (WALL) | kept (CARRIERS) | statement | use lines renamed |
|---|---|---|---|
| `r174w_x_not_mem_Q` | `r174c_x_not_mem_Q` | `x ∉ Q` (both take exactly `D`; `hP` implicit) | 7 |
| `r174w_w_not_mem_Q` | `r174c_w_not_mem_Q` | `w ∉ Q` | 6 |
| `r174w_m_not_mem_Q` | `r174c_m_not_mem_Q` | `m ∉ Q` | 7 |

Kept, statement-identical but with DIFFERENT explicit binders (WALL's Part A takes `hG hG' D`, CARRIERS/SITEIN take
`D` with `hP` implicit), so a rename would have to edit argument lists: `r174c_/r174w_{x,w}_not_mem_Sm`,
`r174c_/r174w_m_mem_Sm`, `r174x_/r174w_good_x₂`, `r174x_/r174w_good_w₂` (8 one-liners; a port may merge them).  The
remaining groups are different definitions of the same type (`r174c_qC`/`r174c_qAB`, `r174c_qA`/`qB`/`qC'`,
`r174w_qA`/`qB`/`qCp`, `r174w_qABi`/`qCi`) or theorems with a common hypothesis prefix — not duplicates.

Two units realise the SAME ledger content independently; both are kept because the composition needs one lemma
from each side and the port can prune: the site inputs `hx'`, `hw'` exist as `r174x_hx'_tau`/`r174x_hw'_tau`
(SITEIN, at `W.τ (r174c_qAB D)`) and as `r174w_x'_mem_retained`/`r174w_w'_mem_retained` (WALL, at
`r174w_τ … (r174w_qAB …)`, the same terms up to `abbrev` unfolding); the retained-crossing correspondence of `AB`
across the wall exists as HREC's `r174h_mem_retained'`/`r174h_retained_of_mem'` and as WALL's
`r174w_retained_qAB` (a `Finset` equation, the one `writhe_wall` uses).

## 3. Composition — how far `RProof.generic_selected` gets

Setting (the binders of `gsc_moves`): `hn`, `hG hG' : CV.Generic`, `D : GT_Endpoint hG.cg hG'.cg hs e f g Q x w m
ℓ₁ ℓ₂ ℓ₃`, `hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃`, `hSm hSxw hSm'`; `W := gsc_wallData_of_endpoint hn
hG hG' D hSm hSm'`.  The carriers are CARRIERS' (`r174c_qC D = L_m(x₁)`, `r174c_qAB D = L_m(x₂)`, `r174c_qA D =
L_xw(m₁)`, `r174c_qB D = L_xw(m₃)`, `r174c_qC' D` case-defined by the `ℓ₁`-order); WALL's ledger theorems take the
carriers as `geoOwner` terms with equations, discharged by the `rfl`-lemmas `r174c_qAB_x₂`, `r174c_qC_x₁`,
`r174c_qA_m₁`, `r174c_qB_m₃`.

### 3a. The glue lemma — `r174_qC'_eq` (standard axioms)
`r174c_qC' D = r174w_qC' hG hG' D`: CARRIERS' `qC'` carries `x₁, w₂` (case A, `r174c_qC'_A`, `r174c_qC'_w₂_A`) or
`x₂, w₃` (case B, `r174c_qC'_B`, `r174c_qC'_w₃_B`), and WALL's `r174w_qC'_unique` says any carrier of the pair row
carrying a visit of `x` and a visit of `w` is `r174w_qC'`; the case split is `lt_or_gt_of_ne (r174c_param_x₁_ne_m₁ D)`.
This is the only bridge the two units needed.

### 3b. The open Prop — `r174_arc_rec`, `r174_arc_rec_moves`
```
abbrev r174_arc_rec hn hG hG' D hSm hSxw hSm' : Prop :=
  r174s_arc_rec_prop hn hG hG' hSxw hSm' (W.τ (r174c_qAB D)) (r174x_hx'_tau hG hG' D hSm hSm' hn) (r174c_qA D) (r174c_qB D)
def r174_arc_rec_moves : Prop :=  -- the binders of gsc_moves, same order
  ∀ (n) [NeZero n] (hn) {P P'} (hG hG') (hs) (e f g) (Q) (x w m) (ℓ₁ ℓ₂ ℓ₃) (D), crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃ →
    ∀ (hSm) (hSxw) (hSm'), r174_arc_rec hn hG hG' D hSm hSxw hSm'
```
(`r174s_arc_rec_prop` is a `def … : Prop` with no `sorry`: ∃ an occurrence `u` of the lifted `x'` on
`D_H = carrierDiagram (W.τ qAB)` such that `D_H.record.restrictCrossings (KeepArc u) ≅ (carrierDiagram qA).record`
and the same for the other arc and `qB`.)

### 3c. The ledger — `r174_ledger_nonempty (hsplit : r174_arc_rec …) : Nonempty (gsc_Ledger … W)`

| `gsc_Ledger` field | witness | unit |
|---|---|---|
| `σ`, `hσ` | `r174w_sigma hG hG' D`, `r174w_hsigma hG hG' D hsgn` | WALL |
| `qC qAB hCAB` | `r174c_qC D`, `r174c_qAB D`, `r174c_hCAB D hSm` | CARRIERS |
| `qC' qA qB hC'A hC'B hAB` | `r174c_qC' D`, `r174c_qA D`, `r174c_qB D`, `r174c_hC'A D hn hSxw`, `r174c_hC'B D hn hSxw hsgn`, `r174c_hAB D hSxw` | CARRIERS |
| `omega_wall` | `r174w_omega_wall_ledger hn hG hG' D hSm hSm' (r174c_qAB D) (r174c_qAB_x₂ D)` | WALL |
| `writhe_wall` | `r174w_writhe_wall_ledger hn hG hG' D hSm hSm' (r174c_qAB D) (r174c_qAB_x₂ D)` | WALL |
| `ρ ρ_AB ρ_C spectator_weight spectator_omega` | `r174c_ρ D hn hSm hSxw hsgn`, `r174c_ρ_AB`, `r174c_ρ_C`, `r174c_spectator_weight hn hG D hSm hSxw hsgn`, `r174c_spectator_omega …` | CARRIERS |
| `omega_C` | `r174_qC'_eq ▸ r174w_omega_C hn hG hG' D hsgn hSm hSxw (r174c_qC D) (r174c_qC_x₁ D).symm` | WALL + glue |
| `weight_C` | `r174_qC'_eq ▸ r174w_weight_C hn hG hG' D hsgn (r174c_qC D) (r174c_qC_x₁ D).symm` | WALL + glue |
| `weight_AB` | `r174w_weight_AB hn hG hG' D hsgn (r174c_qAB D) _ (r174c_qA D) (r174c_qB D) _ _` | WALL |
| `carrierR_add` | `r174w_carrierR_add hn hG hG' D hsgn hSm hSxw (r174c_qAB D) _ (r174c_qA D) (r174c_qB D) _ _` | WALL |
| `D₀ qx fulltwist i j ℓ smoothing writhe_count` | `r174s_ledger_fields hn hG hG' D hsgn hSm hSxw hSm' (r174c_qAB D) (W.τ (r174c_qAB D)) hx' hw' (r174c_qA D) (r174c_qB D) hrec hsplit hwall` with `hx' := r174x_hx'_tau …`, `hw' := r174x_hw'_tau …` (SITEIN), `hrec := r174h_hrec_tau hn hG hG' D hSm hSm' (r174c_qAB D) hx' hw'` (HREC), `hwall := writhe_wall` (WALL), `hsplit` the open Prop | SMOOTH + SITEIN + HREC + WALL |

So `gsc_Ledger` is realised field for field; the ONLY hypothesis is `hsplit`.

### 3d. The row
```
theorem r174_gsc_moves_of_arc_rec (harc : r174_arc_rec_moves) : gsc_moves
theorem r174_generic_selected_of_arc_rec (harc : r174_arc_rec_moves) (hn) (E : CV.Event n) (e f g) (h3) (h4e) (h4f) (h4g)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ :=
  gsc_generic_selected_of_moves (r174_gsc_moves_of_arc_rec harc) CV.carrierSlotFloor hn E e f g h3 h4e h4f h4g hE
```
The second is the fixed statement of `RProof.generic_selected` (work/drafts/cvtail/Statements_FINAL.lean:738)
with the one extra hypothesis `harc`; the composition is exactly the one `gsc_generic_selected_of_moves`'s
docstring prescribes (`CV.carrierSlotFloor = carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC`).  Once
`r174_arc_rec_moves` is proved (§5), `RProof.generic_selected := r174_generic_selected_of_arc_rec <proof>` and the
row 174 leaf closes with no interface edit (`RALedgers.lean` untouched by every unit and by the assembler).
The unconditional `r174_gsc_moves : gsc_moves` was NOT written (it would need the open Prop).

## 4. Compile and axioms

`#print axioms` was run on scratch copies (the deliverable contains no `#print`/`#eval`/`#check`):

| declaration | assembled file (skeleton base) | port draft (`SM.BigonDeletion` base) |
|---|---|---|
| `r174_gsc_moves_of_arc_rec`, `r174_ledger_nonempty`, `r174s_ledger_fields`, `r174s_fulltwist_of_hrec` | standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` **+ `sorryAx`** | standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — **no `sorryAx`** |
| `r174_generic_selected_of_arc_rec` | the above + `SM.lit_homfly_descent, SM.ng_finite_word, SM.src_contact` (from `CV.carrierSlotFloor`, checked separately: `#print axioms CV.carrierSlotFloor` lists exactly these; `gsc_generic_selected_of_moves`, `gsc_ledger` list standard + the homfly triple) | same minus `sorryAx` |
| `s174_site`, `s174_core`, `exists_bigonData_of_triangle`, `gsc_fulltwist_of_bigon` | `+ sorryAx` (the frozen skeleton leaves) | standard (+ the homfly triple for `gsc_fulltwist_of_bigon`) |
| `r174_qC'_eq`, `r174_arc_rec_moves`, `r174h__s174_hrec_prop_proof`, `r174h_hrec_tau`, `r174c_ρ`, `r174x_hx'_tau`, `r174x_hw'_tau`, `r174w_writhe_wall_ledger`, `r174w_weight_AB`, `r174w_weight_C`, `r174w_carrierR_add`, `r174w_hsigma`, `r174s_arc_rec_of_visitData` | `propext, Classical.choice, Quot.sound` | same |
| `r174c_carrierData`, `r174w_omega_wall_ledger`, `r174w_omega_C`, `r174s_smoothing_split_of_arc` | standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the `Ω₁`/`homfly` reads through `CV.gausscode_polynomial`) | same |

All non-standard axioms are the registered literature axioms of `work/lean/axiom-policy.json` (`lit:homfly`,
`lit:homfly (descent sentence)`, `lp:lm`, `lp:lm-uniqueness`, `ng:finite-word`, `src:contact`).  **`sorryAx`
sources on the skeleton base**: only the frozen leaves of `Skeleton_W1` reached by row 174 —
`exists_bigonData_of_triangle` (inside `s174_core`/`s174_site`) and the Wave-1 sub-leaves behind
`gsc_fulltwist_of_bigon → exists_rii_deletion` (`m1_…m6_*`, `reducedRecord_counts`,
`Record.restrictCrossings_switch`).  Every one of them is PROVED in `work/lean/SM/BigonDeletion.lean` (ported
from `Moves_Assembled.lean` at 20:20Z 2026-09-15; `#print axioms SM.Link.exists_bigonData_of_triangle` and
`SM.Link.exists_rii_deletion` there: standard), which is why the port draft is `sorryAx`-free.  The Wave-3 leaf
`G11_core_sw` is NOT reached (the port draft compiles against `SM.BigonDeletion`, which omits it).  No `sorryAx`
enters through any `r174*`/`s174_` declaration of its own.

## 5. Remaining `sorry` / black boxes — exactly

| # | obligation | where | status | estimate |
|---|---|---|---|---|
| 1 | **`r174s_arc_rec_prop`** at the ledger's binding = `r174_arc_rec hn hG hG' D hSm hSxw hSm'`, quantified as **`r174_arc_rec_moves`** (U_R174 §4 items 1–2 in arc form: for an occurrence `u` of `x'` on `D_H = carrierDiagram (W.τ qAB)`, `D_H.record.restrictCrossings (KeepArc u) ≅ (carrierDiagram (Q∪{x,w}) qA).record` and the other arc ≅ `qB`'s record) | SMOOTH §2; the hypothesis of `r174_ledger_nonempty` / `r174_gsc_moves_of_arc_rec` / `r174_generic_selected_of_arc_rec` | **OPEN** — the only open Prop of row 174; stated as a `def : Prop`, never asserted, no `sorry` in the file | **0.6–1.5k lines.**  SMOOTH's `r174s_arc_rec_of_visitData` reduces it to two `r174s_ArcVisitData` (visit bijections `ψ_A : retained visits of qA ≃ retained visits of AB' strictly inside the arc (u, τu)`, `ψ_B` for the other arc; twin-, key-order- and divide-sign-compatible).  Inputs now PROVED: HREC's `r174h_transfer` (the identity on parent visits transported by `visitTransport`, with `r174h_key_lt`/`r174h_cyc` for the key order and `GT_Endpoint.sign_eq` for the bits — the same shape), CARRIERS' `r174c_owner_qAB_iff` (`L_m b = qAB ↔ L_xw b = qA ∨ L_xw b = qB` on non-local marks) and `r174c_entry_qA_qB`, WALL's `r174w_retained_qAB` (`retained(τ AB) = {x', w'} ∪ transport(retained(AB))`) and `r174w_Split` (which arc of `AB` is `A`'s and which `B`'s, in both orientations); what is new is only "a retained visit of `AB'` lies strictly inside the arc `(u, τu)` iff its `P`-preimage is owned by `qA`" (`arcBetween_iff_key` + the cyclic order of `x₂, m₁/m₃, w₂`-visits), in both orientations.  HREC's actual/estimated ratio (449 lines vs 1.5–2.5k) suggests the lower end |
| 2 | the frozen skeleton leaves reached by row 174 (`exists_bigonData_of_triangle`; `m1_…m6_*`, `reducedRecord_counts`, `Record.restrictCrossings_switch` behind `exists_rii_deletion`) | `Skeleton_W1` lines ≤ 1819 (the `sorryAx` of §4 on the skeleton base) | **closed in the library**: `SM/BigonDeletion.lean`; the port draft shows the row material compiles on it with 0 `sorry` | 0 lines (port only) |
| 3 | `G11_core_sw` (Wave 3, row 177 (4)) | skeleton §4 | not reached by row 174 | — |

Nothing else: `s174_hrec_prop` (Site 174's black box) is PROVED (`r174h_hrec_tau`); the site inputs `hx'`, `hw'`
are PROVED (`r174x_hx'_tau`, `r174x_hw'_tau`; also `r174w_x'_mem_retained`, `r174w_w'_mem_retained`);
`writhe_wall` (SMOOTH's `hwall`) is PROVED (`r174w_writhe_wall_ledger`); item 1's fourteen fields, items 2–3 and
`omega_C` are PROVED; items 4–6 are PROVED from #1.

## 6. Name-clash scan (`clash_scan_W1.py` applied to the assembled file; namespace-aware)

765 declarations, 765 distinct fully-qualified names, 0 internal duplicates.  Against every declaration of
`work/lean/**/*.lean` (`.lake` excluded): **0 clashes and 0 short-name coincidences among the new material** (all
496 declarations from line 1868 on: `s174_`, `r174h_`, `r174c_`, `r174x_`, `r174w_`, `r174s_`, `Record.r174s_*`,
`r174_`).  The 251 reported clashes are all in the frozen skeleton prefix (lines 49–1857: `SM.Link.BigonData.*`,
`exists_rii_deletion`, `exists_bigonData_of_triangle`, `gsc_fulltwist_of_bigon`, …) against
`SM/BigonDeletion.lean` — the Wave-1 port that landed at 20:20Z today; they are the SAME declarations, and the
skeleton copy must not be ported again (§7).  The 61 informational short-name coincidences of the W1 report
(`BigonData.*` vs `Smoothing.*`) are unchanged and lie in the skeleton.

## 7. Port notes — library material for `RProof/GenericSelectedUnits.lean` once the row closes

* **Base.**  Do NOT port the skeleton copy (lines 1–1867 of the assembled file): it is `SM/BigonDeletion.lean`.
  The row material imports `SM.BigonDeletion` and `RProof.RALedgers` (no cycle: `RALedgers` imports `X1Rows`,
  `X1Rows2`, `GenericTransport`, `CV.ChamberInvRow`, `CV.FullTwist`, `CV.HomflyRows`, `CV.CarrierFloor`,
  `Bridge.SmR`; `BigonDeletion` imports `SM.Smoothing`, `SM.MarkedProducts`, `SM.SingleCrossing`, `CV.FullTwist`,
  `RProof.GenericTransport`; neither imports the other; both are matched by the lakefile globs `SM.+`/`RProof.+`).
  **`R174_Port_GenericSelectedUnits_draft.lean` IS this port**, tested: exit 0, 0 `sorry`, the composition
  `sorryAx`-free.  Only the module docstrings ("Everything below is NEW (nothing above changed)") need rewording.
* **Namespace.**  Everything is in `SM.Link` (the site's home, because `s174_lift`/`BigonData` live there); the row
  theorems `r174_gsc_moves_of_arc_rec` / `r174_generic_selected_of_arc_rec` could move to `RProof` at port time
  (they only `open` `SM.Link`'s names); `RProof.generic_selected` itself belongs in `RProof/X1Rows.lean`'s row-174
  slot or `RALedgers.lean` next to `gsc_generic_selected_of_moves`.
* **What is library material (keep):**
  - `s174_core` (the generic bigon-site core on any `CarrierGeometry` polygon: the `j = 1` site of
    `exists_bigonData_of_triangle` from A7 exactness + the sign condition) and `s174_order` (the corner traversal
    order forced by the sign condition) — re-used by row 176's `j`-corner site;
  - HREC's `r174h_recordIso` route (record transport across a `GT_Wall` by the identity on parent visits: general
    template for every wall-record identification, incl. row 176's `hrec` and #1 above), its record helpers
    `r174h_switch_*`, `r174h_crossingOf_overVisit_eq_iff`;
  - CARRIERS §1–§2 tools `r174c_pow_eq_of_agree`, `r174c_sameCycle_iff_of_agree`, `r174c_owner_iff_of_avoid`
    (permutations agreeing off a set have the same orbits away from it; "a carrier avoiding the visits of `S ∆ T`
    is the same cycle for both supports") and §6 `r174c_exists_first`/`r174c_first_local` — general
    support-change lemmas for the geo carrier layer (SM/FlatCarriers material);
  - WALL Part B (`r174w_tau`, `r174w_theta`, `r174w_weight_eq`, `r174w_two_pi_rot`, `r174w_F_split`, `r174w_F_two`,
    `r174w_rot_add`, `r174w_carrierR_add_of`, `r174w_angle_add_of_pos/neg`) — the corner-mark reformulation of
    the selector and of `2π·rot`; CV/Rotation-level material, re-usable by every corner ledger (176, 177);
    Part C `r174w_child` (the insertion child data on mark keys) — SM/GeoCarrierCount material;
  - SMOOTH §B (`Record.r174s_KeepArc`, `r174s_smooth_comp_eq_iff`, `r174s_firstReturn_mul_swap_of_apply_eq`,
    `r174s_firstReturn_reconnect_eq`, `r174s_restrict_smooth_iso`) — record-level: the two circles of a smoothing
    of a self crossing on a one-circle record are the two arc restrictions (SM/LinkRecordExtras material); §C
    `r174s_knotRestrict_record_iso`, `r174s_split_of_arc_prop` (generic smoothing-split from arc records);
    the `s7h_*` reproductions `r174s_writhe_*`/`r174s_mixedSignSum_eq`/`r174s_writhe_two_component` DUPLICATE
    SM/CornerChainUnits.lean (not in the import chain) — at port time import that module or move the originals
    to a shared home instead of keeping two copies;
  - SMOOTH §E `r174s_ArcVisitData`, `r174s_recordIso_of_arcVisitData` — the `GT_homfly_wall_gen`-shaped record
    identification from visit data (the interface #1 must be proved against).
* **Row-specific (port with the row, prune at leisure):** `s174_site`, `s174_fulltwist_of_hrec`; HREC §1c and
  `r174h__s174_hrec_prop_proof`/`r174h_hrec_tau`/`r174h_fulltwist`; CARRIERS' `r174c_qC … r174c_ρ`,
  `r174c_carrierData`; SITEIN; WALL Parts A, C (`r174w_Split`), D; SMOOTH §D; the composition block.  The
  duplicates of §2 (8 kept pairs; SITEIN vs WALL site inputs; HREC vs WALL retained correspondence) can be
  pruned to one copy each.
* **Instance hygiene.**  WALL's `r174w_decEqCrossing` (classical `DecidableEq (Crossing P)`, `local instance high`
  in its Parts B–C) exists because SM/GeoCarrierCount's `insert` is classical while `RProof` supplies
  `instDecidableEqCrossing`; the ledger-facing sections deliberately do not activate it.  Keep that separation at
  port time (R174_WALL_REPORT §6.2).

## 8. Findings recorded for the row (no frozen statement needed editing; rule (4) never invoked)

1. **`σ` is orientation-dependent** (WALL §2): the ledger's `σ` must be `r174w_sigma = −τ(m_AB)`, which equals
   `crossingSign ℓ₁ ℓ₂` in the printed orientation and its NEGATIVE in the reversed one
   (`r174w_sigma_vs_crossingSign`); `gsc_sigma_of_endpoint` is a true statement but not the right `hσ` witness.
   The docstrings of `gsc_Ledger`/`gsc_moves` read `σ` as `crossingSign ℓ₁ ℓ₂`; an AUTHOR_NOTES entry should
   record the orientation dependence.  The assembled ledger uses `r174w_sigma`.
2. **`s174_hrec_prop` is provable only at the ledger's binding** (HREC §2): for an arbitrary `q'` it is false; the
   composition uses it at `q' := W.τ (r174c_qAB D)` (`r174h_hrec_tau`), exactly as `gsc_Ledger.fulltwist` binds it.
3. **`qC'` is necessarily case-dependent** (CARRIERS §4): no case-free visit description exists; the two units'
   definitions agree (`r174_qC'_eq`).
4. **The site inputs need no arc argument** (SITEIN §2): the `ℓ₂`-visits are good marks and `x', w' ∈ U(S')`.
5. **Wave 1 is in the library**: `SM/BigonDeletion.lean` (20:20Z) makes the whole row chain `sorryAx`-free on
   the library base — the port draft is the evidence.

## 9. What the next prover gets

Prove `r174_arc_rec_moves` (§5 #1) — i.e. for each configuration, two `r174s_ArcVisitData` on the carrier
diagrams and `r174s_arc_rec_of_visitData` — and then:
```
theorem r174_gsc_moves : gsc_moves := r174_gsc_moves_of_arc_rec <proof>
theorem generic_selected … := r174_generic_selected_of_arc_rec <proof> hn E e f g h3 h4e h4f h4g hE   -- in RProof
```
Start from `R174_Port_GenericSelectedUnits_draft.lean` (library base, no `sorry`), not from the skeleton copy.
