# R176_ASSEMBLY_REPORT — assembly of the row-176 consumer wave (Site_176 + HSUCC + SMOOTH + LEDGER)

Assembler (subagent), 2026-09-15 22:05–22:30 UTC / 6:05–6:30pm ET.  Inputs: `Site_176.lean` (4143 lines, frozen for
the wave), `R176_HSUCC.lean`, `R176_SMOOTH.lean`, `R176_LEDGER.lean` with their reports, `Statements_FINAL.lean`,
`check_W1_identity.py`, `clash_scan_W1.py`.  Compile command throughout: `cd work/lean && lake env lean
../drafts/moves/<file>.lean` (Lean 4.34.0-rc2 toolchain of `work/lean`).  Nothing under `work/lean` was written; no
`lake build`.  Scratch copies (`#print axioms`, the port test) live in the session scratchpad, not in the deliverables.

## 0. Result and checks

**The row is NOT closed; it is reduced to exactly three open Props.**  `r176_extreme_transport_of_curl_outer_mixed
(hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L) (hmixed : r176_mixed_bridge) : RowShape @ExtremeTransportData`
is PROVED (composition of the three units through `s176_est_ledger_weak`'s chain, with the `wind(S) = 0` split added and
`CV.CarrierSlotFloor` discharged by the library's `CV.carrierSlotFloor`).  `hrec` (HSUCC) is closed; the LEDGER's
geometric ledgers (14)/(13)/(12) are closed under `wind ≠ 0`; SMOOTH's smoothing/owner-map constructions are closed
modulo the record-level R-I and the outer-carrier identification.

| item | result |
|---|---|
| **`work/drafts/moves/R176_Assembled.lean`** | **8198 lines**, 617 declarations: skeleton 267 (lines 1–1867) · Site_176 appendix 105 `s176_` (1868–4143) · HSUCC 14 `r176h_` (4144–4492) · SMOOTH 65 `r176s_` (4493–5402) · LEDGER 148 `r176l_` (5403–7504) · composition 18 `r176_` (7505–8198) |
| compile | **exit 0, 0 errors**, 25 s; warnings: exactly the skeleton's **33** `declaration uses sorry` (lines 119…1819, all ≤ 1867) + the skeleton's `<;>` lint (566) + LEDGER's harmless unused-section-variable note (`r176l_selectedPart_eq`, 7013); **no warning from any appendix or from the composition** |
| `grep -c sorry` | **34** = 33 skeleton leaf bodies + the frozen header's docstring mention (line 18); no `sorry` after line 1820 |
| prefix identity | `head -4143` of each unit file `cmp`-identical to `Site_176.lean`; `R176_Assembled.lean[1..4143] == Site_176.lean`; `Site_176.lean` minus its added `import RProof.RALedgers` (line 6) `== Skeleton_W1.lean` byte for byte |
| statement identity | `check_W1_identity.py Statements_FINAL.lean R176_Assembled.lean`: **37/37** declarations byte-identical (changed/missing 0); its two range checks report `False` MECHANICALLY (the import line shifts lines 1–136; an appendix cannot end with the Statements_FINAL suffix) — identical outcome for `Site_176.lean` and every unit file; stronger check: **every line of `Statements_FINAL.lean` except its five leaf `sorry` bodies occurs, in order, in the assembled file** |
| appended-only | every appendix declaration carries its unit prefix (14/14 `r176h_`, 65/65 `r176s_`, 148/148 `r176l_`); no `import`/`set_option`/global `attribute` line added (LEDGER's `attribute [local instance 2000] r176l_decEq` is section-local); 0 duplicate names among appendices + composition + Site |
| `#print axioms` (scratch copy, §4) | the composition on the draft: standard + registered literature axioms + `sorryAx` **through the frozen skeleton only**; on the port-time copy (skeleton → `import SM.BigonDeletion`): **no `sorryAx`** anywhere, registered axioms only |
| port test (`R176_Port_draft.lean`, §7) | assembled lines 1868–8198 under the library imports + `import SM.BigonDeletion`: **exit 0, 0 errors, 0 `sorry`** (6339 lines) |
| name clashes against `work/lean` (§6) | **0** for the 350 Site/unit/composition declarations; 251 fully-qualified hits, ALL at lines ≤ 1857 = the frozen skeleton duplicating the now-ported `SM/BigonDeletion.lean` (resolved by the same import replacement) |
| scripts | `assemble_R176.py` (prefix/appended-only/duplicate checks + concatenation + composition; `python3 assemble_R176.py .` regenerates the file), `gen_R176_compose.py` (the composition section, output `R176_compose_part.lean`), `clash_scan_R176.py` (→ `clash_scan_R176.json`) |

## 1. Verification of the three unit files: APPENDED ONLY

Method: `cmp` of the first 4143 lines of each unit against `Site_176.lean` (equal, all three); the appendix scanned
line by line (`assemble_R176.py`): every `theorem/def/abbrev/structure` name starts with the unit prefix; no
structural line; `check_W1_identity.py` 37/37 on each unit (the two range checks `False` mechanically, as for
`Site_176.lean` itself — see §0).

| unit | appendix lines | declarations | prefixed | `sorry` added | structural lines | black boxes (as hypotheses / `def … : Prop`, no `sorry`) |
|---|---|---|---|---|---|---|
| HSUCC | 349 (Site 4144–4492) | 14 | 14/14 `r176h_` | 0 | none | none |
| SMOOTH | 910 (4144–5053) | 65 | 65/65 `r176s_` | 0 | none | `r176s_curl_removal`, `r176s_outer_carriers`, `r176s_ledger` (Props), `r176s_OuterData` (data) |
| LEDGER | 2102 (4144–6245) | 148 | 148/148 `r176l_` | 0 | `attribute [local instance 2000] r176l_decEq` inside `section L3` (allowed, scoped) | `r176l_SmoothData` (structure), `r176l_smooth_black_box` (Prop) |

Verdict: **all three units only appended prefixed material; no frozen declaration (skeleton or Site) was touched.**

## 2. Assembly

`R176_Assembled.lean` = `Site_176.lean` ++ HSUCC appendix ++ SMOOTH appendix ++ LEDGER appendix ++ the composition
section (in that order: SMOOTH before LEDGER so that the connector §X3 can consume both).  Each appendix is a closed
`namespace RProof … noncomputable section … end … end RProof` block, so plain concatenation is sound; the plain
concatenation (without the composition) was compiled first: exit 0, 0 errors, the same 33 + 2 warnings, 36 s.

De-duplication: by NAME nothing is duplicated (disjoint prefixes; 0 internal duplicates among 617 fully-qualified
names).  By STATEMENT (text up to `:=`, modulo the name) no two declarations of different units coincide
(`assemble_R176.py`, informational scan, 0 pairs after discarding the trivial `def NAME : Prop` heads).  Near
duplicates worth one line at port time (kept, both used): `r176h_record_componentCount` (for `geoPositiveLift`) vs
`r176s_record_componentCount_one` (any one-component diagram); `r176s_third` vs the library's `est_others`
(RALedgers); `r176s_Sfull_ind` (`transportSupport hs (Q ∪ {j, u, v}) ∈ Ind`) vs `r176l_Sf_indep_event`
(`GeoIndependent … (r176l_Sf S' u' v')`, the LEDGER's classical-`insert` form) — the same fact in the two units'
coordinates, bridged by `r176s_Sfull_eq`; `r176l_mixedSignSum_eq` is a copy of the accepted `SM.s7h_mixedSignSum_eq`
(SM/CornerChainUnits.lean, not in the import closure of the draft).  No renames were needed.

**Connecting the LEDGER's black box to SMOOTH's constructions** (the task's item 2) — composition §X1–§X3:

* The two units use different coordinates for `S_full` and the outer carriers.  SMOOTH: `Sf = transportSupport hs
  (Q ∪ {j, u, v})`, carriers `Λ_A, Λ_B` EXISTENTIAL (`r176s_OuterData`), identified with the record arcs by
  `KA_eq/KB_eq`.  LEDGER: `Sf = r176l_Sf S' u' v'` (classical `insert`, forced by the accepted insertion lemmas),
  carriers DEFINED as `Λ₁ = r176l_L1 = owner_{Sf} (v', c)` (kinked), `Λ₂ = r176l_L2 = owner_{Sf} (u', a)` (clean),
  and its ledgers (14)/(13)/(12) are PROVED for these.  Transporting a `GeoComponent` across the propositional
  equality of the two `Sf`s is not worth it; the connector is written in the LEDGER's coordinates:
* `structure r176_OuterDataL` (line 7558) = `r176s_OuterData` with `ΛB := r176l_L1`, `ΛA := r176l_L2` (fields `v₀ hv₀
  subA subB KA_eq r KB_eq r_not r_curl`, verbatim shapes).
* `def r176_smoothData_of (hcurl) … (O : r176_OuterDataL …) (hSf) (hmixed) : r176l_SmoothData hn (genericAt E t' ht'.1)
  hS' q₀' y (r176l_Sf …) hSf (r176l_L1 …) (r176l_L2 …)` (line 7700): `DA := r176s_DA D₊ y`, `smooth := r176s_DA_smooth`,
  `two := r176s_DA_componentCount`, `i/j := r176s_DA_i/j` (the `B`-class of `v₀` / the `A`-class of `τ v₀`),
  `ij := r176s_DA_ij`, `poly₁` via `r176s_homfly_of_liftBlock_curl` + `r176s_knotRestrictIso_i` (the kinked child),
  `poly₂` via `r176s_homfly_of_liftBlock` + `r176s_knotRestrictIso_j`, `mixed := hmixed`.  Compiled first time
  (after one structure-instance indentation fix); axioms standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`.
* The LEDGER's three event theorems are replayed against the connector (`r176_portDataRest_case1 / _labelled /
  _of_uniform`, lines 7749–7990: bodies byte-identical to `r176l_portDataRest_*` except the `hsmooth` call, replaced by
  `hout … ▸ r176_smoothData_of hcurl … O hSf' (hmixed … O)`).

## 3. Composition: how far `RProof.extreme_transport` gets

Chain (every arrow a theorem in the file): open Props → `r176_portDataRest_case1` → `_labelled` (either orientation) →
`_of_uniform` (six relabellings) → `r176_est_port_relation_weak_uniform_of_curl_outer_mixed :
r176l_est_port_relation_weak_uniform` (port from HSUCC's `r176h_est_port_weak`, `hrec` CLOSED) →
`r176_est_row_H_weak_uniform` (the `wind = 0` split, §3.3) → `r176_est_row_weak_uniform` →
`r176_est_extremeTransportData_weak_uniform` → `r176_est_ledger_weak_uniform : CarrierSlotFloor →
r176l_est_port_relation_weak_uniform → RowShape @ExtremeTransportData` → **`r176_extreme_transport_of_curl_outer_mixed`**
(line 8150) with `hF := CV.carrierSlotFloor` (CV/CarrierFloor.lean:482, thm:carrierfloor (C), library).

Naming: the task's `r176_est_port_relation_weak_of_<remaining>` is realised as
**`r176_est_port_relation_weak_uniform_of_curl_outer_mixed`** — the target Prop is the CORRECTED weak interface
`r176l_est_port_relation_weak_uniform` (with `wind(S) ≠ 0`), not `s176_est_port_relation_weak`, because the latter is
(very likely) FALSE as stated (R176_LEDGER_REPORT §3: on a mixed affected carrier (13)/(12) fail; the printed proof
never needs them there).  The ledger therefore had to be re-based once more (§3.3), and after that the corrected
interface reaches `RowShape @ExtremeTransportData` exactly as the frozen one did.  The unconditional
`r176_extreme_transport : RowShape @ExtremeTransportData` is NOT declared: three Props are open (§5).  Once they are
proved the row is `RProof.extreme_transport := r176_extreme_transport_of_curl_outer_mixed <curl> <outer> <mixed>`
(fixed target name of axiom-policy.json; `RProof.extreme_transport` is declared nowhere in `work/lean` — checked).

Also provided: `r176_extreme_transport_of_rest_uniform` (the row from the corrected non-move port data
`hrest` alone: binders with `hcomp hu hju` and `wind ≠ 0`, `hF` discharged), `r176_est_ledger_weak_uniform_of_weak`
(sanity: the frozen weak interface still gives the ledger through the split), and the SMOOTH-route composition
`r176_est_port_relation_weak_of_curl_outer_ledger (hcurl) (hout : r176s_outer_carriers) (hled : r176s_ledger) :
s176_est_port_relation_weak` + `r176_extreme_transport_of_curl_outer_ledger` (`r176s_est_port_relation_weak_of''` with
`hrec` discharged) — formally valid, but `r176s_ledger` asserts (13)/(12) also at `wind = 0`, so it is not the route to
pursue.

### 3.1 Defect found: the LEDGER's black box `r176l_smooth_black_box` is stated too strongly (rule (4))

Its binders are `n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q a b c hab hac hbc u v hjab huac
hvbc hu' hv' hlt_a hSf y hy` — **no `hcomp` (K3 on `H`), no `habc : {a,b,c} = {e,f,g}`, no `hu hv hju hjv huv`**.  A
prover of the smoothing/owner-map data needs the local picture (`s176_nb_a/b/c` from `ExactTriangleVisitOrders`, which
needs `habc` and `hL.gauss_words`; `hρa hρb` from them; the forced order `r176l_lt_c_of_indep`), and without `habc`
the binders allow `u, v` to be outside crossings retained by `q₀'` with `u = {a,c}`, `v = {b,c}` on the triangle labels
of `j` only — the claimed structure is then false in general.  (The LEDGER's own realisation `r176l_portDataRest_case1`
HAS these hypotheses and merely forgot to pass them into the Prop.)  Not edited (the unit file is frozen for the
assembler); superseded: `r176_outer_carriers_L` and `r176_mixed_bridge` carry the full binder list of
`r176l_portDataRest_case1` (+ `hef' heg' hfg' hcomp`, `habc`, `hu hv hju hjv huv`), and the LEDGER's chain is replayed
against them (§2).  `r176l_smooth_black_box` and `r176l_est_port_relation_weak_uniform_of` remain in the file unused
by the composition.

### 3.2 Defects inherited and superseded (already reported by the units)

* `s176_est_port_relation_weak_of` / `_of'` (Site, frozen): the `hrest` binders lack `hcomp hu hju` (R176_SMOOTH_REPORT
  §4) and the `hrec` binders lack `hcomp hu hju` (R176_HSUCC_REPORT §3.5) — neither can be fed the units' theorems;
  every composition here replays their 5-line bodies instead (`r176h_est_port_relation_weak_of_rest`,
  `r176_est_port_relation_weak_uniform_of_*`, `r176_est_port_relation_weak_of_curl_outer_ledger`).
* `est_PortData.rot/alt₁/alt₂` without `wind ≠ 0` (R176_LEDGER_REPORT §3): handled by §3.3.

### 3.3 The `wind(S) = 0` split (the "RALedgers change" of R176_LEDGER_REPORT §3, made on the draft copies)

`r176_est_row_H_weak_uniform` (line 8035) = `est_row_H` (RALedgers:1514) with `by_cases hwind : CV.wind (geomAt E t
ht.1) (Q ∪ {j}) = 0`: if `0`, `rowTerm_of_mem_Ind` on both sides, `GT_wind_eq` carries the selector, both terms are
`0 * ∏ … = 0` (`zero_mul`); otherwise the body of `est_row_H` verbatim with `hport … q hwind ⟨u, hu, hju.symm, hu'⟩`.
Then `r176_est_row_weak_uniform`, `r176_est_extremeTransportData_weak_uniform`, `r176_est_ledger_weak_uniform` are the
`s176_est_*_weak` replays (byte-identical bodies).  Cost: 13 lines.  At port time the same split goes into `est_row_H`
(or `est_port_relation` is replaced by the corrected Prop `r176l_est_port_relation_uniform`, the strong form with
`wind ≠ 0`, which the LEDGER also states).

## 4. Compile and axioms

Draft (`R176_Assembled.lean`, scratch copy with `#print axioms` appended — the deliverable contains no `#print`):

| declaration | axioms |
|---|---|
| `r176h_succ`, `r176h_hrec_wall_proof`, `r176s_DA_componentCount`, `r176s_knotRestrictIso_i`, `r176s_Sfull_ind`, `r176l_ledgerData_case1` | `propext, Classical.choice, Quot.sound` |
| `r176s_homfly_of_liftBlock_curl`, `r176l_portDataRest_of_uniform` | standard + `SM.lit_homfly` |
| `r176_smoothData_of`, `r176_portDataRest_case1`, `r176_portDataRest_of_uniform`, `r176_est_row_H_weak_uniform`, `r176_est_ledger_weak_uniform`, `r176_est_ledger_weak_uniform_of_weak`, `r176s_homfly_of_liftBlock`, `r176s_portDataRest_of`, `s176_est_ledger_weak` | standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` |
| `r176h_est_port_weak`, `r176h_est_ledger_weak_of_rest`, `r176l_est_port_relation_weak_uniform_of`, `r176_est_port_relation_weak_uniform_of_curl_outer_mixed`, `_of_rest`, `r176_est_port_relation_weak_of_curl_outer_ledger`, `s176_port_weak_of_event'`, `est_port_weak_of_bigon` | standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` + **`sorryAx`** (through the frozen skeleton: `exists_bigonData_of_triangle` and the glue `est_port_weak_of_bigon`, whose proofs in `Skeleton_W1` rest on the 33 `sorry` leaves) |
| **`r176_extreme_transport_of_curl_outer_mixed`**, `r176_extreme_transport_of_rest_uniform`, `r176_extreme_transport_of_curl_outer_ledger` | the previous row + `SM.lit_homfly_descent, SM.ng_finite_word, SM.src_contact` (from `CV.carrierSlotFloor` = thm:carrierfloor) |
| `CV.carrierSlotFloor` (library) | standard + `SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact` — no `sorryAx` |

All six `SM.*` are the registered literature axioms of `work/lean/axiom-policy.json` (`lit:homfly`, `lit:homfly (descent
sentence)`, `lp:lm`, `lp:lm-uniqueness`, `ng:finite-word`, `src:contact`).

**Where the draft's `sorryAx` comes from and where the library theorem replaces it.**  The draft is built on
`Skeleton_W1.lean` (lines 1–1867, 33 `sorry` leaves: the 4 frozen leaves incl. `exists_bigonData_of_triangle` at line
1601/1609 and the 29 `m*_` sub-leaves), NOT on `Moves_Assembled.lean`; the whole moves toolkit is now ported, sorry-free,
as `work/lean/SM/BigonDeletion.lean` (5374 lines; `exists_bigonData_of_triangle` at its line 5064, `exists_rii_deletion`
4999, `est_port_weak`, `est_port_weak_of_bigon`, `fulltwist_coefficient_of_port_weak`, `curl_block_value`,
`two_component_row_of_recordIso`, `s7_rii_witnesses`, `gsc_fulltwist_of_bigon` all present; only the Wave-3 §4 material
`G11_ConfigSw / G11_core_sw / esc_switch_riii_of_chain` is not there — row 176 never uses it).  **Port test done**:
`R176_Port_draft.lean` = the six imports of Site_176 + `import SM.BigonDeletion` + assembled lines 1868–8198 verbatim
→ exit 0, 0 errors, 0 `sorry`, 22 s; `#print axioms` there: `r176h_est_port_weak`, `s176_port_weak_of_event'`,
`r176_est_port_relation_weak_uniform_of_curl_outer_mixed`: standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`;
`r176_extreme_transport_of_curl_outer_mixed`, `_of_curl_outer_ledger`: standard + the six registered axioms —
**no `sorryAx`**.  So the replacement point is exactly "delete lines 1–1867, add `import SM.BigonDeletion`"; no name,
statement or proof of the Site/unit/composition material changes.

## 5. Remaining `sorry` / black boxes — exact list with estimates

The assembled file has NO `sorry` outside the frozen skeleton (§4: all 33 closed in the library).  The row is open in
exactly the following hypotheses of `r176_extreme_transport_of_curl_outer_mixed` (all `def … : Prop`, never asserted):

| # | open Prop (file line) | exact content | estimate | notes |
|---|---|---|---|---|
| 1 | **`r176s_curl_removal`** (SMOOTH, 5007) | `∀ ρ, ρ.componentCount = 1 → ∀ (K : Set ρ.Crossing) (r ∈ K), (∃ w hw, ρ.crossingOf w = r ∧ ((ρ.restrictCrossings K).succ ⟨w, hw⟩).1 = ρ.pair w) → ∀ X X', Nonempty (RecordIso X.record (ρ.restrictCrossings K)) → Nonempty (RecordIso X'.record (ρ.restrictCrossings (K \ {r}))) → homfly X = homfly X'` — record-level R-I (lc:single-crossing: the kink is a block of value one) | ≈ 600–900 lines (`BlockSupply` for `ρ|K`, `curl_block_value` of Statements_FINAL / SM.BigonDeletion for `X`, `SM.blocks.product` for `X'`, the block bijection) | shared with rows 174/110; pure record/polynomial material (library candidate SM side) |
| 2 | **`r176_outer_carriers_L`** (composition, 7618) | in the full event binders of `r176l_portDataRest_case1` (K3 side `t`, empty side `t'`, `hcomp`, labels `a b c` with `{a,b,c} = {e,f,g}`, `j' = {a,b}` selected, `u' = {a,c}`, `v' = {b,c}` retained, `u' <_a j'`, `S_full = r176l_Sf S' u' v'` independent, `y ∈ {lift u', lift v'}`): `Nonempty (r176_OuterDataL …)` = an occurrence `v₀` of `y`, a kink `r`, `retained (r176l_L2) ⊆ retained q₀'`, `retained (r176l_L1) ⊆ retained q₀'`, `r176s_KA ρ v₀ = liftBlock q₀' (retained r176l_L2)`, `r176s_KB ρ v₀ = liftBlock q₀' (retained r176l_L1) ∪ {r}`, `r ∉ liftBlock …`, `r_curl` (the two occurrences of `r` consecutive in `ρ|B`) | ≈ 1.5–2.5k lines | the geometric identification (R176_SMOOTH_REPORT §2.2): `geoSmoothingSuccessor` of `S_full` on the visits of `q₀'` against the record arcs read on the parent (`r176s_arcA_iff_key`, `r176s_crossKeep_KA_iff_key`), the LEDGER's children lemmas (`r176l_owner_Sf_cases`, `r176l_children_case1`, `r176l_lt_c_of_indep` give the owner structure; what remains is the arc ↔ owner bridge and the kink adjacency) |
| 3 | **`r176_mixed_bridge`** (composition, 7656) | same binders + `O : r176_OuterDataL …`: `mixedSignSum (r176s_DA D₊ y) (r176s_DA_i D₊ y O.v₀ O.hv₀) (r176s_DA_j D₊ y O.v₀ O.hv₀) = #(r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry S' (r176l_Sf …) q₀' (r176l_L1 …) (r176l_L2 …))` | ≈ 400–700 lines | `r176l_mixedSignSum_eq_card` (all signs `+1`: `geoPositiveLift_sign`; the smoothing keeps the other crossings — needs the sign clause of `IsOrientedSmoothing`/`smoothDiagram_record`) reduces it to a bijection of the mixed crossings of `D_A` with `r176l_mixedSet`: a crossing is mixed iff its two occurrences lie on different arcs (`r176s_smooth_comp_eq_pair_iff`, `r176s_smooth_comp_eq_self_iff`) iff its two parent visits are owned by different children (via #2's `KA_eq/KB_eq` and `r176l_owner_Sf_cases`) |
| — | the 33 skeleton leaves (`exists_bigonData_of_triangle` etc.) | — | **0** (closed in `SM/BigonDeletion.lean`; port test §4) | replace lines 1–1867 by `import SM.BigonDeletion` |
| — | F-176-1 acceptance | `est_PortData.port : est_port_weak …` + the one call in `est_omega1_eq_of_port` (Site_176_REPORT §4) | 5 lines + field type | RALedgers edit by the U-176 owner |
| — | the `wind = 0` split in the consumer | — | **done here** (`r176_est_row_H_weak_uniform`, 13 lines); ≈ 10 lines to port into `est_row_H` | or replace `est_port_relation` by `r176l_est_port_relation_uniform` |
| — | `r176l_smooth_black_box` binder defect (§3.1) | — | 0 (superseded by #2 + #3) | drop at port time |

Superseded / not needed by the chosen route (kept in the file, no `sorry`): `r176s_outer_carriers` (existential
carriers; #2 implies it up to the coordinates), `r176s_ledger` ((14)/(13)/(12) for existential carriers, proved by the
LEDGER under `wind ≠ 0` for its carriers), `r176s_est_port_relation_weak_of''`, `r176l_smooth_black_box`,
`r176l_est_port_relation_weak_uniform_of`, the frozen `s176_est_port_relation_weak_of` / `_of'`.

## 6. Name-clash scan (`clash_scan_R176.py ../../lean R176_Assembled.lean`)

617 declarations, 617 distinct fully-qualified names (0 internal duplicates).  **251 fully-qualified clashes, every
one at an assembled line ≤ 1857 and every one against `SM/BigonDeletion.lean`** — the frozen skeleton (Statements_FINAL
+ the Wave-1 API, `SM.Link.BigonData.*`, `SM.Link.Record.restrictCrossings_switch`, …) which the pod executor ported
verbatim at 20:20 UTC, after this wave's skeleton was frozen.  They vanish with the §4 replacement (the port test
compiles under `import SM.BigonDeletion` with none of them).  **0 clashes for the 350 declarations of the Site
appendix, the three units and the composition.**  Informational short-name coincidences beyond the skeleton: 3
(`RProof.s176_CornerSite.eIn / eOut / eIn_ne_eOut` vs `SM.Link.BigonData.eIn / eOut / eIn_ne_eOut` and
`SM.PLFront.eIn / eOut`) — different namespaces, no conflict.  `RProof.extreme_transport` (the fixed target name) is
declared nowhere in `work/lean`.

## 7. Port notes — library material for `RProof/ExtremeTransportUnits.lean` once the row closes

`RProof/ExtremeTransportUnits.lean` does not exist yet.  Its content is `R176_Port_draft.lean` (6339 lines: the assembled
file from line 1868 on, under `import SM.Smoothing / SM.MarkedProducts / SM.SingleCrossing / CV.FullTwist /
RProof.GenericTransport / RProof.RALedgers / SM.BigonDeletion`), which already compiles sorry-free.  Suggested
partition and status:

| block (assembled lines) | content | port destination | status |
|---|---|---|---|
| Site §A (1888–2175) `s176_CornerSite` + `det_mul_det_neg`, `same_over_switch₁/₂`, `exists_bigon_switch₁/₂`, `s176_four_le_of_crossing` | the abstract `j`-corner bigon site on any positive diagram | library, shared with row 174's site (Site_176_REPORT §7) | proved |
| Site §B (2177–2471) `s176_PortDataWeak/Rest`, `s176_est_omega1_eq_of_port_weak`, `s176_est_port_relation_weak`, `s176_est_row_H_weak … s176_est_ledger_weak`, `s176_est_extreme_transport_of_weak` | the F-176-1 re-base of `est_*` | folds INTO RALedgers when F-176-1 is accepted (the `est_*` bodies are byte-identical) — then delete | proved |
| Site §C–§F (2473–3661), §G–§H (3663–4143) | carrier-level corner site, event site, `hrec` reduction, the wall bijection `s176_wallΦ`, `s176_hrec_wall(_of_succ)`, `s176_port_weak_of_event'` | library (`ExtremeTransportUnits`, section "site") | proved; `s176_hrec_of_site`, `s176_est_port_relation_weak_of/_of'` superseded (drop or keep as sanity) |
| HSUCC §I–§K (4144–4492) | `r176h_succ`, `r176h_hrec_unswitched`, `r176h_hkey_event`, `r176h_hrec_wall_proof`, `r176h_est_port_weak`, `r176h_est_port_relation_weak_of_rest`, `r176h_est_ledger_weak_of_rest` | library ("wall") | proved, standard axioms up to the port |
| SMOOTH §R1 (4533–4877) | record core: arcs of a self crossing, `r176s_firstReturn_reconnect`, `r176s_smoothRestrictIso/'` | GENERAL record lemmas → `SM/LinkRecordExtras.lean` or `SM/Smoothing.lean` neighbourhood (no row data) | proved |
| SMOOTH §R2 (4879–4969) | `r176s_DA`, `r176s_DA_smooth/componentCount/i/j/ij`, `r176s_knotRestrictIso_i/j` | GENERAL diagram lemmas → `SM/Smoothing.lean` neighbourhood | proved |
| SMOOTH §R3 (4971–5078) | `r176s_homfly_eq_groupedPoly`, `r176s_homfly_of_liftBlock(_curl)`, `r176s_arcA_iff_key`, `r176s_crossKeep_KA_iff_key`; the Prop `r176s_curl_removal` | `CV/GroupedKnot`-adjacent (the lift/liftBlock side); `r176s_curl_removal` → SM side, to be PROVED (#1) | proved except #1 |
| SMOOTH §R4–§R5 (5080–5402) | `r176s_Sfull_ind`, `r176s_third`, `r176s_cgL`, `r176s_OuterData`, `r176s_outer_carriers`, `r176s_ledger`, `r176s_portDataRest_of`, `r176s_est_port_relation_weak_of''` | `ExtremeTransportUnits` ("smoothing", SMOOTH-route) — optional once #2/#3 are chosen | proved modulo its Props |
| LEDGER §L0 (5430–5525) | `r176l_OneDissentShape`, `r176l_uniformOrOneDissent_of_shape`, `r176l_one_le_sign_mul_rot_of_shape`, `r176l_rot_uniform_three`, `r176l_abs_ledger` | GENERAL → `CV/UniformRot.lean` neighbourhood | proved |
| LEDGER §L1 (5526–5600) | `r176l_IsMixed`, `r176l_mixedSignSum_eq` (= `SM.s7h_mixedSignSum_eq`, import it and drop the copy), `r176l_mixedSignSum_eq_card` | `SM/ZeroLink.lean` neighbourhood | proved |
| LEDGER §L2 (5601–5816) | `r176l_Children`, `r176l_mixedSet`, `r176l_selectedPart`, `r176l_retained_decomp`, `r176l_card_retained`, `r176l_SmoothData`, `r176l_ell`, `r176l_portDataRest_of`, `r176l_alt_of_shape`, `r176l_rot_ledger` | `ExtremeTransportUnits` ("ledger interface") | proved |
| LEDGER §L3 (5818–7084) | the labelled-corner geometry: children, corner marks, local signs, shapes, `r176l_rot_add_case1`, `r176l_lt_c_of_indep`, `r176l_ledgerData_case1` | `ExtremeTransportUnits` ("ledger geometry"); the `r176l_decEq` local-instance trick is needed wherever the accepted insertion lemmas are used | proved, standard axioms |
| LEDGER §L4–§L5 (7086–7504) | `r176l_Sf_indep_event`, `r176l_uniform_transport`, `r176l_smooth_black_box` (drop, §3.1), `r176l_portDataRest_case1/_labelled/_of_uniform` (superseded by the `r176_` replays, keep or drop), `r176l_est_port_relation_uniform`, `r176l_est_port_relation_weak_uniform`, `_of_weak`, `_of` | `ExtremeTransportUnits`; the two corrected interface Props are the D-F11 statements to adopt in RALedgers | proved modulo its Prop |
| composition §X1–§X6 (7505–8198) | `r176_OuterDataL`, `r176_outer_carriers_L` (#2), `r176_mixed_bridge` (#3), `r176_smoothData_of`, the replays, `r176_est_port_relation_weak_uniform_of_*`, the `wind = 0` split `r176_est_row_H_weak_uniform … r176_est_ledger_weak_uniform`, `r176_extreme_transport_of_*` | `ExtremeTransportUnits` (the row assembly); the split → RALedgers `est_row_H` | proved modulo #1–#3 |

Port-time edits (mechanical): delete assembled lines 1–1867 and add `import SM.BigonDeletion` (verified, §4); on
F-176-1 acceptance replace `s176_est_*_weak` by the `est_*` names; import `SM.CornerChainUnits` for
`s7h_mixedSignSum_eq` or keep the copy; nothing else.  No `set_option`, no `#print`, no `sorry` in the port draft.

## 8. Files

* `R176_Assembled.lean` — the deliverable (8198 lines).
* `R176_Port_draft.lean` — the port-time form (6339 lines, sorry-free, compiles).
* `R176_compose_part.lean` — the composition section alone (generated; lines 7505–8198 of the assembled file).
* `assemble_R176.py`, `gen_R176_compose.py`, `clash_scan_R176.py`, `clash_scan_R176.json`.
* Unit files and `Site_176.lean` untouched.
