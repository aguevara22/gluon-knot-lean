# W3B_REAL_REPORT.md — Wave 3b, unit REAL (the two realisers and the F-177-2 interface replay)

Written 2026-09-15 22:55 UTC / 6:55pm ET by the unit-REAL prover (bounded window, audit A-177-1; hard stop 00:30 UTC).
File: `work/drafts/moves/W3B_REAL.lean` = `W3_A1_Assembled.lean` (7827 lines) + `import RProof.RALedgers` + the new
section `W3BI_REAL` (lines 7825–9004, ≈ 1181 new lines, everything prefixed `w3bi_`).  Nothing under `work/lean`
touched; no frozen statement, name or docstring changed (checks below).

## 0. Result

* `cd work/lean && lake env lean ../drafts/moves/W3B_REAL.lean`: **0 errors**, 33 s.  Warnings: the inherited
  `if_pos/if_neg` deprecations (+2 `dif_pos/dif_neg` in `w3bi_bigon_of_site`, cosmetic) and 15 `declaration uses sorry`
  (10 inherited + 5 of this unit, §3).
* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3B_REAL.lean`: 5/5 frozen blocks IDENTICAL; the checker's
  `imports = draft's + SM.BigonDeletion: False` reflects ONLY the added `import RProof.RALedgers` (needed for
  `esc_switch_riii`, `esc_FullSplitData`, `esc_three_components`, the `esc_` helpers and the ledger; the assembly
  report's namespace-aware clash scan already covered `RALedgers.lean`: 0 clashes).
* `check_W3_statements.py W3B_REAL.lean`: 42/42 skeleton statements byte-identical, no declaration missing.
* `grep -c sorry`: **10 before → 17 after** (17 `sorry` lines = the 10 inherited sub-leaf bodies + 7 of this unit: the 2 black
  boxes `w3bi_esc_outer_data`, `w3bi_site_data_data`, the 2 corrected `w3g` forms, the 3 open orientation cases of
  `w3bi_hrec_general` — §3; the word `sorry` occurs in no docstring).
* **`w3bi_extreme_selected : RowShape @ExtremeSelectedData`** (line 8988) and the fixed-leaf form
  `w3bi_extreme_selected_leaf` (line 8993; the statement of `RProof.extreme_selected`, Statements_FINAL.lean:803,
  byte-for-byte after the name) are PROVED as the replayed composition.  `#print axioms`: `[propext, sorryAx,
  Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word,
  SM.src_contact]` — the registered literature axioms enter through `CV.carrierSlotFloor` (row 155 / SM row 99) and the
  ledger; `sorryAx` enters ONLY through the black boxes of §3.

## 1. Unit (a): the realiser of `esc_MoveData.switch_riii` — PROVED (line 7860)

`w3bi_switch_riii hn hL hGT hR ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi' q₀ q₀' hq₀ hq₀' x_H x_L hxH hxL :
esc_switch_riii (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀) (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') x_H x_L`
for `x_H, x_L` at the double points of `x_ef` and its transport.  Route (as prescribed): `q₀' = GT_carrierEquiv W q₀`
by `esc_contact_unique` (the `hq₀''` block of `esc_contact_identity`), `hcarr := GT_geoCarrierCrossings_eq_of_good
(GT_empty_wall hL hR …) (GT_empty_good ht hQ) q₀`, `htri := esc_contact_owns … hq₀`, `hX := hL.gauss_words t t' ht ht'
hop hs`, `hdet := GT_det_pos_iff_of_sign (hR.sign_eq …)` (as `G11_empty_groupedPoly_eq` :11074), `unfold
CV.carrierDiagram` (the lift is `geoPositiveLift hn (CarrierGeometry.ofDiagrammatic …) _ q₀`, `hT` left to unification as
the accepted code does), the case split `lt_or_gt_of_ne (G11_param_ne …)`: main case `sw := 0` with `w3e_trans_sw_of_alt
_ _ _ ha (w3e_alt_of_completeLocal hGT t ht hef heg hfg hK) 0`; relabelled case `sw := 1` with `heg hef
(G11_isCrossing_comm hfg) (G11_exact_swap hs hX) … (by rw [G11_triangleCrossings_swap]; exact hTq₀)` and the alternation
swapped by the new `w3bi_alt_swap` (line 7843, `decide` after `crossingSign_swap`).  **D3**: the nonzero signs are
`SEL_strandSigns_ne_zero hGT t ht` (X1Rows.lean:1131) — genericity, no added hypothesis.  `hxH`, `hxL` are passed to
`w3e_strong_case_sw` unchanged: `w3e_swPair hef heg hfg 0 = xPair hef`, `w3e_swPair heg hef _ 1 = xPair hef` and
`crossingTransport hs (xPair hef) = xPair ((hs _).mp hef)` are definitional.
`#print axioms`: `[propext, sorryAx, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]` — `sorryAx` only
through `w3e_strong_case_sw` (unit E's three sub-leaves); `w3bi_alt_swap` is standard-axioms only.

## 2. Unit (b): the realiser of (6) in the WEAK form — PROVED modulo the site data (line 8663)

`w3bi_rii_after_smoothing_weak (hsites : w3bi_rii_sites) … x_H x_L hxH hxL : esc_rii_after_smoothing_weak D_H D_L x_H x_L
(crossingPoint (xPair heg)) (crossingPoint (xPair ((hs _).mp heg)))`: the two smoothings are the library's `smoothDiagram D
x (eps D x) (eps_small D x)` (`isOrientedSmoothing_smoothDiagram`; `smoothDiagram_record` for the two record clauses), and
for `y_H, y_L` at the double points of `x_eg` the homfly identity is `esc_rii_after_smoothing_of_bigons`
(BigonDeletion:5313) on the bigon pair and the reduced-record isomorphism of the site box.  No `sorryAx` of its own.

**The site box `w3bi_rii_sites` (Prop, line 8029) is decomposed; all glue PROVED:**

* `w3bi_rii_sites_of (hbig : w3bi_bigon_pair) (hwall : w3bi_wall_data) : w3bi_rii_sites` (line 8628): distinctness of
  `x, y, z` from their double points (`crossingPoint_injective_of_geometry`, `P1.xPair_ef_ne_eg/_ef_ne_fg/_eg_ne_fg`),
  `componentCount = 1` by `rfl`, then `w3bi_hrec_general`.
* **β1 `w3bi_bigon_pair` (Prop, line 8081)**: for `y_H, y_L` on the two `smoothDiagram` outputs at the double points
  of `x_eg`, crossings `z_H, z_L` at the double points of `x_fg` and `BigonData` on the outputs switched at `y` whose
  `{B.y, B.z}` is `{y, z}` in EITHER order (`B.y = y`: the `arcST` orientation; `B.y = z`: `arcTS`; the two sides may
  differ).  **Reduced to the site data β1′** by `w3bi_bigon_pair_of : w3bi_site_data → w3bi_bigon_pair` (line 8271) via
  - `w3bi_SiteData D x py pz` (Prop, line 8167): exactly the inputs of `w3g_bigonData_smooth_arcST/TS` (`g, y, z, hy, hz,
    hsy, htz`, the orientation as a disjunction (D4), `clear`, `clear_vertex`, `hover` (D5)) plus `y ≠ x`, `z ≠ x` and
    which of `y, z` sits at `py` (the consumer's switched double point);
  - `w3bi_bigon_of_site_model` (line 8183), any `SpliceModel`: `y₀, z₀` over `y, z` by `liftCrossing` /
    `origCrossing_liftCrossing`, the consumer's `y_H` is `y₀` or `z₀` by `crossingPoint_origCrossing` + generic
    injectivity, then the four cases: `w3g_bigonData_smooth_arcST` / `_arcTS` when `y` is at `py` (switch at `y₀`), the
    corrected `w3bi_bigonData_smooth_arcST_switch_z` / `_arcTS_switch_z` when `z` is at `py` (switch at `z₀`), consumed
    BY NAME;
  - `w3bi_bigon_of_site` (line 8222): the same on `smoothDiagram … (eps …) (eps_small …)` (`revert; unfold smoothDiagram;
    by_cases h; rw [dif_pos h]` / `[dif_neg h]` — `split_ifs` alone does not rewrite the `dite` inside the binder types);
  - **`w3bi_site_data` (Prop, line 8242) — OPEN black box β1′**: `w3bi_SiteData` for both lifts at `x_H, x_L` with
    `py, pz` the double points of `x_eg, x_fg` (and their transports), same binders as the interface.
* **β2 `w3bi_wall_data` (Prop, line 8498) — PROVED** (`w3bi_wall_data_data := w3bi_wall_data_of w3bi_adjacent_lift_data`,
  standard axioms only): exactly the inputs of `w3h_hrec` (the wall bijection `Ψ` with twins, bits, signs, the cyclic
  order twisted by `swap a₁ a₂ * (swap b₁ b₂ * swap c₁ c₂)`, the six local visits with adjacency, the transported
  crossings).  Pieces (nested `section W3BI_Lift`, W3E variable context):
  - `w3bi_wallEquiv` (line 8300): the `Λ` of `G11_recordIsoData`'s proof (:10852–10920) on its own, `halt`-free — `Λ`
    lifts `visitTransport` through `liftVisitEquiv` (`hcarr`), twins by `liftVisit_twin`/`visitTransport_visitTwin`, bits
    by `overBit_eq_true_iff_parent` + `hdet`, signs `+1` (`geoPositiveLift_sign`), and for ANY `σ` lifting `G11_σP` the
    twisted cyclic clause by `visitBetween_iff_key` + `G11_twisted_key_lt` + `GT_cyc_congr_of_lt` (D6 done);
  - `w3bi_wall_data_lift` (line 8417): the six local lift visits `(liftVisitEquiv).symm ⟨G11_vef, G11_mem_tri_ef …⟩` …,
    `σ` lifts `G11_σP` by `Function.Injective.swap_apply` (×3) with `liftVisit_injective`, twins by
    `gu2_visitTwin_vef/veg/vfg`, double points by `liftVisit_fst` + `crossingPoint_liftCrossing`, the transported
    crossings by generic injectivity on the empty-side lift;
  - `w3bi_adjacent_lift` (Prop, line 8352) PROVED by `w3bi_adjacent_lift_proof` (line 8373): parent adjacency
    (`AdjacentVisits`, R-LOC (2)) ⇒ `nextVisit` adjacency on the one-component lift (`compOf_eq_of_single rfl`,
    `visitBetween_iff_key` = `traversalBetween` of the parents' positions (`Iff.rfl`), `not_visitBetween_nextVisit`,
    `nextVisit_ne_self`, `visitCoord_injOn`, the real trichotomy `w3bi_cycBetween_or`, line 8360);
  - `w3bi_wall_data_of` (line 8546): the site glue (same wall preamble as (a); the adjacencies are
    `hL.adjacent t ht hef heg hfg`, definitionally `AdjacentVisits hG.cg (G11_vef hef) (G11_veg heg)` etc.).
* `w3bi_hrec_general` (line 8589): `w3h_hrec`'s statement with `(B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧ B.z = y₀)` on each
  side (rule (3), §4γ); the `ST/ST` case IS `w3h_hrec` (consumed by name), the three other orientation pairs are open
  (unit H's content: the same proof with `B.y, B.z` renamed — `reducedRecord` depends on `{B.y, B.z}` only).

## 3. Black boxes remaining inside `w3bi_extreme_selected` (exact list)

| box | line | unit | what it is |
|---|---|---|---|
| `w3e_xs_point`, `w3e_liftVisit_σD_sw`, `w3e_recordIsoData_sw` | 7540, 7557, 7583 | E | through `w3e_strong_case_sw` ← `w3bi_switch_riii` |
| `w3bi_esc_outer_data : w3bi_esc_outer` | 8018 | not 177-(4)/(6) | `esc_FullSplitData` (ESC §1, §4–§5) + the `knot_after_two` and `three_components` clauses of `esc_MoveData` (byte-identical field statements as the Props `w3bi_knot_after_two`, `w3bi_three_components`) at a common `Λ`; same binders as the interface |
| `w3bi_site_data_data : w3bi_site_data` | 8267 | G-site + D4/D5 | β1′: `w3bi_SiteData` on both lifts — `g` the third lift strand, `y, z` the lift crossings at the double points of `x_eg, x_fg` (`esc_lift_crossing`), `hy/hz` from the over data at `x` (`gu3_isOver_iff_det_pos`, `G11_carrierSign`), `clear`/`clear_vertex` from `G11_cfg_clear_frontier/vertex`, `hover` from the alternating sign table (D5), the coherent orientation `hys/hzt` from the strand orders (D4), `y ≠ x ≠ z` from the double points |
| `w3g_bigonData_smooth_arcST/TS` | 7683, 7710 | G | consumed by name in `w3bi_bigon_of_site_model` (the `y`-at-`py` cases) |
| `w3bi_bigonData_smooth_arcST_switch_z`, `_arcTS_switch_z` | 8122, 8142 | G (corrected forms, §4β) | consumed by name in `w3bi_bigon_of_site_model` (the `z`-at-`py` cases) |
| `w3h_hrec` | 7795 | H | the `ST/ST` case of `w3bi_hrec_general` |
| `w3bi_hrec_general` (3 of 4 cases) | 8589 | H | the `TS/ST`, `ST/TS`, `TS/TS` orientation pairs |

NOT inside the chain: `w3h_record_core`, `w3h_smooth_record_occ`, `w3h_restrict_switch_deleted` (they feed unit H's
`w3h_hrec`), `w3b_reparam_switch` (optional).  `#print axioms` of the sorry-free members: `w3bi_alt_swap`,
`w3bi_wallEquiv`, `w3bi_wall_data_lift`, `w3bi_wall_data_of`, `w3bi_adjacent_lift_proof`, `w3bi_wall_data_data`,
`w3bi_cycBetween_or` = `[propext, Classical.choice, Quot.sound]`; `w3bi_rii_after_smoothing_weak`,
`w3bi_esc_contact_identity`, `w3bi_esc_couple`, `w3bi_esc_ledger` = the three + `lit_homfly, lp_lm, lp_lm_uniqueness`;
`w3bi_bigon_of_site_model`, `w3bi_bigon_of_site`, `w3bi_bigon_pair_of`, `w3bi_rii_sites_of` carry `sorryAx` only through
the named boxes.

## 4. Rule (3) findings (statements that are not what the consumer needs; nothing frozen was edited)

* **α — the literal `esc_MoveData.rii_after_smoothing` is not realisable** (F-177-1, BigonDeletion's docstring): it
  quantifies over EVERY oriented smoothing.  The interface therefore cannot be "`esc_interface` + `hGT hR`" literally;
  it is `w3bi_esc_interface_ext` (line 7961) with `w3bi_esc_MoveDataWeak` (line 7945): the field
  `rii_after_smoothing_weak : … → esc_rii_after_smoothing_weak D_H D_L x_H x_L pyH pyL`, the three other fields
  byte-identical (`switch_riii`; `knot_after_two`, `three_components` as the Props of lines 7929, 7936).
* **β — `w3g_bigonData_smooth_arcST/TS` switch at `y₀ = {sS D x, g}` (the over strand at `x`)**, the consumer switches
  the crossing at the double point of `x_eg`.  `ExtremeLocal`/`CompleteLocal` is symmetric under the two alternating sign
  orientations, so on the K3 side both `e` over `f` at `x_ef` (then `sS = e`, `y = x_eg`, `w3g_*` apply) and `f` over
  `e` (then `y = x_fg`, `z = x_eg`: the bigon must be read on `(D^x).switch z₀`) occur.  Corrected forms stated as
  `w3bi_bigonData_smooth_arcST_switch_z` / `_arcTS_switch_z` (same statements with `.switch z₀`; true because
  `same_over` holds after switching EITHER of `y, z` by `hover` and no other field sees the over data); both open,
  consumed by `w3bi_bigon_of_site_model`.
* **γ — `w3h_hrec` fixes `B.y = y₀, B.z = z₀` on BOTH sides** = the `arcST` orientation on both sides of the wall.  The
  same-edge visit orders are reversed across the wall (`ExactTriangleVisitOrders`), so mixed pairs occur; `reducedRecord`
  is symmetric in `B.y, B.z`.  Corrected form `w3bi_hrec_general` (§2), `ST/ST` case proved from `w3h_hrec`.
* **δ — D3** needs no hypothesis: `SEL_strandSigns_ne_zero hGT` (the extended interface carries `hGT`).

## 5. Unit (c): the F-177-2 replay — PROVED, `RProof/RALedgers.lean` untouched (D2 / D-RM-5)

* `w3bi_esc_MoveDataWeak` (line 7945), `w3bi_esc_interface_ext` (line 7961): §4α.  `w3bi_esc_outer` (line 7991): the outer box.
* `w3bi_esc_interface_ext_of (houter) (hsites) : w3bi_esc_interface_ext` (line 8696) from (a) + (b) + the outer box;
  `w3bi_esc_interface_ext_holds` (line 8712) with the boxes asserted.
* `w3bi_esc_contact_identity` (line 8722): the accepted `esc_contact_identity` (RALedgers :2088–2272) verbatim except
  `esc_MoveData ↦ w3bi_esc_MoveDataWeak` in the hypothesis and the two smoothing lines: `obtain ⟨D_H0, D_L0, hsmH, hsmL,
  -, -, m6f⟩ := hmove.rii_after_smoothing_weak …` replaces the two `exists_smoothing_record_visit` calls and `m6 := m6f
  y_H0 y_L0 hyH0_pt hyL0_pt` replaces `hmove.rii_after_smoothing …`; everything else (skein at `x`,
  `esc_smoothing_outer`, `knot_after_two`, `three_components`, `esc_coefficient_identity`, the selector branches)
  unchanged.
* `w3bi_esc_couple` (line 8911): the accepted `esc_couple` with the extra hypothesis `(hGT : GenericTableData E e f g δ)`
  passed to the interface.  `w3bi_esc_ledger (hI) (hF) : RowShape @ExtremeSelectedData` (line 8962): the accepted
  `esc_ledger` with the fourth radius `generic_table E e f g h3 h4e h4f h4g hE` and `SEL_genericTableData_mono` at
  `min δL (min δR (min δG δT))` (as `generic_transport` :11157).
* `w3bi_extreme_selected := w3bi_esc_ledger w3bi_esc_interface_ext_holds CV.carrierSlotFloor` (line 8988;
  `CV.carrierSlotFloor` is the PROVED row-155 theorem CarrierFloor.lean:482, from `SM.cf_thm_carrierfloor`).

## 6. Sorry map (`sorry` lines → enclosing declaration; 17 lines, 15 declarations)

* 4095: `w3b_reparam_switch`
* 7553: `w3e_xs_point`
* 7571: `w3e_liftVisit_σD_sw`
* 7604: `w3e_recordIsoData_sw`
* 7700: `w3g_bigonData_smooth_arcST`
* 7727: `w3g_bigonData_smooth_arcTS`
* 7758: `w3h_record_core`
* 7771: `w3h_smooth_record_occ`
* 7780: `w3h_restrict_switch_deleted`
* 7821: `w3h_hrec`
* 8019: `w3bi_esc_outer_data`
* 8139: `w3bi_bigonData_smooth_arcST_switch_z`
* 8159: `w3bi_bigonData_smooth_arcTS_switch_z`
* 8268: `w3bi_site_data_data`
* 8621: `w3bi_hrec_general`
* 8622: `w3bi_hrec_general`
* 8623: `w3bi_hrec_general`

## 7. Notes for the assembler

* Consume by name: `w3bi_switch_riii` (a), `w3bi_rii_after_smoothing_weak` (b), `w3bi_esc_interface_ext_of`,
  `w3bi_esc_ledger`, `w3bi_extreme_selected`.  To close row 177 the assembler needs: unit E's three sub-leaves;
  `w3bi_site_data` (β1′, the D4/D5 site data — the last realiser obligation of this unit, not reached in the window);
  units G's `w3g_*` AND the two `switch_z` forms; unit H's `w3h_hrec` in the general orientation form (the three open
  cases of `w3bi_hrec_general`); the outer data `w3bi_esc_outer` (not part of Wave 3b's units — flag to the lane).
* The (6) smoothings are pinned to `smoothDiagram D x (eps D x) (eps_small D x)`; β1′ is stated at that radius (the
  glue never uses the value; generalise over `ε` if unit G needs another `SmallEps`).
* `w3bi_wall_data_lift` / `w3bi_wallEquiv` (nested `section W3BI_Lift`, W3E variable context) are reusable for any
  two-lift wall record argument (`G11_recordIsoData` minus the core's `Ψ`).
* Compile time unchanged (≈ 33 s); the `#print axioms` scratch is `W3B_REAL_Axioms.lean` in the unit's scratchpad.

## 8. β1′ (`w3bi_site_data`) — the decomposition for the next wave (assessed, not attempted: ≈ 0.6–1k lines)

At a configuration, with `D := geoPositiveLift` (after `unfold CV.carrierDiagram`), `x := x_H` at the double point of
`x_ef`, and the extracted configuration `C := w3e_configOfSw …` (labels `m = G11_mE`, `p = G11_pE`, `q = G11_qE` with
`hmp hmq hpq : IsCrossing C.X {m,p} / {m,q} / {p,q}`, `x = {m,p}`, `y = {m,q}` at the double point of `x_eg`, `z = {p,q}`
at the double point of `x_fg`):

1. **`y, z` and `y ≠ x ≠ z`**: `esc_lift_crossing … (xPair heg) (hTq₀ hyT)` / `(xPair hfg)`; distinctness from the
   double points (`P1.xPair_*_ne_*`, as in `w3bi_rii_sites_of`).  ≈ 20 lines.
2. **`g`, `hy`, `hz`, `hgs`, `hgt`**: the lift strands are `(⟨0, m⟩ ⟨0, p⟩ ⟨0, q⟩ : (Shadow.single C.comp).Strand)`
   (pitfall §5 of the skeleton report: not `⟨0, i⟩ : π.M₀.Γ.Strand`); `x.val = {⟨0,m⟩, ⟨0,p⟩}` etc. need the
   identification of the lift crossings at the three double points with `xPair hmp / hmq / hpq` of `C.X` — this is
   `w3e_xs_point`'s content (`gu3_crossingPoint_symm` + `G11_carrierEdge_crossingPoint` :8976, unit E, still open) plus
   `Shadow.Generic.crossingPoint_injective`.  Then `sS D x ∈ {⟨0,m⟩, ⟨0,p⟩}` (`overStrand_mem`), and the case split
   `sS = ⟨0,m⟩` (`e` over `f`: `g := ⟨0,q⟩`, `y = {sS, g}`, `z = {tS, g}`, `y` at `py`) / `sS = ⟨0,p⟩` (`f` over `e`: the roles
   of `y, z` swap, `y` at `pz` — the second disjunct of `w3bi_SiteData`).  ≈ 150 lines.
3. **`clear`, `clear_vertex`**: from `C.clear_frontier` / `C.clear_vertex` (fields of `G11_ConfigSw`, stated on
   `C.X`'s edge segments and vertices with the three crossing points of `C.X`): `D.Γ.seg ⟨0,h⟩ = edgeSegment C.X h` and
   the vertices `(D.Γ.comp 0).P a` are `C.X`'s vertices (both by `rfl`/one lemma on `Shadow.single`), the crossing
   points by item 2.  ≈ 80 lines.
4. **`hover` (D5)**: `D.overStrand y = g ↔ D.overStrand z ≠ g` from the alternating triple `IsAlternating (strandSign
   C.X m p) (strandSign C.X m q) (strandSign C.X p q)` (`G11_carrierSign` ×3 carries `w3e_alt_of_completeLocal`'s
   parent triple to `C.X`; the copy's `gu3_isOver_iff_det_pos` reads the positive lift's over strand as the det sign):
   `q` over `m` at `y` ⟺ `det(m,q) < 0` ⟺ `det(m,p) > 0` ⟺ `det(p,q) > 0` ⟺ `p` over `q` at `z`, with `sign(m,q) =
   −sign(m,p)`, `sign(p,q) = sign(m,p)`.  ≈ 60 lines.
5. **the coherent orientation (D4)**: `(param y < τs ∧ τt < param z) ∨ (τs < param y ∧ param z < τt)` on the strands
   `s = sS`, `t = tS`.  `C.order` fixes `x` before `y` on `m`; the position of `z` relative to `x` on `p` and the
   over/under choice at `x` are NOT fixed by the configuration alone — the claim is that the alternating sign table
   puts the triangle's corner at `x` in the cone `(s⁻, t⁺)` or `(s⁺, t⁻)`, i.e. `y ∈ s⁻ ↔ z ∈ t⁺`.  This is a
   determinant/half-plane computation on `C.X`'s three edges (the direction of `q` relative to the corner at `x`
   determines on which half-edges of `m, p` its two crossings lie; the alternation of `det(m,p), det(m,q), det(p,q)`
   is exactly the statement that `q` crosses `m⁺`/`p⁻` or `m⁻`/`p⁺`) — the riskiest item (the skeleton's D4), ≈ 200–400
   lines with the affine toolkit (`gu2_mem_segment_*`, `gu4_det_*`).  If it FAILS for some sign pattern, the printed
   proof's bigon does not exist there and row 177 needs a different (6) argument for that pattern.

Everything above is in the W3E variable context (`hn hG hG' hs hT hT' q q'`, `hef … hcfg hX htri hord sw hsw`) and can
be stated as a lift-level theorem `w3bi_site_data_lift … : w3bi_SiteData (geoPositiveLift hn hG hT q) x
(crossingPoint (xPair hceg)) (crossingPoint (xPair hcfg))` with the same site glue as `w3bi_wall_data_of` (the relabelled
case `sw = 1` swaps `f ↔ g`, so `py, pz` swap: state the lift-level theorem for both `sw` or apply it twice).

## 9. Timeline

22:01 UTC start; 22:20 (a) + (c) compiled; 22:27 the (6) decomposition (β1/β2/`w3bi_hrec_general`); 22:39 β2 reduced
to adjacency; 22:43 β2 PROVED; 22:51 β1 reduced to β1′ (consuming `w3g_*`/`switch_z` by name); 22:55 final compile
(0 errors), checks, this report.  Hard stop 00:30 UTC not needed.
