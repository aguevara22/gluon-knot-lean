# W3_BLOCK_REPORT — wave 3 unit BLOCK (prefix `s7k_`; PLAN_FINAL §3.3 bigon (2)-(3); serves U110-K `s7_bigon_law_at`), 2026-09-15

File: `work/drafts/corner/W3_BLOCK.lean` = `W3_Skeleton.lean` (97 lines) + ONE inserted block (lines 37-769, 733 lines;
`diff W3_Skeleton.lean W3_BLOCK.lean` = `36a37,769`, 0 removed lines), placed inside `section VertexEdge` immediately
BEFORE the docstring of `s7_bigon_law_at` (line 770), after the sliding leaf.  No frozen statement, name or docstring
touched; no import added; the two leaf `sorry`s untouched (lines 34, 787).  sha256 `59eb4b37960d376e…`, 830 lines.
Check: `cd work/lean && lake env lean ../drafts/corner/W3_BLOCK.lean` — **0 errors, 0 non-sorry warnings**, exactly 2
`declaration uses sorry` (lines 26 `s7_sliding_law_at`, 778 `s7_bigon_law_at`), 29 s warm.  `grep -c sorry`: 3 before
(skeleton: 2 leaves + 1 header prose) → 3 after (this unit adds NO sorry — no sorried black box, see §3).
Clash scan `grep -rln s7k_ work/lean/SM work/lean/CV work/drafts/corner/*.lean`: only W3_BLOCK.lean.
Axioms (`#print axioms` on a scratch copy, all 36 theorem/def declarations): standard
`[propext, Classical.choice, Quot.sound]` for the record/count/slot material; `+ SM.lp_lm` where `presentations` /
`SM.blocks` enter; `+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` where `cornerHomfly`/`P_eq_homfly` enters
(`s7k_one_newborn_term_zero`: `+ lit_homfly` only) — the plan's policy set; the row assembly's expected list is unaffected.

**Leaf closed: NO** (`s7_bigon_law_at` still `sorry`; this unit was never the closer — it delivers bigon (2)-(3) plus
three further rows in the term shape K sums).  **Nothing believed false; no frozen statement needs a change.**

## 0. What the block renders (PLAN §3.3 bigon (2)-(3), sm-4:496-533, 596-668, 736-769, 785-813, 857-866)

Design decision (load-bearing for K).  Everything is stated on FOUR carriers `q_H, q_L` (full contact carriers on the two
side polygons `P_H, P_L : LabelledTuple n`) and `q₁, q₂` (half contact carriers on the halves `P₁ : LabelledTuple n₁`,
`P₂ : LabelledTuple n₂`), with the geometric outputs of units A/B/C/F/I as HYPOTHESES bundled in three Prop-structures
(`s7k_ContactRowData`, `s7k_InterlacingData`, `s7k_NoninterlacingData`, §H).  The smoothing `D_A` is a PARAMETER with its
record clause `Nonempty (RecordIso D_A.record ((positiveLift q_H).record.smooth v))` (the clause `s7g_cornerHomfly_skein` /
`exists_smoothing_record_visit` return), so K may take G's `D₀` or any other diagram with that record; the skein relation is
transferred to it by `presentations` (`s7k_skein_on`).  The R-II witness is never built here: `s7_switch_value_of_bigon`
(SM.BigonDeletion) is consumed with a `BigonData` on `(positiveLift q_H).switch x` and the record identification of its
reduced record with `(positiveLift q_L).record`.  The R-I step is AVOIDED exactly as WAVE1 §7 / U_S7G §0 recommend: the
curl `y` is a single self-crossing BLOCK of `D_A.knotRestrict 1`'s record, read through `curl_block_value` (value `1`) and
`SM.blocks.writhe_additive` (writhe `+1`), so only the two-component row accounts for it.  The floor `hF` enters ONLY
through `FloorTheoremData.slot_le_of_signed` at `q₁, q₂` (§G); cb:singleton ONLY in `s7k_one_newborn_term_zero` (§M).

| printed (sm-4) | block section / lemmas | status |
|---|---|---|
| 600-606 `P(D_H^{sw}) = F_L` after the R-II deletion | §A `s7k_switch_value` (via `s7_switch_value_of_bigon`) | PROVED, inputs = site + reduced-record iso |
| 596-608 skein at `q`, `F_H = a⁻² F_L + a⁻¹ z F_A` on the given `D_A` | §A `s7k_skein_on` | PROVED |
| eq. s7c:universal-extraction on the actual lifts | §A `s7k_extraction` (`s7_universal_extraction` with `F_H = H⁺_{L_H}`, `F_L = H⁺_{L_L}`, `F_A = P D_A`) | PROVED |
| crossing partition `m_H = m_L + 2` (`X(P₊) ∆ X(P₋) = {x,y}`) | §A `s7k_count_of_site` — FOLLOWS from the site (`reducedRecord_counts` + `crossingCount_eq`), no separate input | PROVED |
| 496-533 `D_A` two components, `w(D_A) = m_H − 1` | §B `s7k_DA_componentCount`, `s7k_DA_writhe` | PROVED |
| eq. s7c:component-polynomial / -data at `ε = 1` (`Q_i = H⁺_{L_i}`, `w_i = m_i`) | §C `s7k_component_value/_writhe/_lift` | PROVED from a record iso |
| 857-866 the curl at `ε = 0` as a block: `Q₁ = H⁺_{L₁}`, `w(D_A∣₁) = m₁ + 1` | §D `s7k_curl_component_value`, `s7k_curl_component_writhe` (+ §I `s7k_single_crossing_writhe`) | PROVED from two `BlockSupply`s + block correspondence |
| 629-632 `k_H = k_L − 2`; 665-670 `k_L + 2ℓ = K`; 758-762 `K − (k_L + 2ℓ) = 2` | §E `s7k_high_slot`, `s7k_interlacing_slot`, `s7k_noninterlacing_slot` (on `D_A`, through `s7h_writhe_two_component`) | PROVED |
| 638-651 / 736-742 `Ω_H − Ω_L = [a^{k_L+2ℓ−2}](Q₁Q₂) − [a^{k_L+2ℓ}](Q₁Q₂)` | §F `s7k_coefficient_difference` (`s7h_extraction_two_component`) | PROVED |
| 655-668 interlacing floor read; 765-769 noninterlacing floor read | §G `s7k_cornerHomfly_z_nonneg` (lp:core `knot_support`), `s7k_interlacing_floor_read` (`s7_corner_product`), `s7k_noninterlacing_floor_read` (`coeffAt_mul_eq_zero_of_lt_floor`) | PROVED |
| **eq. s7c:interlacing-coefficient-result `Ω_H − Ω_L = −ω₁ω₂`** | §H **`s7k_interlacing_row`** | PROVED from the interface |
| **eq. s7c:noninterlacing-extraction, all rows zero `Ω_H − Ω_L = 0`** | §H **`s7k_noninterlacing_row`** | PROVED from the interface |
| "component 1 / component 2" as records (496-533, 800-835) | §K `s7k_knotRestrict_record_iso`, `s7k_component_record_of_gauss`, `s7k_component_iso_of_gauss` | PROVED: reduces B's obligation to abstract Gauss records |
| 602-606 "same complete decorated record as `D_L`" | §L `s7k_crossingImage`, `s7k_mem_crossingImage_iff`, `s7k_restrictCrossings_iso`, `s7k_reducedRecord_iso_of_gauss`, `s7k_reduced_iso_of_gauss` | PROVED: reduces A's obligation to abstract Gauss records |
| 655-663 / 748-757 `R`-identities feeding the rows | §I `s7k_interlacingData_of_patterns`, `s7k_noninterlacingData_of_blocks` (constructors from `s7i_carrierRotationInt_*`, `s7c_signedUniformOrOneDissent_*`) | PROVED |
| 669-676 / 770-776 the TERM with the selector laws | §J `s7k_interlacing_term`, `s7k_noninterlacing_term` (pure ℤ) | PROVED |
| 777-783 one-newborn rows (cb:singleton ENTERS) | §M `s7k_one_newborn_term_zero`: `wind S * cornerProduct S = 0` | PROVED |
| 437-447 contact triangle `wt · c = s₀`, `d = 0`, `|rot| = 1` | §M `s7k_triangle_factor` (`s7c_carrierWeight_triangle` + `corner_values_i`) | PROVED |
| 785-813 different-block alternative `Ω_H = Ω_L = 0` | §M `s7k_different_block_row` | PROVED from `f_H = f_L = f₁f₂` + counts + rotations + patterns |

## 1. Proved (36 theorems/defs + 3 Prop-structures; all inside `section VertexEdge`, sub-`section S7KBlock`)

§A `s7k_switch_value`, `s7k_skein_on`, `s7k_extraction`, `s7k_count_of_site`; §B `s7k_DA_componentCount`, `s7k_DA_writhe`;
§C `s7k_component_value`, `s7k_component_writhe`, `s7k_component_lift`; §D `s7k_curl_component_value`,
`s7k_curl_component_writhe`; §E `s7k_high_slot`, `s7k_interlacing_slot`, `s7k_noninterlacing_slot`;
§F `s7k_coefficient_difference`; §G `s7k_cornerHomfly_z_nonneg`, `s7k_interlacing_floor_read`,
`s7k_noninterlacing_floor_read`; §H `s7k_ContactRowData` (structure), `s7k_InterlacingData` (structure),
`s7k_NoninterlacingData` (structure), **`s7k_interlacing_row`**, **`s7k_noninterlacing_row`**;
§K `s7k_knotRestrict_record_iso`, `s7k_component_record_of_gauss`, `s7k_component_iso_of_gauss`;
§L `s7k_crossingImage` (def), `s7k_mem_crossingImage_iff`, `s7k_restrictCrossings_iso`, `s7k_reducedRecord_iso_of_gauss`,
`s7k_reduced_iso_of_gauss`; §I `s7k_single_crossing_writhe`, `s7k_interlacingData_of_patterns`,
`s7k_noninterlacingData_of_blocks`; §J `s7k_interlacing_term`, `s7k_noninterlacing_term`;
§M `s7k_one_newborn_term_zero`, `s7k_triangle_factor`, `s7k_different_block_row`.

Accepted / ported inputs used: SM.BigonDeletion `BigonData`, `BigonData.reducedRecord`, `BigonData.reducedRecord_counts`,
`s7_switch_value_of_bigon`, `curl_block_value`; `SM.blocks.product`, `SM.blocks.writhe_additive`, `BlockSupply`
(MarkedProducts); `presentations`, `P_eq_homfly`, `P_knot_support` (PolynomialBlock); `positiveLift_componentCount`,
`positiveLift_sign`, `positiveLift_writhe_eq_carrierCrossingCount`, `card_carrierShadow_crossing` (LinkPositiveLift);
`CB.positiveLiftRecordIso`, `CB.gaussRecord`, `CB.cg`, `CB.restrictCrossings_iso_of_recordIso` (CBProducts);
`Diagram.restrictRecordIso`, `Diagram.switchRecordIso`, `Diagram.record_writhe`, `Diagram.record_crossingCount`
(LinkDiagramRecord); `RecordIso.smooth`, `RecordIso.restrict` (LinkRecordExtras), `RecordIso.switch`,
`RecordIso.crossingOf_eq`, `RecordIso.writhe_eq`, `RecordIso.crossingCount_eq` (LinkRecord); the wave-1/2a helpers
`s7g_cornerHomfly_skein`, `s7h_componentCount_of_smooth_iso`, `s7h_writhe_of_smooth_iso`, `s7h_writhe_two_component`,
`s7h_extraction_two_component`, `s7i_carrierRotationInt_interlacing/_noninterlacing`, `s7c_carrierWeight_triangle`,
`s7c_neg_sign_ne_zero`, `s7c_signedUniformOrOneDissent_of_forall/_of_dissent`, `corner_values_i`,
`carrierWeight_eq_zero_of_not_uniform`; the frozen `s7_universal_extraction`, `s7_corner_product`,
`coeffAt_mul_eq_zero_of_lt_floor`, `cornerHomfly_ne_zero`, `FloorTheoremData.slot_le_of_signed`, `CbSingletonData`.

## 2. Unproved — the leaf, and what remains for U110-K/F/B/A (exact estimates)

`s7_bigon_law_at` stays `sorry`.  Composition K still has to write (PLAN §3.3 bigon (1) and (6), and the per-support
instantiation of this block's interface):

1. **`B = (1−ε)J` (U110-F, sm-4:407-480)**: the eligible bijection `T ↔ (T₁, T₂)` and the ineligible cancellation by the
   persistent transport (`s7a_cross` / `s7e_isRotated_of_strictMono` route, W2_S7E §3), the bigon mark map on the
   quotient identifying the two `μ_M` vertices (U_S7B §2.4, "not started"), the `ε = 0` support `T ∪ {x, y}` with the
   contact triangle (`s7k_triangle_factor` reads its factor).  Estimated 1,500-2,200 lines.
2. **The interface fields, per eligible support** (the geometric content of A/B; now REDUCED to abstract Gauss records by
   §K/§L): (a) `s7k_ContactRowData.site` — a `BigonData` on `(positiveLift q_H).switch x` (the triangle builder
   `exists_bigonData_of_triangle` needs the labels, the two crossings, `same_over`, and the printed emptiness of the
   contact disc as `clear`) AND `((gaussRecord X_H).switch w).restrictCrossings K ≅ gaussRecord X_{L_L}`
   (`s7k_reduced_iso_of_gauss`; U110-A's persistent visit order, the `s7d_gaussRecordIso` device); (b)
   `rotation` `R_H = R_L` (`s7i_full_rotation_germ_centre` on the contact carrier's family — U110-A2 excludes the contact
   carrier, W2_S7A2 §4(ii): the family through the wall must be built, est. 400-600 lines); (c) the branch data:
   `comp₁/comp₂` as `((gaussRecord X_H).smooth w).restrict {c} ≅ gaussRecord X_{L_i}` (`s7k_component_iso_of_gauss`;
   U110-B's half visit maps, est. 500-800 lines — no geometry of `D_A`), the `ε = 0` block supplies for
   `s7k_noninterlacingData_of_blocks` (from `product_of_chain`'s family + a one-crossing diagram for the curl block,
   est. 300-500 lines), the corner correspondence `e`/`he` (U_S7B §2.3, est. 400-600 lines) feeding
   `s7k_interlacingData_of_patterns` together with U110-C's live-selector patterns.
3. **The sum (U110-K, sm-4:874-908)**: `C_X1.selector_form` on both sides, the per-support identity
   `wind(S_H) c(S_H) − wind(S_L) c(S_L) = s₀ …` from `s7k_interlacing_term` / `s7k_noninterlacing_term` /
   `s7k_one_newborn_term_zero` / `s7k_different_block_row` with the spectator bookkeeping, `Finset.sum_bij`, the sign
   `(−1)^{|T|+2} = (−1)^{|T|}` and `contactSign = s₀`.  Estimated 400-700 lines.

Total remaining for the bigon leaf: **3,500-5,400 lines**, all geometry/bookkeeping; no skein, record or floor content is
left (this block).  Not attempted here (out of scope, not blocked): everything in 1-3.

## 3. Black boxes — what this unit consumes from other units (rule (3))

No `s7k_` declaration is `sorry`: every consumed output is a HYPOTHESIS, stated exactly as the fields of the three Prop
interfaces (the printed proof's own hypotheses at the contact carrier pair), each with its supplier:

* `s7k_ContactRowData hn hPH hPL hSH hSL qH qL x` — `site : ∃ B : BigonData ((positiveLift q_H).switch x), Nonempty
  (RecordIso B.reducedRecord (positiveLift q_L).record)` [U110-F + U110-A; Gauss-record form `s7k_reduced_iso_of_gauss`];
  `rotation : |rInt q_H| = |rInt q_L|` [U110-I/A2 family through the wall].
* `s7k_InterlacingData … v DA i j` — `record` [G/`exists_smoothing_record_visit`], `ne : i ≠ j` [`s7h_exists_two_components`],
  `comp₁ comp₂` [U110-B; Gauss form `s7k_component_iso_of_gauss`], `rotation : |rInt q_L| = |rInt q₁| + |rInt q₂|`
  [U110-I `s7i_carrierRotationInt_interlacing`, via `s7k_interlacingData_of_patterns`], `pattern₁ pattern₂` [U110-C].
* `s7k_NoninterlacingData … v DA i j` — `record`, `ne`, `curl_value : P (DA.knotRestrict i) = H⁺_{L₁}`,
  `curl_writhe : w(DA∣ᵢ) = m₁ + 1` [both from the block route `s7k_noninterlacingData_of_blocks`: two `BlockSupply`s,
  the curl block `H₀` a positive one-crossing one-circle diagram, block correspondence `eB` with equal values/writhes —
  U110-B/H], `comp₂` [U110-B], `rotation : |rInt q₁| + |rInt q₂| − |rInt q_L| = −1` [U110-I], `pattern₁ pattern₂` [U110-C].
* `s7k_different_block_row`'s `hfH hfL : H⁺_{L_H} = H⁺_{L_L} = H⁺_{L₁} H⁺_{L₂}` [mp:blocks with the two singleton
  newborn blocks, U110-B/H], `hmH hmL` [crossing partition], `hR hRH` [U110-I].
* WALL-LEVEL existence of these data for the eligible supports of `g.sideTuple b t` at a `BigonAt` wall is NOT stated
  (it needs U110-F's eligible-bijection vocabulary, which does not exist yet — U_S7B §2.4); stating it imprecisely
  would violate rule (3), so it is left to F/K with the interfaces above as the target shapes.

## 4. Defects / observations

* None of the printed intermediates used here is false as stated.  Two printed inputs turned out to be REDUNDANT for the
  rows: the crossing partition `m_H = m_L + 2` follows from the R-II site (`s7k_count_of_site`), and the `RIData` curl
  deletion is replaced by the block reading (as WAVE1 §7 recommended) — `s7k_noninterlacing_row` needs only `w(DA∣₁) =
  m₁ + 1` and `P(DA∣₁) = H⁺_{L₁}`, both delivered by `s7k_noninterlacingData_of_blocks`.
* `s7h_writhe_low`'s `hHL : w_H = w_L + 2` is not needed on `D_A`: `s7k_interlacing_slot` / `s7k_noninterlacing_slot` work
  from `w(D_A) = m_H − 1` and the partition directly (`omega`).
* The interface takes `D_A` as a parameter; if K prefers G's existential `D₀`, `s7k_skein_on`'s `presentations` step
  makes the choice irrelevant.

## 5. Mathlib / Lean pitfalls met (v4.34.0-rc2 pin)

1. A `Prop`-valued `structure` cannot carry a data field ("failed to generate projection … field must be a proof"):
   the contact crossing `x` is a PARAMETER of `s7k_ContactRowData`, not a field.
2. `gaussRecord`, `cg`, `positiveLiftRecordIso`, `restrictCrossings_iso_of_recordIso` live in `SM.CB` (CBProducts.lean
   `namespace CB`, `open CB` is file-local): write `CB.…` under the frozen preamble (`open Link Carrier` only).
3. `Finset.prod_subtype` / `Finset.sum_subtype` with the local `Classical.propDecidable` instance: pass the predicate
   explicitly (`(p := fun H => H ≠ H₀)`), the membership proof as `fun H => by simp`, and the function explicitly; then
   `Fintype.prod_equiv e _ _ he` closes the transported product.
4. `RecordIso.crossingOf_eq` gives the image crossing as a `Subtype.mk` of `Finset.map Φ`; after `rw … at h` the
   projection `.1` is only definitionally the mapped finset — restate with `have h' : … := h` before
   `Finset.map_injective`.
5. `omega` handles `|carrierRotationInt …|` and `twoLinking …` as atoms after `unfold cornerSlot; push_cast`, so all slot
   identities are one-liners on the carriers' own vocabulary (no `s7i_*_slot` pure-ℤ lemmas needed).
6. `exact P_eq_homfly _` closes `SM.P (positiveLift …) = cornerHomfly …` only after `unfold cornerHomfly`.

## 6. Notes for the assembler

* Position: the block starts with `/-! ### Unit BLOCK (wave 3, prefix s7k_ …` (line 37) and ends with `end S7KBlock`
  (line 768), inside `section VertexEdge`, immediately before the bigon leaf's docstring; it opens its own
  `section S7KBlock` with `variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]` (closed before the leaf, so the frozen
  statements see no extra variables).  All names `s7k_`-prefixed; one `def` (`s7k_crossingImage`), three structures.
* Consumption by K (interlacing row, per eligible support): `s7k_interlacing_row hF hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁
  hP₂ hS₁ hS₂ q₁ q₂ x hc v hv DA i j hb` with `hc : s7k_ContactRowData … x`, `hb` from
  `s7k_interlacingData_of_patterns`; then `s7k_interlacing_term` with `s7c_carrierWeight_interlacing`.  Noninterlacing:
  `s7k_noninterlacing_row … hb` with `hb` from `s7k_noninterlacingData_of_blocks`, then `s7k_noninterlacing_term`; the
  one-newborn supports by `s7k_one_newborn_term_zero hsing …`; the different-block supports by
  `s7k_different_block_row`; the `ε = 0` triangle factor by `s7k_triangle_factor`.
* Diff summary: `+` 733 lines, `−` 0 lines.  Reproduce: `cp W3_Skeleton.lean W3_BLOCK.lean`, insert the block, `cd
  work/lean && lake env lean ../drafts/corner/W3_BLOCK.lean`.
