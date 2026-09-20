# W3C_KNOT_REPORT.md — Wave 3c, unit KNOT (`w3ck_`): `esc_MoveData.knot_after_two` / `three_components`

Prover: W3C KNOT unit, 2026-09-15 23:19Z → 23:55Z (bounded window, hard stop 2026-09-16 01:45Z; audit A-177-2).
File: `work/drafts/moves/W3C_KNOT.lean` (12 898 lines = `W3B_Assembled.lean` byte-identical through `end W3BI_REAL`
(line 11846) + 1 047 inserted lines, all `w3ck_`-prefixed inside `section W3CK_KNOT`, lines 11866–12893, + the original
closing lines).  Nothing frozen edited;
no leaf body replaced; nothing under `work/lean` touched.

## 1. Result in one paragraph

Both outer clauses are PROVED at every configuration of the extended interface **in their record-clause forms**:
`w3ck_knot_after_two` (the `K3` side: `D_H^{xy}` is a knot) and `w3ck_three_components_count` (the empty side:
`D_L^{xy}` has three components), on `[propext, Classical.choice, Quot.sound]` only.  The identification clauses
of `three_components` (`twoLambda J = 2Λ`, the bijection of the three components with `A, B, C`) are NOT proved;
they are stated as the black box `w3ck_split_ident` together with SPLITB's `esc_FullSplitData` (one new `sorry`,
`w3ck_split_ident_data`).  Rule-3 finding: the frozen `w3bi_knot_after_two` / `w3bi_three_components` (and the
literal `esc_MoveData` fields) quantify over EVERY relational `IsOrientedSmoothing`; the library identifies the
record only of `smoothDiagram` (`smoothDiagram_record`), so the literal forms are not provable from record-level
reasoning (their truth would need the general record bridge `IsOrientedSmoothing D x D₀ → RecordIso …`, which is
not in the library — LinkMoves.lean:1115 states it only as a clause).  The corrected forms carry record clauses
(§3).  To show the corrected shape is what the ledger needs, the whole `w3bi_` chain is replayed on it
(§4): `w3ck_extreme_selected : RowShape @ExtremeSelectedData`, whose `sorryAx` sources are exactly
`w3ck_split_ident_data` and the site data `w3bi_rii_sites_data` — `w3bi_esc_outer_data` is no longer in the chain.

## 2. Compile and checks

* `cd work/lean && lake env lean ../drafts/moves/W3C_KNOT.lean`: **0 errors**, 41 s; warnings = the pre-existing
  deprecations + 8 `declaration uses sorry` (the 7 pre-existing leaves + `w3ck_split_ident_data` at line 12478).
* `grep -c sorry`: 8 before → **9** after (the one new black box body; no `sorry` string in prose).
* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3C_KNOT.lean`: the five frozen blocks IDENTICAL; the two
  `False` lines (`imports = draft's + SM.BigonDeletion`, `G11_core_sw body starts with sorry`) are the baseline
  values on `W3B_Assembled.lean` (RALedgers import; core proved).  `check_W3_statements.py W3C_KNOT.lean`: 42/42
  skeleton statements byte-identical, none missing.  `head -11846 | cmp`: byte-identical through `end W3BI_REAL` (line 11846); the `w3ck_` block is inserted there and the original closing `end` / `end SM.Link` are retained at the file end.
* `#print axioms` (scratch copy): `w3ck_knot_after_two`, `w3ck_three_components_count`, `w3ck_interlaces_iff_arcs`,
  `w3ck_isSelfCrossing_smooth_iff` = `[propext, Classical.choice, Quot.sound]`; `w3ck_esc_outer_occ_of` = those +
  `lit_homfly`; `w3ck_esc_ledger`, `w3ck_esc_interface_ext_of`, `w3ck_rii_after_smoothing_weak_occ` = registered
  axioms only (`lit_homfly, lp_lm, lp_lm_uniqueness`); `w3ck_extreme_selected` = `w3bi_extreme_selected`'s list
  (with `sorryAx`, sources as in §1).

## 3. The exact shape `w3bi_esc_outer` needs (rule 3)

The ledger (`w3bi_esc_contact_identity`, lines 11685–11692) consumes the two outer clauses ONLY at
* `D_H0, D_L0` = the smoothings provided by the weak (6) clause (`esc_rii_after_smoothing_weak`, realised by
  `smoothDiagram` with `smoothDiagram_record`), and
* `J_H, J_L` = the smoothings of `exists_smoothing_record_visit` (record iso available, dropped as `-`).

Two facts force the corrected shape:
1. **The literal fields are not realisable** (same defect as F-177-1 for (6)): the record of an arbitrary
   `OrientedSmoothingData` is not identified by the library.
2. **A bare `RecordIso` is not enough for the first smoothing**: to read "`y` at the double point of `x_eg`" in the
   smoothed record one must know that the iso carries the crossing of `D_H0` at a double point to the crossing of
   `D_H` at the same double point — `w3h_smooth_record_occ`'s clause.  For the second smoothing only the count of
   `J` matters, so a bare `RecordIso` suffices.

Hence (lines 12298–12345):
```
def w3ck_SmoothRecordOcc (D) (x) (D₀) : Prop :=
  ∃ ι : RecordIso D₀.record (D.record.smooth (D.overVisit x)),
    ∀ v : D₀.Γ.Visit, D.Γ.crossingPoint (ι.Φ v).1.1 = D₀.Γ.crossingPoint v.1
def w3ck_knot_after_two_occ (D_H) (pxH pyH) : Prop :=
  ∀ x_H, crossingPoint x_H = pxH → ∀ D_H0, IsOrientedSmoothing D_H x_H D_H0 → w3ck_SmoothRecordOcc D_H x_H D_H0 →
  ∀ y_H, crossingPoint y_H = pyH → ∀ J_H, IsOrientedSmoothing D_H0 y_H J_H →
    Nonempty (RecordIso J_H.record (D_H0.record.smooth (D_H0.overVisit y_H))) → J_H.componentCount = 1
def w3ck_three_components_occ (D_L) (pxL pyL) (Λ) (fA fB fC) : Prop :=   -- same binders, conclusion
    … → esc_three_components J_L Λ fA fB fC
```
`w3ck_esc_outer_occ` (line 12421) = `w3bi_esc_outer` with these two clauses (same binders, `esc_FullSplitData`
byte-identical).  The weak (6) form must expose the same clause: `w3ck_esc_rii_after_smoothing_weak_occ` (line
12507) = `esc_rii_after_smoothing_weak` with `w3ck_SmoothRecordOcc` in place of `Nonempty (RecordIso …)`; it is
realised verbatim by the existing realiser with `w3h_smooth_record_occ` in place of `smoothDiagram_record`
(`w3ck_rii_after_smoothing_weak_occ`, line 12562, sorry-free).  **Port-time edits implied**: the two frozen Props
`w3bi_knot_after_two` / `w3bi_three_components` and the field `rii_after_smoothing_weak` of `w3bi_esc_MoveDataWeak`
get the record clauses (a Wave-3b skeleton statement edit, like the `w3g_` non-kink fix); `esc_MoveData` in
RALedgers is unaffected since the interface is replayed (D2 / D-RM-5).  Nothing frozen was edited here; the
corrected chain lives next to the old one under `w3ck_`.

## 4. What is PROVED (line numbers of `W3C_KNOT.lean`)

* **K1 (11873–11907) record-level counts**: `w3ck_componentCount_double_mixed` / `_double_self` — from
  `componentCount = 1`, a record clause for `D₀` and one for `J`, and `y` mixed / self in `D₀.record`:
  `J.componentCount = 1` / `= 3` (`Record.componentCount_smooth_of_mixed/_self`, `RecordIso.componentCount_eq`,
  `record_componentCount`; every occurrence of a one-circle record is a self crossing).
* **K2 (11910–12115)**: port of R176_SMOOTH §R1 (`r176s_` → `w3ck_`, byte-identical proofs; lines 4183–4318 of
  R176_SMOOTH.lean, which is a draft, not a library module) up to `w3ck_smooth_comp_eq_pair_iff` /
  `_self_iff`, plus NEW `w3ck_isSelfCrossing_smooth_iff`: on a one-circle record, a retained `w` is a self
  crossing of `ρ^x` iff `w, τw` lie on the same open arc of `x` (`ArcA x w ↔ ArcA x (τw)`).
* **K3 (12121–12190) the bridge**: `w3ck_arcA_iff_between` (record arc of the lift ↔ `geometricCrossingVisitBetween`
  of the parents, via `CV.arcBetween_iff_key`), `w3ck_interlaces_iff_arcs`: `GeometricInterlaces hG.cg (parent v)
  (parent w) ↔ ¬ (ArcA v w ↔ ArcA v (τw))` (via `CV.geometricInterlaces_iff_unique`, `crossing_unique_visit_iff`,
  `crossing_visits_exhaust`, `liftVisit_twin`), `w3ck_liftVisit_fst_of_point` (parent crossing from the double
  point: `liftVisit_fst`, `crossingPoint_liftCrossing`, `crossingPoint_injective_of_geometry`).  This is the
  "bridge record-interlacement ↔ `GeometricInterlaces` for retained crossings of a carrier" that
  `cvtail/U_R177_REPORT.md` item 3 listed as missing — it is ≈ 70 lines, not 300–600, because
  `CV.arcBetween_iff_key` already exists.
* **K4 (12194)** `w3ck_isSelfCrossing_iso`: self/mixed transported along a `RecordIso`.
* **K5 (12202–12284) at a carrier diagram**: `w3ck_isSelfCrossing_smooth_iff_not_interlaces` (the status of `y` in
  `D^x` ↔ `¬ GeometricInterlaces c_x c_y`), `w3ck_knot_after_two_of`, `w3ck_three_components_count_of`.
* **K6 (12293–12410) the configuration**: `w3ck_knot_after_two hn E e f g t ht₀ hef heg hfg hK hQi q₀ :
  w3ck_knot_after_two_occ (carrierDiagram_H q₀) (pt x_ef) (pt x_eg)` from `hK.1 : EdgeAB` (`CompleteLocal` = the
  `K3` edge `x_ef ∼ x_eg`; `CrossingGeometry P : Prop`, so `geomAt` and the lift's `hG'.cg` agree by proof
  irrelevance); `w3ck_three_components_count … : w3ck_three_components_count_occ (carrierDiagram_L q₀') …` from
  `PRE_176_graphs_complementary` (`EmptyLocal` at `t'`, first clause `¬ EdgeAB`) and `P1.xPair_ef_ne_eg`.
  `w3ck_esc_three_components_of` / `w3ck_three_components_occ_of`: `esc_three_components` = count + identification.
* **K7 (12415–12490)**: `w3ck_esc_outer_occ`, the black box `w3ck_split_ident` (§5), `w3ck_esc_outer_occ_of :
  w3ck_split_ident → w3ck_esc_outer_occ` (PROVED), `w3ck_esc_outer_occ_holds`.
* **K8 (12498–12890) the chain**: `w3ck_esc_rii_after_smoothing_weak_occ`, `structure w3ck_esc_MoveDataOcc`,
  `w3ck_esc_interface_ext_occ`, `w3ck_rii_after_smoothing_weak_occ`, `w3ck_esc_interface_ext_of (houter :
  w3ck_esc_outer_occ) (hsites : w3bi_rii_sites)`, `w3ck_esc_contact_identity` / `w3ck_esc_couple` /
  `w3ck_esc_ledger` (byte-faithful copies of the `w3bi_` replay; the ONLY changes are the two consumption lines
  `hmove.knot_after_two … hoccH … hJH_rec` and `hmove.three_components … hoccL … hJL_rec`, the pattern
  `⟨D_H0, D_L0, hsmH, hsmL, hoccH, hoccL, m6f⟩` and keeping the isos of `exists_smoothing_record_visit`),
  `w3ck_extreme_selected : RowShape @ExtremeSelectedData`.

## 5. OPEN — the black box `w3ck_split_ident` (line 12452; body `w3ck_split_ident_data`, line 12478)

Same binders as `w3bi_esc_outer`; conclusion `∃ A B C Z Λ, esc_FullSplitData … A B C Z Λ ∧
w3ck_three_components_ident_occ (carrierDiagram_L q₀') (pt x_ef') (pt x_eg') Λ f_A f_B f_C`, where
`w3ck_three_components_ident_occ` (line 12332) has the record-clause binders of §3 and concludes
`w3ck_IdentData J_L Λ f_A f_B f_C := twoLambda J_L = 2Λ ∧ ∃ σ : Fin 3 ≃ Fin J_L.Γ.c, homfly (knotRestrict (σ 0)) =
f_A ∧ … f_B ∧ … f_C`.  Two parts:
* `esc_FullSplitData` — unit SPLITB (not this unit).
* the identification (ESC §3 (9)–(11)) — this unit's remaining content, NOT reached in the window.  Route: the
  three components of `J_L` are, at the record level, `D_L.record` restricted to the crossings with both
  occurrences on each of the three arcs cut by `x_L, y_L` (the `r176s_smoothRestrictIso` / `r176s_KA` pattern of
  R176_SMOOTH §R1–§R2, applied once to `x_L` and once more on the `A`-component to `y_L` — needs Stack.lean's
  `restrictSmoothIso` / `restrictSmoothDisjointIso` and a restrict-of-restrict lemma); geometrically those three
  crossing sets are `liftBlock` of the retained crossings of `A, B, C` (SPLITB's split), whence
  `r176s_homfly_of_liftBlock` + `r176s_homfly_eq_groupedPoly` give the three polynomials (the central triangle
  `Z` carries no piece: the one-crossing positive piece is an unknot, cor:groupedknot (A)/(B)); `twoLambda = 2Λ`
  from the writhe count (17) with the mixed crossings of `J_L` = the crossings between distinct outer carriers.
  Estimate ≈ 0.4–0.8k lines record-level + the SPLITB geometry it shares.  The `r176s_` material is a DRAFT
  (R176_SMOOTH.lean), not a library module: whatever is used must be ported under the unit's prefix as K2 does.

## 6. Black boxes of other units consumed (unchanged, their `sorry` untouched)

`w3bi_rii_sites_data` (→ `w3bi_site_data_data`, `w3g_bigonData_smooth_arcST/_TS` (false as stated, `hk5`),
`w3bi_bigonData_smooth_arcST/_TS_switch_z`, the three open cases of `w3bi_hrec_general`), `CV.carrierSlotFloor`.
`w3bi_esc_outer_data` is NOT consumed by the `w3ck_` chain.

## 7. Notes / pitfalls

* `set D := CV.carrierDiagram …` inside a proof made `rw` fail and hit a `whnf` heartbeat timeout (the abbrev
  unfolds to `geoPositiveLift`): write the term out and pass the lift's `hG' := CarrierGeometry.ofDiagrammatic
  (hG.diagrammatic hn)`, `hT := CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS` explicitly.
* `GeometricInterlaces (geomAt E t ht.1)` vs `GeometricInterlaces hG'.cg`: not syntactically equal, so `rw` does
  not see them; `exact` does (proof irrelevance of `CrossingGeometry P : Prop`).
* `Sigma` visits: `u.2 ≠ (visitTwin u).2` is proved by `congrArg (fun j => ⟨u.1, j⟩) h.symm` (the two fibres are
  defeq because `visitTwin_crossing` is `rfl`); `heq_of_eq` does not unify.
* `open … in section …` wraps the `section` command and breaks the scope; put the `open` inside the section.
* The copied `w3bi_` proofs need the same section context: `variable {n : ℕ} [NeZero n]` and
  `open RProof CV SM.GeoCarrier SM.Carrier Smoothing`.

## 8. API reconnaissance for the open identification (for the next unit; nothing here is proved)

Record-level route for "the three knot restrictions of `J_L = D_L^{xy}` are `D_L.record` restricted to the three
arc crossing sets", with `ρ := D_L.record` (one circle), `v := overVisit x_L`, `w := ι₀.Φ (overVisit y_L)` a retained
occurrence with `w, τw` both on one arc of `v` (the empty side, `w3ck_isSelfCrossing_smooth_iff`):
* one smoothing (R176_SMOOTH §R1, draft lines 4319–4531, to be ported under the unit's prefix): `r176s_KA ρ x`
  (the crossings with both occurrences on `A`), `r176s_smoothB` (the `A`-component as a block),
  `r176s_smoothRestrictIso : RecordIso ((ρ.smooth x).restrict smoothB) (ρ.restrictCrossings KA)` and the primed
  `B`-versions (via `Record.smoothPairIso`); the knot restrictions of the first smoothing follow the pattern
  `r176s_knotRestrictIso_i` (draft 4613): `Diagram.restrictRecordIso` (LinkDiagramRecord.lean:1454, `RecordIso
  (D.restrict B hB).record (D.record.restrict B)`) ∘ `RecordIso.restrict` ∘ `smoothRestrictIso`.
* the second smoothing on the `A`-component: Stack.lean:915 `Record.restrictSmoothIso v B hv B' hB' hB'' :
  Nonempty (RecordIso ((ρ.smooth v).restrict B') ((ρ.restrict B).smooth ⟨v, hv⟩))` (smoothing then restricting to
  the block `B'` of the smoothed circles = restricting then smoothing), and its companion after line 925 (restriction
  of the smoothing at an EXTERNAL crossing = the old restriction — for the `B`-component untouched by `y`); then
  §R1 applied to the one-circle record `(ρ.smooth v).restrict smoothB ≅ ρ.restrictCrossings KA` at the image of `w`,
  and a restrict-of-restrict identification `(ρ.restrictCrossings K).restrictCrossings K' ≅ ρ.restrictCrossings K''`
  (not found in the library; `CBProducts.lean:1358 restrictCrossings_iso_of_recordIso` transports
  `restrictCrossings` along a `RecordIso` given the crossing-set correspondence `hX`).
* the geometric half (SPLITB's split): the three arc crossing sets are `CV.liftBlock` of `geoCarrierCrossings` of
  `A, B, C` in `Q' ∪ T'` (`CV.crossKeep_liftBlock_iff`, GroupedKnot.lean:213), whence `r176s_homfly_of_liftBlock`
  (draft 4640: a diagram with record `lift.record.restrictCrossings (liftBlock W')` has the `homfly` of the lift of
  the inner carrier) and `r176s_homfly_eq_groupedPoly` (draft 4630) give `homfly (knotRestrict (σ i)) = f_A, f_B,
  f_C`.  The bridge of K3 (`w3ck_arcA_iff_between`, `w3ck_interlaces_iff_arcs`) is the tool for "both occurrences
  on arc `A`" ↔ a geometric position statement on `Γ`.
* `twoLambda J_L = 2Λ`: `twoLambda` = Σ over unordered component pairs of `mixedSignSum` (MarkedProducts.lean:148);
  the mixed crossings of `J_L` are the retained crossings of `D_L` with occurrences on two different arcs; `Λ` is
  fixed by `esc_FullSplitData.writhe` (17) `w = 3 + w_A + w_B + w_C + 2Λ`, so `2Λ = w − 3 − Σ w_i` = the signed count
  of the crossings between distinct outer carriers (`CV.groupedWrithe_eq_card_geoCarrierCrossings`-type lemmas of
  the accepted U-SPLIT material).

Time used: 23:19Z–23:56Z (about 37 min of the 2 h 26 min window; the hard stop was not approached).
