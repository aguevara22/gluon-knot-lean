# W4_ASSEMBLY_REPORT — corner wave 4 (row 110 `thm:C-S7`) MERGE, 2026-09-19 08:20 UTC / 4:20am ET (under D-AUTH-20260919, no bound)

File: **`work/drafts/corner/W4_Assembled.lean`** (19,974 lines, sha256
`9c0ec3b7a8b631a8815a4bb0cc8e7cd1c4354559aa568e08496c1dad1b6bcaca`) = `W3_Assembled.lean` (8,958 lines, `109050d9…`) + the
eight wave-4 unit blocks (S3G `s7g_`, S1P `s7u_`, FB1 `s7fa_`, FB2 `s7fb_`, FB3 `s7fc_`, SITEC `s7sc_`, SITEH `s7sh_`, B3 `s7o_`,
10,247 lines, 977 declarations) + the assembly glue `w4_` (17 declarations, 407 lines incl. the S3' closure).
**Compile** (`cd work/lean && lake env lean ../drafts/corner/W4_Assembled.lean`, 34 s): **0 errors, 0 warnings other than
exactly 5 `declaration uses sorry`** — lines 4437 `s7q_box_ret` (false as stated, superseded), 18053 `s7z_F_exists` (superseded),
18494 `s7z_returned_of_FSector` (superseded), **19857 `w4_box_returnedRows` (Prop B2', the ONE live black box)**, 19922
`s7_bigon_law_at` (the bigon leaf, waits on B2').  `grep -c sorry` = 16 = 5 bodies + 11 prose mentions.

## 0. In one paragraph

**The SLIDING leaf `s7_sliding_law_at` is CLOSED**: `#print axioms` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly,
SM.lp_lm, SM.lp_lm_uniqueness]` — no `sorryAx`, registered axioms only.  S1P's corrected first-return box S1' (`s7u_box_ret'`,
standard axioms) and S3G's carriers box on RET's two transports (`s7g_box_carriers'`, standard axioms) together give S1P's
restated Prop S3' `s7u_SlidingCarriers'`: the assembler discharged S1P's black box `s7u_box_carriers'` from `s7g_box_carriers'`
by the visit dichotomy `s7e_visit_of_fst` (109 lines of glue, §3), and the leaf's body is S1P's composition
`s7u_sliding_law_at_of hn g h h₁ h₂ (s7u_box_carriers' hn g h h₁ h₂)`.  **The BIGON leaf is NOT closed** but its remaining input
is now exactly ONE Prop: with F's three boxes (FB1, FB2, FB3), SITE's two boxes (SITEC), SITE's record identification
(SITEH) and K's box B3 (B3) all proved, K's F-ALIGNED route (`s7z_bigon_law_at_of_residual`, W3_K_REPORT §4(a)) is built in
`section W4Bigon`: F's sorry-free `s7f_exists_law_residual`, the eligible bijection `w4_eligibleEquiv`, B3's one-newborn rows read
in F's vocabulary (`w4_oneNewborn_rows`) and the returned rows **`w4_BigonReturnedRows` (B2', black box `w4_box_returnedRows`)**
give the frozen leaf statement (`w4_s7_bigon_law_at_of`, sorry-free).  K's own boxes B1 `s7z_F_exists` and B2
`s7z_returned_of_FSector` are superseded by this route (no F→K shape bridge is needed) and stay sorried off every proved
path.  **`thm_C_S7` still carries `sorryAx`, through exactly one source: the bigon leaf's own `sorry` body**; the leaf closes as
`w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` once wave 5 proves B2' (§5).  Not port-ready
(§7).

## 1. Task (1): unit diffs against `W3_Assembled.lean` — all clean

`diff W3_Assembled.lean W4_<U>.lean` hunks (verified 07:50Z): pure insertions plus `sorry`-body replacements; the deleted side of
every diff is exactly the replaced `  sorry` lines; the five frozen declarations and every other existing statement/name/docstring
byte-identical in all eight files.

| unit | prefix | hunks (W3 anchors) | block lines in unit file | anchor | body replaced |
|---|---|---|---|---|---|
| S3G | `s7g_` | `4507a4508,7644` + `4545c7682` | 4508-7644 (3,137; 162 decls) | before `s7q_box_carriers` docstring (in `section S7QBoxes`) | `s7q_box_carriers` → `exact s7g_box_carriers_literal hn g h h₁ h₂` |
| S1P | `s7u_` | `4840a4841,5238` | 4841-5238 (398; 10 decls, one `sorry`: `s7u_box_carriers'`) | before `s7_sliding_law_at` docstring | none (new black box S3') |
| FB1 | `s7fa_` | `5362a5363,5697` + `5379c5714` | 5363-5697 (335; 6) | before `s7f_exists_bigonSplit` docstring | `s7f_exists_bigonSplit` |
| FB2 | `s7fb_` | `5380a5381,9400` + `5405c9425` | 5381-9400 (4,020; 204) | before `s7f_exists_twoNewbornTerm` docstring | `s7f_exists_twoNewbornTerm` |
| FB3 | `s7fc_` | `5716a5717,6559` + `5729c6572,6573` | 5717-6559 (843; 56) | before `s7f_exists_ineligible_transport` docstring | `s7f_exists_ineligible_transport` (2-line body) |
| SITEC | `s7sc_` | `6959a6960,7174` + `6981c7196,7246` + `7010a7276,7603` + `7023c7616,7629` | 6960-7174 (215), 7276-7603 (328) | before `s7s_clear_local` / `s7s_wallTriangleData_of_bigon` docstrings | both SITE boxes (51- and 14-line bodies) |
| SITEH | `s7sh_` | `8615a8616,9036` | 8616-9036 (421; 23) | before `s7z_returned_of_FSector` docstring (in `section S7ZBigon`) | none (proves SITE's stated Prop `s7s_hrec_prop`) |
| B3 | `s7o_` | `8636a8637,9485` + `8642c9491` | 8637-9485 (849; 45) | before `s7z_oneNewborn_exists` docstring | `s7z_oneNewborn_exists` → `exact s7o_oneNewborn_exists hsing hn h` |

Every block is a balanced set of `section … end` groups inside `section VertexEdge`; no unit added an import, a top-level
`variable`, or an `open` at the `VertexEdge` level; every top-level name carries its unit's prefix (the unprefixed ones live in
`namespace s7g_Delete` / `namespace s7fb_BigonTransport`).

## 2. Task (2): layout of `W4_Assembled.lean` (dependency order; producers before consumers)

The merge applies the sixteen hunks of §1 in DESCENDING order of their W3 anchor (`<scratchpad>/w4/assemble.py`), then the glue
by unique-anchor string matches (`assemble2.py`); `diff W3_Assembled.lean W4_Assembled.lean` has 18 hunks, deleting only the six
W3 header lines and eight `  sorry` lines.

| W4 lines | content |
|---|---|
| 1-6 | assembly header (prose, `--` comments) |
| 7-4507 | W3 verbatim: imports, `namespace SM`, SPLIT, RET, ROT up to the docstring of `s7q_box_carriers` |
| 4508-7644 | **S3G** block verbatim (`s7g_box_carriers'` at 7229, `s7g_box_carriers_literal` at 7549), then ROT's `s7q_box_carriers` with S3G's body (7682) |
| 7645-7977 | W3 verbatim (rest of `S7QBoxes`, `section W3Sliding` 7826-7976) |
| 7978-8302, 8344-8351, 8353-8484 | **S1P** block verbatim (`section S7UTransport` 7998-8088, `section S7UBoxes` 8090-8483: `s7u_box_ret'` 8163, `s7u_SlidingCarriers'` 8250, glue `s7u_box_rows'_of`, `s7u_sliding_law_at_of` 8465) |
| **8303-8343** | **`w4_` sliding glue** `section W4SlidingNoTransport` (`w4_B_no_transport'_vl` 8316), inside S1P's `section S7UBoxes` immediately before the S3' box |
| **8345-8415** | **`s7u_box_carriers'`** (8352) with the assembler's docstring ("DISCHARGED at assembly (wave 4) from unit S3G's `s7g_box_carriers'`") and its 63-line proof (§3) |
| 8485-8496 | W3 skeleton: `s7_sliding_law_at` (8488), body **`exact s7u_sliding_law_at_of hn g h h₁ h₂ (s7u_box_carriers' hn g h h₁ h₂)`** (8496) |
| 8499-9006 | W3 verbatim: F's `S7FBigonSides`, `S7FSectors`, `S7FSplit`, `S7FDecompositions`, `S7FTriangle`, `section S7FSectorSplit` header |
| 9007-9341 | **FB1** block verbatim, then `s7f_exists_bigonSplit` with FB1's body (9358) |
| 9359-13382 | **FB2** block (verbatim + four `set_option linter.unusedSectionVars false in` lines, §8), then `s7f_exists_twoNewbornTerm` with FB2's body (13408) |
| 13409-13719 | W3 verbatim (`S7FSplitOf`, `section S7FPersistent` up to the docstring of box 3) |
| 13720-14562 | **FB3** block verbatim, then `s7f_exists_ineligible_transport` with FB3's body (14575-14576); `s7f_exists_law_residual` 14780 (now sorry-free) |
| 14577-15806 | W3 verbatim (`S7FOneNewborn`, `S7FResidual`, SITE through `S7SiteBlocks`, `section S7SiteWall` header) |
| 15807-16021, 16123-16450 | **SITEC** blocks verbatim; `s7s_clear_local` body 16043-16093, `s7s_wallTriangleData_of_bigon` body 16463-16476; `s7s_siteData_of_wall` 16114 (now sorry-free) |
| 16477-18068 | W3 verbatim: BLOCK, J, K §A-D, K's box `s7z_F_exists` (18053, sorried, superseded) |
| 18069-18489 | **SITEH** block verbatim (`s7sh_hrec_prop_side` 18460-ff), then `s7z_returned_of_FSector` (18494, sorried, superseded) |
| 18511-19359 | **B3** block verbatim, then `s7z_oneNewborn_exists` with B3's body (19365) |
| 19366-19619 | W3 verbatim: K §F (`s7z_bigon_law_at_of_residual` 19503-ff), `section W3Bigon` 19530-19619 |
| **19621-19912** | **`w4_` bigon glue `section W4Bigon`** (§4): `w4_EligDec` 19646, `w4_liftEquiv` 19668, `w4_eligibleEquiv` 19701, `w4_ReturnedRow` 19748 (**Prop B2' at `t`**), `w4_sum_one_eq` 19770, `w4_sum_ret_eq` 19793, `w4_residualData` 19812, `w4_BigonReturnedRows` 19851 (**Prop B2'**), `w4_box_returnedRows` 19857 (**black box**), `w4_oneNewborn_rows` 19863, `w4_s7_bigon_law_at_of` 19887 |
| 19914-19931 | W3 skeleton: `s7_bigon_law_at` (19922), body `sorry` (19931) |
| 19932-19974 | W3 skeleton verbatim (`end VertexEdge`, `thm_C_S7_of` 19940, `thm_C_S7_of_floor` 19965, `thm_C_S7` 19970, `end`, `end SM`) — the last 43 lines byte-identical to `W3_Skeleton.lean` |

**Renames: none needed** (disjoint prefixes; `python3 tools/clash_scan.py W4_Assembled.lean`: `duplicates_in_assembled: []`,
`full_name_clashes: {}` against 702 library files / 23,890 declarations, 1,028 new declarations; 34 short-name coincidences, all in
DIFFERENT namespaces: the pre-existing RET `s7r_SlidingTransport'.*` / U110-B `s7b_SlidingTransport.*` pairs, FB2's
`s7fb_BigonTransport.*` vs `s7b_SlidingTransport.*` / `sftd_LoopTransport.componentEquiv`, `s7g_Delete.pred_succ` vs two
library `pred_succ`).  **De-duplication: none applied** — the content duplicates are kept under their own names, to be resolved
at port (§8): `s7u_CarrierData'` (S1P) ≡ `s7g_CarrierData'` (S3G) (identical bodies; the S3' closure passes one for the other by
`exact`, i.e. by definitional unfolding); `s7o_side_of_r`/`s7o_sideData`/`s7o_persistent_of_ne` (B3) ≡
`s7fa_side_of_r`/`s7fa_sideData`/`s7fa_not_affected_of_ne` (FB1); K's `s7z_side`/`s7z_x`/`s7z_y`/`s7z_dirSign` ≡ F's
`s7f_side`/`s7f_x`/`s7f_y`/`s7f_dirSign` (W3, definitional; the glue relies on the definitional identity, §4).

### Black boxes connected / not connected

| box (unit) | producer | connected |
|---|---|---|
| `s7q_box_carriers` (ROT, S3 as stated) | S3G's `s7g_box_carriers_literal` | **YES** (S3G's own body replacement; `w3_SlidingCarriers_of_box` sorry-free, standard axioms) |
| `s7u_box_carriers'` (S1P, **S3'**) | S3G's `s7g_box_carriers'` (the box at the specific visits, both transports) | **YES — at assembly** (§3; standard axioms) |
| `s7q_box_ret` (ROT, S1) | none — FALSE as stated (W3_RET_REPORT §2); replaced by S1P's `s7u_box_ret'` (proved) | NO; sorried, off every proved path; drop at port |
| `s7f_exists_bigonSplit` / `_twoNewbornTerm` / `_ineligible_transport` (F) | FB1 / FB2 / FB3 | **YES** (their own body replacements); `s7f_exists_law_residual` sorry-free |
| `s7s_clear_local`, `s7s_wallTriangleData_of_bigon` (SITE) | SITEC | **YES**; `s7s_siteData_of_wall` sorry-free (standard axioms) |
| `s7s_hrec_prop` (SITE's stated Prop, a `def`) | SITEH `s7sh_hrec_prop_side` / `_carrier` | proved in the applied form (a consumer of wave 5) |
| `s7z_oneNewborn_exists` (K, B3) | B3 | **YES**; `w3_BigonOneNewborn_of_box` sorry-free; consumed by `w4_oneNewborn_rows` |
| `s7z_F_exists` (K, B1) | none needed: the F-aligned route consumes F's `s7f_exists_law_residual` directly | superseded; sorried, off every proved path; drop at port |
| `s7z_returned_of_FSector` (K, B2) | none: restated in F's vocabulary as **B2' `w4_BigonReturnedRows`** (black box `w4_box_returnedRows`) | superseded; sorried, off every proved path; drop at port |

## 3. Task (3): SLIDING — closed

**Do S1' and S3G's geometry give `w3_SlidingCarriers` in its restated form (S3')?  YES.**  S3G proved two things: the frozen
box `s7q_box_carriers` AS STATED (its leg-`M` clause vacuous — no `s7b_SlidingTransport` exists there, `s7g_B_no_transport_vl` /
`s7g_B_no_transport_va`), and, for the leaf, **`s7g_box_carriers'`** (W4 line 7229): the box on RET's two transports —
`s7b_SlidingTransport` at `s7e_vl hc` on the side whose contact crossing is `{a, M − 1}`, `s7r_SlidingTransport'` at `s7e_va hc`
on the side carrying `{a, M}` — with `first = !s7e_leg g M a`, `τ = turn g.center M`, the per-carrier data as `s7q_CarrierData`
resp. S3G's `s7g_CarrierData'`.  S1P's S3' `s7u_SlidingCarriers'` (8250) is the same statement with the leg case split made
explicit and the transports quantified at an ARBITRARY pivot `v` with `v.1 = x∓`.  The gap is exactly the pivot: by
`s7e_visit_of_fst` such a `v` is `s7e_va hc` or `s7e_vl hc`; the two cases S3G's box covers are read off directly, the two it does
not cover are EMPTY:

* leg-`(M − 1)` side, `s7b_SlidingTransport` at `v_a`: S3G's `s7g_A_no_transport_va` (cheap: `f v_a = μ_M` is an image mark);
* leg-`M` side, `s7r_SlidingTransport'` at `v_ℓ`: **new lemma `w4_B_no_transport'_vl`** (8316, 26 lines): `ι (inr (inl 0)) =
  μ_M` (`secondHalfIndex_zero`), `nextMark μ_M = v_ℓ` (`s7r_nextMark_M`) and `v_ℓ = ι (inl (inl 0))` is an image mark at the first
  step, so `ret.step` forces `k = 1` and `ι (inl (inl 0)) = ι (inr (ρ₂ (inl 0)))`, against `ret.inj` (the primed twin of S3G's
  `s7g_B_no_transport_vl`; the injectivity is the `inj` field of `s7b_ReturnTransport`, so no copy of `s7r_slidingMark'_injective`
  at `v_ℓ` was needed).

The closure of `s7u_box_carriers'` (8352-8415, 63 lines): `obtain` S3G's box and `s7a2_exists_intervalLocal` (for `hη`, `hloc`),
`δ := min`, then per side and leg (`cases` on `s7e_leg g M a` through the two implications of S3'): `hc` from `s7e_hxm`/`s7e_hxp`
rewritten by the leg, the visit dichotomy with `v.1.val = {a, contactLeg _ M}` by `simp only [s7e_xm_val, hl]` (resp. `s7e_xp_val`,
`Bool.not_false`/`Bool.not_true`), `subst`, and either S3G's clause (`hAm hcm hT`, …) or the vacuity lemma with `s7e_hw hn g hloc
t ht₂ b` and `s7r_huniq`/`s7r_huniq'`.  The `s7g_CarrierData'` ↔ `s7u_CarrierData'` identification is by `exact` (identical
definitions).  **Axioms: `s7u_box_carriers'` = `[propext, Classical.choice, Quot.sound]`** (S3' PROVED on standard axioms, like
S1' and S3G's box).  Compiled on the first probe (`<scratchpad>/w4/pfx/ProbeA.lean` against a prefix olean, 14 s), then in place.

**The leaf** (8488-8496): the frozen docstring and statement byte-identical (`tools/stmt_check.py --base W3_Skeleton.lean`
5/5 PASS); body `exact s7u_sliding_law_at_of hn g h h₁ h₂ (s7u_box_carriers' hn g h h₁ h₂)` — S1P's glue
(`s7u_box_rows'_of` from S1' + `s7q_box_order` (S2, W3) + S3'; `s7e_sliding_law_at_of_contact` ← `s7q_box_split` (SPLIT, W3) +
`s7q_hterm_of_rows` + `s7e_contactSector_of_pivotSplit`).  This IS the `w3_s7_sliding_law_at_of₂`-style two-Prop composition on
the RESTATED Props (S1' proved inside `s7u_box_rows'_of`, S3' the argument); the frozen `w3_s7_sliding_law_at_of₂ hret hcar`
itself is not used because its `hret : w3_SlidingRet` is the false Prop S1 (W3_RET_REPORT §2).
**`#print axioms s7_sliding_law_at` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`.**
Consequently `thm_C_S7_of`, `thm_C_S7_of_floor`, `thm_C_S7` carry `sorryAx` through the BIGON leaf only.

## 4. Task (4): BIGON — wired on K's F-aligned route; ONE Prop remains

Wiring done by the merge itself: F's three boxes closed ⇒ `s7f_exists_law_residual` (14780) sorry-free (§6); SITE's two boxes
closed ⇒ `s7s_siteData_of_wall` (16114) sorry-free on standard axioms, so the SITE chain `s7s_siteData_of_wall → s7s_site →
s7s_rii_witnesses → s7s_switch_value → s7s_cornerHomfly_skein` has no sorry; B3 closed ⇒ `s7z_oneNewborn_exists` (19365)
sorry-free.  The glue (`section W4Bigon`, 19621-19912, `variable (hn) (g) {M a} (h : g.BigonAt M a) (h₁) (h₂)`) instantiates
W3_K_REPORT §4(a)'s recipe, with one correction to it:

* **K's recipe took `Elig := univ.filter (s7f_Eligible …)`, but the eligible bijection must land in the DECOMPOSITION pairs, and
  F's eligibility does not imply that `T₀` (or its lift) is a decomposition.**  The glue therefore sums over the eligible
  DECOMPOSITIONS `w4_EligDec hn g h t := univ.filter (fun T₀ => s7f_Eligible … T₀ ∧ IsDecomposition hn hP₂ (lift T₀))` and shows
  that F's two residual sums over the F-eligible supports equal the sums over `w4_EligDec` (`w4_sum_ret_eq`: `term₂(lift T₀) = 0`
  and `term₀ T₀ = 0` when the lift is not a decomposition, the latter through FB3's `s7fc_isDecomposition_lift`; `w4_sum_one_eq`:
  the newborn extensions of a non-decomposition are non-decompositions, `w4_not_isDecomposition_insert`).
* `w4_liftEquiv hsplit : {T₀ // T₀ ∈ w4_EligDec} ≃ {T : Finset (Crossing P₂) // IsDecomposition T ∧ ∀ z ∈ T, z ∈ range ι₁ ∪ range ι₂}`
  (`Equiv.ofBijective` of `s7f_lift`; injective `s7f_lift_injective`, surjective `s7f_lift_surj` with newborn-freeness of the
  target from `hsplit.x_not₁/₂`, `y_not₁/₂`); `w4_eligibleEquiv hsplit := w4_liftEquiv.trans (s7b_eligibleDecompositionEquiv hn h.1.1
  h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)) (s7f_hP₂ g M a t) h₁ h₂ hsplit.split)`; its components are the half preimages
  `s7b_pre ι₁ (lift T₀)`, `s7b_pre ι₂ (lift T₀)` by `rfl` (`w4_eligibleEquiv_fst/_snd`).
* `w4_oneNewborn_rows hsing : ∃ δ > 0, ∀ t < δ, ∀ hsplit, ∀ T₀ ∈ w4_EligDec, term₂(T₀∪{x}) = 0 ∧ term₂(T₀∪{y}) = 0` — B3's
  `s7z_oneNewborn_exists` at the lift: K-eligibility (`s7z_Eligible`: decomposition ∧ no selected crossing interlaces both
  newborns) from F-eligibility through `hsplit.x_free₁/₂` (a half-image crossing interlaces neither newborn); K's
  `s7z_side/s7z_x/s7z_y/s7a_sideGeneric` accepted for F's `s7f_side/s7f_x/s7f_y/s7f_hP₂` by definitional unfolding / proof
  irrelevance (no bridge lemma needed).
* `w4_residualData hloc ht hsplit hid hrow hone : s7z_ResidualData hn h h₁ h₂ t` — K's per-`t` residual data with `b := s7f_side`,
  `x y := s7f_x, s7f_y`, `d := s7f_dirSign` (`s7f_dirSign_sq`; `s7z_s₀ g M a (s7f_side g M a) = s7f_dirSign g M a * contactSign` by
  `unfold; split_ifs <;> ring`), `ε := s7f_Interlacing`, `α := Finset (Crossing P₀)`, `lift := s7f_lift`, `term₀ := s7e_term hn hP₀`,
  `Elig := w4_EligDec`, `e := w4_eligibleEquiv`, `hres := hid` (F's identity, sums rewritten by the two lemmas), `hrow`/`hone`.
* **`w4_s7_bigon_law_at_of hsing (hrows : w4_BigonReturnedRows hn g h h₁ h₂) : ⟨the frozen leaf statement⟩`** := `s7z_bigon_law_at_of_residual`
  on the radii of `s7f_exists_law_residual`, `s7f_exists_bigonSplit`, `s7a2_exists_intervalLocal`, `w4_oneNewborn_rows`, `hrows`.
  **Axioms `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — no `sorryAx`.**

The leaf `s7_bigon_law_at` keeps the skeleton's `sorry` (merge rule: its input B2' is not proved).  Closure line, once wave 5
lands: `s7_bigon_law_at hF hsing hn g M a h h₁ h₂ := w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)`
(the frozen `hF` enters only through B2', `hsing` only through B3).

## 5. What remains for B2 — EXACTLY, as named Props with sizes (this defines wave 5)

**The one open Prop** (W4 19851; its per-`t` form 19748):

```
def w4_BigonReturnedRows hn g h h₁ h₂ : Prop := ∃ δ > 0, ∀ t < δ, w4_ReturnedRow hn g h h₁ h₂ t
def w4_ReturnedRow hn g h h₁ h₂ t : Prop := ∀ T₀ ∈ w4_EligDec hn g h t,
  s7e_term hn hP₂ (lift T₀) - s7e_term hn hP₀ T₀ =
    (if s7f_Interlacing hn h t then 1 else 0) * (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
      (s7e_term hn₁ h₁ (s7b_pre ι₁ (lift T₀)) * s7e_term hn₂ h₂ (s7b_pre ι₂ (lift T₀)))
theorem w4_box_returnedRows (hF : FloorTheoremData) : w4_BigonReturnedRows hn g h h₁ h₂ := by sorry   -- wave 5 replaces this body
```
(`hP₂ := s7f_hP₂ g M a t`, `hP₀ := s7f_hP₀ g M a t`, `ι₁/ι₂ := s7b_first/secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))`,
`lift := s7f_lift hn g h t`, `hnᵢ := (contactHalfSizes_bounds hn h.1.1).i.1`.)  Sm-4:448-770 and 785-825: for an eligible
decomposition `T₀` of `P₀` with lift `T` on `P₂` — newborn-free, eligible — the carriers of `T` are the carriers of `T₀`
(U110-A, FB3's `s7fc_e`) except that the FULL CONTACT CARRIER `q_H` of `T` (through `μ_M`, with both newborns as self-crossings)
corresponds to `q_L = s7fc_e.symm q_H` on `P₀`; `term = wind · ∏ coef`; the printed `B + R_ret = J` needs, per `T₀`, the
following Props (all four are geometry/instantiation on interfaces that are PROVED; no algebra, skein, record or floor content
is open).  Sizes are estimates against W3_BLOCK_REPORT §2 (3,500-5,400 for the whole box) minus what SITEC (608 lines) and
SITEH (420 lines) closed.

| wave-5 unit | Prop (per eligible decomposition `T₀`, below a radius) | interfaces instantiated (all proved) | est. lines |
|---|---|---|---|
| **W5-RT** (returned transport) | `w5_ReturnedTransport`: the newborn-free lift `T` on `P₂` has a component correspondence `Component P₂ T ≃ (C₁ ⊕ C₂)` with the two half contact carriers `L₁ ∈ C₁`, `L₂ ∈ C₂` IDENTIFIED (both map to `q_H`), every other carrier of `T` carrying exactly the images of one half carrier with equal weights (`s7c_carrierWeight_eq_sel` patterns), equal rotations and equal coefficients — so that `∏_{q ≠ q_H} wt·coef = (∏_{L ≠ L₁} …)(∏_{L ≠ L₂} …)` and `term(T₁) term(T₂) = (wt₁ ω₁)(wt₂ ω₂) · spectators`; and on `P₀` the U110-A transport `s7fc_e` with `s7fc_wind_eq`/`s7fc_coef_eq` off the contact carrier (FB3) | FB2's mark map / first-return engine (`s7fb_mark`, `s7fb_BigonTransport`, `componentEquiv`, `cornerList_*_rotated`, `carrierRotation_first/second`, `coef_first/second`) with the unit component removed and the two `μ_M` vertices merged; RET's transit engine; FB3's `s7fc_*` transport for `P₀` | 1,000-1,500 |
| **W5-SITE** (contact carrier pair) | `w5_ContactRowData`: `s7k_ContactRowData hn hP₂ hP₀ hT hT₀ q_H q_L x` — `site` (the bigon site on the switched high lift with the reduced record ≅ the low lift's record) from SITE's `s7s_siteData_of_wall` (wall data `s7s_wallTriangleData_of_bigon`, both sorry-free) + SITEH's `s7sh_hrec_prop_side` (its `S' := T₀`, `hSS'` := FB3's `s7fc_hSS'`, `q := q_H`, `hxq hyq` from `x, y ∈ carrierCrossings q_H` via `s7s_mem_geoCarrierCrossings_iff`), read into BLOCK's `site` shape (or the skein equation `s7s_cornerHomfly_skein` fed to `s7k_skein_on` directly, whichever is shorter); `rotation : |R_H| = |R_L|` — the rotation of the contact carrier THROUGH the wall (A2's family excludes it; FB2's Part E corner family `s7fb_Kind`/`s7fb_family_*` adapted to the returned configuration, or `s7i_full_rotation_germ_centre`) | SITE §5 recipe, SITEH §4 recipe, BLOCK `s7k_ContactRowData`, FB2 Part E, U110-I | 600-1,000 |
| **W5-BR** (branch data) | `w5_InterlacingData` (`ε = 1`): `s7k_InterlacingData … q_H q_L … L₁ L₂ v D_A i j` — `record` (D_A := the smoothing `D₀` of `s7s_cornerHomfly_skein` with its record clause), `ne`, `comp₁/comp₂` (the two components of `D_A` are the positive lifts of `L₁`, `L₂`: U110-B's half visit maps through `CB.positiveLiftRecordIso`), `rotation : |R_L| = |R₁| + |R₂|` (`s7i_carrierRotationInt_interlacing` on C's uniform patterns), `pattern₁/₂` (`s7c_uniform_halves_of_interlacing`); `w5_NoninterlacingData` (`ε = 0`): `s7k_NoninterlacingData` — `curl_value/_writhe` (BLOCK's `s7k_curl_component_value/_writhe`), `comp₂`, `rotation : |R₁|+|R₂|−|R_L| = −1` (`s7i_carrierRotationInt_noninterlacing`), one-dissent patterns (`s7c_dissent_halves_of_noninterlacing`); the `ε` ↔ turn-sign link (B3's `s7o_interlaces_iff`, `s7o_turn_M_of_lt`; `s7i_contact_dichotomy`) | BLOCK `s7k_InterlacingData` / `s7k_NoninterlacingData`, U110-B, U110-C, U110-I, B3 | 800-1,300 |
| **W5-ROW** (the row) | `w4_ReturnedRow hn g h h₁ h₂ t` from the three above: `ε = 1` by `s7k_interlacing_row` (`Ω_H − Ω_L = −ω₁ω₂`, the floor `hF` through `s7j_interlacing_entry_at_halves` at `L₁ L₂`) + `s7k_interlacing_term` (`hwt : wt = −s₀ · wt₁ wt₂`, C's selector pattern of the contact carrier); `ε = 0` by `s7k_noninterlacing_row` / `s7k_different_block_row` + `s7k_noninterlacing_term` (`s7j_noninterlacing_entry_at_halves`, `s7j_different_block_entry_at_halves`); the spectator product bookkeeping (`Fintype.prod_equiv`, `s7c_map_univ_eq_of_equiv`) through W5-RT; then the radius (`s7a2_exists_intervalLocal`, F's split radius, SITE's wall radius) into `w4_box_returnedRows` | BLOCK §H/§J row and term laws, J's floor entries, C's selectors | 400-700 |

**Total ≈ 2,800-4,500 lines** over as many waves as it takes (D-AUTH-20260919 G-01).  Suggested order: W5-RT first (it fixes the
carrier vocabulary `q_H`, `q_L`, `L₁`, `L₂` that W5-SITE and W5-BR instantiate); W5-SITE and W5-BR in parallel; W5-ROW last.  Each
unit should follow the S1P pattern (a `def … : Prop` + one sorried theorem per sub-Prop, glue proved) so that the merge assembler
replaces exactly one body per unit; the final body replacement is `w4_box_returnedRows`'s `sorry`, and then the leaf's.

## 6. Task (5): compile, axioms, frozen statements, clash scan

Compile: §header.  `#print axioms` (scratch copy `<scratchpad>/w4/W4_Assembled_axioms.lean` = the file + 38 `#print axioms
SM.<name>` lines after `end SM`, 45 s; standard = `propext`, `Classical.choice`, `Quot.sound`; the six registered literature axioms
of `axiom-policy.json` = `lit_homfly`, `lit_homfly_descent`, `lp_lm`, `lp_lm_uniqueness`, `ng_finite_word`, `src_contact`):

| declaration | sorryAx | other axioms | sorryAx source |
|---|---|---|---|
| **`thm_C_S7`** | **YES** | standard + all six literature (the `thm_floor` chain adds `lit_homfly_descent`, `ng_finite_word`, `src_contact`) | **exactly one: the body of `s7_bigon_law_at`** |
| `thm_C_S7_of_floor`, `thm_C_S7_of` | YES | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | the bigon leaf |
| **`s7_sliding_law_at`** (leaf) | **no** | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — **CLOSED** |
| `s7_bigon_law_at` (leaf) | YES (own `sorry`) | standard + `lit_homfly` | — |
| **`s7u_box_carriers'`** (S3'), `w4_B_no_transport'_vl`, `s7u_box_ret'` (S1'), `s7g_box_carriers'`, `s7g_box_carriers_literal`, `s7q_box_carriers`, `w3_SlidingCarriers_of_box` | no | standard only | — |
| `s7u_sliding_law_at_of`, `s7u_box_rows'_of` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| `s7q_box_ret`, `w3_SlidingRet_of_box` | YES | standard | `s7q_box_ret`'s own `sorry` (false as stated; off every proved path) |
| **`w4_s7_bigon_law_at_of`** | **no** | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| `w4_residualData`, `w4_oneNewborn_rows`, `w4_sum_ret_eq` | no | standard + `lit_homfly` | — |
| `w4_eligibleEquiv` | no | standard | — |
| **`w4_box_returnedRows`** (B2') | YES (own `sorry`) | standard + `lit_homfly` | the wave-5 black box |
| `s7f_exists_law_residual`, `s7f_exists_twoNewbornTerm`, `s7f_exists_ineligible_transport` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| `s7f_exists_bigonSplit`, `s7s_siteData_of_wall`, `s7s_clear_local`, `s7s_wallTriangleData_of_bigon`, `s7sh_hrec_prop_side` | no | standard only | — |
| `s7s_cornerHomfly_skein` | no | standard + `lit_homfly`, `lp_lm`, `lp_lm_uniqueness` | — |
| `s7z_oneNewborn_exists`, `w3_BigonOneNewborn_of_box`, `w3_s7_bigon_law_at_of`, `s7z_bigon_law_at_of_residual` | no | standard + `lit_homfly` | — |
| `s7z_F_exists`, `s7z_returned_of_FSector`, `s7z_exists_rowSector` | YES | standard + `lit_homfly` | K's superseded boxes (off every proved path) |

No unregistered axiom appears anywhere.  **`thm_C_S7` is NOT sorry-free**; its `sorryAx` enters through the bigon leaf's own
body only (not through any black box, because the leaf's body is the skeleton's `sorry`; wiring the leaf to
`w4_box_returnedRows` would move the source to that box without changing the count).

Frozen statements: `python3 tools/stmt_check.py W4_Assembled.lean --base W3_Skeleton.lean` → **5/5 byte-identical and unique
(PASS)**; `tail -n 43` identical to `W3_Skeleton.lean`; the deleted side of `diff W3_Assembled.lean W4_Assembled.lean` is the six
W3 header lines and eight `  sorry` lines only.  Clash scan: §2.  Verbatim check (each unit block's line range located in
`W4_Assembled.lean`): S3G, FB1, FB3, SITEC ×2, SITEH, B3 verbatim; S1P verbatim except the two docstring lines and the body of
`s7u_box_carriers'` (§3, §8); FB2 verbatim except four inserted `set_option` lines (§8).

## 7. Task (6): port — NOT ready

`thm_C_S7` carries `sorryAx` (§6), so `work/drafts/corner/port/CS7/` is not prepared.  For the port once wave 5 closes B2':
`SM/CS7Units.lean` = W4 lines 24-19912 minus the row theorems' tail, minus the superseded sorried declarations and their shape
checks (`s7q_box_ret`, `w3_SlidingRet`, `w3_SlidingRet_of_box`, `w3_box_rows_of`, `w3_s7_sliding_law_at_of`,
`w3_s7_sliding_law_at_of₂` (all take `hret : w3_SlidingRet`), `s7z_F_exists`, `s7z_returned_of_FSector`, `s7z_exists_rowSector`,
`w3_BigonFSector`, `w3_BigonReturnedRows`, `w3_BigonFSector_of_box`, `w3_BigonReturnedRows_of_box`, `w3_s7_bigon_law_at_of` (takes
B1, B2)); `SM/CS7.lean` = the two leaves (bodies as in W4 / the wave-5 closure line), `thm_C_S7_of`, `thm_C_S7_of_floor`,
`theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor`; imports `SM.CornerChainUnits SM.CS7Sliding SM.BigonDeletion
SM.CarrierFloorRows`; the content duplicates of §2 to be collapsed (keep `s7g_CarrierData'`, `s7fa_side_of_r`, `s7fa_sideData`,
`s7fa_not_affected_of_ne`; rename the S1P/B3 uses); the 11 prose `sorry` mentions and the "BLACK BOX … NOT proved" docstrings of
closed theorems reworded (OPEN_ITEMS §E-23).

## 8. Deviations and assembler's edits, disclosed

1. **Inside S1P's block**: the docstring of `s7u_box_carriers'` (2 lines) reworded from "BLACK BOX (unit S3G …) Unit S3G replaces
   this body" to "Prop S3' — DISCHARGED at assembly (wave 4) from unit S3G's `s7g_box_carriers'` …" (W3 precedent: ROT's
   `s7q_box_split`/`s7q_box_order` docstrings), and its body `sorry` → the 63-line proof of §3; the 41-line
   `section W4SlidingNoTransport` inserted before it (inside `section S7UBoxes`, whose `(hn)` it uses; its own `{M a}` shadow the
   section's, as S3G's `S7GNoTransport` does).  Statement byte-identical.
2. **Inside FB2's block**: four lines `set_option linter.unusedSectionVars false in` inserted before the docstring/`include` line
   of `s7fb_BigonTransport.owner_yl` (10715), `.markTurn_first` (12019), `.markTurn_second` (12050), `.triangle_sum` (12147) —
   the four cosmetic linter notes W4_FB2_REPORT §1 disclosed ("`omit hT in` breaks the dot-notation call sites").  No declaration
   changed; the file now compiles with no warning other than the five `sorry` notes.
3. The bigon leaf keeps its `sorry` although a one-line closure through the black box exists (§4): the merge rule (leaves close
   when their inputs are proved), as in W3 and S1P.
4. `tools/clash_scan.py`'s `prefix_stats` reports the two-letter prefixes (`s7fa_`, `s7fb_`, `s7fc_`, `s7sc_`, `s7sh_`) and `w3_`/`w4_`
   as "UNPREFIXED" — its regex knows only `s7[a-z]_`; cosmetic, the clash results themselves are namespace-aware and clean.
5. K's §4(a) recipe corrected as in §4 (eligible DECOMPOSITIONS, not eligible supports, index the bijection); K's `s7z_ResidualData`
   and `s7z_law_at_of_residual` are consumed unchanged.
6. Nothing believed false; no frozen statement touched; no import added; nothing written under `work/lean`.

## 9. Reproduce

```
python3 <scratchpad>/w4/assemble2.py work/drafts/corner/W4_Assembled.lean <scratchpad>/w4/W4_Assembled_axioms.lean
   # = assemble.py's descending-anchor merge of the 16 hunks of §1 + the glue files glue_sliding.lean, body_box_carriers.lean,
   #   glue_bigon.lean by unique-anchor matches + the four set_option lines + the header; assert-guarded
cd work/lean && lake env lean ../drafts/corner/W4_Assembled.lean        # 0 errors; 5 × "declaration uses sorry" (4437 18053 18494 19857 19922); 34 s
cd work/lean && lake env lean <scratchpad>/w4/W4_Assembled_axioms.lean  # the 38 axiom lines of §6; 45 s
python3 work/drafts/corner/tools/stmt_check.py work/drafts/corner/W4_Assembled.lean --base work/drafts/corner/W3_Skeleton.lean   # 5/5 PASS
python3 work/drafts/corner/tools/clash_scan.py work/drafts/corner/W4_Assembled.lean   # duplicates [], full-name clashes {}
diff work/drafts/corner/W3_Assembled.lean work/drafts/corner/W4_Assembled.lean | grep -E '^[0-9]'   # 18 hunks (§2)
```
Method: the units-only merge compiled first (07:58Z, 0 errors, 6 sorries); a prefix olean of everything before the bigon leaf
(`lake env lean --root=<dir> -o W4Prefix.olean`, 47 s) served two probes — `ProbeA.lean` (the S3' closure and the sliding leaf,
14 s, first run clean) and `ProbeB.lean` (the bigon glue, 14 s, first run clean but for the two linter notes fixed in the final
text: `omit [NeZero n] in` on `w4_not_isDecomposition_insert`, `_hsplit` in `w4_oneNewborn_rows`) — then the final assembly and
compile (08:12Z).  Zero failed attempts; the reassessment rule was not triggered.  Timeline: 07:43 UTC start (author_response.md,
D-AUTH-20260919 at AN L6520, the eight unit reports, W3 reports, the K/F/SITE/BLOCK interfaces); 07:58 units-only merge compiles;
08:03 prefix olean; 08:06 ProbeA; 08:08 ProbeB; 08:12 `W4_Assembled.lean` compiles; 08:14 axioms; 08:16 checks; 08:20 report.
