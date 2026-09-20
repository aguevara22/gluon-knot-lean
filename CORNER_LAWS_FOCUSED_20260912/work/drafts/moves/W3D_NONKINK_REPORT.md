# W3D_NONKINK_REPORT.md — Wave 3d, unit NONKINK: the kink case of the 177 site (row 177 (6), leaf `w3cs_not_kink_site_data`)

Written 2026-09-19, 05:40 – 07:15 UTC / 1:40 – 3:15am ET, by the unit-NONKINK prover, under D-AUTH-20260919
(G-02b: one substantive derivation attempt, then the executor's choice; §2 of the decision: no time bound).
File: `work/drafts/moves/W3D_NONKINK.lean` = `W3C_Assembled.lean` (16 945 lines, sha256 `dbcd1037…`) + two
insertions of `w3dk_` material (1 582 lines before `end W3BI_REAL`, 62 lines before `end W3CK_Chain`):
18 589 lines, sha256 `2fb42d319cd06237c9b3268759e0b6522270286a51fd57313c35388c0f660f48`.  Compiles from `work/lean`
with `lake env lean ../drafts/moves/W3D_NONKINK.lean`: **0 errors**, 65 s (warnings: the pre-existing deprecations,
unused-variable notes, and exactly the four pre-existing `declaration uses sorry`).  Nothing under `work/lean`
touched; `lake build` never run; every existing statement, name, docstring and proof body byte-identical (the
pristine file is recovered by deleting the two inserted blocks, verified with `difflib`).

## 0. Result in one paragraph

**The leaf `w3cs_not_kink_site : Prop` is FALSE as stated and no derivation of it from the 177 configuration data
exists (§1).  It is NOT needed.**  The row's (6) content is realised without it: a new Prop
`w3dk_rii_value_sites` — the *value form* of the site data, `homfly ((D_H^x).switch y_H) = homfly ((D_L^x).switch
y_L)` at every configuration for the two library smoothings — is PROVED (`w3dk_rii_value_sites_data`, `#print
axioms` = `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`, **no
`sorryAx`**), by cases at each side: in the non-kink case through the bigon of `w3bi_bigon_of_site` and the
library's R-II deletion, exactly as before; in the kink case (the crossing `x_ef` is a kink of the one-component
lift, the smoothing splits off a 4-gon and `BigonData.hk : 5 ≤ k` fails) by a **flat subdivision of the carrier
polygon**: one extra vertex on the single edge between the two strands of the kink (allowed by the library's
`Regular`, "zero turns are allowed so that subdivision vertices stay in the class"), which is a reparametrisation
(CS3's `appendVertex` after a cyclic shift) and hence induces a record isomorphism; on the subdivided carrier the
crossing is no longer a kink, the site data transports, the bigon exists, the deletion applies, and the record
identification is carried back through a point-compatible record isomorphism of the switched smoothing outputs.
The operative chain is re-derived on the value form: `w3dk_extreme_selected : RowShape @ExtremeSelectedData` with
`#print axioms` = `[propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm,
SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` — the same registered axioms as `w3ck_extreme_selected`,
and **`sorryAx` now only through the OUTER residue `w3cx_outer_residue_data`** (§5.4), no longer through the site
leaf.  No hypothesis on the RIII event is added (route (b) of the brief is NOT needed; FR-R-177-K does not arise).
`grep -c sorry`: 6 before → 6 after (no `sorry` term added; the frozen leaf body at :13746 is untouched).

## 1. The derivation attempt (G-02b, route (ii)) and its audit — WHY the leaf is false as stated

### 1.1 The binder inventory of `w3cs_not_kink_site`

The leaf quantifies over `E : CV.Event n`, `e f g`, `δ`, `hL : LocalizationData E e f g δ`, `hGT : GenericTableData
E e f g δ`, `hR : AV_EventRadius E δ`, the two punctured parameters with `OppositeSides`, the crossing-set
identification `hs`, the three triangle crossings, `CompleteLocal` (the `K3` side), `Q ∈ outsideSupports`,
`FullAvail`, the two independence proofs, the two contact carriers `q₀, q₀'` with `¬TriangleDisjoint`, and the two
lift crossings at the double point of `x_ef`.  Every one of these is checked against what it can say about the
LABELS of the corner polygon (`geoCornerPolygon`, whose edges are the pieces of the `P`-edges between consecutive
corners = owned vertices and smoothed `Q`-visits):

* `LocalizationData` (RProof/Cores.lean:611–700) is purely combinatorial: crossing set constant, adjacency of the two
  triangle visits on each of `e, f, g` (`AdjacentVisits`), reversal of their order across the wall, persistence of
  every other same-edge order, `ExactTriangleVisitOrders`, the interlacement toggle and the complement on `T`.  It
  has no field about a disc, no field about vertices, no field about label distances.  (The brief's phrase
  "LocalizationData's disc" refers to the printed R-LOC-2 clause 2(b), "the event disc has no parent vertex on its
  three local strand segments", which is NOT a field of the Lean structure and, even as printed, only says the
  triangle's three sides carry no `P`-vertex — the kink's two corners are far from the triangle.)
* `GenericTableData` (Cores.lean:2281–2400): nonvanishing of `D_ef, D_eg, D_fg, Δ`, the Cramer identities, the sign
  vector, the six-letter word, the alternating/extreme classification.  Signs and orders only.
* `AV_EventRadius` (X1Rows2.lean:3298): turn signs and crossing signs constant on the punctured radius, one reference
  ray.  Nothing about which labels are consecutive.
* `IsSimpleRIII` (CV/Events.lean:1131) is not even a binder of the leaf; and its `remote e f` (Polygon.lean:66,
  `¬ adjacent`) excludes only `f − e ∈ {−1, 0, 1}`, not distance 2.
* `outsideSupports` (Cores.lean:455) removes from `Q` exactly the three triangle crossings; `FullAvail` says `Q`'s
  members interlace none of `x, y, z`; `CompleteLocal` is the `K3` graph; `¬TriangleDisjoint` picks the contact
  carrier.  None mentions the label `e − 1`, `e + 1`, `f ± 1` or a monogon.

So the leaf's hypotheses are invariant under any change of the event that keeps the interlacement data, the
visit orders, the signs and the triangle — in particular under `e, f` being at label distance two with the
intervening edge `Q`-free.

### 1.2 The kink configuration is a genuine 177 configuration

Take a generic polygon `P` with a monogon `e → e+1 → e+2 =: f` (the edges `e` and `e+2` cross at `x_ef`, the loop
`x_ef → X_P(e+1) → X_P(e+2) → x_ef` is a triangle in the plane), and a third edge `g` cutting the two loop sides
near `x_ef` (`y = x_eg` on `e`, `z = x_fg` on `f`, the small triangle `x y z` strictly inside the loop; SITE's
numerical example W3C_SITE_REPORT §4(a) with `(m−2, m−1, m) = (f, e+1, e)` realises it).  Move `g` through `x_ef`:
this is a simple transversal RIII event (zero set `{G3, G4 ×3}`, `e, f, g` pairwise remote since `f = e + 2`),
its `K3` side is the side where `g` cuts the loop, the words are `x y A z x B y z C` / `y x A x z B z y C` exactly
as in `R_EXTREME_SELECTED_COUPLE_PROOF.md` (1) with `A` the (possibly empty) string of retained crossings on the
loop, `Q = ∅` is an outside support with full availability, and the contact carrier is `P` itself.  Every binder of
the leaf holds; the corner polygon's carrier edges of `x_ef` are `e` and `e + 2`, at cyclic distance two.  The
leaf's conclusion `w3cs_NotKink (carrierDiagram …) x_H` is false there (its first clause reads
`⟨0, e − 1⟩ ≠ ⟨0, (e+2) + 1⟩`… in the orientation `sS = e+2`, `tS = e`: `⟨0, (e+2) − 1⟩ = ⟨0, e + 1⟩ = ⟨0, e + 1⟩`).

The printed proof does not exclude it and does not need to: its component "`A`" (§3 (9)) may be the crossing-free
4-gon (§4 "If the carrier bears no piece, `thm:carrierfloor(D)` supplies the same lower-support conclusion"), and
the RII deletion of the `y, z` bigon (§2, equation (6)) is geometrically valid on a 4-gon.  The only obstacle is the
library interface `BigonData.hk : j + 3 ≤ k` (OPEN_ITEMS §C-11, "stronger than needed"), which the RII constructor
`exists_rii_deletion` (SM/BigonDeletion.lean, 56 uses of `hk`) cannot do without.

**Verdict of the attempt (audit A-177-NK-1).** No derivation exists: the statement is false in a configuration that
satisfies all its hypotheses; every hypothesis was inspected and none constrains the label distance of `e, f` or
the `Q`-freeness of the intervening edge.  Method changed after this one attempt, as the brief prescribes.  No
kernel-checked counterexample was built: `w3cs_not_kink_site` is a draft leaf, not a row statement (the package rule
of `work/repairs/` applies to row statements); building one would require a concrete `CV.Event` with a
`LocalizationData` proof (unit L discharged those from `CV.Event.TripleEventData`), a multi-day construction with no
consumer.  The one positive combinatorial fact found on the way (not needed, not formalised): of the two kink
orientations only the one whose loop contains the `e`- and `f`-visits of `y, z` can occur — the other would make
`g` the loop's third edge, whose corners would be the smoothed crossings `{f, g}` or `{e, g}` (`= z, y ∉ Q`) or a
`P`-vertex making `g` adjacent to `e` or `f`.

### 1.3 Consequence (rule (3))

The frozen leaf `w3cs_not_kink_site_data` is left with its `sorry` body (:13746, statement untouched).  The frozen
Props `w3bi_bigon_pair` (:12826) and `w3bi_rii_sites` (:12774) are likewise FALSE as stated in the kink
configuration (they assert a `BigonData` on the `K3`-side switched smoothing, whose run component is the 4-gon).
The first true statement of the chain is the *value form* of (6), stated as `w3dk_rii_value_sites` (§3.7) and
proved.  This is the corrected form the brief asks for.

## 2. Route (a): the different (6) argument — the flat subdivision

**Mathematics.**  On the `K3` side at a kink, the oriented smoothing at `x_H` splits off the component
`K = [x⁻ → arc → x⁺ → (e-remainder, through y) → V₁ → (the old edge b₀) → V₂ → (f-remainder, through z) → x⁻]`,
a 4-gon; the bigon `y, z` (after switching `y`) has its run `x⁻, x⁺` on `K`, so `BigonData` needs `5 ≤ 4`.
Insert one vertex `p = edgePoint X b₀ u` on the old edge `b₀` of the CARRIER polygon `X` (before smoothing).  The
subdivided polygon `X'` has the same trace, the same crossings at the same points, the same over data (both are
positive diagrams), and the image `x'` of `x` has carrier edges at cyclic distance three.  Hence:
`record(D_H) ≅ record(D_H')` (a reparametrisation preserves the oriented cyclic order of the occurrences, so it is
a named record isomorphism), `record(D_H).smooth ≅ record(D_H').smooth` (the oriented smoothing is natural in
record isomorphisms), so `record((D_H^x).switch y) ≅ record((D_H'^{x'}).switch y')` point-compatibly; on `D_H'`
the site data holds at `x'` (same points, same parameters, same clearance — the new vertex lies on `b₀`, which is
clear of the triangle), the non-kink condition holds (label arithmetic, `k ≠ 4`), the bigon `B'` exists
(`w3bi_bigon_of_site`), the deletion gives `E'` with `homfly E' = homfly ((D_H'^{x'}).switch y') = homfly
((D_H^x).switch y)` (`homfly_reidemeister_II`, `presentations`) and `record E' ≅ B'.reducedRecord ≅ record((D_H^x).switch
y).restrictCrossings (keep y z)` (transport of `restrictCrossings` along the point-compatible isomorphism).  The
two sides are then glued exactly as unit H glued the two bigons: `w3h_hrec`'s body with the two `BigonData` replaced
by the explicit retained sets (`w3dk_hrec_free`), and `presentations`.

The brief's variant "both row terms vanish" was checked and does NOT hold: at a kink the 4-gon outer carrier `A`
is UNIFORM (its two `P`-corners have the sign of the loop's orientation, `= −s_x`, which is also the sign of the
two smoothing corners by (1c)), so no weight vanishes; the identity is realised, not trivialised.

## 3. What was proved (104 declarations, all `w3dk_`, all standard-axiom unless stated)

### 3.1 Step 1 — a reparametrisation induces a record isomorphism (general; `section W3DK_Reparam`)
| name | content |
|---|---|
| `w3dk_reparam_exists_visit`, `w3dk_reparamVisit`, `_spec`, `_injective`, `_over`, `_under`, `_surjective`, `w3dk_reparamVisitEquiv` | the induced bijection of occurrences of `r : ReparamData D D'` (over occurrences by `over_map`/`over_surj`, under ones by `usw_reparam_under`) |
| `w3dk_reparamVisit_point`, `_compOf`, `_twin`, `_overBit` | same double point, component `r.e`, twins, bits |
| `w3dk_cycBetween_asymm`, `w3dk_cycBetween_total`, `w3dk_reparam_key_between`, `w3dk_reparamVisit_between` | `r.between` preserves AND reflects the strict cyclic order of keys (trichotomy + asymmetry + injectivity of `traversalKey`) |
| **`w3dk_recordIso_of_reparam`** `(hpos : ∀ x, D.sign x = 1) (hpos' : …) : RecordIso D.record D'.record` | `succ_eq` by `nextVisit_comm_of_visitBetween_iff`; signs by all-positivity (the only non-general hypothesis: a general `Reparam` would need a direction clause) |

### 3.2 Step 2 — the oriented smoothing is natural in record isomorphisms (general; `section W3DK_SmoothIso`)
`w3dk_iso_swap`, `w3dk_iso_reconnect` (+`_pow`, `_sameCycle`), `w3dk_iso_smoothKeep`, `w3dk_iso_freeComp`,
**`w3dk_recordIso_smooth (ι : RecordIso ρ ρ') (x) : RecordIso (ρ.smooth x) (ρ'.smooth (ι.Φ x))`** (`e` by
`Quotient.congr` on the reconnected cycles ⊕ the free circles, `succ` by `firstReturn_map_val`), and the variant
`w3dk_recordIso_smooth'` landing on a named occurrence with `w3dk_recordIso_smooth'_Φ_val`.

### 3.3 Step 3 — the flat subdivision as an explicit reparametrisation (`section W3DK_Subdiv`)
`w3dk_remote_sub`; **`w3dk_exists_off`** (a parameter `u ∈ (0,1)` of the edge `b` whose point lies on no other closed
edge: the bad set is a finite union of subsingletons, adjacent edges by `regular_adjacent_meet`, remote ones by
`intersection_parameters_unique`); `w3dk_subdivPoly C b₀ u := ⟨k+1, _, appendVertex (shift (b₀+1) C.P) u⟩` with
**`w3dk_subdivPoly_generic`** (CS3's `single_generic_appendVertex` after `single_generic_shift`); the circle map
`w3dk_subdivMap := traversalShiftEquiv (b₀+1) ≫ subdivPt` with `_apply`, `_eval`, `_between`, `_remote`, `_det`,
`_remote_back`; `w3dk_single_crossing_pts`; **`w3dk_subdivReparam : ReparamData (positiveDiagram (single C))
(positiveDiagram (single (w3dk_subdivPoly …)))`** (over occurrences located on both sides by CS3's
`exists_crossing_overVisit_eq`).

### 3.4 Step 4 — label bookkeeping (`section W3DK_Labels`)
`w3dk_D₀`, `w3dk_D₂` (abbreviations of the two positive diagrams); `w3dk_lab b₀ l := insertIndex (l − (b₀+1))` with
`_injective`, `_ne_last`, `_ne_inserted`; `w3dk_seg_lab`, `w3dk_edge_lab` (old labels keep segment and direction),
`w3dk_seg_last_subset`, `w3dk_seg_inserted_subset` (the two halves lie in the old edge), `w3dk_vertex_old`,
`w3dk_vertex_new_mem`, `w3dk_label_cases`; the visit map `w3dk_σ` with `w3dk_visitPt_eq`, `w3dk_σ_visitPt`,
**`w3dk_σ_strand`** (an occurrence on an old label goes to `⟨0, w3dk_lab …⟩`), **`w3dk_σ_param`** (crossing parameter
unchanged); the crossing map `w3dk_χ` with `_overVisit`, `_underVisit`, `_point`, `_overStrand`, `_underStrand`,
`_injective`; the record isomorphism `w3dk_ι` of the subdivision.

### 3.5 Step 5 — the kink arithmetic and the site data on the subdivided diagram (`W3DK_Arith`, `W3DK_SiteTransport`)
`w3dk_lab_kink_arith` (`insertIndex 0 = 0` and `insertIndex (−2)` are not at cyclic distance two in `ZMod (k+1)`,
`k ≠ 4`), **`w3dk_ne_four`** (a kink `t = s ∓ 2` with a third label remote from both forces `k ≠ 4`, by `decide` in
`ZMod 4`), `w3dk_adjacent_symm`, `w3dk_pair_cases`, `w3dk_crossingParam_congr`, `w3dk_single_strand_ext/_ne`,
`w3dk_not_adjacent_of_crossing`; `w3dk_st` (image strand) with `_injective`, `_seg`; `w3dk_seg_cases`,
`w3dk_vertex_cases`; **`w3dk_siteData_subdiv`** (`w3bi_SiteData D₀ x py pz → w3bi_SiteData D₂ (w3dk_χ x) py pz` when
`b₀` is adjacent to and different from the two strands of `x`: `g` is not `b₀`, the images of `y, z` have the image
strands, parameters equal by `w3dk_σ_param`, the triangle is the same, `clear` by `w3dk_seg_cases` + the clearance of
`b₀`, `clear_vertex` by `w3dk_vertex_cases`, `hover` by injectivity of the strand image); **`w3dk_notKink_subdiv`**
(`w3cs_NotKink D₂ (w3dk_χ x)` from the kink equation and `k ≠ 4`).

### 3.6 Step 6 — the reduced value at one side (`section W3DK_Reduced`)
`w3dk_keep D y z` (= `BigonData.keep` without the bigon), `w3dk_keep_comm`, `w3dk_keep_eq_of_bigon`,
`w3dk_mem_keep_iff`; **`w3dk_ReducedValue D x py pz : Prop`** (§0); `w3dk_reducedValue_of_notKink` (axioms `+
lit_homfly`); **`w3dk_smooth_iso_subdiv`** (the point-compatible `RecordIso` of the two library smoothings:
`w3h_smooth_record_occ` ∘ `w3dk_recordIso_smooth'` ∘ `w3h_smooth_record_occ⁻¹`); **`w3dk_reducedValue_of_kink`**
(the kink equation from `¬ w3cs_NotKink`, `k ≠ 4`, the edge `b₀`, `w3dk_exists_off`, the transports, the bigon on
`D₂`, `exists_rii_deletion`, the isomorphism `Θ` of the switched outputs by `switchRecordIso` ∘ `Θ₀.switch` ∘
`switchRecordIso⁻¹`, `presentations`, and `restrictCrossings_iso_of_recordIso Θ.symm` for the retained sets; axioms
`+ lit_homfly, lp_lm, lp_lm_uniqueness`); **`w3dk_reducedValue_of_site`** (by cases).

### 3.7 Step 7 — the BigonData-free identification and the two-sided Prop (`section W3DK_Sites`)
**`w3dk_reduced_to_smooth_free`** (unit H's `w3bh_reduced_to_smooth` with `w3dk_keep y₀ z₀` in place of `B.keep`;
only Step A/B of the body changes), **`w3dk_hrec_free`** (unit H's `w3h_hrec` without the two bigons; body verbatim
otherwise; standard axioms), **`w3dk_rii_value_sites : Prop`** (the binders of `w3bi_rii_sites`, conclusion the HOMFLY
equality of the two switched smoothings), **`w3dk_rii_value_sites_data`** (β1′ `w3bi_site_data_data` + β2
`w3bi_wall_data_data` + `w3dk_reducedValue_of_site` on both sides + `w3dk_hrec_free` + `presentations`).

### 3.8 Step 8 — the chain (before `end W3CK_Chain`)
`w3dk_rii_after_smoothing_weak_occ` (copy of `w3ck_rii_after_smoothing_weak_occ` on the value form),
`w3dk_esc_interface_ext_of` (copy of `w3ck_esc_interface_ext_of`), `w3dk_esc_interface_ext_occ_holds :
w3ck_esc_interface_ext_occ := w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds w3dk_rii_value_sites_data`,
**`w3dk_extreme_selected : RowShape @ExtremeSelectedData := w3ck_esc_ledger w3dk_esc_interface_ext_occ_holds
CV.carrierSlotFloor`**.

## 4. For the executor: the rewiring (no frozen statement changes)

1. **Operative chain.** Replace the terminal `w3ck_extreme_selected` by `w3dk_extreme_selected` (or equivalently
   change the body of `w3ck_esc_interface_ext_occ_holds` to `w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds
   w3dk_rii_value_sites_data` at port time).  After this the `sorryAx` footprint of row 177 is exactly the OUTER
   residue `w3cx_outer_residue_data` (§A-16); the non-kink leaf is out of the chain.
2. **Non-operative material** (keep as documentation or drop at port, W3C §7 (d) style): `w3cs_NotKink`,
   `w3cs_not_kink_arcST/TS`, `w3cs_not_kink_site`, `w3cs_not_kink_site_data` (false as stated, §1), `w3bi_bigon_pair`,
   `w3bi_bigon_pair_of`, `w3bi_bigon_pair_data`, `w3bi_rii_sites`, `w3bi_rii_sites_of`, `w3bi_rii_sites_data`,
   `w3bi_rii_after_smoothing_weak`, `w3bi_esc_interface_ext_of/_holds`, `w3ck_rii_after_smoothing_weak_occ`,
   `w3ck_esc_interface_ext_of`, `w3ck_esc_interface_ext_occ_holds`, `w3ck_extreme_selected`.  `w3bi_bigon_of_site`
   and `w3bi_site_data_data` REMAIN operative (consumed by `w3dk_reducedValue_of_notKink` and
   `w3dk_rii_value_sites_data`).
3. **Register (§A-17, §A-18, §C-06).** Record: the four `j = 2` bigon sub-leaves were restated with the non-kink
   hypothesis (A-18 item 1) — that hypothesis is now DISCHARGED where it holds and BYPASSED where it fails; the
   frozen Props `w3bi_bigon_pair`, `w3bi_rii_sites`, `w3cs_not_kink_site` are false as stated in the kink
   configuration (§1.2) and superseded by `w3dk_rii_value_sites`.  §A-17 closes with "not a consequence of the
   configuration data; not needed" (route (a) of the brief).  FR-R-177-K (a narrowing) does NOT arise; no edit to
   `IsSimpleRIII`, `CV.hyp_R`, `Bridge.sm_R_of_cv_R` or the SM germs.
4. **Port (W3C §7).** The `w3dk_` material of §3.1–3.5 is library-grade and independent of row 177 (it depends on
   `SM.CS3`, `SM.CChamber`, `SM.LinkDiagramRecord`, `SM.LinkRecordExtras`, `SM.CBProducts` and `SM.Smoothing` only);
   a natural home is a new module `SM/FlatSubdivision.lean` (steps 1–4) or the moves toolkit.  §3.6–3.8 belong to
   `RProof/ExtremeSelectedUnits.lean` next to the `w3bi_`/`w3ck_` material they replace.  The two copied bodies
   (`w3dk_reduced_to_smooth_free`, `w3dk_hrec_free`) can at port time REPLACE `w3bh_reduced_to_smooth` / `w3h_hrec`
   (the bigon forms follow from the free ones by `w3dk_keep_eq_of_bigon`), removing ~150 lines of duplication.

## 5. Checks

* **Compile**: `cd work/lean && lake env lean ../drafts/moves/W3D_NONKINK.lean` — exit 0, 0 errors, 65 s; four
  `declaration uses sorry` warnings at 4093 (`w3b_reparam_switch`, optional), 11689 (`w3bi_esc_outer_data`,
  superseded), 13745 (`w3cs_not_kink_site_data`, THIS leaf, left as stated), 18007 (`w3cx_outer_residue_data`, the
  OUTER residue; was 16425).
* **Identity**: `python3 check_W3_identity.py Port_GenericTransportSw_draft.lean W3D_NONKINK.lean` — `G11_ConfigSw`
  structure, namespace block, `G11_core_sw_statement`, `G11_core_sw` statement, `esc_switch_riii_of_chain`: all
  **IDENTICAL**; the two trailing `False` lines (imports, body) are the pre-existing notes (W3B_REAL_REPORT §0).
* **Statements**: `python3 check_W3_statements.py W3D_NONKINK.lean` (cwd `work/drafts/moves`) — 42/42 skeleton
  statements present, 40 byte-identical, the two differing exactly the pre-existing restatements
  `w3g_bigonData_smooth_arcST/TS` (A-18 item 1), `w3a_` count 20, nothing missing.
* **Pristine text**: `difflib` between `W3C_Assembled.lean` and `W3D_NONKINK.lean`: exactly two `insert` opcodes
  (after pristine line 15508: 1 582 lines; after pristine line 16936: 62 lines); no `replace`, no `delete`.
* **`grep -c sorry`**: 6 (W3C_Assembled) → 6 (W3D_NONKINK): the four terms at 4095, 11690, 13746, 18008 and the
  two prose mentions at 7856, 14706 (A-18 item 3); the new material contains no `sorry` (not even in prose).
* **`#print axioms`** (scratch copy `scratchpad/nonkink/W3D_Axioms.lean`, exit 0):
  * `w3dk_extreme_selected`, `w3dk_esc_interface_ext_occ_holds`: `[propext, sorryAx, Classical.choice, Quot.sound,
    SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]` (=
    `w3ck_extreme_selected`'s list);
  * `w3dk_rii_value_sites_data`, `w3dk_reducedValue_of_site`, `w3dk_reducedValue_of_kink`: `[propext,
    Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — **no `sorryAx`**;
  * `w3dk_reducedValue_of_notKink`: `[propext, Classical.choice, Quot.sound, SM.lit_homfly]`;
  * `w3dk_hrec_free`, `w3dk_siteData_subdiv`, `w3dk_notKink_subdiv`, `w3dk_subdivReparam`,
    `w3dk_recordIso_of_reparam`, `w3dk_recordIso_smooth`, `w3dk_exists_off`: `[propext, Classical.choice, Quot.sound]`;
  * `w3cs_not_kink_site_data`: `[propext, sorryAx, Classical.choice, Quot.sound]` (unchanged).
  The isolation of the `sorryAx` path of `w3dk_extreme_selected` is in §5.4.

### 5.4 Isolation of the `sorryAx` path of `w3dk_extreme_selected` (scratch copy `W3D_Axioms2.lean`, exit 0)

`w3dk_extreme_selected := w3ck_esc_ledger w3dk_esc_interface_ext_occ_holds CV.carrierSlotFloor` and
`w3dk_esc_interface_ext_occ_holds := w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds w3dk_rii_value_sites_data`.
Footprints of the inputs: `w3ck_esc_ledger`, `w3dk_esc_interface_ext_of`, `w3bi_switch_riii`: `[propext,
Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`; `w3dk_rii_after_smoothing_weak_occ`:
`[propext, Classical.choice, Quot.sound, SM.lit_homfly]`; `w3dk_rii_value_sites_data`: as in §5 (no `sorryAx`);
`w3bi_site_data_data`, `w3bi_wall_data_data`, `w3bi_bigon_of_site`, `w3h_smooth_record_occ`, `w3h_record_core`:
`[propext, Classical.choice, Quot.sound]`; **`w3ck_esc_outer_occ_holds` and `w3cx_outer_residue_data`: `[propext,
sorryAx, Classical.choice, Quot.sound, SM.lit_homfly]`** — the one and only `sorryAx` source of the new chain (the
OUTER residue, §A-16).  For comparison the superseded inputs `w3bi_rii_sites_data`, `w3bi_bigon_pair_data` carry
`sorryAx` (through `w3cs_not_kink_site_data`), unchanged and no longer consumed by the operative chain.

## 6. Pitfalls met (for whoever ports or extends this)

1. `Diagram.switch` is a plain `def`, so `(D.switch y).Γ.Crossing` does not reduce to `D.Γ.Crossing` at reducible
   transparency: `rw` with lemmas stated on `D` fails on goals stated on `D.switch y` ("motive is not type
   correct" / "did not find the pattern") even though `exact` accepts them.  Use `Eq.trans`/`Iff.trans`/`congrArg`
   terms, or state the lemma with the switched diagram.  The same holds for `(positiveDiagram hX).Γ` versus
   `Shadow.single C`, and for `Smoothing.sS` (an abbrev) versus `overStrand` inside `ring`/`linear_combination`
   (different atoms) — state the hypotheses in the form the tactic will see.
2. `w3dk_keep (D.switch y) y z ≠ w3dk_keep D y z` definitionally (the `overVisit y` of the switched diagram is the
   other occurrence); the sets are equal but the unifier will not see it — always name the diagram explicitly.
3. `set D₀ := …` on a Diagram introduces shadowed variables (`x✝`) and breaks later `rw`; `local notation` with a
   projection body fails the quotation precheck and does not support dot-notation; `include … in` is not available
   in this toolchain — use `noncomputable abbrev` (`w3dk_D₀`, `w3dk_D₂`) or explicit binders.
4. Numerals in `Fin ((…).Γ.c)` need the ascription `(⟨(0 : Fin 1), l⟩ : (Shadow.single C).Strand)`; `.snd` of a
   `Sigma` whose second type depends on the first is extracted with `eq_of_heq (Sigma.ext_iff.mp h).2`, not
   `congrArg`.
5. `linear_combination` fails silently ("ring failed") when the two sides of an equation carry syntactically
   different (defeq) `ZMod` instances; restate the equation once at a homogeneous type (`have hk' : … := hkink`).
6. `obtain ⟨κ⟩ := (… : Nonempty _)` must happen while the goal is a Prop (`Nonempty.casesOn` cannot eliminate into a
   `RecordIso`).
7. `Set.Infinite.exists_notMem_finset` (not `exists_not_mem_finset`) in this Mathlib; `Set.Infinite.diff` is
   deprecated for `sdiff`.

## 7. Timeline (UTC / ET)

05:40 / 1:40am start: author response, AUTHOR_NOTES, register §A-15–A-18, SITE/G/BIGON reports, the printed proof,
`LocalizationData`, `GenericTableData`, `IsSimpleRIII`, `AV_EventRadius`, `BigonData`, the record layer;
06:00 / 2:00am the derivation attempt concluded (§1) and the subdivision route designed; 06:12 step 1 compiles in
scratch (9 s); 06:16 step 2; 06:28 step 3; 06:40 step 4; 06:52 step 5; 06:56 steps 1–5 integrated, full compile 0
errors; 07:02 / 3:02am steps 6–8 integrated, full compile 0 errors (65 s); 07:05 axiom audit; 07:08 identity and
statement checks; 07:15 / 3:15am this report.  Scratch: `scratchpad/nonkink/` (`S1.lean`–`S5.lean`, `S6.lean.new`,
`S7.lean.new`, `S8.lean.new`, `mk_unit.py` which rebuilds `W3D_NONKINK.lean` from `W3C_Assembled.lean` + the
blocks, `W3D_Axioms.lean/.log`, `W3D_Axioms2.lean/.log`).
