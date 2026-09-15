# NOTES_B — R lane, panel B (consumer-first): rows 168, 170, 172–178

File: `work/drafts/rlane2/Statements_B.lean` (839 lines). Checked 2026-09-14 with
`cd work/lean && lake env lean ../drafts/rlane2/Statements_B.lean`: exit 0, no errors, exactly nine `sorry`
warnings = the nine row theorems `RProof.exterior` (L241), `availability_zero_one` (L300),
`generic_selector` (L380), `generic_transport` (L435), `generic_selected` (L480), `extreme_pair_zero` (L555),
`extreme_transport` (L597), `extreme_selected` (L643), `cv_R` (L709). Everything else is a definition or
PROVED; `#print axioms` on the proved reductions: `propext, Classical.choice, Quot.sound, SM.lit_homfly`
(the accepted literature interface `lit:homfly`, entering through `homfly` in every X₁ statement).

## 0. Decisions shared by all nine rows

* **Domain, F2(A), no narrowing.** `E : CV.Event n`, `E.IsSimpleRIII e f g h3 h4e h4f h4g`, sides `E.curve t`
  with `Punctured E δ t`, `OppositeSides E t t'`; the four accepted cores' vocabulary (RProof/Cores.lean) is
  reused verbatim (`triangleCrossings`, `xPair`, `avail`, `outsideSupports`, `localFibre`, `fibreSum`,
  `strandSign`, `Selected*`, `Edge*`, `ExtremeLocal`). `hn : 3 ≤ n` is a parameter of every X₁-dependent row
  (needed by `CV.X1`; CV fixes `n ≥ 3` globally, d1_setup.tex:932; R6 quantifies it in `CV.hyp_R`).
* **X₁ consumed literally.** "`F_±(S)`, the complete summand of CV def:X1 at `S` on that side, including the
  selector and every carrier coefficient with the printed empty conventions" (R_ASSEMBLY_SPEC.md:31–33) is
  `summandAt hn E t ht := CV.X1Summand hn (genericAt E t ht)` (CV/ChamberInvII.lean:461: `wind(S) ∏_L Ω₁(S,L)`
  if `S ∈ Ind`, else `0` — which is exactly the RA convention "absent rows being zero"). `Φ_±(Q)` (SPEC:36–39)
  is `fibreTermAt := fibreSum … (summandAt …) Q`, the accepted row 171 sum at the complete summand. Every
  per-carrier object is the accepted CV/X1.lean one: `Omega1`, `slot`, `carrierR`, `groupedPoly`,
  `groupedWrithe`; def:wind's `weight`/`wind`/`CarrierUniform`/`CarrierMixed` (CV/Carriers.lean:437–449);
  def:pieces' `Piece`/`pieceOf`/`pieceLabels`/`piecesOn` (:694–716); carriers `GeoComponent`, owners
  `geoOwner`, corner turns `geoCornerTurn` (SM/FlatCarriersDefs.lean:258, 262, 446).
* **Across the wall.** Supports are carried by carrying edge pairs: `wallMap hs Q := Q.map (crossingTransport
  hs).toEmbedding` (= the accepted `transportSupport`, `rfl`), triangle crossings by `crossingTransport hs
  (xPair h) = xPair ((hs _).mp h)` (`rfl`). `wallMapEmb hs` is the same map as an embedding for `Finset.map`
  reindexing (`wallMapEmb_apply`, proved).
* **Full availability** (`FullAvail`): `avail hP e f g Q = triangleCrossings P e f g`
  (R_ATTACHMENT_WARRANTS.md:5–7 "Full availability means that the availability set … equals … `T`").
* **Orbits.** Generic = `¬ ExtremeLocal`; extreme `K₃` side = `LocalComplete` (all three `Edge*`), empty side =
  `LocalEmpty` (none). With `LocalizationData.complement_on_triangle`, opposite sides of an extreme event are
  one of each; the bundles name the side by its own graph, as the RA texts do ("`H`", "`L`", "`P`", "`E`").
* **Selected pair without relabelling.** The RA proofs are printed in canonical relabelled branches
  (`P = a b A a c B b c C`, selected couple `b/ac`). The rows are stated label-free: `selectedPair hef heg hfg`
  is the pair singled out by the separating-strand test (4) of R_GENERIC_NONSELECTED_SELECTOR_PROOF.md:93–117
  (`ac` iff `s_a = s_c`, `ab` iff `s_a = −s_b`, `bc` iff `s_b = −s_c`; exactly one in the generic orbit,
  `GenericTableData.selected_unique`), `selectedCentre` its complement. `GenericTableData.selected_is_graph_selected`
  identifies it with the graph-selected pair (degree-two vertex complement on `P`, the edge on `E`), so
  "endpoint rows" = singletons of the two members of `selectedPair`, "`b`" = `selectedCentre`, "`P`" = the side on
  which `Q ∪ selectedPair` is independent. The three `if`s are evaluated in the order AC, AB, BC; only in the
  extreme orbit (all three conditions true) does the order matter, and no row reads `selectedPair` there.
* **Shape.** `structure <Row>Data (hn) (E) (e f g) (δ) : Prop`, one field per specified clause, clause quoted
  in the docstring; `theorem RProof.<name> (hn) (E) (e f g) h3 h4e h4f h4g (hE) : ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧
  <Row>Data hn E e f g δ` (the accepted shape). Row 178 is `RProof.cv_R : CV.hyp_R` (R6, below).

## 1. Row 168 — R:exterior (`ExteriorData`, L200; R_ATTACHMENT_WARRANTS.md:154–185)

| sentence | field |
|---|---|
| :156–170 "Fix an outside independent set `Q` … let `A` be any subset of `T` for which `S = Q ∪ A` is independent. A carrier of `S` is *triangle-disjoint* when it contains none of the six traversal visits belonging to `T`, including a selected triangle crossing's smoothing-site visits. Define `C_{Q,σ}(A) = ∏ … wt_σ(L) · Ω_{1,σ}(S,L)`" | definitions `TriangleDisjoint` (no visit mark of a triangle crossing is owned by the carrier; `geoOwner` covers selected visits), `exteriorFactor`, `touchingFactor` |
| :177 "Then `C_{Q,σ}(A)` is independent of `A`" | `exterior_independent_of_A` (any `A, A' ⊆ T`, both rows independent) |
| :177–178 "and its common value is the same for `σ = −` and `σ = +`" | `exterior_wall_invariant` (any `A` on one side, `A'` on the other) |
| :179–183 "Consequently every full-availability row factors exactly as `τ_σ(A) = C_Q · ρ_σ(A)`" | `factorization` with `C_Q` = the base row's factor (`A = ∅`, `Q ∈ Ind`) |
| OPEN_WORK.md:21–23 "without division; absent supports, empty products, dead selectors, both directions" | the fields quantify both directions, take independence as hypotheses, and never divide; `wt = 0` is allowed |

PROVED here: `summandAt_eq_exterior_mul_touching` — `X1Summand hn hG S = exteriorFactor * touchingFactor` for any
independent `S` (def:wind `wind = ∏ wt` + `Finset.prod_filter_mul_prod_filter_not`). So `factorization` =
`exterior_independent_of_A` (at `A, ∅`) + this lemma: a plain instantiation. Dependency note: DEPENDENCIES.json
lists `CV:cor:groupedknot` for this row; the printed R-EXTERIOR proof (§3–§4) cites def:piecediagram,
lem:piececurve, ax:gausscode, ax:homfly, lem:turnlift(ii), not cor:groupedknot. What it does need is the
choice-independence of `pieceHomfly` (CV:lem:pieceintrinsic, row 156, pending; U5a REPORT §6) to make
"`def:piecediagram` gives the same piece diagram, hence the same `P_H`" a Lean fact for pieces of different
supports/sides with the same restricted record. Reading (adopted): `Ω_{1,σ}(S,L)` is `Omega1` at `S`, so
`exteriorFactor` depends on `hS`; independence of `A` is stated across different `hS` proofs.

## 2. Row 170 — R:availability_0_1 (`AvailabilityZeroOneData`, L259; R_ASSEMBLY_SPEC.md:55–64)

| sentence | field |
|---|---|
| :61 "At availability zero or one the local supports themselves correspond" | `fibre_zero` (`Ind(G[𝓐(Q)]) = {∅}`), `fibre_one` (`𝓐(Q) = {z}`, fibre `{∅, {z}}`), `fibre_correspond` (the fibre on the other side is the image) |
| :61–63 "but that does **not** prove their summands agree. Prove the required carrier/record, selector, rotation and coefficient transport" | `summand_transport`: for each `J` in the fibre, `SummandTransport` = `wind` equal (selector) ∧ ∃ carrier bijection `τ` with `weight`, `carrierR` (rotation), `groupedWrithe`/`groupedPoly` (record), `Omega1` (coefficient) matched |
| :57–59 "(4) `Φ₊(Q) = Φ₋(Q)`" at these availabilities; OPEN_WORK.md:13–14 | `fibre_identity` |
| :63–64 "These cases cannot be omitted because the four core proofs assume full availability" | the hypothesis `card = 0 ∨ card = 1` (the sizes `≠ 3` of `FibrePartitionData.avail_card`) |

Reading: the summand identity is stated as a carrier-by-carrier transport (the SPEC's four named transports),
which is what the lem:silence-type argument delivers at availability ≤ 1 (the two dominated triangle crossings
are erased marks, the third is unselected or a singleton support whose smoothing does not touch retained data).
`fibre_identity` follows from `summand_transport` by `Finset.sum_bij` along `fibre_correspond` and the
per-carrier product (`Fintype.prod_equiv τ`) — a plain instantiation once the transport is proved.

## 3. Row 172 — R:generic_selector (`GenericSelectorData`, L327; R_GENERIC_NONSELECTED_SELECTOR_PROOF.md:7–15, 119–151)

| sentence | field |
|---|---|
| :10–12 "Among the three one-sided local pair supports, one is the graph-selected pair complementary to the degree-two singleton of `P3`" | `graph_selected`: `insert centre pair = T`, `centre ∉ pair`, `card = 2`, and either (`P₃`: centre interlaces both, pair independent) or (one edge: pair interlaced, centre isolated) |
| :119–143 "The mixed carrier … one carrier contains the entire arc and both of its endpoint smoothing corners … the signs in (6) are opposite. The carrier is mixed regardless of all its other corners" | `mixed_carrier`: two smoothing-site visits `v, w` of the two crossings of `J` on their shared strand (`v.2.val = w.2.val`), same owner, nonzero opposite `geoCornerTurn`s, `CarrierMixed` |
| :12–13 "Each of the other two pair rows has winding selector zero on the side where it is present"; :146–149 "its weight is zero by def:wind. The support's winding selector … is zero" | `wind_zero` (hypothesis `Q ∪ J ∈ Ind`) |
| :149–150 "Consequently its entire X1 row is zero before any coefficient is read" | `row_zero` (no presence hypothesis: absent rows are `0` by `X1Summand`) |
| :13–15 "arbitrary exterior gaps and outside independent support `Q`; no coefficient, exterior-factor division, or nonvanishing hypothesis" | quantification over all `Q`; no nonvanishing hypothesis anywhere |

## 4. Row 173 — R:generic_transport (`GenericTransportData`, L394; R_GENERIC_COMMON_TRANSPORT_PROOF.md:16–59)

| sentence | field |
|---|---|
| :16–47 canonical branch / labels; "Every generic branch can be put in this form by relabelling" | label-free via `selectedPair`/`selectedCentre`; `selected_pair_invariant` (the same pair on both sides: strand signs are wall-invariant, `GenericTableData.chamber_change`) |
| :56 "(2) `T_P(∅) = T_E(∅)`" | `empty_row` |
| :57–58 "(2) `T_P(a) = T_E(a)`, `T_P(c) = T_E(c)`" | `endpoint_rows` (∀ `x ∈ selectedPair`) |

Not rendered as fields (proof devices): "the arbitrary-Q successor lift (2a)" (:61–83), the residual-graph
isomorphisms `c ↦ b`, `a ↦ b` (:134–208). They are the proof-lane lemmas (unit split §8). Dependencies:
`CV:cor:groupedknot` (:95–100, the empty-row grouped polynomial via an RIII move on the grouped diagram) and
`R:exterior`; also lem:pieceintrinsic for the endpoint rows' piece polynomials.

## 5. Row 174 — R:generic_selected (`GenericSelectedData`, L448; R_GENERIC_SELECTED_COUPLE_PROOF.md:17–37)

| sentence | field |
|---|---|
| :30–31 "Thus `b` is the degree-two vertex of the path, and `ac` is its complementary independent pair on `P`" | `centre_is_degree_two` (on a side where `Q ∪ selectedPair ∈ Ind`) |
| :31–35 "(GSC) `T_E(b) = T_P(b) + T_P(ac)`", "absent rows being zero" | `couple` with `t` = the side `P` (selected pair present), `t'` = `E` |

Waits for `CV:thm:carrierfloor` (:207–236, clause (C) and (D)), `CV:lem:fulltwist` (accepted), `CV:lem:homflyrows`
(accepted), `CV:cor:groupedknot` (:132–206), `R:exterior`, `R:generic_selector`.

## 6. Row 175 — R:extreme_pair_zero (`ExtremePairZeroData`, L497; R_EXTREME_PAIR_ZERO_PROOF.md:7–51)

| sentence | field |
|---|---|
| :10–11 "Each local pair support is absent on the `K3` side" | `pair_absent_on_complete` |
| :11 "and present on the empty-graph side"; :20–22 "The support `S` is independent" | `pair_present_on_empty` |
| :24–37 "The remaining crossing `z` is undominated by `S` … Hence `{z}` is a singleton residual piece" | `third_singleton_piece` (`z ∈ U(Q ∪ J)`, `pieceLabels (pieceOf z) = {z}`) |
| :39–45 "If `wind(S) = 0` … Otherwise every carrier of `S` is uniform. Let `A` be the carrier owning `{z}`. The hypotheses of `thm:s7universal(D)(i)` now hold, so `Ω₁(S,A) = 0`" | `singleton_factor_zero` (= CV:singleton_D_i, d6_vertexedge.tex:2682–2688, instantiated) |
| :11–13 "Its complete X1 term on the latter generic polygon is zero, for arbitrary outside support and exterior geometry" | `row_zero` |

Waits for `CV:singleton_D_i` (pending: ← cor:groupedknot, carrierfloor, cb:singleton). All other fields are
X₁-free or def:pieces-level and provable now (from `ParityData.interlaced_pair`, `CV.mem_U`, `CV.mem_Ind_iff`).

## 7. Row 176 — R:extreme_transport (`ExtremeTransportData`, L567; R_EXTREME_SINGLETON_TRANSPORT_PROOF.md:13–35)

| sentence | field |
|---|---|
| :21–23 "Full availability is part of the statement: every member of `T` is nonadjacent to `Q`, so every `Q ∪ {j}` is independent on both sides" | `singletons_present` |
| :31–34 "(2) `T_H(x) = T_L(x)`, `T_H(y) = T_L(y)`, `T_H(z) = T_L(z)`", "separately and without a symmetry assumption" | `singleton_rows` (∀ `x ∈ T`) |

Waits for `CV:thm:carrierfloor` (:250–271), `lem:fulltwist`, `lem:homflyrows`, `R:exterior`, cor:groupedknot
(:103–105, 191–195) and lem:pieceintrinsic.

## 8. Row 177 — R:extreme_selected (`ExtremeSelectedData`, L611; R_EXTREME_SELECTED_COUPLE_PROOF.md:14–38)

| sentence | field |
|---|---|
| :25–27 "it … makes `Q ∪ T` an independent support on `L`" | `full_present_on_empty` |
| :27–28 "On `H`, `T` is not independent because its induced graph is `K3`" | `full_absent_on_complete` |
| :33–38 "(2) `T_H(∅) − T_L(∅) = T_L(xyz)`", "with an absent row read as zero" | `couple` (`t` = `H` = `LocalComplete`, `t'` opposite) |

Waits for `CV:thm:carrierfloor` (:340–358), `lem:homflyrows` (iii), ax:homfly knot parity (accepted),
cor:groupedknot, `R:exterior`.

## 9. Row 178 — R:cv_theorem (`CvTheoremData` L660, `CvRNear`, `ChamberInvII`, `RProof.cv_R : CV.hyp_R` L709)

Consumer analysis (BRIDGE.md §3:1443–1475, DECISION_FINAL.md R6/R7). `Bridge.sm_R` fixes an SM simple triple
germ `g.TripleAt e f k`, builds `E := Bridge.eventOfTriple hn g h` (B1), which is `IsSimpleRIII` (B2+B3 =
`RProof.isSimpleRIII_eventOfTriple`, after naming the triple by `exists_sorted_tripleAt`), applies the CV theorem
at ONE pair of side parameters `(g.sideTime true t, g.sideTime false t)` to get `X₁(E.curve t₊) = X₁(E.curve t₋)`
(BRIDGE (20)), then B4 `pointwise` (BRIDGE (17), `X1 hn P (generic_of_sm hn hP) = cornerStateSum hn hP`) turns
both values into `C` (BRIDGE (18), (21)). Hence:

* `CV.hyp_R` (L57) is R6's printed chamber-value form: for every simple RIII event and EVERY `tp > 0 > tm`,
  `X1 hn (E.curve tp) _ = X1 hn (E.curve tm) _` (def:event d1:1080–1083: the sides are the two chambers).
* The R lane's own product is the punctured form: `CvRNear` = ∀ event, ∃ δ, `CvTheoremData` with fields
  `state_sum` ((3) at the complete summand, SPEC:40–46), `outside_supports_transport` ("the same finite
  outside-support set", SPEC:72–73), `fibre_identities` ((4) for every `Q`, SPEC:57–59), `near` ("Equality is
  preserved by finite summation, giving exactly CV ax:R", SPEC:73–74).
* PROVED reductions: `state_sum_of_fibrePartition` (the X₁ flag of NOTES_FINAL §3 closed:
  `X1_eq_sum_X1Summand` + `FibrePartitionData.state_sum_partition`); `near_of_fibre_identities` and
  `CvTheoremData.of_fibre_identities` (the finite summation, from rows 164/171 + the two wall clauses);
  `hyp_R_of_near_of_chamberinv : CvRNear → ChamberInvII → CV.hyp_R` (R6's "cv_R = cv_R_near + chamberinv(ii)",
  via `Event.curve_mem_sideChamber_pos/neg`, `chamber_eq_of_mem`); `smR_shape_of_hyp_R : CV.hyp_R → (B4 pointwise)
  → ∀ germ, ∀ t, C(P₊) = C(P₋)` (the printed SM hyp:R, sm-4-knotlaws.tex:1149–1150, at every side parameter —
  the shape `Bridge.sm_R` will have; not the fixed row).
* Therefore `RProof.cv_R`'s proof is `hyp_R_of_near_of_chamberinv cv_R_near chamberinv_ii` where `cv_R_near`
  is `CvTheoremData.of_fibre_identities` on rows 164/171 + `outside_supports_transport` (from
  `FibrePartitionData.graph_on_W_same`, `LocalizationData.crossing_set_constant`) + `fibre_identities` assembled
  from rows 170–177 (§8 unit A3). `chamberinv_ii` is `CV.X1_eq_of_mem_chamber_of_pieceHomfly` once
  `PieceHomflyTransported` is proved (lem:pieceintrinsic route, U5a REPORT §6).

## 10. Provable now vs waiting (candid)

Accepted and available: rows 164/167/171/172 cores, CV:def:X1, def:wind, def:pieces, def:smoothing, lem:carriers,
lem:carrierword, def:piecediagram, lem:piececurve (implemented), selector_A, homflyrows, fulltwist, uniformrot,
turnlift, ax:homfly, ax:gausscode (record-iso form). Pending: thm:carrierfloor (GAP-2), cor:groupedknot,
singleton_D_i, cb:singleton, lem:pieceintrinsic (156), prop:chamberinv (ii), Bridge:B4.

* **Provable now: 172 R:generic_selector** (all four fields). `graph_selected` = `GenericTableData.selected_is_graph_selected`
  + `selected_unique` + `Edge*` case analysis; `mixed_carrier`: `LocalizationData.adjacent` (no outside visit
  strictly between the two triangle visits on the shared strand) + the geo carrier layer (the arc between two
  consecutive marks lies in one carrier: `geoSmoothingSuccessor` moves along the marked circle and reconnects
  only at selected visits; both endpoints are selected visits of `J`) + `turn_visit_of_traced`
  (CV/Carriers.lean:533: turn at a smoothing site = `crossingSign` of the two edges) + `GenericTableData.sign_vector`/
  `selected_unique` for the opposite signs; `wind_zero` = `weight_of_mixed` + `Finset.prod_eq_zero`; `row_zero`
  by cases on `Q ∪ J ∈ Ind` (`X1Summand` unfolds to `wind * _` or `0`). ≈ 350–450 lines. X₁ enters only through
  `X1Summand = 0`.
* **Partly provable now: 175** (`pair_absent_on_complete`, `pair_present_on_empty`, `third_singleton_piece`:
  ≈ 150 lines from `CV.mem_Ind_iff`, `CV.mem_U`, `ParityData.interlaced_pair`, `FullAvail`); `singleton_factor_zero`
  and `row_zero` wait for CV:singleton_D_i.
* **Partly provable now: 168** `factorization` given `exterior_independent_of_A` (`summandAt_eq_exterior_mul_touching`
  is proved); the two constancy fields need the piece-polynomial record invariance (lem:pieceintrinsic) and the
  wall transport of carriers/rotation (`SM.GeoPathTransport`, `geoCarrierRotation_eq_of_family`) — X₁-only
  content, no carrierfloor/groupedknot/singleton needed despite DEPENDENCIES.json.
* **X₁-only but waiting on lem:pieceintrinsic: 170** (`fibre_zero/one/correspond` provable now ≈ 100 lines;
  `summand_transport` needs the record-invariance of `pieceHomfly` across supports/sides, as chamberinv(ii) does).
* **Waiting on carrierfloor (GAP-2): 174, 176, 177**; **waiting on singleton_D_i: 175 (two fields)**;
  **waiting on cor:groupedknot: 173 (empty row), 174, 176, 177**. Their statements are fixed now; the proofs are the
  RA texts' ledgers instantiated on `summandAt` (see §8).
* **178**: `CvTheoremData.of_fibre_identities`, `hyp_R_of_near_of_chamberinv`, `smR_shape_of_hyp_R` PROVED; `cv_R`
  itself waits on all of 170–177 and on chamberinv(ii) (⇐ lem:pieceintrinsic).

## 11. Unit split and effort (statements fixed; proof lane)

* **A1 (now, ≈ 120)** `outside_supports_transport` from `FibrePartitionData.graph_on_W_same` +
  `LocalizationData.crossing_set_constant` (`Finset.ext`, `F1.mem_outsideSupports`, `CV.mem_Ind_iff`, transported
  interlacement); `triangleCrossings` transport lemma (`ext; simp [wallMap, P1.mem_triangleCrossings,
  crossingTransport_support]`).
* **A2 (now, ≈ 200)** the fibre decomposition at full availability: `Φ(Q) = Σ_{J ∈ powerset T} X1Summand (Q ∪ J)`
  (absent `J` contribute `0`; `localFibre = Ind.filter (⊆ T)`, `X1Summand_eq_zero_of_not_mem_Ind`), then the
  eight-subset case analysis: generic — `∅` (173), `{x},{y}` for the selected pair (173), `{z}` and the pair
  `{x,y}` (174, one side only), the two nonselected pairs (172 on the present side, absent on the other), `T`
  (absent both sides); extreme — `∅` and `T` (177), three singletons (176), three pairs (175 zero on `L`, absent on
  `H`). Availability 0/1: row 170 directly. This is `fibre_identities`; with A1 and
  `CvTheoremData.of_fibre_identities` it is `CvRNear`.
* **G-SEL (now, ≈ 400)** row 172 as in §10.
* **PZ (≈ 150 now + 100 after singleton_D_i)** row 175.
* **EXT (≈ 500 after lem:pieceintrinsic)** row 168: carrier fibre-stability (R-EXTERIOR §1: `geoSmoothingSuccessor`
  commutes for disjoint selected sets — `geoSmoothingSuccessor_union_of_disjoint` exists), piece stability (§2:
  `CV.mem_U`, `pieceLabels`), wall transport (§4: `GeoMarkTransport.ofOrderAgrees` on the erased word,
  `geoCarrierRotation_eq_of_family`, `gausscode_polynomial` on the piece records).
* **AV (≈ 400 after lem:pieceintrinsic)** row 170: the same transport applied to all carriers.
* **GT (≈ 700 after cor:groupedknot + pieceintrinsic)** row 173; **GS (≈ 900 after carrierfloor)** row 174;
  **ET (≈ 900 after carrierfloor)** row 176; **ES (≈ 1000 after carrierfloor)** row 177 — each a transcription of
  the RA ledger ((4)–(13), (5)–(16), (1c)–(20)) onto `Omega1`/`carrierR`/`groupedPoly` with `fulltwist`,
  `homflyrows`, `uniformrot`, `turnlift`, `carrierfloor` at the printed slots.
* **CV (≈ 60 after A2 + chamberinv(ii))** `cv_R := hyp_R_of_near_of_chamberinv cv_R_near chamberinv_ii`.

## 12. Fidelity risks

1. **`CV.hyp_R` all-sides form (R6) makes `cv_R` depend on prop:chamberinv (ii)**, which is blocked on
   lem:pieceintrinsic (`PieceHomflyTransported`). The reductions isolate this: if (ii) slips, `CvRNear` and
   `smR_shape_of_hyp_R`'s hypotheses show that `Bridge.sm_R`'s mathematical content needs only the punctured form
   + B4 `pointwise` + SM `prop_C_chamber` (side values constant on SM chambers) — a second reduction lemma
   `smR_shape_of_near` (not written; needs the SM side-chamber membership of `sideTuple`) would bypass (ii). Changing
   the form of `CV.hyp_R` is a decision for the executor (DECISION_FINAL §8 recorded the alternative).
2. **`selectedPair` is sign-defined** (test (4)), not graph-defined; equivalence is row 171's
   `selected_is_graph_selected` (iff, generic orbit). A reviewer reading "graph-selected" literally must cite that field.
3. **`ExteriorData.factorization` represents `C_Q` by the base row `A = ∅`**; the text says "that single value";
   with `exterior_independent_of_A` any representative is equal. `exteriorFactor` carries `hS` (through `Omega1`).
4. **Row 170's `summand_transport` is a carrier-by-carrier bijection** (the SPEC's four transports, adopted as the
   clause); it is stronger than the bare `fibre_identity` and is the true shape of the silence-type argument, but a
   reviewer may prefer only `fibre_identity` as the row and the transport as a proof lemma.
5. **Rows 174/177 name the side by its local graph** (`Q ∪ selectedPair ∈ Ind` / `LocalComplete`) rather than by
   `δ = ±1`; the RA texts also name sides by graphs ("independent of coorientation", SELECTED_COUPLE:36–38).
6. **Presupposition fields** added beyond the bare claims: `graph_selected` (172), `selected_pair_invariant` (173),
   `centre_is_degree_two` (174), `pair_absent/present` (175), `singletons_present` (176), `full_present/absent`
   (177), `state_sum`/`outside_supports_transport` (178). Each is a sentence of the Statement paragraphs, none is
   stronger than the RA proofs establish.
7. **`mixed_carrier` fixes the two corners as the smoothing-site visits on the shared strand** (the text's "both of
   its endpoint smoothing corners"); the arc itself ("contains the entire arc") is not a separate clause.
8. **DEPENDENCIES.json vs printed dependencies**: R:exterior lists cor:groupedknot though the R-EXTERIOR text does not
   use it; conversely lem:pieceintrinsic (156) is not listed for any R row but is needed by 168/170/173/174/176/177
   (every "same `P_H`" step). Record in the review note.
9. **Domain**: all rows on CV events (F2(A)); the SM germ reaches them through `isSimpleRIII_eventOfTriple`, as
   `smR_shape_of_hyp_R` shows (the naming by increasing representatives does not change the event).
10. **`SM.lit_homfly`** appears in `#print axioms` of every X₁ statement (through `homfly`); it is the accepted
    literature interface, not a new axiom.
