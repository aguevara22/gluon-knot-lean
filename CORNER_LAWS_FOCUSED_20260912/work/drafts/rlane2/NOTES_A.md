# NOTES_A — R lane part 2, statement design of the nine remaining obligation rows (TAG A, spec-first)

File: `work/drafts/rlane2/Statements_A.lean` (1065 lines). Checked 2026-09-14 with
`cd work/lean && lake env lean ../drafts/rlane2/Statements_A.lean`: exit 0, no errors, exactly nine `sorry`
warnings — the nine row theorems `RProof.exterior` (L290), `availability_zero_one` (L363),
`generic_selector` (L506), `generic_transport` (L601), `generic_selected` (L662), `extreme_pair_zero` (L714),
`extreme_transport` (L797), `extreme_selected` (L852), `cv_R : CV.hyp_R` (L971). Everything else is a
definition or PROVED; `#print axioms` of the proved auxiliaries: `propext, Classical.choice, Quot.sound`
plus `SM.lit_homfly` wherever `CV.X1` is mentioned (the registered literature interface reached through
`homfly`; axiom-policy.json `literature`). Rows (claims.py ids / ORDER.md numbers): R:exterior 168/170,
R:availability_0_1 170/176, R:generic_selector 172/177, R:generic_transport 173/178, R:generic_selected
174/182, R:extreme_pair_zero 175/183, R:extreme_transport 176/175, R:extreme_selected 177/174,
R:cv_theorem 178/185.

## 0. Shared decisions

* **Domain — F2(A), no narrowing.** Every bundle is `structure <Row>Data (hn : 3 ≤ n) (E : CV.Event n)
  (e f g) (δ : ℝ) : Prop`, every row theorem `(E e f g h3 h4e h4f h4g) (hE : E.IsSimpleRIII …) : ∃ δ, 0 < δ
  ∧ δ ≤ E.radius ∧ <Row>Data (three_le_of_h3 h3) E e f g δ` — the shape of the four accepted cores.
  `hn : 3 ≤ n` is needed by `CV.X1`/`CV.Omega1` (CV def:polygon, reading (iii) of DECISION_FINAL §2); it is
  DERIVED from `h3` (`three_le_of_h3`, L118: `1 ≤ rep e < rep f < rep g ≤ n`), so the theorems keep the
  accepted signature; consumers may pass any proof (proof irrelevance).
* **X₁ consumed literally.** `T_ν(J)` = "the complete X1 term of `Q ∪ J` on side `ν`, absent rows being
  zero" (every RA file) = `rowTerm hn (genericAt E t ht.1) (Q ∪ J)` := `CV.X1Summand` (CV/ChamberInvII.lean):
  `wind(S) ∏_L Ω₁(S,L)` if `S ∈ Ind(G_P)`, else `0` (`rowTerm_of_mem_Ind`, `rowTerm_of_not_mem_Ind`, L138/146).
  `X_1(P_±)` = `CV.X1 hn (E.curve t) (genericAt E t ht.1)`; `Φ_±(Q)` = `fibreSum (geomAt …) e f g (rowTerm …) Q`
  (the accepted `fibreSum` at `F := F_±`). The accepted `FibrePartitionData.state_sum_partition` at this
  summand closes NOTES_FINAL §3's "X₁ flag": `X1_eq_sum_fibreSum` (L184, PROVED) is display (3).
* **Sides and transport.** As in Cores: `t t' : E.Parameter`, `Punctured E δ t`, `OppositeSides E t t'`,
  `hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s`; supports read on the far side through
  `SM.transportSupport hs Q` (= `Q.map (crossingTransport hs).toEmbedding`, `rfl` — the form of the accepted
  `avail_same`). Sides are never called `P₊/P₋`: an identity symmetric in the sides is stated for `t, t'`
  opposite; a side the text names by its graph (`H`/`K3`, `L`/empty, `P` two-edge, `E` one-edge) is
  identified by the local-edge predicates `CompleteLocal`, `EmptyLocal`, `EdgeAB ∧ EdgeBC`, ….
* **Full availability** = `FullAvail hP e f g Q : avail hP e f g Q = triangleCrossings P e f g`
  (R_ATTACHMENT_WARRANTS.md:5–6 "the availability set … equals the three-element local crossing set T").
* **Fixed labels, relabelled branches.** The RA files relabel so that `P = a b A a c B b c C`, `E = b a A c a
  B c b C` (generic) or `H = x y A z x B y z C`, `L = y x A x z B z y C` (extreme). Here `a = x = x_ef`,
  `b = y = x_eg`, `c = z = x_fg` are FIXED (the labels of the accepted `generic_table`), and a text stated "in
  the displayed labels" is rendered by (i) its canonical-branch clause (selected pair `ac`, `s_a = s_b =
  s_c`) and (ii) the two relabelled instances (selected pair `ab`, `bc`) — R_GENERIC_COMMON_TRANSPORT_PROOF.md:49
  "Every generic branch can be put in this form by relabelling the strands … The same relabelling carries the
  crossings". The extreme texts state all three singleton rows, so no relabelling clause is needed there.
* **Carriers, weights, factors** are CV's own on the accepted geo layer: `q : GeoComponent hP S`,
  `CV.weight hP S q` (`wt(L)`), `CV.wind`, `CV.CarrierMixed`, `CV.Omega1 hn hG hS q` (`Ω₁(S,L)`),
  `CV.carrierR` (`R(L)`), `CV.U`, `CV.pieceOf`, `CV.pieceLabels`; "a carrier contains a visit" =
  `geoOwner hP S (Sum.inr v) = q` (conv:selected-visits at selected visits, DECISION_FINAL §4).
* **`CV.hyp_R`** (L94) is defined verbatim per DECISION_FINAL R6 (all-sides point-value form, `hn` explicit,
  `E.generic_punctured tp hp.ne'`); it is the CV:ax:R row's fixed-name declaration, placed here because
  `RProof.cv_R` has this type; the assembler moves it to the CV row module.

## 1. R:exterior (168) — `ExteriorData` (L252), `RProof.exterior` (L290)

Source: R_ATTACHMENT_WARRANTS.md:154–182 (R-EXTERIOR-1, Statement); OPEN_WORK.md:21 item 4.

| sentence | rendering |
|---|---|
| :167–169 "A carrier of `S` is triangle-disjoint when it contains none of the six traversal visits belonging to `T`, including a selected triangle crossing's smoothing-site visits" | `TriangleDisjoint hP S e f g q` (L212): no visit of a triangle crossing is owned by `q` |
| :171–175 `C_{Q,σ}(A) = ∏_{triangle-disjoint L} wt_σ(L) Ω_{1,σ}(S,L)` | `exteriorFactor hn hG hS e f g` (L219); `ρ_σ(A)`: `touchingFactor` (L227) |
| :177 "Then `C_{Q,sigma}(A)` is independent of `A`" | `independent_of_A` (any two `A, A' ⊆ T` with `Q ∪ A`, `Q ∪ A'` independent, one side) |
| :177–178 "and its common value is the same for `sigma=-` and `sigma=+`. Write that single value as `C_Q`; it may be zero." | `wall_invariant` (any `A` at `t`, any `A'` at `t'`, `Q` transported) |
| :179–184 "Consequently every full-availability row factors exactly as `tau_sigma(A) = C_Q * rho_sigma(A)`" | `factorization`: under `FullAvail Q`, `∃ C, ∀ A …, rowTerm (Q ∪ A) = C * touchingFactor` on both sides with the SAME `C` |
| proof §3 "Partitioning the carriers into disjoint and touching classes … `tau_sigma(A) = C_{Q,sigma} * rho_sigma(A)` as an identity" | `rowTerm_eq_exterior_mul_touching` (L239, PROVED: `wind = ∏ wt`, `prod_filter_mul_prod_filter_not`) |

Readings. `τ_σ(A)` is the complete X₁ term (`rowTerm`), so `τ = C_{Q,σ}(A)·ρ_σ(A)` is a definitional product
split (proved); the row's content is (a)+(b). `factorization` keeps the printed "full-availability" binder;
the general form for every `A` follows from (a)+(b)+the proved split in two lines (not asserted, to stay
literal). `independent_of_A`/`wall_invariant` are NOT restricted to full availability (the Statement is not),
which is what R:availability_0_1 consumes at `|𝓐(Q)| ≤ 1`. Cross-wall `A'` is an arbitrary subset of `T'`
(not the transport of `A`): the printed "independent of `A`" + "same on both sides" is exactly that.

## 2. R:availability_0_1 (170) — `AvailabilityData` (L311), `availability_zero_one` (L363)

Source: R_ASSEMBLY_SPEC.md:59–64 (display (4) and the paragraph after it); OPEN_WORK.md:13–14 item 2.

| sentence | rendering |
|---|---|
| :61 "At availability zero or one the local supports themselves correspond" | `local_supports_correspond`: `J ∈ Ind(G_t[𝓐(Q)]) ↔ transportSupport hs J ∈ Ind(G_t'[𝓐(Q')])` |
| :61–63 "but that does not prove their summands agree. Prove the required carrier/record, selector, rotation and coefficient transport" | `carrier_transport`: for every `J` of the fibre, `∃ φ : GeoComponent_t (Q∪J) ≃ GeoComponent_t' (Q'∪J')` with `wt`, `R(L)`, `Ω₁` equal carrier by carrier (record transport = the mechanism of `Ω₁` equality) |
| (the summands then agree) | `summands_agree`: `rowTerm_t (Q ∪ J) = rowTerm_t' (transport (Q ∪ J))` |
| :59 "(4) `Φ_+(Q) = Φ_-(Q)`", OPEN_WORK item 2 "the fibre identities for availability 0 and 1" | `fibre_identity`: `fibreSum_t (rowTerm_t) Q = fibreSum_t' (rowTerm_t') (transport Q)` |

Readings. Availability is `(avail … Q).card = 0 ∨ = 1` (`FibrePartitionData.avail_card` excludes 2).
`carrier_transport` is an existential bijection (the SPEC names the four transports without prescribing a
mechanism; the RA proofs' mechanism is the "arbitrary-Q successor lift"); it implies `summands_agree`
(`wind = ∏ wt` reindexed along `φ`, `∏ Ω₁` likewise) which with `local_supports_correspond` implies
`fibre_identity` — the three levels are kept as three printed clauses. Not restricted to any orbit.

## 3. R:generic_selector (172) — `GenericSelectorData` (L420), `generic_selector` (L506)

Source: R_GENERIC_NONSELECTED_SELECTOR_PROOF.md:7–14 (Statement), :93–118 ("Which pair is selected"),
:119–152 ("The mixed carrier"). Labels: pair `ab` shares `u = e` (others `f, g`); `ac` shares `f`; `bc` shares `g`.

| sentence | rendering |
|---|---|
| :11–12 "one is the graph-selected pair complementary to the degree-two singleton of `P3`" (+ :105 "exactly one condition in (4) holds") | `selected_pair_unique` (event level; the graph identification is the accepted `selected_is_graph_selected`) |
| :126 (5) "`sgn det(u,v) = sgn det(u,w)`", :142–148 (6) "`det(v,u) = -det(u,v)`, and `det(u,w)`. By (5), the signs in (6) are opposite" | `corner_signs_opposite`: per nonselected pair, both traversal orders, e.g. `¬SelectedAB → crossingSign f e = -crossingSign e g ∧ crossingSign g e = -crossingSign e f` (`strandSign = crossingSign`, `rfl`, L412) |
| :135–148 "one carrier contains the entire arc and both of its endpoint smoothing corners … one endpoint turns from `v` into `u` and the other from `u` into `w` (or … interchanged) … The carrier is mixed" | `mixed_carrier`: `MixedSharedStrandCarrier` (L401) = `∃ q` owning the corner marks `inr (visitOn x v)` (arrive `v`, leave `u`) and `inr (visitOn y u)` (arrive `u`, leave `w`), or the reversed pair, `∧ CV.CarrierMixed q` |
| :12–13 "Each of the other two pair rows has winding selector zero on the side where it is present" (:149–151 "its weight is zero by def:wind … winding selector … is zero") | `selector_zero`: `Q ∪ J ∈ Ind → CV.wind (Q ∪ J) = 0` |
| :151–152 "Consequently its entire X1 row is zero before any coefficient is read" | `row_zero`: `rowTerm (Q ∪ J) = 0` (no presence hypothesis: absent rows are zero) |
| :13–14 "for arbitrary exterior gaps and outside independent support `Q`; no coefficient, exterior-factor division, or nonvanishing hypothesis" | the quantification: `∀ Q ∈ outsideSupports, FullAvail Q →`, generic orbit `¬ExtremeLocal`, nothing else |

Corner marks: at a selected visit `v` the carrier arrives along `v.2` and leaves along the twin's edge
(`CV.turn_visit_of_traced`), so "turns from `v` into `u`" is the mark of `x_{uv}`'s visit on edge `v`. Which of
the two orders occurs depends on `q_u`; both are stated (":or the same description with the order reversed").

## 4. R:generic_transport (173) — `GenericTransportData` (L534), `generic_transport` (L601)

Source: R_GENERIC_COMMON_TRANSPORT_PROOF.md:16–58 ("Statement and canonical branch").

| sentence | rendering |
|---|---|
| :38–46 "the selected pair is `ac` … equality of the `a` and `c` determinant signs. If the `b` sign were opposite, the triple would be … alternating … Hence … `= sigma` (1)" | `canonical_branch`: generic → (`SelectedAC ↔ s_a = s_b ∧ s_b = s_c`) |
| :56 (2) "`T_P(empty)=T_E(empty)`" | `empty_row` (all generic branches) |
| :57 "`T_P(a)=T_E(a)`", :58 "`T_P(c)=T_E(c)`" in the canonical branch | `endpoint_a`, `endpoint_c` under `s_a = s_b ∧ s_b = s_c` |
| :49–52 "Every generic branch can be put in this form by relabelling … carries the crossings" | `relabelled_branches`: `SelectedAB → rows a, b transport`; `SelectedBC → rows b, c transport` |

Readings. The identities are symmetric in the sides, so `P` is not named. "Endpoint rows" = the singleton rows of
the two crossings of the graph-selected pair (the complement of the degree-two vertex); in branch `ab` these
are `a, b`, in `bc` they are `b, c` (from `selected_is_graph_selected`). The "arbitrary-Q successor lift"
(2a) (:61–83) and the undominated-graph isomorphisms are proof steps, not clauses (recorded as the proof
route; see §11 risk 5).

## 5. R:generic_selected (174) — `GenericSelectedData` (L624), `generic_selected` (L662)

Source: R_GENERIC_SELECTED_COUPLE_PROOF.md:17–37 (Statement).

| sentence | rendering |
|---|---|
| :28–33 "`b` is the degree-two vertex of the path, and `ac` its complementary independent pair on `P` … `T_E(b) = T_P(b) + T_P(ac)` (GSC)" | `couple_canonical`: `s_a = s_b = s_c`, `t` the two-edge side (`EdgeAB ∧ EdgeBC`), `t'` the other: `rowTerm_t' (Q'∪{b'}) = rowTerm_t (Q∪{b}) + rowTerm_t (Q∪{a,c})` |
| :20–27 "Relabel the three local crossings so …" | `couple_relabelled`: `SelectedAB` (centre `c`, two-edge side `ac, bc`): `T_t'(c) = T_t(c) + T_t(ab)`; `SelectedBC` (centre `a`, two-edge side `ab, ac`): `T_t'(a) = T_t(a) + T_t(bc)` |
| :34–37 "with the opposite coorientation obtained by multiplying the equation by `-1`" | remark, not rendered (algebraic rewriting of the same equation) |

The proof's ledgers (5)–(8), (13) are proof steps (the selector ledger (6) is X₁-free and a natural first
proof-lane lemma; §10).

## 6. R:extreme_pair_zero (175) — `ExtremePairZeroData` (L682), `extreme_pair_zero` (L714)

Source: R_EXTREME_PAIR_ZERO_PROOF.md:7–13 (Statement), :15–42 (proof paragraphs 2–3).

| sentence | rendering |
|---|---|
| :11–12 "Each local pair support is absent on the `K3` side and present on the empty-graph side" | `pair_absent_present` (`J ⊆ T`, `|J| = 2`; `CompleteLocal → Q∪J ∉ Ind`, `EmptyLocal → Q∪J ∈ Ind`) |
| :24–33 "The remaining crossing `z` is undominated by `S` … It is a singleton component there … `{z}` is a singleton residual piece" | `remaining_singleton_piece`: `∃ hz : z ∈ CV.U (Q∪J), pieceLabels (pieceOf z hz) = {z}` — the hypothesis under which thm:s7universal (D)(i) (CV:singleton_D_i) is read |
| :12–13 "Its complete X1 term on the latter generic polygon is zero, for arbitrary outside support and exterior geometry" | `pair_row_zero`: `EmptyLocal → rowTerm (Q ∪ J) = 0` |

## 7. R:extreme_transport (176) — `ExtremeTransportData` (L739), `extreme_transport` (L797)

Source: R_EXTREME_SINGLETON_TRANSPORT_PROOF.md:13–44.

| sentence | rendering |
|---|---|
| :23–25 "Full availability is part of the statement … every `Q union {j}` is independent on both sides" | `singleton_rows_present` (each side, each `j ∈ T`) |
| :25–26 "R-LOC-2 clause 4 identifies … `H[T]=K3` if and only if `L[T]` is empty" | `graphs_complementary`: `CompleteLocal_t ↔ EmptyLocal_t'` |
| :42–44 (3) "`s_x = sigma`, `s_y = -sigma`, `s_z = sigma`" | `sign_branch`: extreme → `s_a = s_c ∧ s_b = -s_a` |
| :31–34 (2) "separately and without a symmetry assumption, `T_H(x)=T_L(x)`, `T_H(y)=T_L(y)`, `T_H(z)=T_L(z)`" | `transport_x`, `transport_y`, `transport_z` (three fields, symmetric in the sides) |

The words (1) and the rowwise table (5) are the proof's canonical data (proof steps).

## 8. R:extreme_selected (177) — `ExtremeSelectedData` (L821), `extreme_selected` (L852)

Source: R_EXTREME_SELECTED_COUPLE_PROOF.md:14–69.

| sentence | rendering |
|---|---|
| :27–31 "Full availability … makes `Q union T` an independent support on `L`. On `H`, `T` is not independent" (:38 "`xyz` is absent on the `K3` side") | `full_row_present_absent` |
| :69 (1a) "the extreme orbit is precisely `s_x = s_z = -s_y`" | `extreme_signs` (`ExtremeLocal ↔ s_a = s_c ∧ s_b = -s_a`; the accepted `extreme_iff_alternating`) |
| :37 (2) "`T_H(empty) - T_L(empty) = T_L(xyz)`" | `couple`: `CompleteLocal_t → rowTerm_t Q - rowTerm_t' Q' = rowTerm_t' (Q' ∪ T')` |
| :39–42 "whose sides are named by their graphs, is independent of coorientation" | the side is named by `CompleteLocal` (no coorientation enters) |

(1b)–(1c) (divide over-orders, outer port signs) are the proof's ledger, not rendered.

## 9. R:cv_theorem (178) — `CVTheoremData` (L880), `CVRNear` (L873), `RProof.cv_R : CV.hyp_R` (L971)

Source: R_ASSEMBLY_SPEC.md:72–76; OPEN_WORK.md:21–24 item 4; d10_axioms.tex:18–24; DECISION_FINAL.md R6.

| sentence | rendering |
|---|---|
| :46 (3) at `F_±` "the same finite outside-support set in (3)" | `state_sum` (= `X1_eq_sum_fibreSum`, PROVED from `fibre_partition`) |
| :72 "the proved identities (4)" | `fibre_identities`: `Φ_+(Q) = Φ_-(Q)` for every outside `Q` |
| :72–73 "sum … Equality is preserved by finite summation" | `near`: `X₁` equal at every opposite pair within `δ` (`near_of_fibre_identities`, L1048, PROVED: `state_sum` + `outsideSupports_transport` + `Finset.sum_map`) |
| :73 "giving exactly CV ax:R" (R6: `cv_R = cv_R_near + chamberinv(ii)`) | `sides`: the all-sides point-value form; `CVTheoremData.cvRNear` (L908, PROVED) is R6's `cv_R_near`; `sides_of_near` (L921, PROVED) derives `sides` from `CVRNear` + the chamber constancy of `X₁` (chamberinv (ii), an explicit hypothesis until CV row 147 lands) through `CV.Event.sideChamber`; `hyp_R_of_data` (L956, PROVED): the bundle at every event gives `CV.hyp_R` |

Shape of `cv_R`. `theorem RProof.cv_R : CV.hyp_R` is the fixed-name row theorem (the ninth `sorry`); the
bundle is its clause map. The proof lane is: for each event, `∃ δ, CVTheoremData` from rows 168–177
(availability cases via `avail_card`) + `near_of_fibre_identities` + `sides_of_near` with
`CV.X1_eq_of_mem_chamber_of_pieceHomfly` (needs `PieceHomflyTransported`, CV row 147) — then `cv_R :=
hyp_R_of_data …`. `Bridge.sm_R` applies `cv_R` at `Bridge.eventOfTriple hn g h` with `isSimpleRIII_eventOfTriple`
(Cores) at one pair `(tp, tm)`, then Bridge:B4 `sides`.

## 10. Provable now / blocked, unit split, effort

Available: the four cores, CV:def:X1, def:wind, def:pieces, lem:carriers, lem:carrierword, selector_A,
homflyrows, fulltwist, PieceCurve, ChamberInvII (chamber transports), TripleEvents. NOT available:
CV:thm:carrierfloor (GAP-2), CV:cor:groupedknot, CV:singleton_D_i, cb:singleton, chamberinv (ii) proper.

| row | provable now? | why / what it waits for | units (lines, hours) |
|---|---|---|---|
| R:generic_selector | **YES** (X₁-free: `wind`, carriers, adjacency) | `selected_pair_unique`, `corner_signs_opposite` from `generic_table` (sign case analysis); `mixed_carrier`: adjacency (R-LOC-2 (2b), `LocalizationData.adjacent`) ⇒ the two same-edge visits are consecutive marks (`geoMarkList` sorted, no vertex mark strictly inside one edge) ⇒ `geoSmoothingSuccessor (twin m₁) = m₂` ⇒ same cycle; corner turns by `CV.turn_visit_of_traced` + `tracedSuccessor_of_mem_Ind`; mixed via `corners_enumerated`; `wind = 0` by `weight_of_mixed`, `Finset.prod_eq_zero`; `row_zero` by `rowTerm_of_mem_Ind`/`_not_mem_Ind` | S1 signs ~120 / 1 h; S2 consecutive marks ~250 / 3 h; S3 carrier & mixed ~200 / 2 h |
| R:exterior | **partly**: (a) `independent_of_A` and (b) at the level of weights, `R(L)`, piece label sets are on the accepted layer (chamber-style transports of GeoMarkTransport/ChamberInvII adapted to the wall); the `Ω₁` part of (b) needs the piece polynomials across the wall = the record isomorphism → `CV.gausscode_polynomial` (available) but the pieces' `pieceSupport` is a `Classical.choose` (same obstacle as `PieceHomflyTransported`); (c) from (a)+(b)+`rowTerm_eq_exterior_mul_touching` | X1 wt/R part ~600 / 8 h; X2 piece polynomials ~400 / 6 h (shares the U5a open point); X3 (c) ~40 / 0.5 h |
| R:availability_0_1 | **partly**: `local_supports_correspond` now (avail_same + interlace toggle); the carrier bijection with `wt`, `R` now (as X1); `Ω₁` as X2; no floor/full-twist needed (the dominated triangle crossings are in no piece) | A1 supports ~120 / 1 h; A2 carriers ~500 / 7 h; A3 sum ~60 / 1 h |
| R:extreme_pair_zero | `pair_absent_present`, `remaining_singleton_piece` now (parity P1 + `CV.mem_U`); `pair_row_zero` waits for CV:singleton_D_i (← carrierfloor) | Z1 ~200 / 2 h now; Z2 after singleton_D_i ~150 / 2 h |
| R:extreme_transport | `singleton_rows_present`, `graphs_complementary`, `sign_branch` now (Cores); `transport_*` wait for thm:carrierfloor (C)(D) via lem:fulltwist (available) + homflyrows (ii) (available) | T1 ~150 / 1.5 h now; T2 (successor lift, records) ~900 / 12 h; T3 (floor step (16)) after carrierfloor ~300 / 4 h |
| R:generic_transport | `canonical_branch` now; rows wait for CV:cor:groupedknot (empty-row grouped polynomial) — endpoint rows may go through record isomorphisms directly (as X2) | G1 ~60 / 0.5 h now; G2 ~900 / 12 h after groupedknot |
| R:generic_selected | waits for thm:carrierfloor (C),(D), homflyrows (ii) (available), fulltwist (available), groupedknot | selector ledger (6) now ~250 / 3 h; rest ~900 / 12 h after carrierfloor |
| R:extreme_selected | as above plus the two matched switches (records) | ~1000 / 14 h after carrierfloor |
| R:cv_theorem | `state_sum`, `near_of_fibre_identities`, `cvRNear`, `sides_of_near`, `hyp_R_of_data` PROVED now; `fibre_identities` = the eight rows + `avail_card` case split (~150 / 2 h once they exist); `sides` needs chamberinv (ii) proper (`PieceHomflyTransported`, CV row 147) | C1 assembly ~150 / 2 h after rows; blocked on 147 for `sides` |

Whole-row verdict (theorem provable to zero `sorry` with today's library): **R:generic_selector only**.
Statement-only today: the other eight (their X₁-free/partial clauses listed above can be proved as
intermediate lemmas now).

## 11. Fidelity risks

1. **`carrier_transport` (row 170) is an existential bijection** — the SPEC lists four transports without a
   statement shape; the bijection with `wt`/`R`/`Ω₁` equalities is the RA proofs' own conclusion at
   singleton rows ("common/affected carriers", `(6)`), but a reviewer may prefer the transports as separate
   (record-level) clauses. Downgrade path: drop `carrier_transport`, keep `summands_agree` + `fibre_identity`.
2. **`factorization` keeps the printed "full-availability" binder**; the general factorization is one line
   from (a)+(b)+`rowTerm_eq_exterior_mul_touching`. Reviewer should not read the binder as a narrowing.
3. **Relabelled branches** (rows 173, 174): the texts prove the canonical branch and assert the others "by
   relabelling"; the explicit `ab`/`bc` instances are the literal content of that sentence with our fixed
   labels. The endpoint/centre assignment per branch follows `selected_is_graph_selected`; check it.
4. **Side identification by graphs** (`CompleteLocal`, `EdgeAB ∧ EdgeBC`) instead of by coorientation is the
   texts' own convention (R_EXTREME_SELECTED_COUPLE_PROOF.md:39–42); the generic two-edge side is `δ = +1` in
   the canonical branch (`canonical_words`).
5. **Skeleton ↔ carrier identification** (NOTES_FINAL §6 risk 6) is now IMPLICIT in rows 173–177: the words
   `P/E`, `H/L` and the "arbitrary-Q successor lift" are proof steps; the bundles assert only the row-term
   identities. The proof lane must build the lift on `geoSmoothingSuccessor` (CV/CarrierWord `refinement`).
6. **`PieceHomflyTransported`-type obstacle**: every `Ω₁` transport (rows 168, 170, 173, 176, 177) meets the
   `Classical.choose` in `pieceSupport`; the record-isomorphism route (`CV.gausscode_polynomial`,
   `RecordIso`) must be built once (shared with CV row 147) — the single largest shared risk.
7. **`CV.hyp_R` defined in an R draft**: fixed name of a CV row; the assembler must move it (or import it) so
   that the CV:ax:R row and `RProof.cv_R` see one declaration. Its shape is R6's verbatim.
8. **`hn` derived from `h3`**: `three_le_of_h3` is a proof; consumers passing another `hn` are fine (proof
   irrelevance), but the bundle's `hn` parameter is visible in its type.
9. **`SM.lit_homfly` in `#print axioms`** of anything touching `CV.X1` — expected (registered literature
   interface), to be listed in the review note.
10. **Presuppositions added**: `selected_pair_unique`, `canonical_branch`, `sign_branch`, `extreme_signs`,
    `graphs_complementary`, `singleton_rows_present`, `pair_absent_present`, `remaining_singleton_piece`
    restate sentences of the texts' Statement/scene-setting paragraphs; each is provable from the accepted
    cores and is listed here so the reviewer sees they are not stronger than the printed prose.

## 12. Validation performed

`lake env lean` on the file: exit 0, nine `sorry` warnings (the nine row theorems), no errors; `#print
axioms` (scratch copy) of `three_le_of_h3` (standard), `X1_eq_sum_fibreSum`, `rowTerm_eq_exterior_mul_touching`,
`sides_of_near`, `hyp_R_of_data`, `CVTheoremData.cvRNear`, `rowTerm_of_mem_Ind`, `near_of_fibre_identities`
(standard + `SM.lit_homfly`). Hand check of the corner-sign clause (6) for the three pairs and both
traversal orders against `crossingSign_swap` and the three selected-conditions (4); hand check of the
branch/endpoint/centre table against the six-case table of R_GENERIC_NONSELECTED_SELECTOR_PROOF.md:110–116.
