# NOTES_B — R lane, Designer B (text-first), rows 166/167/169/171

File: `work/drafts/rlane/Statements_B.lean` (937 lines). Checked 2026-09-14 with
`cd work/lean && lake env lean …/Statements_B.lean`: no errors; `sorry` only in the four row theorems
and three auxiliaries (`indep_partition`, `localization_of_tripleAt`, `both_orbits_occur`).
Proved with standard axioms: `skeleton_wellFormed`, `successorTable`, `residualWordTable`,
`two_colouring_bichromatic_pairs`, `isSimpleRIII_eventOfTriple`.

Fixed names (axiom-policy targets): `RProof.localization` (L456), `RProof.parity` (L567),
`RProof.fibre_partition` (L652), `RProof.generic_table` (L928). Each has the shape
`(E : CV.Event n) (e f g) (h3 h4e h4f h4g) (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) →
∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Row>Data E e f g δ`. The bundle carries the common punctured radius `δ`
as a parameter (a `Prop` structure cannot hold the datum `δ`, and the RA texts use ONE punctured
neighbourhood for all clauses); this is the same shape as the accepted `SM.triple_sides`
(SM/TripleSides.lean:87) and `CV.guardconst` (CV/Events.lean:1084).

## 0. Domain and the shared vocabulary (Statements_B.lean L258–358)

Decision F2(A): no narrowing. Every row is stated on the CV locus: `E : CV.Event n`
(CV/Events.lean:411), `E.IsSimpleRIII` (CV/Events.lean:1131, the forced bundle of ax:R with the
concurrency point and transversality). Sides are `E.curve t`, `t ≠ 0`, CV-generic
(`E.generic_punctured`); the Gauss word / interlacement live on `CrossingGeometry (E.curve t)` via
`CV.Generic.crossingGeometry` (CV/Setup.lean:1154) — the same domain on which the accepted
CV:def:interlace row is stated (`CV.Ind` CV/Events.lean:165, `CV.U` :177).

| Lean (this file) | renders | source sentence |
|---|---|---|
| `Punctured E δ t := t.val ≠ 0 ∧ |t.val| < δ` (L352) | "on a punctured neighbourhood of t = 0", "near the wall" | R-LOC-2, R-PAR |
| `Opposite E t t' := t.val * t'.val < 0` (L355) | "the two sides", `P₊`/`P₋` | all four |
| `SameSide E t t'` (L358) | one side (one CV chamber) | implicit |
| `genericAt`, `geomAt` (L343, L348) | `P(t)` CV-generic; its crossing geometry | def:event |
| `triangleSupports e f g = {{e,f},{e,g},{f,g}}` (L265) | "`T = {x_ef,x_eg,x_fg}`", "indexed by carrying edge pairs" | R-LOC-2 |
| `triangleCrossings P e f g` (L268) | `T` as actual crossings of `P` | |
| `xPair h : Crossing P` (L279) | `x_{ij}` | |
| `visitOn x h hh : Visit P` (L283) | the occurrence of `x` on edge `h` | def:interlace "two occurrences" |
| `AdjacentVisits hP v w` (L289) | "adjacent crossing-visits of the traversal circle" | R-LOC-2 (2) |
| `clump P e f g h` (L298), `InArc` (L303) | clumps `C_e,C_f,C_g`; the 2-colouring | R-PAR proof |
| `interlacedTriangle hP e f g y` (L309) | `I(y)`, "the interlaced pair" | R-PAR (P1)/(P2) |
| `avail hP e f g Q` (L316) | `avail(S')` = `𝓐(Q)` | R-PAR (P2), SPEC (1) |
| `outsideSupports hP e f g` (L323) | `Ind(G[W])` | SPEC (3) |
| `localFibre hP e f g Q` (L329) | `Ind(G_±[𝓐(Q)])` | SPEC (2) |
| `fibreSum hP e f g F Q` (L336) | `Φ_±(Q)` with abstract summand `F` | SPEC (2) |
| `instDecidableEqCrossing` (L260) | crossings compared by their edge pairs (`∪ ∩ \` on supports) | SPEC "identify the crossing sets with one finite set V" |

Cross-wall identification: clause (1) of R-LOC-2 gives `hs : ∀ s, IsCrossing (E.curve t) s ↔
IsCrossing (E.curve t') s`; crossings/visits are transported by the accepted `crossingTransport hs`
(SM/CrossingTransport.lean:12) / `visitTransport hs` (:18), which fix the support (`rfl`). Clauses that
need it quantify `∀ hs` (proof-irrelevant; supplied by `crossing_set_constant`), the shape of the
accepted `SM.TripleWallSidesData` (SM/TripleWallSides.lean:14).

Order along an edge: `CV.crossParam P e f` (CV/Setup.lean:397) is the printed `t_f` of def:guarded;
`CV.crossParam_eq_edgeParameter` (:572) identifies it with SM's `edgeParameter` (SM/Chambers.lean:86),
and `visitParameter_eq_of_support_pair_of_geometry` links it to the visit coordinate.

## 1. Row 166 — R:localization (`LocalizationData`, L374; theorem L456)

Source: R_ATTACHMENT_WARRANTS.md, "R-LOC-2 — localization", Statement lines 14–29, proof 31–100.

| RA sentence | field |
|---|---|
| "Let `T = {x_ef, x_eg, x_fg}`" (presupposes the three crossings on the punctured neighbourhood) | `triangle_crossings` |
| (1) "the crossing set, indexed by carrying edge pairs, is constant" | `crossing_set_constant` (`IsCrossing` on supports, all `t, t'` punctured) |
| (2) "on each of e,f,g the two crossings of T carried by that edge occupy adjacent crossing-visits of the traversal circle" | `adjacent` (`AdjacentVisits` of the two `visitOn`s on `e`, on `f`, on `g`) |
| (2) "and their order along that edge is opposite on the two sides" | `order_reverses` (both `<` directions, per edge, as in the accepted `TriangleOrderExchanges`) |
| implicit in "the two sides": the order is a function of the side | `order_same_side` (ADDED, see readings) |
| (3) "every other pair of crossings keeps its order along every edge" | `other_orders_persist` (two crossings on `h` not both in `T`) |
| proof (3), last sentence: "the two Gauss words differ by exactly the three transpositions of (2a)" | `gauss_words` = accepted `SM.ExactTriangleVisitOrders` (SM/TripleVisitExchanges.lean:18) |
| (4) "hence `G⁺ = G⁻ △ binom(T,2)`" | `interlace_toggle` (`Xor` with `x ≠ y ∧ x,y ∈ T`) |
| implicit in "`G⁺`, `G⁻`" | `interlace_same_side` (ADDED) |
| Corollary, sentence 1: "`G[T]` maps to its complement in `T`" | `complement_on_triangle` |
| Corollary, sentence 2: "Both orbits of that map occur" | NOT in the bundle: `both_orbits_occur` (L516), see open questions |

Readings chosen.
* "adjacent crossing-visits": `v ≠ w` and one of the two arcs cut by `v, w` contains no crossing visit
  (`traversalBetween`, SM/Traversal.lean:73, on `geometricVisitPosition`, SM/GeometricVisits.lean:12).
  This is what R-LOC-2 (2b) proves ("some punctured neighbourhood is free of them … adjacent among
  crossing visits") and what R-PAR's proof consumes ("no crossing-visit lies between the two members
  of a clump"). On the SM locus it is equivalent to the accepted list form `SM.VisitsAdjacent`
  (SM/TripleAdjacency.lean:12) / `GaussVisitsAdjacent` (SM/GaussCyclicGap.lean:25) by
  `gauss_adjacent_empty_arc` (:45) and `sorted_indices_adjacent`.
* "the crossing set": SM's `IsCrossing` (closed segments meet, SM/Crossings.lean:12). On a CV-generic
  polygon this is CV's activation `Crosses` for remote pairs (`CV.crosses_iff_isCrossing`,
  CV/Setup.lean:566); the row is stated with the accepted crossing type so that `Crossing`, `Visit`,
  `GeometricInterlaces` apply directly.
* "bundle pair" in (3): two crossings on a common edge `h` both belonging to `T` (they then share
  exactly `h`); "other pair" = `¬(both ∈ T)`. In `gauss_words` the accepted predicate uses the
  equivalent `x.val ∪ y.val = {e,f,g}`.
* Two clauses ADDED beyond the printed list: `order_same_side`, `interlace_same_side`. They are the
  content of "on the two sides" (each side is one CV chamber; guardconst on the active `G4`s) and are
  needed for `G⁺`/`G⁻`/"the order on a side" to be well defined, hence for R-PAR's "either side's
  polygon". They are not stronger than what the proof of (3) establishes. Flagged for the reviewer.
* `both_orbits_occur` is kept out of the bundle: it is an existence claim about events (two concrete
  RIII events would have to be constructed) and nothing downstream (CV:ax:R, SPEC) consumes it.

Reused: `CV.Event`, `IsSimpleRIII` (CV/Events.lean:411, 1131), `CV.crossParam` (Setup:397),
`GeometricInterlaces` (SM/GeometricInterlacement.lean:16), `crossingTransport` (CrossingTransport:12),
`ExactTriangleVisitOrders` (TripleVisitExchanges:18), `Bridge.eventOfTriple`/`B2`/`B3`
(Bridge/B1.lean:126, 339; Bridge/B3.lean:186).

SM-germ instance (the route "where the RA text is about the SM triple germ"):
`isSimpleRIII_eventOfTriple` (L467, PROVED from B2, B3 and `tripleAt_remote_and_common_point`) shows the
event of every `g.TripleAt e f k` (sorted representatives) is a simple RIII event of ax:R;
`localization_of_tripleAt` (L483, sorry) is `LocalizationData` for `Bridge.eventOfTriple hn g h`. The
accepted triple lane supplies (1)–(3) on the SM locus: `triple_wall_sides` (SM/TripleWallSides.lean:26:
crossing equivalence, `ExactTriangleParameterOrders`, `ExactTriangleVisitOrders`, `TripleSides` = the
three adjacencies as `VisitsAdjacent`, on one radius), `triple_order_exchanges`
(TripleSideExchanges:29), `triple_other_orders_sides` (:40), `triple_sides_crossing_equiv`
(TripleVisitExchanges:55).

## 2. Row 167 — R:parity (`ParityData`, L539; theorem L567)

Source: R_ATTACHMENT_WARRANTS.md "R-PAR-v6", Statement lines 105–121, proof 123–147.

| RA sentence | field |
|---|---|
| "the three crossings of T" | `triangle_card` (`(triangleCrossings …).card = 3`) — ADDED presupposition |
| (P1) "Every crossing y ∉ T interlaces exactly 0 or exactly 2 of the three crossings of T — never 1, never 3" | `parity`, first disjunct / `card = 2` |
| (P1) "Moreover the interlaced pair … is … the two crossings sharing one of the three bundle edges" | `parity`, `∃ h ∈ {e,f,g}, I(y) = T.filter (h ∈ ·.val)` |
| (P2) "For any set S' of crossings disjoint from T, avail(S') has size 3, 1, or 0 — never 2" | `trichotomy` |
| (P2) "avail(S') is the same set on the two sides of the wall" | `avail_wall_invariant` (`Finset.map (crossingTransport hs)`) |
| proof: "Write the three adjacent pairs as clumps C_e, C_f, C_g" | `clump P e f g h` (definition, L298) |
| proof: "each clump lies wholly in one of the two arcs … This is a 2-colouring" | `InArc hP u v C` (L303) |
| proof: "A 2-colouring of three objects has either 0 bichromatic pairs or exactly 2" | `two_colouring_bichromatic_pairs` (L105, PROVED by `decide`) |

Readings: "never 1, never 3", "never 2" are implied by the disjunctions (cards are of a subset of a
3-set). `y ∉ T` is `y.val ∉ triangleSupports`. `avail` is stated with `¬ GeometricInterlaces hP q x`
(q ∈ S'); the relation is symmetric (`geometricInterlaces_symm`).

## 3. Row 169 — R:fibre_partition (`FibrePartitionData`, L598; theorem L652)

Source: R_ASSEMBLY_SPEC.md paragraphs 2–4, displays (1)–(3).

| SPEC sentence | field |
|---|---|
| "use its carrying-edge labels to identify the crossing sets with one finite set V" | `crossingTransport hs` on supports (vocabulary) |
| "both graphs induce the same graph on W" | `graph_on_W_same` |
| "and have the same adjacencies between W and T" | `W_to_T_same` |
| (1) `𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}` | `avail` (L316) |
| "It is the same on both sides" | `avail_same` (for `Q ∈ Ind(G[W])`) |
| "Every independent support S … decomposes uniquely into Q = S ∩ W and J = S ∩ T. Q is independent in the outside graph. J is independent in the local graph and belongs to the availability set" | `decompose` (`S = (S\T) ∪ (S∩T)`, disjoint, `S\T ∈ outsideSupports`, `S∩T ∈ Ind`, `S∩T ⊆ avail (S\T)`) |
| "Conversely, these three conditions imply that Q ∪ J is independent" | `compose` |
| "This proves a bijection of supports" | `bijection` (`Set.BijOn (S ↦ (S\T, S∩T)) Ind {(Q,J) | Q ∈ Ind(G[W]), J ∈ localFibre Q}`) |
| (2) `Φ_±(Q) = Σ_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J)` | `fibreSum` (L336) |
| (3) "The finite bijection … partitions the exact state sum, so X₁(P_±) = Σ_Q Φ_±(Q)" | `state_sum_partition` — X₁-FREE FORM: for every `F : Finset (Crossing P) → M`, `Σ_{S ∈ Ind} F S = Σ_Q Φ(Q)` |

X₁ flag. `F_±(S)`, "the complete summand of CV def:X1", and `X₁` are not in Lean (CV:def:X1 is blocked on
the diagram/record layer; scout §5 row 146). What (3) asserts about X₁ is precisely
`state_sum_partition` applied to `F := F_±` once `X₁(P) = Σ_{S ∈ Ind(G_P)} F(S)` exists; no other
property of `F_±` is used ("Equality is preserved by finite summation"). The specialisation is a
one-line corollary to be added when def:X1 lands (then `F_±` must be evaluated at supports of the
respective side; `Φ₊` and `Φ₋` use `fibreSum` at `t` and `t'`). The abstract engine is
`indep_partition` (L89, sorry): the same identity for an arbitrary finite `SimpleGraph`, with
`graphAvail` (L81); the row's `state_sum_partition` is its instance at `geometricInterlacementGraph`
with `T := triangleCrossings`.

Not duplicated here (belongs to R:parity, cited by the SPEC between (3) and (4)): "availability has
size three, one or zero" = `ParityData.trichotomy`.

## 4. Row 171 — R:generic_table (`GenericTableData`, L738; theorem L928)

Sources: R_GENERIC_ORBIT_ACTUAL_TABLE.md (whole file); the sign classification it cites in
R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, sections "Oriented line-order calculation" (1)–(3) and "Which
pair is selected" (4) + table; the canonical branch (1) of R_GENERIC_COMMON_TRANSPORT_PROOF.md.

Vocabulary (L670–736): `strandSign P i j = sgn G5_{ij}` (`s_a = strandSign e f`, `s_b = strandSign e g`,
`s_c = strandSign f g`), `concurrenceSign = sgn G3` (`δ`), `orderSign P h i j = sgn(t_hi − t_hj)`
(`q_e = orderSign e f g`, `q_f = orderSign f e g`, `q_g = orderSign g e f`), `IsAlternating`,
`SelectedAB/AC/BC` (all decidable), `triangleVisits hP e f g` (the T-visits of the geometric Gauss list
in traversal order), `blockWord`, `wordPVisits`, `wordEVisits`.

| source sentence | field |
|---|---|
| "All four quantities are nonzero on either chamber" | `nonzero` |
| NONSELECTED (1), the three Cramer identities | `cramer` (with `Δ = CV.G3`, `D_ij = CV.G5`) |
| NONSELECTED (2) `(q_e,q_f,q_g) = −δ(s_a s_b, s_a s_c, s_b s_c)` | `sign_vector` |
| NONSELECTED (3) edge(a,b) iff q_e = −1; edge(a,c) iff q_f = +1; edge(b,c) iff q_g = −1 | `edges_iff` |
| "Changing chamber changes the sign of Δ, so (2) negates all three q's" | `chamber_change` (also `s` constant: active G5, guardconst) |
| "The local graph is extreme exactly when … s_a = s_c = −s_b … the generic orbit is exactly the other six" | `orbit_classification` (via `localEdgeCount ∈ {0,3}` / `{1,2}`) |
| "six generic nonalternating sign branches and two extreme alternating branches" | `branch_count` (finite count over nonzero sign triples) |
| NONSELECTED (4) + six-case table; "exactly one condition in (4) holds" | `selected_unique` |
| "the P3 graph on either chamber has as its degree-two vertex the crossing complementary to that pair. Thus the unique separating-strand pair is precisely the graph-selected pair" | `selected_is_graph_selected` |
| "After erasing every outside visit, the traversal encounters the e, f, g two-crossing blocks in that order" | `local_word` (`triangleVisits ~r blockWord`) |
| TABLE: "P = a b A a c B b c C (edges ab, bc; centre b); E = b a A c a B c b C (edge ac; b isolated)" | `canonical_words` (canonical branch `s_a=s_b=s_c`: P is the side `δ=+1`, E the side `δ=−1`) |
| TABLE: "The supports ab, bc, T are absent on P; ac, T are absent on E" (+ the listed present rows) | `local_supports` |
| TABLE: "Local undominated table" | `local_undominated` (`CV.U hP S ∩ T`, plus "b → ac (connected)" as `a ~ c`) |
| TABLE: "Full availability plus R-PAR sharpens the exterior masks … twins … only mask-zero outsiders survive" | `exterior_masks` |
| TABLE: "Successor cycles" (11 rows) | `successor_table : SuccessorTable` (L183; PROVED on the skeleton) |
| TABLE: residual words (`c B c C`/`b B b C`, `a A a C`/`b A b C`, `C|AB`, `a A c a B c`, `C|A|B`) | `residual_words : ResidualWordTable` (L225; PROVED) |
| TABLE: "The exact generic obligations are consequently: …" | not a claim (list of rows 172–174); omitted |

Readings chosen.
* Labels: `a = x_ef = (u_1,u_2)`, `b = x_eg = (u_1,u_3)`, `c = x_fg = (u_2,u_3)` (COMMON_TRANSPORT),
  `e < f < g` in representatives (ax:R). The block order `e, f, g` is the traversal order of the edges
  up to rotation (`traversalKey`), hence `List.IsRotated`.
* Which side is "P": from (2), `q = (−,−,−)` (word `a b | a c | b c`) iff `δ·s_a s_b = δ·s_a s_c = δ·s_b s_c = 1`,
  which in the canonical branch is `δ = +1`; `E` is `δ = −1`. Checked by hand and numerically
  (Cramer identities verified against the accepted `G3 = concurrenceDet`).
* The successor-cycle and residual-word tables are stated on an abstract LOCAL SKELETON
  (`wordP/twinP`, `wordE/twinE : Fin 9 → …`, `localSucc` = "reconnect the traversal at the two visits of
  each selected crossing", gaps `A,B,C` as single opaque positions = "fixed boundary-to-boundary
  successor paths"). This is the finite computation the TABLE performs and is proved (`decide`). NOT
  stated (needs the Carrier lane / CV:def:smoothing, F2-blocked): the identification of the skeleton
  cycles with the actual carriers `smoothingSuccessor`/`Component` of `Q ∪ J` on `E.curve t` after
  collapsing each exterior gap (R-EXTERIOR-1 §1, "arbitrary-Q successor lift" (2a)). Flagged.
* `exterior_masks` is stated as the P1-consequence "an outside crossing non-adjacent to one triangle
  crossing is adjacent to both or neither of the other two" without the full-availability/`Q`
  hypothesis of the TABLE sentence (which is exactly this fact applied to survivors). Equivalent
  content, simpler binder; flagged.

Reused: `CV.G3/G5/crossParam` (Setup:387,383,397), `CV.G3_eq_concurrenceDet` (:450),
`SM.concurrenceDet_order_identity` (SM/ConcurrenceOrder.lean:14 — already the first Cramer identity up
to sign convention), `CV.Generic.g3/g4/g5/crossParam_ne` (Setup:1096–1130), `geometricGaussList`
(GeometricVisits:51), `CV.U`, `CV.Ind`.

## 5. Open questions (for the executor / reviewers)

1. Rows carry `∃ δ … ∧ <Row>Data E e f g δ` rather than a bare `<Row>Data`. Acceptable, or should a
   `def <Row>Statement E e f g : Prop := ∃ δ, …` wrapper be the reviewed type?
2. `LocalizationData.order_same_side` / `interlace_same_side` (constancy on one side) are not in the
   printed list (1)–(4). Keep (recommended: they are what "the two sides" means and what R-PAR's
   "either side's polygon" needs) or move to a separate lemma?
3. Corollary sentence "Both orbits of that map occur": kept as the separate `both_orbits_occur` (not
   consumed by ax:R). Drop, keep sorried, or prove with two explicit hexagon events?
4. `ParityData.triangle_card` and `LocalizationData.triangle_crossings` make the presupposition
   "the three crossings of T" explicit. Fine?
5. R:fibre_partition (3) is X₁-free (`∀ F`). When CV:def:X1 lands, add the one-line specialisation
   `X₁(E.curve t) = Σ_Q fibreSum … F_t Q` as a further field or as a corollary?
6. R:generic_table: is the abstract skeleton (`SuccessorTable`, `ResidualWordTable`) an acceptable
   rendering of the TABLE's "proved at … successor-cycle level", with the skeleton↔carrier
   identification recorded as a separate obligation of rows 172–174 (where the table is consumed)?
7. `crossParam` (CV) vs `edgeParameter` (SM) in the order clauses: CV-native chosen; the SM triple lane
   proves the `edgeParameter` form (`crossParam_eq_edgeParameter` bridges).
8. Should the R rows also be stated with `hn : 3 ≤ n`? Omitted (derivable from `h3`; the CV rows omit it).

## 6. Proof-lane sketch and estimates

R:localization (~600 lines total).
* Route A (SM germ first, then transport; the scout's "START NOW"): `localization_of_tripleAt` from
  `triple_wall_sides` (SM/TripleWallSides.lean:26): (1) = `g1_center_side_crossings`
  (GermG1Crossings:12) on each side + `triple_sides_crossing_equiv` across; (2)-reversal =
  `triple_order_exchanges` after `crossParam_eq_edgeParameter`; (2)-adjacency = `TripleSides`
  (`VisitsAdjacent`) → `AdjacentVisits` via `gauss_adjacent_empty_arc`, `geometricVisitPosition_eq_generic`
  (~120); (3) = `triple_other_orders_sides` (~40); `gauss_words` = `triple_exact_visit_orders` (rfl
  modulo `eventOfTriple_sideCurve`); (4) from `gauss_words` + `interlaces_iff_count` /
  `geometricInterlaces_iff_unique` (CV/Events.lean:136): count visits on the arc, transposition of two
  adjacent visits flips membership for the pair and preserves it otherwise (~200, the core of R-LOC-2
  (4)); same-side clauses from the chamber-path constancy `generic_family_*` (~60); punctured radius
  `δ` from `triple_wall_sides`' third clause and `eventually_center_iff_radius` (~40).
* Then `localization` for CV events: either (i) redo the six Triple* lemmas on `CrossingGeometry`
  with CV guardconst (`CV.guardconst`, `Generic.g4`, `G4_factorization`) — the modules use
  `edgeParameter`, not `SM.Generic`, so mostly binder changes (~300 extra) — or (ii) a domain-transfer
  lemma. (i) recommended.

R:parity (~300): from `LocalizationData.adjacent`: each clump avoids `y`'s visits and lies in one
arc (`traversalBetween` trichotomy, ~80); "x interlaces y iff its two clumps have different colours"
(`geometricInterlaces_iff_unique`, ~80); the count by `two_colouring_bichromatic_pairs` after
abstracting the three clumps to `Fin 3` (~60); (P2) card case analysis on subsets of a 3-set (~40);
wall invariance from `interlace_toggle` restricted to `T`-to-outside pairs (~40).

R:fibre_partition (~200): `indep_partition` by `Finset.sum_bij`/`sum_sigma` on `S ↦ (S \ T, S ∩ T)`
(~120, pure Mathlib); the event clauses are `interlace_toggle` specialised (W–W, W–T pairs, ~40) and
the instance of `indep_partition` at `geometricInterlacementGraph` (~40).

R:generic_table (~450): `cramer` from `concurrenceDet_order_identity` + `G3_eq_concurrenceDet` +
`det_swap` (three `field_simp; ring`, ~60); `sign_vector` by `sign_mul`, `sign_div`, `sign_neg`
(~40); `edges_iff` from the block structure of `geometricGaussList` (edges visited in `val` order)
and `geometricInterlaces_iff_unique` (~150, the only geometric part); `chamber_change` from
`IsSimpleRIII` transversality of `G3` and `CV.guardconst` on the three active `G5` (~50); the
classification, tables and counts are finite case analyses on `SignType` (`decide` after abstracting,
~60); `local_word`/`canonical_words`: sortedness of the geometric Gauss list (~60);
`local_supports`/`local_undominated`: `CV.mem_Ind_iff`, `mem_U` + `edges_iff` (~40); `exterior_masks`
from `ParityData.parity` (~20); `successor_table`, `residual_words`: done.
