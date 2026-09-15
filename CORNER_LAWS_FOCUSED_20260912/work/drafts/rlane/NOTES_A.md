# R lane, designer A — notes for Statements_A.lean

File: `work/drafts/rlane/Statements_A.lean` (compiles with `lake env lean`; exactly four `sorry`
warnings, one per row theorem: `RProof.localization`, `RProof.parity`, `RProof.fibre_partition`,
`RProof.generic_table`). Written 2026-09-14 (statement-designer subagent A of the pod executor).

Method: spec-first. Each row is a `structure <Row>Data (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop`
with one field per printed/specified clause, the clause quoted in the field docstring, and
`theorem RProof.<name> (hn) (E) (e f g) (h3 h4e h4f h4g) (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Row>Data E e f g δ`. The radius `δ` carries "on a punctured neighbourhood
of `t = 0`" (R-LOC-2) / "near the wall" (R-PAR-v6); a `Prop`-structure cannot hold the radius as data,
so it is the existential in the theorem and a parameter of the bundle.

## 0. Domain and the standing identifications

* **Domain (F2(A), no narrowing).** All four rows are stated for a CV event `E : CV.Event n`
  (CV/Events.lean:411) with `E.IsSimpleRIII e f g h3 h4e h4f h4g` (CV/Events.lean:1131), i.e. exactly
  the domain of the printed CV ax:R (d10_axioms.tex:18–24): zero set the forced bundle, `e<f<g` in
  `CV.rep`, pairwise remote, concurrent at an interior point, transversal. The four side-condition
  binders `h3 h4e h4f h4g` are those of `IsSimpleRIII` itself. `hn : 3 ≤ n` is carried for uniformity
  with the library (it follows from the remoteness data; harmless).
* **Where the RA text is about the SM germ.** R-LOC-2's statement is about the CV event; nothing in the
  RA files is stated for the SM germ only. The SM triple germ `SM.WallGerm.TripleAt`
  (SM/NamedWallPredicates.lean:30) reaches these rows through `Bridge.eventOfTriple` (Bridge/B1.lean:126),
  `Bridge.B2` (zero set, Bridge/B1.lean:339) and `Bridge.B3_unsorted` (transversality,
  Bridge/B3.lean:207): for that event, `IsSimpleRIII` holds after sorting the triple
  (`Bridge.exists_sorted_tripleAt`, Bridge/B1.lean:405). The accepted lem:triple-sides lane then proves
  clauses (1)–(3) of R-LOC-2 on SM-generic sides (see §5). The module docstring says so.
* **Punctured sides.** `RProof.Punctured E δ t := t.val ≠ 0 ∧ |t.val| < δ`; `OppositeSides E s t :=
  s.val * t.val < 0`; `SameSide E s t := 0 < s.val * t.val`. Every punctured value is CV-generic
  (`E.generic_punctured`) hence `SM.CrossingGeometry` (`CV.Generic.crossingGeometry`,
  CV/Setup.lean:1154); `RProof.sideGeometry E ht` is that proof. All CV objects of def:interlace are
  read through it: `SM.GeometricInterlaces` (SM/GeometricInterlacement.lean:16),
  `SM.geometricInterlacementGraph` (:31), `SM.geometricVisitPosition` (SM/GeometricVisits.lean:12),
  `SM.geometricGaussList` (:51), `CV.Ind`/`CV.N`/`CV.U` (CV/Events.lean:165/171/177).
* **Crossings across the wall.** "the crossing set, indexed by carrying edge pairs" (R-LOC-2 (1)) is
  rendered by the accepted `SM.Crossing P = {s : Finset (ZMod n) // IsCrossing P s}`
  (SM/Crossings.lean:12–15). Statements that compare the two sides are written on supports:
  `SupportInterlaces hP a b := ∃ x y : Crossing P, x.val = a ∧ y.val = b ∧ GeometricInterlaces hP x y`
  and `supports P S := S.image Subtype.val`. No transport bijection is chosen in any statement (the
  proof lane can use `SM.crossingTransport` (SM/CrossingTransport.lean:12) once clause (1) is proved).
* **The triangle.** `triangleSupports e f g = {{e,f},{e,g},{f,g}}`; `triangle P e f g : Finset (Crossing P)`
  = the crossings with those supports. Names as in the RA files: `a = x_{ef}`, `b = x_{eg}`,
  `c = x_{fg}` (R_GENERIC_COMMON_TRANSPORT_PROOF.md "a=(u1,u2), b=(u1,u3), c=(u2,u3)").
* **Orders along an edge.** CV's `t_f` is `CV.crossParam P e f` (CV/Setup.lean:397); it equals SM's
  `edgeParameter` (SM/Chambers.lean:86) by `CV.crossParam_eq_edgeParameter` (CV/Setup.lean:572), which
  is how the accepted SM order predicates (`SM.TriangleOrderExchanges`, SM/TripleExchanges.lean:20;
  `SM.TripleUnchangedOrders`, SM/TripleOrder.lean:44; `SM.ExactTriangleParameterOrders`,
  SM/TripleVisitExchanges.lean:11) become the fields `order_reverses`, `other_orders_persist`.
* **Visits and adjacency.** A crossing-visit is `SM.Visit P` (SM/GaussVisits.lean:17); "the visit of
  `x_{ef}` on `e`" is `SM.pairVisit hef` (SM/PairVisits.lean:11). "adjacent crossing-visits of the
  traversal circle" is `RProof.GaussAdjacent hP v w`: `v ≠ w` and one of the two open arcs between them
  (`SM.traversalBetween`, SM/Traversal.lean:73) contains no crossing visit. This is the empty-arc form
  of the accepted `SM.GaussVisitsAdjacent` (SM/GaussCyclicGap.lean:25; the implication is
  `SM.gauss_adjacent_empty_arc`, :45). It is chosen over `SM.VisitsAdjacent` (SM/TripleAdjacency.lean:12,
  linear `idxOf` adjacency) because it is defined on `CrossingGeometry` (needs no `SM.Generic`), is
  manifestly cyclic, and is what R-PAR's proof consumes ("no crossing-visit lies between the two members
  of a clump").
* **Classical decidability.** `open scoped Classical` (low priority) supplies `DecidableEq (Crossing P)`
  for the `Finset` operations; the derived instances of the abstract table still win, so its clauses
  remain `decide`-able (verified, §6).

## 1. R:localization (`RProof.localization`, R_ATTACHMENT_WARRANTS.md:12–101)

Field ↔ clause:

| field | RA text |
|---|---|
| `triangle_present` | "Let `T = {x_{ef}, x_{eg}, x_{fg}}`" — the presupposition that the three bundle pairs are crossings on every punctured value (from the activation of the `G3` member of `Z` + constancy of activation, cf. `Bridge.crosses_const`, Bridge/B1.lean:218, for the SM germ). |
| `crossing_set_constant` | (1) "the crossing set, indexed by carrying edge pairs, is constant" — `∀ s t punctured, ∀ c, IsCrossing (E.curve s) c ↔ IsCrossing (E.curve t) c`. |
| `adjacent` | (2) "on each of `e, f, g` the two crossings of `T` carried by that edge occupy adjacent crossing-visits of the traversal circle" — `GaussAdjacent` of `pairVisit hef, pairVisit heg` (on `e`), `pairVisit hfe, pairVisit hfg` (on `f`), `pairVisit hge, pairVisit hgf` (on `g`); exactly the visit pairs of the accepted `SM.TripleSides` (SM/TripleSides.lean:20). |
| `order_reverses` | (2) "and their order along that edge is opposite on the two sides" — for `OppositeSides s t`, `t_ef < t_eg` at `s` iff `t_eg < t_ef` at `t`, and likewise on `f`, `g`. One `↔` per edge suffices because generic sides have no ties (`CV.Generic.crossParam_ne`, CV/Setup.lean:1130). Reading: "order" is the strict parameter order; no product-sign form is imposed. |
| `other_orders_persist` | (3) "every other pair of crossings keeps its order along every edge" — `∀ i j k, IsCrossing {i,j} → IsCrossing {i,k} → {i,j,k} ≠ {e,f,g} → (order at s ↔ order at t)` across the wall; the shape of `SM.TripleUnchangedOrders`. |
| `same_side_orders` | "on a punctured neighbourhood": constancy of every order (bundle pairs included) on one side — needed for `G^±` to be well defined; the RA statement presupposes it. |
| `triangle_pairs_toggle` | (4) "`G^+ = G^- △ binom(T,2)`: the three internal pairs of `T` toggle" — for distinct `a, b ∈ triangleSupports`, `SupportInterlaces_s a b ↔ ¬ SupportInterlaces_t a b`. |
| `other_pairs_unchanged` | (4) "and no other pair changes". |
| `same_side_graph` | the graph is constant on each side (the two graphs `G^±`). |
| `induced_graph_complement` | Corollary, "The induced graph `G[T]` maps to its complement in `T` across the wall" — the three local edges `EdgeAB/AC/BC` each flip. |
| `orbit_preserved` | Corollary, "Both orbits of that map occur — the extreme orbit (empty ↔ complete) and the one-edge ↔ two-edge orbit" — rendered as the exhaustive, wall-invariant dichotomy `Extreme_s ↔ Extreme_t` (the case split the assembly consumes). **Not rendered:** the existence assertion that events of each orbit exist; it is illustrative, consumed by no proof, and would require constructing two explicit events. Open question Q1. |

Readings recorded: the three clauses (1)–(3) are stated on parameters in the same punctured
neighbourhood, arbitrary sides; "the two sides" = `OppositeSides`. Clause (2)'s adjacency is stated per
side (a property of one polygon). Clause (4) is stated on supports, which is the only meaningful
cross-wall comparison of graphs on different crossing types.

## 2. R:parity (`RProof.parity`, R_ATTACHMENT_WARRANTS.md:103–148)

| field | RA text |
|---|---|
| `two_colouring` | proof core, R_ATTACHMENT_WARRANTS.md:136–141: "A 2-colouring of three objects has either 0 bichromatic pairs (monochromatic) or exactly 2 (the odd object pairs bichromatically with each of the other two, while those two pair monochromatically). Never 1, never 3." — `∀ χ : Fin 3 → Bool, (∀ i j, χ i = χ j) ∨ ∃ h, ∀ i ≠ j, (χ i ≠ χ j ↔ (i = h ∨ j = h))`. Decidable tautology (verified by `decide`). Optional: a reviewer may drop it as a proof step; it is the "clump/2-colouring lemma" of the executor's work list. |
| `clumps` | "Write the three adjacent pairs as clumps `C_e = {visits of x_{ef}, x_{eg} on e}`, `C_f`, `C_g`. Each crossing of `T` has one visit in each of two clumps." — `clump P e f g h` (the triangle visits on edge `h`); every triangle visit lies in one of the three clumps and each clump has two elements. |
| `clump_monochromatic` | "no crossing-visit lies between the two members of a clump (adjacency), so neither `u` nor `v` lies inside a clump: each clump lies wholly in one of the two arcs that `u, v` cut `Γ` into" — for the two visits `u ≠ v` of `y ∉ T`, the two visits of each clump have the same `ArcSide` (membership in the arc from `u` to `v`). |
| `parity` | **(P1)** "Every crossing `y ∉ T` interlaces exactly 0 or exactly 2 of the three crossings of `T`" — `(interlacedTriangle hP e f g y).card = 0 ∨ = 2`. |
| `interlaced_pair` | **(P1)** "Moreover the interlaced pair, when nonempty, is one of `{x_ef,x_eg}`, `{x_ef,x_fg}`, `{x_eg,x_fg}`" — `mask hP e f g y ∈ {{{e,f},{e,g}}, {{e,f},{f,g}}, {{e,g},{f,g}}}` as an explicit disjunction. |
| `trichotomy` | **(P2)** "For any set `S'` of crossings disjoint from `T`, `avail(S')` has size 3, 1, or 0 — never 2" — `S'` is any `Finset (Crossing P)` disjoint from `T` (independence is *not* assumed, as printed). |
| `avail_wall_invariant` | **(P2)** "And `avail(S')` is the same set on the two sides of the wall" — for `S'` on side `s` and `S''` on side `t` with the same supports, the availability sets have the same supports. Quantified over all punctured `s, t` (same or opposite side). |

Definitions: `avail hP T Q := T.filter (fun x => ∀ y ∈ Q, ¬ GeometricInterlaces hP x y)` renders both
"`avail(S') = {x ∈ T : x interlaces no member of S'}`" and the spec's `𝓐(Q)`; `interlacedTriangle`,
`mask`, `clump`, `ArcSide` as documented in the file.

## 3. R:fibre_partition (`RProof.fibre_partition`, R_ASSEMBLY_SPEC.md (1)–(3); OPEN_WORK.md item 1)

The spec's argument is a statement about a finite graph, a distinguished 3-set `T` and an arbitrary
summand; the X₁-dependent content is only *which* summand. So the bundle has an abstract half
(arbitrary `V : Type`, `G : SimpleGraph V`, `T : Finset V`) and a CV half (each punctured side,
`G := geometricInterlacementGraph`, `T := triangle`, `Ind := CV.Ind`).

Definitions: `indepSets G := univ.powerset.filter (G.IsIndepSet ↑·)` ("`Ind(G)`, including `∅`";
same shape as `CV.Ind`, CV/Events.lean:165); `availSet G T Q := T.filter (fun x => ∀ q ∈ Q, ¬ G.Adj q x)`
(spec (1)); `fibreSum G T F Q := ∑ J ∈ (indepSets G).filter (· ⊆ availSet G T Q), F (Q ∪ J)` (spec (2):
`Ind(G[𝓐(Q)])` = independent sets contained in `𝓐(Q)`).

| field | spec text |
|---|---|
| `abstract_decompose` | "Every independent support `S` on either side decomposes uniquely into `Q = S ∩ W` and `J = S ∩ T`. `Q` is independent in the outside graph. `J` is independent in the local graph and belongs to the availability set" — `(S \ T) ∪ (S ∩ T) = S`, `Disjoint (S \ T) T`, `S \ T ∈ Ind`, `S ∩ T ∈ Ind`, `S ∩ T ⊆ 𝓐(S \ T)` (`W = Tᶜ`, so `S ∩ W = S \ T`). |
| `abstract_compose` | "Conversely, these three conditions imply that `Q ∪ J` is independent … This proves a bijection of supports" — `Q ∪ J ∈ Ind`, `(Q ∪ J) \ T = Q`, `(Q ∪ J) ∩ T = J` (uniqueness = the two maps are inverse). |
| `abstract_partition_sum` | (2)+(3) "The finite bijection just established partitions the exact state sum, so `X₁(P_±) = ∑_{Q ∈ Ind(G[W])} Φ_±(Q)`" — `∑_{S ∈ Ind} F S = ∑_{Q ∈ Ind, Disjoint Q T} fibreSum G T F Q` for every `F : Finset V → ℤ`. |
| `outside_graph_unchanged` | "R-LOC-2 says only the three internal pairs of `T` toggle. Consequently both graphs induce the same graph on `W` and have the same adjacencies between `W` and `T`." |
| `avail_wall_invariant` | (1) "It is the same on both sides because the `W`-to-`T` adjacencies are unchanged" (for independent outside `Q`, on supports). |
| `decompose`, `compose`, `partition_sum` | the CV instances of the three abstract fields on each punctured side (`CV.Ind (sideGeometry E ht)`, `triangle (E.curve t) e f g`). |
| `avail_card` | "Thus availability has size three, one or zero" (the spec's paragraph after "Prove R-PAR-v6(P1) before using availability sizes"; OPEN_WORK item 1 "availability sizes 0, 1 or 3 on both sides"). |

**X₁ flag.** `F_±(S)`, "the complete summand of CV def:X1 at `S` on that side, including the selector and
every carrier coefficient with the printed empty conventions", is not in Lean (row 146 blocked by the
diagram/record layer). The partition holds for *every* summand, so (3) is stated for arbitrary
`F : Finset (Crossing P) → ℤ`; when `CV.X1` lands, (3) is `partition_sum … (fun S => wind S * ∏ L, Ω₁ S L)`
plus the unfolding of def:X1 — no new obligation. `Φ_±(Q)` is `fibreSum` with that `F`. The integer
codomain is def:X1's (`Ω₁` is a coefficient in `ℤ`, `wind ∈ {0,±1}`); if X₁ is later valued in a
different `AddCommMonoid`, generalise the codomain of `F` (the proof does not depend on it).

Reading: "`Q` in `W`" and "independent in the outside graph" = `Q ∈ Ind ∧ Disjoint Q T` (independence in
`G[W]` for `Q ⊆ W` is independence in `G`).

## 4. R:generic_table (`RProof.generic_table`, R_GENERIC_ORBIT_ACTUAL_TABLE.md; sign classification of R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (1)–(4))

Two parts.

**Part A — the printed table, abstractly (`RProof.LocalTable`).** "Use the three unchanged exterior gaps
`A,B,C` between the RIII strand blocks: `P = a b A a c B b c C` (edges ab, bc; centre b),
`E = b a A c a B c b C` (edge ac; b isolated)." The finite model: `Letter = a | b | c | A | B | C`,
`wordP wordE : Fin 9 → Letter`; the table's visit numbers `1..6` are positions `0,1,3,4,6,7`, the gaps
`A,B,C` positions `2,5,8`. `Interlaces w ℓ ℓ'` is CV:def:interlace on the word (exactly one visit of `ℓ'`
strictly between the two visits of `ℓ`); `Indep`, `undominated` (`U(J) ∩ T` of def:pieces) follow.
Oriented smoothing at the selected letters `S`: `succ w S i := (if w i ∈ S then partner w i else i) + 1`
— the traversal successor after exchanging the two visits of every selected crossing, i.e. the
reconnection `p ↦ q+1, q ↦ p+1` (the Carrier lane's `smoothingSuccessor = selectedMarkPerm ∘
markSuccessor` on the six local marks). A row's successor cycles are `IsCycleDecomposition (succ w S) ls`
(each list a cycle, the lists together a permutation of `0..8`); the residual word of a cycle is its
letters with selected and dominated local crossings erased (`residual`).

| field | table text |
|---|---|
| `graph_P`, `graph_E` | "(edges ab, bc; centre b)", "(edge ac; b isolated)". |
| `cycles_P_empty … cycles_E_bc` (11 fields) | the "Successor cycles" block, row by row; e.g. "P b : (126)[C](345)[AB]" = `[[0,1,7,8],[3,4,5,6,2]]`. |
| `present_absent` | "The supports ab,bc,T are absent on P; ac,T are absent on E" + the tabulated rows are present. |
| `undominated_P`, `undominated_E` | "Local undominated table" including "b -> ac (connected)" (`Interlaces wordE a c`). |
| `residual_endpoint_a`, `residual_endpoint_c`, `residual_selected` | "For endpoint a, the unsigned residual word is c B c C on P versus b B b C on E, with the A-carrier unchanged. For endpoint c, it is a A a C versus b A b C, with the B-carrier unchanged. For the selected row, P-b has no local residual on carriers C\|AB; E-b has residual a A c a B c on AB …; and P-ac has three local-empty carriers C\|A\|B." |

Every Part-A field was machine-checked by `decide` against these exact definitions (§6).

**Carrier flag (not statable without def:smoothing).** The table's status line "proved at unsigned graph,
mask, residual-word, and successor-cycle level" is about the actual carriers of the event's polygons
after smoothing `Q ∪ J`. The identification "abstract successor cycle on the six local marks with the
three gap symbols = the actual carrier, with `A,B,C` the boundary-to-boundary successor paths after the
`Q`-smoothings" (the "arbitrary-Q successor lift (2a)" of R_GENERIC_COMMON_TRANSPORT_PROOF.md) needs
CV:def:smoothing / lem:carriers on the CV locus (rows 135–137, deferred under F2(A)) and is **not
asserted** here. What *is* asserted on the event (Part B, `local_word`, `canonical_words`) is that the
six triangle visits of each side form the three blocks in cyclic order `e, f, g` with the printed
internal orders — the unsigned word content that the abstract table takes as input.

**Part B — on the event's sides.** Sign data (all on CV's own guards): `strandSign P i j = sgn G5_{i,j}`
(`s_a, s_b, s_c` = `strandSign e f, e g, f g`), `concurrenceSign = sgn G3_{e,f,g}` (`delta`),
`orderSign P i j k = sgn (t_ij − t_ik)` (`q_e = orderSign e f g`, `q_f = orderSign f e g`,
`q_g = orderSign g e f`), `Alternating` (`s_a = s_c = −s_b`), `SelectedAB/AC/BC` ((4)).

| field | text |
|---|---|
| `nonzero` | "All four quantities are nonzero on either chamber of a simple wall." |
| `cramer` | (1) the three Cramer identities `t_ef − t_eg = −Delta/(D_ef D_eg)`, etc. Sign convention checked against CV's `G4_factorization` (CV/Setup.lean:587) with `G4 = −G3`, `G4 P f e g = G3`, `G4 P g e f = −G3` (CV/Setup.lean:437/441/445) and numerically (§6). |
| `sign_identity` | (2) `(q_e,q_f,q_g) = −delta (s_a s_b, s_a s_c, s_b s_c)` in `SignType`. |
| `edge_reading` | (3) "edge(a,b) is present iff `q_e = −1`, edge(a,c) iff `q_f = +1`, edge(b,c) iff `q_g = −1`" — `EdgeAB ↔ orderSign e f g = neg`, `EdgeAC ↔ orderSign f e g = pos`, `EdgeBC ↔ orderSign g e f = neg`. (Depends on the block structure of R-LOC-2 (2); consumes R:localization.) |
| `wall_toggle` | "Changing chamber changes the sign of Delta, so (2) negates all three q's; (3) therefore toggles exactly the three local graph edges, consistently with R-LOC" — `delta` flips, the three strand signs are constant (active `G5` members outside `Z`, `CV.guardconst`), the three `q` negate. |
| `extreme_iff` | "The local graph is extreme exactly when all three indicators in (3) agree. That requires `(q_e,q_f,q_g)` to be `(−,+,−)` or `(+,−,+)` … equivalent to `s_a = s_c = −s_b`" — both equivalences. |
| `generic_iff` | "Therefore the generic orbit is exactly the other six, nonalternating triples." |
| `exactly_one_selected` | (4) "For each nonalternating sign triple exactly one condition in (4) holds" (the six-row table). |
| `selected_is_graph_selected` | (4) "the P3 graph on either chamber has as its degree-two vertex the crossing complementary to that pair. Thus the unique separating-strand pair is precisely the graph-selected pair" — in the generic orbit: `SelectedAC ↔ (P3 with centre b) ∨ (one edge ac)`, and cyclically for `AB` (centre c / edge ab) and `BC` (centre a / edge bc). The one-edge side is included because the table's `E` calls `ac` the selected pair there. |
| `local_word` | "After erasing every outside visit, the traversal encounters the e, f, and g two-crossing blocks in that order" — `triangleWord hP e f g` (the `Cycle` of triangle-visit supports in `geometricGaussList` order) equals `blockE q_e ++ blockF q_f ++ blockG q_g` as a cyclic word. Stated as a `Cycle` because the SM traversal cut is at edge `0`, which may be `g` (`CV.rep 0 = n`). |
| `canonical_words` | the printed `P`, `E` as the event's words in the canonical branch `s_a = s_b = s_c` (R_GENERIC_COMMON_TRANSPORT_PROOF.md (1)): `P` where `Delta > 0`, `E` where `Delta < 0` (from (2),(3); checked numerically). Other generic branches are the label/block rotations the table calls "the same mechanism after permuting labels" — not rendered separately (Q3). |
| `mask_sharpening` | "Full availability plus R-PAR sharpens the exterior masks: after a, survivors have mask 0 or bc, so b,c are twins; after c, mask 0 or ab …; after b, mask 0 or ac …; after any present pair only mask-zero outsiders survive." — survivors are `CV.U hP (insert x Q)` (def:pieces), masks as `mask`; full availability = `avail Q = triangle`. |

Not rendered (descriptive, not claims): the paragraph "The exact generic obligations are consequently: …"
(an obligation list for rows 173–174), "The graph-selected generic complement couple in these labels is
therefore b/ac. The abstract c/ab notation … is the same mechanism after permuting labels" (a naming
remark), and the whole "Earliest remaining interface" section except its classification sentence (which
is (2)–(4) above); its selector-vanishing claim is row 172 R:generic_selector's.

## 5. Proof-lane sketch and estimates

* **R:localization (~650 lines on the CV locus; ~350 if first done for `Bridge.eventOfTriple` only).**
  (1) `crossing_set_constant`, `triangle_present`: activation of every pair is constant on a punctured
  neighbourhood (all `G2` members are unconditional and outside `Z`: `CV.guardconst` (CV/Events.lean:1084)
  + `CV.Generic.crosses_iff` (CV/Setup.lean:1090), finitely many pairs → one `δ`). (2a)
  `order_reverses`: `G4_{e;f,g} ∈ Z` changes sign (`E.Transversal`), `G4 = (t_f − t_g)·D_f·D_g`
  (`CV.G4_factorization`), the two `G5` factors are active and outside `Z` (`guardconst`) → the difference
  changes sign; same-side constancy from the intermediate value theorem as in `Bridge.neg_iff_of_ne_zero`.
  (3) `other_orders_persist`, `same_side_orders`: the member-valued accessor `G4⟨i;j,k⟩` is active and
  outside `Z` → `guardconst`. (2b) `adjacent`: by contradiction as printed — an intervening visit on `e`
  is a crossing `x_{eh}` (`SM.visit_on_edge_pair`, SM/PairVisits.lean) whose parameter is squeezed to the
  concurrency parameter at `t = 0`, so `G4⟨e;f,h⟩` vanishes at the centre while relevant → in `Z`,
  contradiction with the forced bundle; this needs continuity of `crossParam` along the event
  (`SM.continuousAt_edgeParameter` exists for SM `G1`; on the CV side use `CV.continuous_G2`/`G5` and
  the quotient formula). (4) `triangle_pairs_toggle`, `other_pairs_unchanged`: from (2)–(3) via
  `SM.geometric_interlaces_transport` (SM/GeometricInterlacement.lean:69) for non-triangle pairs — its
  hypothesis `CrossingParameterOrderAgrees` fails only on bundle pairs, so either prove a relative
  version (agreement outside the three comparisons) or argue with `CV.geometricInterlaces_iff_unique`
  (CV/Events.lean:136) and the empty-arc adjacency directly (the printed transposition argument).
  SM germ route (start now): `SM.triple_sides` (SM/TripleSides.lean:87) gives (2b) and the crossings;
  `SM.WallGerm.triple_exact_parameter_orders` / `triple_exact_visit_orders` (SM/TripleVisitExchanges.lean:63/85)
  give (2a)+(3); `SM.WallGerm.triple_sides_crossing_equiv` (:55) gives (1); `SM.gauss_adjacent_empty_arc`
  turns `VisitsAdjacent` into `GaussAdjacent` (via `GaussVisitsAdjacent`; a small bridge lemma
  `VisitsAdjacent → GaussVisitsAdjacent` for same-edge visits is needed, ~60 lines). Under F2(A) the same
  six lemmas must be re-proved from `CrossingGeometry`+`CV.Generic` (they use `SM.Generic` only for
  `generic_edgeParameters_ne`, which is `CV.Generic.crossParam_ne`).
* **R:parity (~300 lines).** `two_colouring`: `decide`. `clumps`: from `triangle_present` and
  `visits_per_crossing`. `clump_monochromatic`: `GaussAdjacent` + `traversalBetween` transitivity
  (`SM.traversalAlternating_rotate`, `traversalBetween_complement`). `parity`, `interlaced_pair`: the
  printed 2-colouring argument — `CV.geometricInterlaces_iff_unique` reads "interlaces" as "the two
  visits of `x` are on different arcs of `y`", then count bichromatic clump pairs. `trichotomy`: a
  `Finset.card` case analysis on the union of pairs (≤ 3 elements; `Finset.card_eq_three`).
  `avail_wall_invariant`: `other_pairs_unchanged`/`same_side_graph` of localization on supports.
* **R:fibre_partition (~200 lines).** Abstract fields: `Finset` algebra + `Finset.sum_nbij'` (or
  `sum_sigma`/`sum_finset_product`) with the bijection `S ↦ (S \ T, S ∩ T)`; CV fields are the
  instantiation (`CV.mem_Ind`, CV/Events.lean:181, `geometricInterlacementGraph` adjacency is
  `GeometricInterlaces`). `avail_card` from parity's `trichotomy`; `avail_wall_invariant`,
  `outside_graph_unchanged` from localization.
* **R:generic_table (~400 lines).** Part A: `decide` per field (split the 18-way conjunction; each
  piece decides in < 1 s). Part B: `nonzero`, `cramer`: `CV.Generic.g5/g3`, `G4_factorization`,
  `field_simp; ring`; `sign_identity`: `sign` of a quotient; `edge_reading`: the block argument from
  localization's `adjacent` + `same_side_orders` + `CV.geometricInterlaces_iff_unique`; `wall_toggle`:
  transversality of `G3 ∈ Z` and `guardconst` on the three active `G5`; `extreme_iff`, `generic_iff`,
  `exactly_one_selected`, `selected_is_graph_selected`: `SignType` case analysis (`decide` after
  abstracting the eight sign triples); `local_word`: sortedness of `geometricGaussList` +
  `traversalKey_lt_iff` + adjacency; `canonical_words`: instance of `local_word` and (2);
  `mask_sharpening`: parity's `interlaced_pair` + `CV.mem_U`.

## 6. Validation done while designing

* `lake env lean work/drafts/rlane/Statements_A.lean`: no errors; four `sorry` warnings (the row theorems).
* Every Part-A field of `GenericTableData` and the `two_colouring` field of `ParityData`, copied
  verbatim from the file, proved by `decide` against the file's own definitions (scratch
  `/tmp/rlane_validate.lean`; the 18-way `present_absent` conjunction needs splitting before `decide`
  because instance synthesis gives up on the whole conjunction and falls back to the classical instance).
* Numeric check (20 000 random configurations, Python, with CV's `row/det3/G3`, `crossParam`, `G5`):
  the three Cramer identities hold (residual < 3e-12); `(q_e,q_f,q_g) = −delta(s_a s_b, s_a s_c, s_b s_c)`
  exactly; extreme ↔ alternating ↔ `q ∈ {(−,+,−),(+,−,+)}`; on nonalternating triples exactly one
  selected condition holds and it matches the graph-selected pair as stated in
  `selected_is_graph_selected` (both the P3 side and the one-edge side); in the canonical branch
  `Delta > 0 ⇒ q = (−,−,−)` (word `P`) and `Delta < 0 ⇒ q = (+,+,+)` (word `E`).

## 7. Open questions

* **Q1 (localization corollary).** "Both orbits of that map occur" is an existence claim about events;
  rendered only as the dichotomy `orbit_preserved`. If the reviewer wants the existence, it needs two
  explicit `CV.Event` instances (a generic-orbit and an extreme-orbit RIII event) — ~300 lines, consumed
  by nothing.
* **Q2 (proof-core fields).** `ParityData.two_colouring`, `clumps`, `clump_monochromatic` and
  `LocalizationData.same_side_orders/same_side_graph`, `FibrePartitionData.avail_card` render proof
  steps / presuppositions rather than statement clauses. They are all consequences the assembly uses;
  drop or keep at the executor's discretion (dropping weakens nothing downstream).
* **Q3 (generic branches other than the canonical one).** `canonical_words` states the `P/E` words for
  `s_a = s_b = s_c` only, as the table prints them; the other four generic branches are cyclic
  relabellings (label shift `a→c→b→a` together with a rotation of the block order, checked by hand).
  `local_word` covers all branches uniformly, so nothing is lost; a field spelling out the relabelling
  map could be added if rows 173–174 want it.
* **Q4 (the summand `F`).** `partition_sum` quantifies over all `F : Finset (Crossing P) → ℤ`; the
  instance `F = wind·∏Ω₁` awaits row 146. If X₁ is formalised with a different codomain the field should
  be generalised to an `AddCommMonoid` (cosmetic).
* **Q5 (adjacency predicate).** `GaussAdjacent` (empty arc) rather than the accepted `SM.VisitsAdjacent`
  / `SM.GaussVisitsAdjacent` (which need `SM.Generic`). The bridge `GaussVisitsAdjacent → GaussAdjacent`
  is `SM.gauss_adjacent_empty_arc`; the converse holds on `CrossingGeometry` but is not in the library.
* **Q6 (carrier identification).** Part A of the generic table is deliberately abstract; the sentence
  identifying the abstract cycles with the event's carriers is the CV def:smoothing obligation (F2(A))
  and is not part of this row's bundle. Record where it will live (row 135/137 or row 173's "arbitrary-Q
  successor lift").
