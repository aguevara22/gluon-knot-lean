# NOTES_FINAL — R lane, judge's merge of Statements_A / Statements_B (rows 164, 167, 171, 172)

File: `work/drafts/rlane/Statements_FINAL.lean` (1085 lines). Checked 2026-09-14 with
`cd work/lean && lake env lean ../drafts/rlane/Statements_FINAL.lean`: exit 0, no errors, six
`sorry` warnings — the four row theorems `RProof.localization` (L623), `RProof.parity` (L735),
`RProof.fibre_partition` (L838), `RProof.generic_table` (L1076) and the two flagged auxiliaries
`RProof.indep_partition` (L112, proof-lane engine) and `RProof.both_orbits_occur` (L675, OPTIONAL).
Proved with standard axioms only (`#print axioms`: propext, Classical.choice, Quot.sound):
`LocalTable.skeletonTable`, `LocalTable.successorTable`, `LocalTable.residualWordTable`,
`two_colouring_bichromatic_pairs`, `isSimpleRIII_eventOfTriple`; `localization_of_tripleAt` is proved
from `localization` (inherits its sorry).

Inputs judged: `Statements_A.lean` (773 lines, 4 sorry) + `NOTES_A.md`; `Statements_B.lean` (937 lines,
7 sorry) + `NOTES_B.md`. Both compile. Both were compared clause by clause against R_ASSEMBLY_SPEC.md,
R_ATTACHMENT_WARRANTS.md (R-LOC-2, R-PAR-v6), R_GENERIC_ORBIT_ACTUAL_TABLE.md,
R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (1)–(4), R_GENERIC_COMMON_TRANSPORT_PROOF.md (1), and the
scout report §5 rows 166/167/169/171. The two drafts agree on every mathematical reading (domain,
punctured radius, crossings as supports, CV `crossParam`, empty-arc adjacency, Cramer sign convention,
P = side δ=+1 in the canonical branch, X₁-free partition, abstract skeleton for the cycles); they differ
in *packaging* (support-level vs actual-crossing statements, proof-core fields, abstract-in-bundle vs
abstract-outside). The merge takes B's vocabulary and shape and grafts A's clause splits and its literal
mask-sharpening / graph-selected iff / q-triple intermediate.

## 0. Shared decisions (both rows and the merge)

* **Domain — F2(A), no narrowing.** `E : CV.Event n`, `E.IsSimpleRIII e f g h3 h4e h4f h4g`
  (CV/Events.lean:1131, the forced bundle of ax:R, concurrency point, transversality). Sides
  `E.curve t`, `t ≠ 0`, are CV-generic (`E.generic_punctured`) hence `CrossingGeometry`
  (`CV.Generic.crossingGeometry`, CV/Setup.lean:1154); all Gauss-word / interlacement notions are the
  accepted geometric ones on which CV:def:interlace (row 134) is stated: `geometricVisitPosition`
  (SM/GeometricVisits.lean:12), `geometricGaussList` (:51), `GeometricInterlaces`
  (SM/GeometricInterlacement.lean:16), `CV.Ind`/`CV.N`/`CV.U` (CV/Events.lean:165/171/177). No SM
  genericity anywhere. Where the RA text is about the SM triple germ (R-LOC-2's proof route through
  lem:triple-sides): `isSimpleRIII_eventOfTriple` (PROVED from Bridge.B2/B3 and
  `tripleAt_remote_and_common_point`) puts every `g.TripleAt e f k` (sorted representatives) in the
  rows' domain; `localization_of_tripleAt` is the row instantiated there (proved from the row).
* **Shape.** `structure <Row>Data (E) (e f g) (δ : ℝ) : Prop` with one field per printed/specified
  clause, docstring quoting the clause; `theorem RProof.<name> (E e f g h3 h4e h4f h4g) (hE) : ∃ δ,
  0 < δ ∧ δ ≤ E.radius ∧ <Row>Data E e f g δ`. The radius is "on a punctured neighbourhood of t = 0" /
  "near the wall"; a `Prop` structure cannot hold it as data, so it is the existential of the theorem
  and a parameter of the bundle (same shape as the accepted `SM.triple_sides`, `CV.guardconst`).
  `hn : 3 ≤ n` omitted (B; derivable from `h3`: three distinct one-based representatives; the CV rows
  omit it) — A carried it "for uniformity", harmless but unnecessary.
* **Crossings across the wall.** `IsCrossing (E.curve t) s` on supports `s : Finset (ZMod n)`; the
  identification "by carrying edge pairs" is the accepted `crossingTransport hs`
  (SM/CrossingTransport.lean:12, support-preserving by `rfl`), `hs` being clause (1) of R-LOC-2 at the
  two parameters; cross-wall fields quantify `∀ hs` (proof-irrelevant), the shape of the accepted
  `SM.TripleWallSidesData`. REJECTED: A's `SupportInterlaces hP a b := ∃ x y, x.val = a ∧ y.val = b ∧
  x ∼ y` and `supports S = S.image Subtype.val` — correct, but statements on supports have to be
  re-lifted to `Crossing`/`CV.Ind`/`CV.U` by every consumer (rows 168–178 are all on actual
  crossings), while the transport form is consumable as is.
* **Vocabulary kept from B:** `xPair h : Crossing P`, `visitOn x h hh : Visit P`,
  `triangleSupports`, `triangleCrossings`, `AdjacentVisits`, `clump`, `InArc`, `interlacedTriangle`,
  `avail hP e f g Q`, `outsideSupports`, `localFibre`, `fibreSum`, `Punctured`, `SameSide`,
  `geomAt`; renamed `Opposite → OppositeSides` (A). Kept from A: `EdgeAB/AC/BC` and the explicit
  extreme-orbit predicate, restated on actual crossings (`ExtremeLocal hP hef heg hfg`), replacing
  B's `localEdgeCount ∈ {0,3}`.
* **`instDecidableEqCrossing`** (B): crossings compared by their supports, so `∪ ∩ \ insert` on
  `Finset (Crossing P)` need no classical choice. Risk for the proof lane: the accepted `CV.Ind`,
  `CV.U`, `interlacedTriangle`, `avail` use `classical` internally; Finset lemmas are instance-generic,
  but occasional `convert`/`Subsingleton.elim` on decidability instances may be needed.
* **Adjacency predicate.** `AdjacentVisits hP v w` = `v ≠ w` and one of the two open arcs of `Γ`
  between them (`traversalBetween`, SM/Traversal.lean:73) contains no crossing visit. Identical in A
  (`GaussAdjacent`) and B. It is the empty-arc form of the accepted `SM.GaussVisitsAdjacent`
  (SM/GaussCyclicGap.lean:25, implication `gauss_adjacent_empty_arc` :45), chosen because the accepted
  predicates need `SM.Generic`, because it is manifestly cyclic, and because it is literally what
  R-LOC-2 (2b) proves and R-PAR's proof consumes. The converse bridge (empty arc → list adjacency) is
  not in the library (only needed if a consumer wants the list form).
* **Orders along an edge.** CV's `t_f = CV.crossParam P e f` (CV/Setup.lean:397) = SM's
  `edgeParameter` (`crossParam_eq_edgeParameter`, :572); the accepted triple lane proves the
  `edgeParameter` form.

## 1. Row 164 — R:localization (`LocalizationData`, L536; theorem L623)

Adopted: B's bundle verbatim (renamings only), 12 fields.

| RA sentence (R_ATTACHMENT_WARRANTS.md, R-LOC-2) | field |
|---|---|
| "Let `T = {x_ef, x_eg, x_fg}`" (presupposition: the three pairs are crossings on the punctured neighbourhood) | `triangle_crossings` |
| (1) "the crossing set, indexed by carrying edge pairs, is constant" | `crossing_set_constant` |
| (2) "on each of e,f,g the two crossings of T carried by that edge occupy adjacent crossing-visits of the traversal circle" | `adjacent` (the three visit pairs of the accepted `SM.TripleSides`) |
| (2) "and their order along that edge is opposite on the two sides" | `order_reverses` (both `<` directions per edge, as `SM.TriangleOrderExchanges`) |
| implicit in "the two sides" / "punctured neighbourhood": orders constant on one side | `order_same_side` (ADDED, both drafts) |
| (3) "every other pair of crossings keeps its order along every edge" | `other_orders_persist` |
| proof of (3), last sentence: "the two Gauss words differ by exactly the three transpositions of (2a)" | `gauss_words` = accepted `SM.ExactTriangleVisitOrders` (SM/TripleVisitExchanges.lean:18) |
| (4) "hence `G⁺ = G⁻ △ binom(T,2)`: the three internal pairs of T toggle and no other pair changes" | `interlace_toggle` (`Xor` with `x ≠ y ∧ x,y ∈ T`) |
| implicit in "`G⁺`, `G⁻`": the graph is constant on one side | `interlace_same_side` (ADDED, both drafts) |
| Corollary sentence 1: "The induced graph G[T] maps to its complement in T across the wall" | `complement_on_triangle` |
| Corollary sentence 2: "Both orbits of that map occur — …" | NOT in the bundle: `both_orbits_occur` (L675, sorry, OPTIONAL) |

Rejected alternatives and why.
* A's `orbit_preserved : Extreme_s ↔ Extreme_t` as the rendering of "Both orbits of that map occur".
  It is a true and useful consequence of `complement_on_triangle` (one line), but it is a *different*
  statement from the printed existence claim; recording it as that clause would misdocument the text.
  The assembly's case split (extreme vs generic) comes from `GenericTableData.extreme_iff_alternating`
  + `chamber_change` (strand signs are wall-invariant), or from `complement_on_triangle` directly.
* A's `same_side_graph`/`same_side_orders` ≡ B's `interlace_same_side`/`order_same_side` — kept once.
* A's `order_reverses` with one `↔` per edge: equivalent on generic sides (no ties,
  `CV.Generic.crossParam_ne`), but the two-directional form is what the accepted lane delivers and does
  not rely on no-ties. Kept B's.
* A's `adjacent` quantified over `hfe : IsCrossing {f, e}` (a second crossing object with the
  reordered support) — replaced by `visitOn (xPair hef) f (mem_pair_right e f)` (one crossing, both
  visits), which is what `clump`/R-PAR need.
* A's `other_orders_persist` side condition `{i,j,k} ≠ {e,f,g}` vs B's `¬({h,i} ∈ T ∧ {h,j} ∈ T)`:
  equivalent for distinct crossings; B's is the printed "other than a bundle pair" verbatim.
* B's separate `both_orbits_occur`: kept, OUTSIDE the bundle, marked OPTIONAL. Not consumed by any R
  row or by CV:ax:R (checked against §5 of the scout report and R_ASSEMBLY_SPEC). Proving it needs two
  explicit RIII events (a generic-orbit and an extreme-orbit hexagon), ~300 lines each, for no
  consumer; the executor may drop it under the "illustrative remark, outside the formal scope"
  rule (as with D2/11) with a note, or prove it later. `SimpleRIIIEvent` exists only to state it.

Fidelity notes. `gauss_words` is redundant with `order_reverses` + `other_orders_persist` (visit
parameters are the crossings' edge parameters: `pairVisit_parameter`, `crossParam_eq_edgeParameter`);
it is kept because it is the sentence the proof of (3) ends with and the exact output of the accepted
lane (`triple_exact_visit_orders`), and because (4)'s proof reads it. `interlace_toggle` covers both
halves of (4) in one field (A split them into `triangle_pairs_toggle` / `other_pairs_unchanged`; the
`Xor` form is the printed symmetric difference and is what rows 169's `graph_on_W_same`/`W_to_T_same`
and `complement_on_triangle` specialise).

## 2. Row 167 — R:parity (`ParityData`, L701; theorem L735)

Adopted: B's bundle with (P1) split into two fields (A's split), 5 fields.

| RA sentence (R-PAR-v6) | field |
|---|---|
| "the three crossings of T" | `triangle_card` (ADDED presupposition, `card = 3`) |
| (P1) "Every crossing y ∉ T interlaces exactly 0 or exactly 2 of the three crossings of T — never 1, never 3" | `parity` |
| (P1) "Moreover the interlaced pair, when nonempty, is one of {x_ef,x_eg}, {x_ef,x_fg}, {x_eg,x_fg} — the two crossings sharing one of the three bundle edges" | `interlaced_pair` (`∃ h ∈ {e,f,g}, I(y) = T.filter (h ∈ ·.val)`) |
| (P2) "For any set S' of crossings disjoint from T, avail(S') has size 3, 1, or 0 — never 2" | `trichotomy` (any `S'`, independence not assumed — as printed) |
| (P2) "And avail(S') is the same set on the two sides of the wall" | `avail_wall_invariant` (`Finset.map (crossingTransport hs)`, opposite sides) |
| proof: clumps `C_e, C_f, C_g`; "each clump lies wholly in one of the two arcs … a 2-colouring"; "A 2-colouring of three objects has either 0 bichromatic pairs or exactly 2" | supporting definitions `clump`, `InArc` (L353, L359) and the PROVED lemma `two_colouring_bichromatic_pairs` (L129) — not fields |

Rejected alternatives and why.
* A's fields `two_colouring`, `clumps`, `clump_monochromatic`: proof steps, not statement clauses
  (the design brief puts clumps/2-colourings among the supporting definitions above the bundle). They
  weaken nothing downstream when dropped; the 2-colouring count is proved once as a lemma.
* B's single `parity` field for both (P1) sentences: split, one field per sentence.
* A's `interlaced_pair` as an explicit disjunction of three support-pairs (`mask = {{e,f},{e,g}} ∨ …`):
  equivalent; B's "the two crossings sharing the bundle edge `h`" is the printed characterisation and
  is what row 172's mask sharpening and R_EXTREME_PAIR_ZERO's "adjacent to at least one of x,y" read.
* A's `avail_wall_invariant` quantified over all pairs of punctured parameters (same or opposite
  side) with "same supports": more than the sentence (same-side constancy is
  `LocalizationData.interlace_same_side`); B's is the literal "on the two sides of the wall".

## 3. Row 171 — R:fibre_partition (`FibrePartitionData`, L770; theorem L838)

Adopted: B's bundle (7 fields) + A's `avail_card` (8th field). Abstract engine `indep_partition`
(L112, sorry) kept OUTSIDE the bundle as the proof-lane lemma.

| SPEC sentence | field |
|---|---|
| "R-LOC-2 says only the three internal pairs of T toggle. Consequently both graphs induce the same graph on W" | `graph_on_W_same` |
| "and have the same adjacencies between W and T" | `W_to_T_same` |
| (1) `𝓐(Q) = {t ∈ T : no element of Q is adjacent to t}`; "It is the same on both sides" | definition `avail`; field `avail_same` (for `Q ∈ Ind(G[W])`) |
| "Every independent support S … decomposes uniquely into Q = S ∩ W and J = S ∩ T. Q is independent in the outside graph. J is independent in the local graph and belongs to the availability set" | `decompose` |
| "Conversely, these three conditions imply that Q ∪ J is independent" | `compose` |
| "This proves a bijection of supports, not merely an injection or a list of examples" | `bijection` (`Set.BijOn (S ↦ (S\T, S∩T)) Ind {(Q,J) …}`) |
| (2) `Φ_±(Q)`; (3) "partitions the exact state sum, so X₁(P_±) = Σ_Q Φ_±(Q)" | definition `fibreSum`; field `state_sum_partition` (∀ `AddCommMonoid M`, ∀ `F`) |
| "Prove R-PAR-v6(P1) before using availability sizes … Thus availability has size three, one or zero"; OPEN_WORK item 1 "availability sizes 0, 1 or 3 on both sides" | `avail_card` |

**X₁ flag (both drafts, adopted).** `F_±(S)` = "the **complete** summand of CV def:X1 at S on that
side, including the selector and every carrier coefficient with the printed empty conventions", and
`X₁(P_±)`, are not in Lean (CV:def:X1, row 146, blocked by the diagram/record layer, F2(A)). The
partition is a statement about the index set only; (3) is therefore stated for every summand
`F : Finset (Crossing (E.curve t)) → M` into an `AddCommMonoid`. When def:X1 lands,
`X₁(E.curve t) = Σ_{Q} fibreSum … F_t Q` is `state_sum_partition ht F_t` plus the unfolding of def:X1 —
a one-line corollary, to be added then (as a further field or a separate lemma); no new obligation.
`Φ₊`/`Φ₋` are `fibreSum` at `t`/`t'`, and their comparison (4) is rows 170–177.

Rejected alternatives and why.
* A's abstract fields `abstract_decompose/compose/partition_sum` (quantifying `∀ (V : Type) …
  (G : SimpleGraph V)` inside the bundle): a general graph lemma asserted afresh at every event is odd
  packaging; the brief puts supporting lemmas above the bundle. B's `indep_partition` is that lemma
  (arbitrary finite graph, `graphAvail`), sorried as the first proof-lane unit.
* A's `ℤ` codomain for `F`: def:X1's coefficients are integers, but nothing in the partition depends
  on it; B's `AddCommMonoid M` costs nothing and avoids a later generalisation.
* B's omission of `avail_card` ("belongs to R:parity"): it is R-PAR (P2)'s instance, but the SPEC
  states it in this row's paragraph and OPEN_WORK item 1 lists it with the partition; rows 170 and 178
  read it here. One-line proof from `ParityData.trichotomy`.
* A's `compose` conclusion `(Q ∪ J) \ T = Q ∧ (Q ∪ J) ∩ T = J` (the inverse property): subsumed by
  `bijection`.

## 4. Row 172 — R:generic_table (`GenericTableData`, L861; theorem L1076)

Adopted: the sign part merged from both (A's iff form of "graph-selected", A's `q`-triple
intermediate, B's abstract `selected_unique` with the six-case table and `branch_count`); B's
event-level `local_word`/`canonical_words`/`local_supports`/`local_undominated` in the canonical
branch; A's literal `mask_sharpening` restated on actual crossings; the abstract skeleton (A's derived
`partner`/`undominated`/`residual`, `IsCycleDecomposition` = the complete cycle decomposition) packaged
as three per-row structures `LocalTable.SkeletonTable` / `SuccessorTable` / `ResidualWordTable`, all
PROVED by `decide` (L216–L300) and consumed by three bundle fields. 19 fields.

| source sentence | field |
|---|---|
| "All four quantities are nonzero on either chamber of a simple wall" | `nonzero` |
| NONSELECTED (1), the three Cramer identities | `cramer` |
| NONSELECTED (2) `(q_e,q_f,q_g) = −δ(s_a s_b, s_a s_c, s_b s_c)` | `sign_vector` |
| NONSELECTED (3) "the traversal encounters the e, f, g two-crossing blocks in that order … edge(a,b) iff q_e = −1, edge(a,c) iff q_f = +1, edge(b,c) iff q_g = −1" | `edges_iff` |
| "Changing chamber changes the sign of Δ, so (2) negates all three q's; (3) therefore toggles exactly the three local graph edges" | `chamber_change` (incl. strand signs constant) |
| "The local graph is extreme exactly when all three indicators in (3) agree. That requires (q_e,q_f,q_g) to be (−,+,−) or (+,−,+)" | `extreme_iff_orders` |
| "… this is equivalent to s_a = s_c = −s_b, namely one of the two alternating sign triples" | `extreme_iff_alternating` |
| "Therefore the generic orbit is exactly the other six, nonalternating triples" | `generic_iff_nonalternating` |
| TABLE "Earliest remaining interface": "six generic nonalternating sign branches and two extreme alternating branches" | `branch_count` (finite count, abstract) |
| NONSELECTED (4) + six-case table: "For each nonalternating sign triple exactly one condition in (4) holds" | `selected_unique` (abstract over `SignType`) |
| "the P3 graph on either chamber has as its degree-two vertex the crossing complementary to that pair. Thus the unique separating-strand pair is precisely the graph-selected pair" | `selected_is_graph_selected` (iff, generic orbit) |
| "After erasing every outside visit, the traversal encounters the e, f, and g two-crossing blocks in that order" | `local_word` (`triangleVisits ~r blockWord`) |
| TABLE "P = a b A a c B b c C (edges ab, bc; centre b); E = b a A c a B c b C (edge ac; b isolated)" + COMMON_TRANSPORT (1) canonical branch | `canonical_words` (P = side δ=+1, E = side δ=−1) |
| TABLE "The supports ab,bc,T are absent on P; ac,T are absent on E" (+ tabulated rows present) | `local_supports` (event, canonical branch) + `SkeletonTable.present_*/absent_*` |
| TABLE "Local undominated table" (incl. "b -> ac (connected)") | `local_undominated` (event, `CV.U`) + `SkeletonTable.undominated_*` |
| TABLE "Full availability plus R-PAR sharpens the exterior masks: after a, survivors have mask 0 or bc, so b,c are twins; … after any present pair only mask-zero outsiders survive" | `mask_sharpening` |
| TABLE "Successor cycles" (11 rows) | `successor_table : SuccessorTable` (proved) |
| TABLE residual words paragraph (`c B c C`/`b B b C`, `a A a C`/`b A b C`, `C\|AB`, `a A c a B c`, `C\|A\|B`) | `residual_table : ResidualWordTable` (proved) |
| TABLE words' graphs | `skeleton_table : SkeletonTable` (proved) |

Not rendered (not claims): "The graph-selected generic complement couple in these labels is
therefore b/ac. The abstract c/ab notation … is the same mechanism after permuting labels" (naming);
"The exact generic obligations are consequently: …" (the obligation list of rows 172–174); the
selector-vanishing sentence of "Earliest remaining interface" (row 172 R:generic_selector's claim);
the "signed cross-corner carrier ledger" paragraph (rows 173–174).

Readings and checks.
* Labels: `a = x_ef = (u_1,u_2)`, `b = x_eg = (u_1,u_3)`, `c = x_fg = (u_2,u_3)` (COMMON_TRANSPORT);
  `s_a = sgn G5_{ef}`, `s_b = sgn G5_{eg}`, `s_c = sgn G5_{fg}`, `δ = sgn G3_{efg}`, `q_e = sgn(t_ef −
  t_eg)` etc. with `t_ij = CV.crossParam P i j`.
* Cramer sign convention (judge's re-derivation from the accepted CV identities): `G4_factorization`
  gives `G4_{e;f,g} = (t_ef − t_eg)·det(d_f,d_e)·det(d_g,d_e)` and `G4_eq_neg_G3`,
  `G4_swap_first_eq_G3`, `G4_last_eq_neg_G3` give `G4_{e;f,g} = −G3`, `G4_{f;e,g} = +G3`,
  `G4_{g;e,f} = −G3`; with `det(d_f,d_e) = −G5_{ef}` the three printed identities follow exactly as
  stated in `cramer`. Confirmed numerically (200 000 random configurations, `/tmp/rlane_signs.py`,
  zero violations) together with `sign_vector`, `edges_iff` (from the block words), `extreme_iff_*`,
  `selected_unique`, the iff form of `selected_is_graph_selected` on all six nonalternating triples,
  and the canonical words (δ=+1 → `a b | a c | b c` = P; δ=−1 → `b a | c a | c b` = E).
* Block order: the traversal cut of `geometricGaussList` is at the edge with `ZMod.val = 0`
  (`traversalKey = val + parameter`), so the `e, f, g` blocks appear in that cyclic order up to a
  rotation: `List.IsRotated`.
* Canonical branch only for `canonical_words`, `local_supports`, `local_undominated` (both drafts,
  Q3): the TABLE is printed in labels where no relabelling is needed, i.e. `s_a = s_b = s_c`
  (COMMON_TRANSPORT (1)); the other four generic branches are the label/block relabellings the TABLE
  calls "the same mechanism after permuting labels" and are fully determined by `sign_vector`,
  `edges_iff`, `local_word` (all branches) and the definitions of `CV.Ind`/`CV.U`. A relabelling field
  can be added if rows 173–174 want it spelled out.
* `mask_sharpening` (A's literal reading, adopted over B's `exterior_masks`): B stated the underlying
  P1 consequence without the `Q`/full-availability binder ("equivalent content, simpler binder"); the
  merge keeps the TABLE's own hypotheses (outside independent `Q`, `𝓐(Q) = T`) and its own objects
  (survivors = `CV.U (insert x Q)`, masks = `interlacedTriangle`, "any present pair" = `J ⊆ T`,
  `|J| = 2`, `Q ∪ J ∈ Ind`), so the field is neither stronger nor weaker than the sentence. The proof
  needs only `ParityData.interlaced_pair` + `CV.mem_U` (full availability is not used).
* `selected_is_graph_selected` as `↔` (A) rather than B's `→`: given `selected_unique` (exactly one
  pair selected) and mutual exclusivity of the three graph shapes, the implications and the
  equivalences are interderivable; the `↔` is the printed "precisely".

**Carrier flag (both drafts, adopted).** The TABLE's status "proved at unsigned graph, mask,
residual-word, and successor-cycle level" is about the actual carriers of the event's polygons after
smoothing `Q ∪ J`. The identification of the skeleton's cycles (six local marks + three opaque gaps,
`succ` = reconnection at the two visits of each selected letter) with `smoothingSuccessor`/`Component`
of the Carrier lane after collapsing the exterior gaps (R-EXTERIOR-1 §1, the "arbitrary-Q successor
lift" (2a) of COMMON_TRANSPORT) needs CV:def:smoothing / lem:carriers on the CV locus (rows 135–137,
deferred under F2(A)) and is NOT asserted. It should be recorded as an obligation of rows 172–174
(where the table is consumed), not of this row.

Rejected alternatives and why.
* A's 18 abstract per-row fields inside the event bundle (`cycles_P_a`, …, `residual_selected`):
  same content; packaging them as proved sub-structures keeps the bundle readable and makes the row
  theorem's remaining obligation visibly the event-level part. A's `residual … = [B, A]` (plain list
  equality, start-point dependent) replaced by `IsRotated … [A, B]` (cyclic word, as printed).
* B's `SuccessorTable` as a 22-way conjunction with `cycleList`/`IsRotated` per cycle: replaced by A's
  `IsCycleDecomposition` (each listed cycle is a cycle AND the lists partition all nine positions — the
  complete decomposition, which is what a table of "the" successor cycles asserts), one field per row.
* A's `triangleWord : Cycle (Finset (ZMod n))` (visits written as supports): loses which edge a visit
  is on; B's `triangleVisits : List (Visit P)` with `blockWord` on `visitOn` is exact.
* A's event-level `exactly_one_selected` (on the event's signs): implied by B's abstract
  `selected_unique` + `nonzero`; the abstract form is the printed one and is `decide`-provable now.
* B's `orbit_classification` via `localEdgeCount ∈ {0,3}`: replaced by the explicit `ExtremeLocal`
  (empty ↔ complete) and split into the two printed sentences (`extreme_iff_orders`,
  `extreme_iff_alternating`) plus `generic_iff_nonalternating`.

## 5. Verdicts (per row)

* R:localization — B's rendering adopted (transport form on actual crossings; accepted
  `ExactTriangleVisitOrders`; complement corollary in the bundle; existence remark separate and
  optional). A's `orbit_preserved` rejected as a misreading of "both orbits occur"; A's support-level
  form rejected for consumability. Both faithful to (1)–(4); neither stronger nor weaker.
* R:parity — B's rendering with A's clause split. A's proof-core fields rejected (not clauses).
  Faithful; `triangle_card` is a presupposition (flagged).
* R:fibre_partition — B's rendering (incl. `Set.BijOn`, monoid-valued summand, engine outside) plus
  A's `avail_card`. X₁ enters only as an arbitrary summand (flagged; both drafts agree).
* R:generic_table — merged; sign classification checked by re-derivation from the accepted CV
  identities and numerically; skeleton tables proved; canonical-branch restriction and skeleton↔carrier
  identification flagged (both drafts agree).

## 6. Fidelity risks for the executor

1. **`both_orbits_occur`** (R-LOC-2 corollary, sentence 2) is stated but sorried and consumed by
   nothing; decide (with a note) whether it is in scope. If it is, two explicit hexagon events must be
   constructed (~300 lines each).
2. **Added/presupposition fields**: `LocalizationData.triangle_crossings`, `order_same_side`,
   `interlace_same_side`, `gauss_words`; `ParityData.triangle_card`; `FibrePartitionData.avail_card`.
   None is stronger than what the RA proofs establish (guardconst on the active `G4`s; the accepted
   lane's `triple_exact_visit_orders`; R-PAR (P2)), but each goes beyond the bare printed list; the
   review note should list them.
3. **`gauss_words` redundancy**: equivalent to `order_reverses` + `other_orders_persist` via
   `pairVisit_parameter`/`crossParam_eq_edgeParameter`; keep both (each renders a sentence) or record
   the derivation.
4. **X₁-free (3)**: `state_sum_partition` quantifies over all summands; the specialisation to
   `F_±` and the statement `X₁(P_±) = Σ_Q Φ_±(Q)` must be added when CV:def:X1 lands (row 146). If X₁
   is formalised with a codomain that is not an `AddCommMonoid` in `Type` (universe 0), adjust `M`.
5. **Canonical branch** for `canonical_words`, `local_supports`, `local_undominated`: the other four
   generic branches are not spelled out; rows 173–174 must either relabel or read `edges_iff` +
   `local_word` directly.
6. **Skeleton ↔ carrier identification** not asserted (Carrier lane, F2(A)); rows 172–174 must state
   and prove the "arbitrary-Q successor lift" when they consume the table.
7. **`AdjacentVisits`** is a new predicate (empty arc on `CrossingGeometry`); the accepted list-form
   adjacency (`GaussVisitsAdjacent`, `VisitsAdjacent`) needs `SM.Generic`; only the direction
   list-form → empty-arc (`gauss_adjacent_empty_arc`) exists.
8. **`instDecidableEqCrossing`** vs the classical instances inside `CV.Ind`/`CV.U`: instance
   mismatches in proofs (standard fix: instance-generic Finset lemmas, `convert`).
9. **`hn : 3 ≤ n` omitted** from the row theorems: the proof lane derives it from `h3` (three distinct
   values of `CV.rep`).
10. **Domain**: under F2(A) the printed CV domain is `CV.Generic` sides; the accepted `Triple*` lane is
    on `SM.Generic` sides (`SM.WallGerm`). `localization_of_tripleAt` shows the SM germ is an
    instance; the CV-locus proof must re-derive the six `Triple*` lemmas on `CrossingGeometry` +
    `CV.Generic` (they use `SM.Generic` only through `generic_edgeParameters_ne`, which is
    `CV.Generic.crossParam_ne`) or prove a domain-transfer lemma.

## 7. Proof-lane sketch, accepted lemmas to consume, unit split

Unit F1 — `indep_partition` (~120 lines, pure Mathlib): `Finset.sum_bij'`/`sum_sigma'` on
`S ↦ (S \ T, S ∩ T)` with inverse `(Q, J) ↦ Q ∪ J`; independence of subsets
(`SimpleGraph.IsIndepSet.subset`), `Finset.sdiff_union_inter`, `Finset.disjoint_sdiff_inter`.

Unit L1 — R:localization (1), (2a), (3), same-side clauses (~250): `crossing_set_constant`,
`triangle_crossings`: every `G2` member is outside `Z` (`hE.1`) → `CV.guardconst` (CV/Events.lean:1084)
+ `CV.crosses_iff_isCrossing` (CV/Setup.lean:566) + `CV.Generic.crosses_iff`; finitely many pairs → one
`δ` via `E.eventually_center_iff_radius` (:608). `order_reverses`: `G4_{e;f,g} ∈ Z` sign-changes
(`E.Transversal`, `hE.2.2`), `CV.G4_factorization` (:587), the two `G5` factors active and outside `Z`
(`guardconst`) → the difference changes sign; same-side constancy by connectedness of each side
(`isConnected_Ioo`, as in `Bridge.neg_iff_of_ne_zero`). `other_orders_persist`, `order_same_side`: the
member-valued `G4acc` (:688) is active and outside `Z` → `guardconst`.
Unit L2 — (2b) adjacency (~200): by contradiction as printed — an intervening visit on `e` is a
crossing `x_{eh}` (`crossing_support_partner`, SM/CrossingTransport.lean; `pairVisit`), its parameter
is squeezed to the concurrency parameter at `t = 0` by continuity of `crossParam` along the event
(`CV.continuous_G2`/`G5`, quotient), so `G4⟨e;f,h⟩` vanishes at the centre while relevant → it is in
`Z`, contradicting the forced bundle. Then the traversal sub-arc between the two visits lies inside
edge `e` and carries no vertex → `AdjacentVisits` (empty arc via `traversalBetween` on same-edge
positions, `traversalKey_lt_iff`).
Unit L3 — `gauss_words`, (4) (~200): `SM.exactTriangleVisitOrders_of_parameters`
(SM/TripleVisitExchanges.lean) from an `ExactTriangleParameterOrders` built out of L1 (needs `G1` on
CV-generic sides: `CV.Generic.g1`); (4) from `gauss_words` + adjacency through
`CV.geometricInterlaces_iff_unique` (CV/Events.lean:136) — a transposition of two *adjacent* visits
flips "exactly one visit of `y` between the two visits of `x`" for the pair and preserves it for every
other pair (the printed (4) argument); `SM.geometric_interlaces_transport`
(SM/GeometricInterlacement.lean:69) for pairs whose visit orders all agree.
SM-germ check (~100, optional): compare with `SM.triple_wall_sides` (SM/TripleWallSides.lean:26) on
`Bridge.eventOfTriple` (`eventOfTriple_sideCurve` is `rfl`): `triple_sides_crossing_equiv`,
`triple_exact_visit_orders`, `TripleSides` → `AdjacentVisits` via `gauss_adjacent_empty_arc` +
`geometricVisitPosition_eq_generic`.

Unit P1 — R:parity (~300): from `LocalizationData.adjacent` each clump avoids the two visits of `y`
and lies in one arc (`traversalBetween` trichotomy/rotation, `traversalAlternating_rotate`); "x
interlaces y iff its two clumps have different colours" (`geometricInterlaces_iff_unique`); the count
by `two_colouring_bichromatic_pairs` after abstracting the three clumps to `Fin 3`; `interlaced_pair`:
the odd clump `C_h` gives the two crossings containing `h`; `trichotomy`: `Finset.card` case analysis
on unions of the three named pairs (`Finset.card_eq_three`, ≤ 3 elements); `avail_wall_invariant`:
`interlace_toggle` restricted to `T`-to-outside pairs (the `Xor` second component is false).

Unit F2 — R:fibre_partition (~120): `graph_on_W_same`, `W_to_T_same`, `avail_same` from
`interlace_toggle`; `decompose`/`compose`/`bijection`/`state_sum_partition` = `indep_partition` at
`geometricInterlacementGraph (geomAt E t _)`, `T := triangleCrossings`, via `CV.mem_Ind`
(CV/Events.lean:181); `avail_card` from `ParityData.trichotomy`.

Unit G1 — sign classification (~250, START NOW, no dependency on L/P): `nonzero`: `CV.Generic.g5/g3`
(CV/Setup.lean:1096–1130); `cramer`: `G4_factorization` + `G4_eq_neg_G3`/`G4_swap_first_eq_G3`/
`G4_last_eq_neg_G3` (:437–445) + `det_swap`, `field_simp`; `sign_vector`: `sign_mul`, `sign_div`,
`sign_neg`; `chamber_change`: `G3 ∈ Z` sign-changes (`hE.2.2`), the three `G5` are active and outside
`Z` (`guardconst`); `extreme_iff_orders`/`extreme_iff_alternating`/`generic_iff_nonalternating`:
`edges_iff` + `SignType` case analysis (`decide` after abstracting the eight sign triples);
`branch_count`, `selected_unique`: `decide`; `selected_is_graph_selected`: `edges_iff` + `sign_vector`
+ case analysis.
Unit G2 — words (~200, needs L2/L3): `local_word`: sortedness of `geometricGaussList`
(`Finset.sort_sorted_lt`, `geometricVisitKey`), the two visits on each bundle edge are consecutive
(`adjacent`) and ordered by `crossParam` (`pairVisit_parameter`, `visitParameter`); the three blocks
appear in `val` order → `IsRotated`; `edges_iff`: `geometricInterlaces_iff_unique` read on the block
word; `canonical_words`: `local_word` + `sign_vector`; `local_supports`/`local_undominated`:
`CV.mem_Ind_iff`, `CV.mem_U`, `mem_N` + `canonical_words`; `mask_sharpening`:
`ParityData.interlaced_pair` + `CV.mem_U`.
Unit G3 — tables: done (`decide`).

Totals: localization ~650, parity ~300, fibre partition ~250 (incl. engine), generic table ~450
(G1 ~250 can start immediately, in parallel with L1).

## 8. Validation performed by the judge

* `lake env lean` on Statements_A, Statements_B, Statements_FINAL: all exit 0 (A 4 sorry, B 7, FINAL 6).
* `#print axioms` on the FINAL's proved declarations: standard axioms only (§ header).
* `#eval` of the skeleton: `succ wordP {b}` = `[1,7,3,4,5,6,2,8,0]` (cycles `[0,1,7,8]`,
  `[3,4,5,6,2]`); `residual wordE {b} [1..7] = [a,A,c,a,B,c]`; `undominated wordE {b} = {a,c}`;
  `Interlaces wordP a b`, `¬ Interlaces wordP a c`, `Interlaces wordE a c`.
* Hand re-derivation of the three Cramer identities from `G4_factorization` and the three
  `G4 = ±G3` identities of CV/Setup.lean; hand check of the edge reading (3) from the block words for
  all eight `q`-triples; numeric check (`/tmp/rlane_signs.py`, 200 000 configurations, CV's `row`,
  `det3`, `crossParam`, `G5`): zero violations of `cramer`, `sign_vector`, `edges_iff`,
  `extreme_iff_*`, `selected_unique`, `selected_is_graph_selected` (iff form), `canonical_words`.
