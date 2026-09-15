# NOTES_B — marked-product block statements, designer B (diagram-first)

File: `work/drafts/markedproducts/Statements_B.lean` (compiles under `lake env lean` from `work/lean`;
exactly four `sorry`s: `SM.join`, `SM.lowest`, `SM.blocks`, `SM.homflyrows`; every definition and the one
sanity lemma are sorry-free with standard axioms).  Source: frozen `reference/SM/` (frame SM15):
sm-3-statesum.tex 1362-1437 (marked join paragraph + mp:join), 1582-1596 (mp:lowest), 1624-1636 (mp:blocks);
sm-4-knotlaws.tex 230-266 (lem:homflyrows).  The printed statements AND proofs were read to fix every notion;
the accepted layer (work/lean/SM) was read for reuse.  Row names: `SM.join`, `SM.lowest`, `SM.blocks`,
`SM.homflyrows` (none of the four is in the fixed-name list of axiom-policy.json; style of `SM.zero_link`,
`SM.split_circle`, `SM.stack`).

Method: each row is a `structure <Row>Data : Prop` with one field per printed clause (docstring quoting the
clause) and `theorem SM.<row> : <Row>Data := by sorry`; the definitions the rows need sit above the bundles,
with docstrings quoting the printed sentences they render.  Designer-B principle: marked diagrams and clean
marked joins are predicates on ACTUAL diagrams stated on their components, visits (crossing occurrences),
successor maps, pairing, bits and signs, exactly as the printed paragraph lists the "finite data"; the
comparison with the record-level `Record.joinRecord` is a separate Prop (`markedJoin_record_statement`).

---------------------------------------------------------------------------------------------------------

## 0. Definitions introduced (all in `SM.Link` unless noted) and what they render

| Lean | printed words (sm-3 unless noted) | notes |
|---|---|---|
| `Diagram.Mark D` (fields `I : D.Γ.Arc`, `marked : IsMarkedInterval D I`) | 1366-1369 "A marked diagram is a nonempty actual diagram with a specified closed nonsingular oriented interval I on one component; I contains no crossing and is contained in a clean disc." | nonempty = `c ≥ 1` in `Diagram`; the interval is the closed traversal arc `I` on component `I.i`; "contains no crossing and is contained in a clean disc" is the ACCEPTED `IsMarkedInterval` (LinkMoves.lean:1107), whose docstring cites the same printed sentence. |
| `Diagram.Mark.IsGap μ v` | 1375 "at their marked gaps" | `v` is the occurrence of the marked component met last before `I.start` (no occurrence of that component cyclically strictly between `v` and `I.start`, via `cycBetween` on `visitCoord`); since `I` carries no occurrence (`IsMarkedInterval`), `I` lies in the gap from `v` to `D.nextVisit v`. |
| `Diagram.Mark.IsCrossingFree μ` | 1433-1434 "an arbitrary crossing-free marked component" | no occurrence on the marked component. |
| `MarkedJoinData A B μA μB J` (Type) | 1370-1379, one field per clause (see §1) | the "finite data" of a clean marked join, on visits/successor/pairing/bits/signs/components of the actual diagrams. |
| `IsCleanMarkedJoin A B μA μB J : Prop := Nonempty (MarkedJoinData …)` | 1427-1429 "any actual clean marked join J(A,B) just specified" | |
| `MarkedJoinData.componentCount` (proved) | 1378-1379 "The component number is c(A)+c(B)−1." | sanity consequence of the component clause. |
| `markedJoin_record_statement : Prop` | 1374-1379 "Its finite data are precise …" compared with the record | bridge (to prove in the proof phase): with record marks naming the diagram gaps, `IsCleanMarkedJoin ↔ Nonempty (RecordIso (Record.joinRecord νA νB) J.record)`. |
| `Diagram.knotRestrict D i := D.restrict {i} _` | 1584 "their actual knot restrictions D_i" | `Diagram.restrict` (LinkDiagram.lean:1082), mp:stack's `D_i` with a one-component block (Stack_statement.lean `blockRestrict`). |
| `twoLambda D` | 1585-1586 "ℓ_ij = ½ Σ σ(x) using ALL mixed crossings between the original components i, j, and put Λ = Σ_{i<j} ℓ_ij" | `2Λ = Σ_{i<j} mixedSignSum D i j` (`mixedSignSum`, ZeroLink.lean:31 — the accepted rendering of "the sum of the decorated signs over the mixed crossings between components i and j"); each summand is even (`SM.zero_link.half_sum_integer`), so `a^{−2Λ} = T (−twoLambda D)` needs no division. |
| `aMinusAInv : LaurentPolynomial ℤ := T 1 − T (−1)` | "(a − a⁻¹)" inside a z-row | |
| `Diagram.Interlaces D x y` | 1626-1627 "its interlacement graph" (chords interlace = alternating endpoints, proof 1639-1651) | the accepted one-polygon `SM.Interlaces` (Interlacement.lean:16: "alternating visits of actual geometric crossings") read on the occurrences of a `Diagram`: some occurrence of `y` lies cyclically strictly between the over and under occurrence of `x`, the other between the under and over occurrence (`cycBetween` on `visitCoord`); meaningful when `c = 1`. |
| `Diagram.interlacementGraph D := SimpleGraph.fromRel D.Interlaces` | "its interlacement graph" | `fromRel` symmetrises (the relation is symmetric anyway, cf. accepted `interlaces_symm`); vertices = crossings. |
| `Record.restrictOcc ρ p hp` | 1628 "restricted named cyclic record" | occurrence-level copy of the accepted block restriction `Record.restrict` (LinkRecord.lean:1144): same circles, occurrences with `p`, first-return successor (`firstReturn`, LinkRecord.lean:100), old pairing/bits/signs. |
| `Diagram.blockRecord D H := D.record.restrictOcc (· .1 ∈ H) _` | 1627-1628 "an actual retained diagram C_H with exactly that restricted named cyclic record" | the record of `D₀` restricted to the occurrences of the crossings in `H`; "exactly" = `RecordIso`. |
| `JoinTree C S J` (inductive Prop) | 1629 "a finite succession of clean marked joins of these actual diagrams" | leaves `C i`; a node is a clean marked join of two subtrees with disjoint leaf sets; `JoinTree C Set.univ J` = every supplied diagram used exactly once. |

Reused unchanged from the accepted library: `Diagram` (LinkDiagram.lean:490), `Diagram.restrict` (:1082),
`Diagram.sign` (:552), `Diagram.writhe` (:577), `Diagram.componentCount` (:580); `Diagram.record`
(LinkDiagramRecord.lean:500), `compOf` (:164), `visitCoord` (:181), `nextVisit` (:258), `twin` (:413),
`overBit` (:470), `cycBetween` (:78); `Record` (LinkRecord.lean:309), `RecordIso` (:539), `firstReturn`
(:100), `Record.Mark` (:1226), `Record.joinRecord` (:1513); `Arc` (LinkMoves.lean:145), `IsMarkedInterval`
(:1107) with `IsDisc` (:100), `Clean` (:342), `ArcCover` (:208); `P` (LocalPolynomial.lean:66); `homfly`
(LinkInterfaces.lean:131), `homfly_descent` (:395), `LinkEquiv` (LinkMoves.lean:760); `R.delta`
(LinkLaurentRing.lean:193), `zRow` (:335, whose docstring already names mp:lowest's `[z^{1−c}]P_D`),
`coeffAt` (:286); `mixedSignSum` (ZeroLink.lean:31), `Shadow.MixedPair` (:25).  Mathlib:
`SimpleGraph.fromRel`, `SimpleGraph.ConnectedComponent` (+ `.supp`), `LaurentPolynomial.T`.

---------------------------------------------------------------------------------------------------------

## 1. The marked-join paragraph (sm-3:1362-1426) → `Diagram.Mark`, `MarkedJoinData`

| printed (sm-3) | Lean |
|---|---|
| 1366-1367 "A marked diagram is a nonempty actual diagram" | `D : Diagram` (c ≥ 1 built into the type) |
| 1367-1368 "with a specified closed nonsingular oriented interval I on one component" | `μ.I : D.Γ.Arc` (component `μ.I.i`, closed cyclic arc `start → stop` in the orientation) |
| 1368-1369 "I contains no crossing and is contained in a clean disc" | `μ.marked : IsMarkedInterval D μ.I` = no occurrence on the closed arc ∧ ∃ disc `U` (`IsDisc`), `Clean U D`, `ArcCover U {I}` |
| 1369-1370 "All crossing discs used in a recursion are chosen disjoint from I" | proof-side choice; not data (noted) |
| 1370-1372 "A marked join … cuts a smaller open interval inside each mark and joins the oriented ends crosswise, preserving the surviving collars" | the construction; its effect on the finite data is the fields below (see reading R1) |
| 1372-1373 "There are no additional crossings in the joining arcs" | `Φ : A.Γ.Visit ⊕ B.Γ.Visit ≃ J.Γ.Visit` (the occurrences of `J` are exactly the old ones; no new crossing) |
| 1373-1375 "Its finite data are precise: concatenate the marked component cycles at their marked gaps" | `succ_inl`, `succ_inr` (successors kept away from the gaps), `succ_gap_left`, `succ_gap_right` (at the gap of `A` continue into `B` right after its gap and back), `succ_gap_left_free`, `succ_gap_right_free` (a factor whose marked component has no gap occurrence, i.e. is crossing-free, inserts nothing).  The four cases (gap on A?, gap on B?) are exhaustive by construction. |
| 1375-1376 "retain every other component" | `e : Fin A.Γ.c ⊕ {j // j ≠ μB.I.i} ≃ Fin J.Γ.c`, `comp_inl`, `comp_inr`, `comp_inr_marked` (the two marked components become one, named by `A`'s) |
| 1376-1377 "and keep exactly all old crossing pairings, bits and signs" | `pair_eq`, `bit_eq`, `sgn_eq` |
| 1378-1379 "The component number is c(A)+c(B)−1" | consequence: `MarkedJoinData.componentCount` (proved) |
| 1379-1381 "The two old marks in the separate factors remain distinguished during recursion; a smoothing selects the unique resulting component containing the relevant interval." | proof device of mp:join (not data) |
| 1381-1382 "The operation is not defined as an unspecified ambient isotopy class." | honoured: `IsCleanMarkedJoin` is a predicate on actual diagrams by finite data, no isotopy class |
| 1384-1426 "These actual clean joins exist … Here are sufficient planar constructions … This realizes the stated record concatenation. The old A presentation, the new one and any other actual clean realization are compared only by Lemma lc:presentations." | existence prose — NOT a field of any row (per instructions); it is consumed by mp:blocks' realization clause (see open question Q1).  1417-1418 fixes reading R1. |

Reading R1 (the main decision).  "Any actual clean marked join J(A,B) just specified" is read as: an actual
diagram `J` whose finite data (occurrences, successor, pairing, bits, signs, components) are the printed
concatenation of those of `A` and `B`.  Justification from the printed text: "Its finite data are precise"
(1373-1374); the realizations are "compared only by Lemma lc:presentations" (1417-1418), i.e. by named record;
the sufficient construction itself MOVES `A` (sphere chart change 1386-1390, affine shrinking into the clean
disc of `I_B` 1411-1414), so no clause about the plane position of `A ∪ B ∪ joining arcs` can be part of the
definition; "The operation is not defined as an unspecified ambient isotopy class" (1381-1382).  Consequence:
the geometric clauses of 1370-1373 (cut interval, crosswise ends, collars, joining arcs) are the construction
whose only trace in the finite data is `Φ` (no new crossings, all old ones kept) and the successor clauses.
The design record (work/reports/design-decision-diagram-record-20260913.md, D9) took the same reading at the
record level and flagged it as making mp:join "stronger than printed" under a purely geometric reading; under
the printed "finite data" sentence it is exactly as printed.  The diagram-level `MarkedJoinData` and the
record-level `RecordIso (joinRecord νA νB) J.record` are expected to be equivalent
(`markedJoin_record_statement`), since `D.record` is literally `(compOf, nextVisit, twin, overBit, sign)`.

Reading R2 (the gap).  The printed "marked gap" is the cyclic interval between consecutive occurrences of the
marked component that contains `I`; it is named by the occurrence `v` just before `I` (`IsGap`), and the
concatenation happens between `v` and `nextVisit v` (record-level `Record.Mark.gap = some v`).  A crossing-free
marked component has no gap occurrence (record-level `gap = none`, "an arbitrary crossing-free marked
component" 1433-1434).  Uniqueness of the gap occurrence and its existence when the component carries an
occurrence are lemmas for the proof phase (needed for the bridge), not part of the statement.

Reading R3 ("clean disc").  Reused accepted `IsMarkedInterval`: the disc meets the diagram exactly in the
closed arc `I`, with the ends of `I` on `∂U` (`ArcCover U {I}`).  This is the library's rendering of the same
sentence (its docstring cites 1367-1369); a literal "I strictly inside a clean disc" differs only by extending
`I` to the intersection with the disc, which is harmless (marks may be shrunk/extended inside the clean disc;
the theorem does not depend on it).

## 2. mp:join (sm-3:1427-1437) → `JoinData`, `SM.join`

| printed | field |
|---|---|
| 1428-1431 "For two nonempty actual marked diagrams and any actual clean marked join J(A,B) just specified, P_{J(A,B)} = P_A P_B" (eq. mp:join-value) | `value : ∀ A B μA μB J, IsCleanMarkedJoin A B μA μB J → P J = P A * P B` |
| 1432-1434 "This includes smoothing-created multi-component factors and an arbitrary crossing-free marked component." | `crossing_free_marked` (the printed special case with a crossing-free marked component on either side; implied by `value`).  "smoothing-created multi-component factors" is the absence of any restriction on the factors (any `Diagram`, any component number) — no separate field, since a smoothing-created diagram is just a diagram. |
| 1434-1435 "No assertion about a marked terminal tangle being ambient-trivial is needed." | non-claim; honoured (nothing about tangles or isotopy in the statement) |

## 3. mp:lowest (sm-3:1582-1596) → `LowestData`, `SM.lowest`

| printed | Lean |
|---|---|
| 1583-1584 "Let D be an actual diagram with c ≥ 1 tagged oriented components" | `D : Diagram`, `c = D.componentCount` (≥ 1 in the type), tags = `Fin D.Γ.c` |
| 1584 "and let D_i be their actual knot restrictions" | `D.knotRestrict i` |
| 1585-1586 "Define ℓ_ij = ½ Σ σ(x) using ALL mixed crossings between the original components i, j, and put Λ = Σ_{i<j} ℓ_ij" | `twoLambda D = Σ_{i<j} mixedSignSum D i j = 2Λ` (integer; no division) |
| 1588-1591 eq. mp:lowest-value "[z^{1−c}] P_D = a^{−2Λ}(a − a⁻¹)^{c−1} ∏_{i=1}^c [z^0] P_{D_i}" | `lowest : zRow (1 − c) (P D) = T (−twoLambda D) * aMinusAInv ^ (c − 1) * ∏ i, zRow 0 (P (D.knotRestrict i))` in `LaurentPolynomial ℤ` |
| 1592-1595 "For c = 2 this is the two-component mixed row; the two tagged restrictions are intrinsic knot diagrams while ℓ_12 is computed in their original common diagram." | `two_component` (the printed specialisation, implied by `lowest`): for `hc : D.Γ.c = 2`, `zRow (−1) (P D) = T (−mixedSignSum D 0 1) * aMinusAInv * (zRow 0 (P D_0) * zRow 0 (P D_1))`; `ℓ_12` from `mixedSignSum` of the common diagram `D`, the restrictions are `knotRestrict` |

Reading R4 (z-rows).  `[z^k] f` is rendered by the accepted `zRow k f : LaurentPolynomial ℤ` (the `a`-Laurent
polynomial of the `z^k` row; `coeff_zRow : (zRow k f).coeff d = coeffAt d k f`), so the printed equation is an
equation in `ℤ[a^{±1}]` with `a ↦ LaurentPolynomial.T 1`.  Equivalent coefficientwise form: `∀ d, coeffAt d (1−c)
(P D) = …` (by `LaurentPolynomial` extensionality); the row form was chosen because it is literal.

## 4. mp:blocks (sm-3:1624-1636) → `BlocksData`, `SM.blocks`

| printed | Lean |
|---|---|
| 1625-1626 "Let an actual oriented one-circle decorated record have a nonempty crossing set" | `D₀ : Diagram`, `D₀.componentCount = 1`, `Nonempty D₀.Γ.Crossing`; the record is `D₀.record` ("actual" = the record of an actual diagram; see reading R5) |
| 1626-1627 "partitioned into the connected components of its interlacement graph" | `H : D₀.interlacementGraph.ConnectedComponent`, crossing set `H.supp` |
| 1627-1628 "Suppose that for every component H an actual retained diagram C_H with exactly that restricted named cyclic record is supplied" | `C : … → Diagram`, `∀ H, Nonempty (RecordIso (C H).record (D₀.blockRecord H.supp))` |
| 1629-1630 "Then a finite succession of clean marked joins of these actual diagrams realizes the full record" | `realizes : ∃ J, JoinTree C Set.univ J ∧ Nonempty (RecordIso J.record D₀.record)` |
| 1630-1631 "and every actual diagram with that full record has polynomial ∏_H P_{C_H}" | `product : ∀ D, Nonempty (RecordIso D.record D₀.record) → P D = ∏ H, P (C H)` |
| 1631-1632 "The joins preserve the sign of every crossing" | `sign_preserved : ∀ J, JoinTree C Set.univ J → ∃ φ : (Σ H, (C H).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2` ("Every old crossing is present once, with its old sign", proof 1682-1683) |
| 1632 "and the writhe is the sum of the writhes of C_H" | `writhe_sum : ∀ D, Nonempty (RecordIso D.record D₀.record) → D.writhe = Σ H, (C H).writhe` |
| proof 1684-1688 "In the canonical application each sign is positive … If there are no owned blocks, the grouped value remains … 1 … No empty link is introduced" | proof remarks / consumer (cb:products) facts; not fields |

Reading R5 (record vs diagram).  Parametrising by an actual one-circle diagram `D₀` and using `D₀.record` is
the diagram-first rendering of "an actual … record": every realizable record is `RecordIso` to some
`D₀.record`, and every hypothesis and conclusion is `RecordIso`-invariant (the interlacement graph is
determined by the successor, `blockRecord` transports along `RecordIso.restrict`-style isomorphisms).  An
abstract-record variant (`ρ : Record`, `IsRealizable ρ`, `Fintype.card ρ.comps = 1`) is equivalent; the
diagram form avoids a record-level interlacement definition by `succ`-iteration.

Reading R6 (interlacement).  `Diagram.Interlaces` mirrors the accepted `SM.Interlaces` (alternating visits) on
the occurrences of a `Diagram`, using the per-component cyclic coordinate `visitCoord` and `cycBetween`.  For a
one-circle diagram this is the chord-interlacement of the record (the printed proof's "Cutting the circle at
the endpoints of b gives two open intervals … Such chords cannot alternate", 1639-1645).  It equals the
record's chord interlacement because `D₀.record.succ` is the cyclic successor of `visitCoord` (accepted
`nextVisit_no_between`).  The bridge to the accepted `interlacementGraph hn hP` on `Crossing P` (for
`singleDiagram C hP ov hov`, through `singleCrossingEquiv`) is a lemma for the consumer cb:products.

Reading R7 ("a finite succession of clean marked joins of these actual diagrams").  `JoinTree C Set.univ J`:
a binary tree of clean marked joins whose leaves are the supplied `C H`, each used exactly once (disjoint leaf
sets at every node), as the printed proof does ("Start with the actual C_A. For each gap attach the recursively
constructed actual diagrams", 1664-1666).  Marks at each node are existential (chosen by the construction).

## 5. lem:homflyrows (sm-4:230-236) → `HomflyRowsData`, `SM.homflyrows`

| printed | Lean |
|---|---|
| 231 "For oriented knots K, J, H_{K#J} = H_K H_J" | `connected_sum`: for one-component diagrams `K`, `J` (`componentCount = 1`), marks `μK`, `μJ`, and any clean marked join `S`, `homfly S = homfly K * homfly J` — the printed proof (239-243): "Choose actual knot diagrams for K, J with clean marked intervals. The clean joining construction preceding Theorem mp:join gives a diagram of their ordinary oriented connected sum." |
| 231-232 "and H_{K⊔J} = (a−a⁻¹)/z H_K H_J" | `split_union`: for a two-component diagram `D` with no crossing between its components (the representatives "with disjoint page images", 243-244; mp:stack's "presented without mixed crossings"), `homfly D = R.delta * (homfly D_0 * homfly D_1)` with `D_i = D.knotRestrict i` the two knot diagrams |
| 232-234 "For a two-component oriented link diagram D = D_1 ∪ D_2 with linking number lk, [z^{−1}] H_D = (a−a⁻¹) a^{−2lk} [z^0](H_{D_1} H_{D_2})" | `two_component_row`: `hc : D.Γ.c = 2`, `zRow (−1) (homfly D) = aMinusAInv * T (−mixedSignSum D 0 1) * zRow 0 (homfly D_0 * homfly D_1)`; `2·lk = mixedSignSum D 0 1` ("Its linking half-sum is computed from the original common presentation, with the crossing signs of def:positive-lift, exactly the lk in the statement", 252-255) |
| proof 247-250 "Passing from these chosen representatives to the knot-class notation uses the full global source premise explicitly retained in Literature input lit:homfly; it is not a conclusion of the local construction alone." | the knot-class reading is `homfly_descent` (LinkEquiv-invariance, lit:homfly's last clause) applied to the diagram-level fields; the well-definedness of the class-level `K#J` is not claimed (design record D10 says the same) |

Reading R8.  `H` is `homfly`, lit:homfly's chosen witness (the lemma is about `H`; lp:core's `P_eq_homfly`
transfers the `P`-rows).  "Knot" = one-component diagram.  "Split union" = two-component diagram without
mixed crossings: for a generic polygonal shadow, two components with no crossing between them have disjoint
page images (strands on different components are never adjacent, `tail_off` excludes vertex contacts), so this
is exactly "disjoint page images".  The knot diagrams `D_1, D_2` are the component restrictions (as in mp:lowest
"the two tagged restrictions are intrinsic knot diagrams").

---------------------------------------------------------------------------------------------------------

## 6. Ambiguities and the readings chosen (summary)

1. Clean marked join = actual diagram with the printed finite data (R1).  Alternative (geometric clauses on
   the plane position) is unusable because the printed construction moves `A`; the printed text itself says the
   finite data are the definition and the realizations are compared only by lc:presentations.
2. Marked gap named by the last occurrence before `I` (R2); no gap ⇔ crossing-free marked component (lemma).
3. "Clean disc" = accepted `IsMarkedInterval` (R3).
4. `[z^k]` rows in `LaurentPolynomial ℤ` via the accepted `zRow` (R4); `a^{−2Λ} = T(−2Λ)` with `2Λ` the integer
   `twoLambda D` (no half-integers).
5. mp:blocks on `D₀.record` for an actual one-circle `D₀` (R5); interlacement on the diagram's occurrences (R6);
   "finite succession of joins" as `JoinTree` with each supplied diagram used once (R7).
6. lem:homflyrows on diagrams; classes via `homfly_descent` (R8).  Two-component statements fix the components
   `⟨0,_⟩`, `⟨1,_⟩` of `Fin D.Γ.c` from `hc : D.Γ.c = 2` (as "D = D_1 ∪ D_2"); `mixedSignSum D 0 1` is the
   ordered-pair sum, symmetric in the two components (each mixed crossing is one ordered strand pair).
7. "In particular"/specialisation sentences kept as (implied) fields, following the accepted bundles
   (`LpCoreData.circle`, `SplitCircleData.crossing_free`): `JoinData.crossing_free_marked`,
   `LowestData.two_component`.

## 7. Not claimed (printed non-claims and prose, honoured)

- mp:join: "No assertion about a marked terminal tangle being ambient-trivial is needed"; "The operation is not
  defined as an unspecified ambient isotopy class"; "These actual clean joins exist" (1384; existence prose, not
  a field — but see Q1); "All crossing discs used in a recursion are chosen disjoint from I", "The two old marks
  … remain distinguished during recursion" (proof devices).
- mp:lowest: "No coefficient or whole polynomial has been assumed nonzero or divided out" (proof remark).
- mp:blocks: "no assumption that an arbitrary restricted word is realizable" (1673-1674), "No empty link is
  introduced and no knot is asserted to represent that empty product" (1688-1689).
- lem:homflyrows: "No division by either knot polynomial or by a corner coefficient has been used".

## 8. Open questions / obligations for the proof phase

Q1. `BlocksData.realizes` is printed in the lemma and is kept as a field; its proof needs the geometric
    existence of clean marked joins (the constructions of sm-3:1380-1425: sphere-chart change, ribbon, affine
    shrinking into the clean disc), which the design record (D9) files as an explicitly tracked sub-obligation
    (estimated 1500+ lines).  The consumer cb:products only needs `product`.  Decision for the executor: prove
    it, or accept mp:blocks only when it is proved (never drop it silently).
Q2. Bridge `markedJoin_record_statement` (diagram-level `MarkedJoinData` ⇔ `RecordIso (joinRecord νA νB)
    J.record`); needs the gap lemmas (uniqueness; existence when the marked component has an occurrence, so
    that `Record.Mark.gap = none` ⇔ `IsCrossingFree`).  Expected short (definitional unfolding of `D.record`).
Q3. Bridge `Diagram.Interlaces` ⇔ accepted `SM.Interlaces` for `singleDiagram` (through `singleCrossingEquiv`,
    `singleDiagram_visitCoord`), needed by cb:products, not by mp:blocks.
Q4. The proof of `LowestData.lowest` applies mp:stack (`SM.stack`, work/drafts/Stack_statement.lean, in flight
    on SM/Stack.lean) with singleton blocks `blk = id`, `blockRestrict D id _ i = D.knotRestrict i`
    (definitionally `D.restrict (univ.filter (· = i)) _` vs `D.restrict {i} _`: same Finset, possibly a
    `Finset.filter_eq'` rewrite), plus `P_knot_support`/`InSupportM` for the row extraction and mp:zero-link.
Q5. Symmetry `mixedSignSum D i j = mixedSignSum D j i` (needed only if a consumer wants the unordered form).
Q6. Whether `Diagram.Mark` should also record the clean disc `U` as data (currently existential inside
    `IsMarkedInterval`); not needed by any row.
