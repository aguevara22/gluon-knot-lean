# NOTES_A — marked-product block, Designer A (record-first)

File: `work/drafts/markedproducts/Statements_A.lean` (imports `SM.PolynomialBlock`, `SM.ZeroLink`,
`Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`; `lake env lean`: no errors, exactly the four
`sorry` warnings of the row theorems `SM.join`, `SM.lowest`, `SM.blocks`, `SM.homflyrows`).
Rows: mp:join (sm-3:1427-1437), mp:lowest (sm-3:1582-1596), mp:blocks (sm-3:1624-1636),
lem:homflyrows (sm-4:230-238).  Source frame SM15, `reference/SM/`.

Design principle (Designer A): every notion that the rows quantify over is fixed at the RECORD level
(`SM.Link.Record`), and the diagram side enters only through `Diagram.record` and `RecordIso`.  The
only new diagram-level definitions are `Diagram.knotRestrict` (a singleton `Diagram.restrict`),
`IsCleanMarkedJoin` / `IsSplitUnion` (both "the record of the diagram is the record-level object"),
the two linking sums (wrappers of the accepted `mixedSignSum`) and the inductive `JoinForest`.

## 0. Definitions introduced (all in `SM.Link` unless noted) and what they render

| Lean | printed notion (source lines) | remarks |
|---|---|---|
| `aPow n := LaurentPolynomial.T n` | `a^n` inside `[z^k] f ∈ ℤ[a^{±1}]` | the row ring of the accepted `zRow` (LinkLaurentRing.lean:335, `coeff_zRow` :338) |
| `MarkedDiagram = ⟨D, μ : D.record.Mark⟩` | "A marked diagram is a nonempty actual diagram with a specified closed nonsingular oriented interval I on one component; I contains no crossing" (1363-1365) | `Record.Mark` is accepted (LinkRecord.lean:1226): marked component + gap occurrence, `gap = none` iff the marked circle is crossing-free ("an arbitrary crossing-free marked component", 1431-1432) |
| `IsCleanMarkedJoin A B J := Nonempty (RecordIso J.record (Record.joinRecord A.μ B.μ))` | "any actual clean marked join J(A,B) just specified" (1428-1429); finite data 1375-1378 | `Record.joinRecord` (LinkRecord.lean:1513) IS the record-level marked join of the brief (`Record.markedJoin`); not re-aliased, to keep `rw` with `componentCount_joinRecord` (:1560) / `writhe_joinRecord` (:1590) working; sanity theorems `IsCleanMarkedJoin.componentCount` (= printed "c(A)+c(B)−1") and `.writhe` are proved |
| `Diagram.knotRestrict D i := D.restrict {i} _` | "their actual knot restrictions D_i" (1584) | `Diagram.restrict` (LinkDiagram.lean:1082) = the mp:stack block restriction (Stack_statement.lean `blockRestrict`) with a singleton block; `knotRestrict_componentCount` proved; its record is `D.record.restrict {i}` by `Diagram.restrictRecordIso` (LinkDiagramRecord.lean:1454) |
| `twoLinking D i j := mixedSignSum D i j` | "ℓ_ij = ½ Σ σ(x) using ALL mixed crossings between the original components i, j" (1585-1586), doubled | `mixedSignSum` is the accepted mp:zero-link rendering (ZeroLink.lean:31; `MixedPair` :25); `2ℓ_ij` is an integer by construction, `ℓ_ij` itself by `SM.zero_link.half_sum_integer` (ZeroLink.lean:1325) |
| `twoLambda D := Σ_i Σ_j [i<j] twoLinking D i j` | "Λ = Σ_{i<j} ℓ_ij" (1586), doubled | `a^{−2Λ} = aPow (−twoLambda D)` |
| `Record.steps ρ v w` | forward step count along `succ` from `v` to `w` | classical `Nat.find`; `0` off the circle of `v`; `steps_self` proved |
| `Record.ArcBetween ρ v w u` | "w lies on the open interval from v to u" (proof 1638-1640 "Cutting the circle at the endpoints of b gives two open intervals") | `0 < steps v w < steps v u` |
| `Record.Interlaces ρ x y` | chords x, y "alternate" (proof 1643-1645) | `x ≠ y ∧ ∀ v ∈ x, ∀ w ∈ y, Xor (w ∈ arc(v, τv)) (τw ∈ arc(v, τv))` |
| `Record.interlacementGraph ρ := SimpleGraph.fromRel ρ.Interlaces` | "its interlacement graph" (1626) | vertices = `Record.Crossing` (LinkRecord.lean:461) |
| `ρ.interlacementGraph.ConnectedComponent`, `H.supp` | "the connected components of its interlacement graph" (1626), the crossing set of a component | Mathlib; local `Fintype` instance via `Fintype.ofFinite` |
| `Record.CrossKeep ρ S v := ρ.crossingOf v ∈ S`, `Record.restrictCrossings ρ S` | "that restricted named cyclic record" (1628) | the accepted `Record.restrict` pattern (LinkRecord.lean:1144: retained occurrences, `firstReturn` successor :100, old pairing/bits/signs) with the retained set given by a crossing subset; circles unchanged (`componentCount_restrictCrossings` is `rfl`) |
| `BlockSupply ρ C` | the hypotheses of mp:blocks (1625-1628) | `one_circle`, `nonempty`, `supplied` |
| `JoinForest C S J` (inductive, `SM.Link`) | "a finite succession of clean marked joins of these actual diagrams" (1629-1630) | leaf `C i` on `{i}`; node = `IsCleanMarkedJoin` of two forests on disjoint index sets |
| `IsSplitUnion K J D` | "K ⊔ J" (sm-4:232, proof 245-247) | two nonempty component blocks `B`, `Bᶜ`, no crossing between the blocks, block restrictions record-isomorphic to `K`, `J` |

Reused without change: `SM.P` (LocalPolynomial.lean:22), `SM.homfly` (LinkInterfaces.lean:131),
`homfly_descent` (:395), `LinkEquiv` (LinkMoves.lean:760), `R.delta` (LinkLaurentRing.lean:193),
`zRow` (:335), `Diagram.record` (LinkDiagramRecord.lean:500), `record_componentCount` (:537),
`record_writhe` (:578), `RecordIso` (LinkRecord.lean:539), `Diagram.sign` (LinkDiagram.lean:552),
`Diagram.writhe` (:577), `Diagram.componentCount` (:580).

## 1. mp:join (sm-3:1427-1437) → `JoinData`, `SM.join`

| printed clause | field | rendering |
|---|---|---|
| "For two nonempty actual marked diagrams and any actual clean marked join J(A,B) just specified, P_{J(A,B)} = P_A P_B" (mp:join-value) | `join_value` | `∀ A B : MarkedDiagram, ∀ J, IsCleanMarkedJoin A B J → P J = P A.D * P B.D`; "nonempty" is automatic (`Diagram` has `c ≥ 1`) |
| "This includes smoothing-created multi-component factors" | `multi_component_factors` | the same identity under `1 < c(A) ∨ 1 < c(B)` (a specialisation: `join_value` has no component-count hypothesis; the field records the printed inclusion) |
| "and an arbitrary crossing-free marked component." | `crossing_free_marked_component` | the same identity under `A.μ.gap = none ∨ B.μ.gap = none` |
| "No assertion about a marked terminal tangle being ambient-trivial is needed." | — | negative remark, not a claim |

Reading chosen for "clean marked join": a diagram `J` is a clean marked join of `(A, I_A)`, `(B, I_B)`
iff its named record is isomorphic to the record-level join `joinRecord A.μ B.μ`.  Justification from
the printed text: "Its finite data are precise: concatenate the marked component cycles at their marked
gaps, retain every other component, and keep exactly all old crossing pairings, bits and signs"
(1375-1377) — exactly `joinRecord`'s definition (`M_A ⊕ M_B`, `joinSucc = (s_A ⊕ s_B) ∘ gapSwap`,
`Sum.elim` for pairing/bits/signs, `comps_A ⊕ Unmarked_B`); "The old A presentation, the new one and
any other actual clean realization are compared only by Lemma lc:presentations" (1420-1421); and the
proof itself uses "the actual smoothed diagram as the realization of J(A⁰,B), or apply
lc:presentations to a newly chosen clean realization" (1477-1479).  So the theorem is exactly about
diagrams with that record.  This reading is not weaker than printed (every geometric clean join has
this record, 1375-1378) and not stronger in content (the value depends only on the record by
lc:presentations = `SM.presentations`, PolynomialBlock.lean:1177).

Marked interval: the record keeps only the gap (the occurrence just before I; `none` on a crossing-free
circle).  "contained in a clean disc" (1365) has no record content; it matters only for the existence
of actual clean joins (prose 1387-1425).  The diagram-level `IsMarkedInterval D a` (LinkMoves.lean:1107)
exists in the library and could be attached to a `MarkedDiagram` by a Designer-B route; A does not
need it because no row quantifies over the interval's geometry.

## 2. mp:lowest (sm-3:1582-1596) → `LowestData`, `SM.lowest`

| printed clause | field | rendering |
|---|---|---|
| "[z^{1−c}] P_D = a^{−2Λ}(a − a⁻¹)^{c−1} ∏_{i=1}^c [z^0] P_{D_i}" (mp:lowest-value) | `lowest_value` | `zRow (1 − c) (P D) = aPow (−twoLambda D) * (aPow 1 − aPow (−1))^(c−1) * ∏ i, zRow 0 (P (D.knotRestrict i))` in `LaurentPolynomial ℤ`, `c = D.componentCount` (the `∏` runs over `Fin D.Γ.c`, the tagged components) |
| "For c = 2 this is the two-component mixed row; the two tagged restrictions are intrinsic knot diagrams while ℓ_12 is computed in their original common diagram." | `two_component_row` | `c = 2`, components `i ≠ j`: `zRow (−1) (P D) = aPow (−twoLinking D i j) * (aPow 1 − aPow (−1)) * (zRow 0 (P D_i) * zRow 0 (P D_j))` |
| "Let D be an actual diagram with c ≥ 1 tagged oriented components" | (hypothesis) | any `D : Diagram`; `c ≥ 1` is built in, tags are `Fin D.Γ.c` |
| "let D_i be their actual knot restrictions" | (definition) | `Diagram.knotRestrict` |
| "Define ℓ_ij = ½ Σ σ(x) using ALL mixed crossings between the original components i, j, and put Λ = Σ_{i<j} ℓ_ij" | (definition) | `twoLinking`, `twoLambda`: the statement only uses `2Λ`, an integer (the brief's remark) — no `½` and no division appears; ℓ_ij's integrality is mp:zero-link's `half_sum_integer` |

Readings: (a) `[z^k]` is the accepted `zRow k` (its docstring, LinkLaurentRing.lean:324-327, already
names mp:lowest as its purpose); the identity is in `ℤ[a^{±1}]` with `a^n = LaurentPolynomial.T n`.
(b) `mixedSignSum D i j` is symmetric in `(i, j)` (the decorated sign of a crossing does not depend on
which component is named first), so `two_component_row` is stated for any ordered pair `i ≠ j`; with
`c = 2` these are the two components.  (c) The exponent `c − 1` is natural subtraction, `c ≥ 1`.
(d) The proof's uses of mp:stack with singleton blocks and of mp:zero-link are proof devices; the
statement mentions neither.

## 3. mp:blocks (sm-3:1624-1636) → `BlocksData`, `SM.blocks`

Hypotheses bundled in `BlockSupply ρ C` (fields `one_circle : ρ.componentCount = 1`,
`nonempty : Nonempty ρ.M`, `supplied : ∀ H, Nonempty (RecordIso (C H).record (ρ.restrictCrossings H.supp))`).

| printed clause | field | rendering |
|---|---|---|
| "Let an actual oriented one-circle decorated record have a nonempty crossing set, partitioned into the connected components of its interlacement graph." | `BlockSupply.one_circle`, `.nonempty`; the partition is Mathlib's `ConnectedComponent` of `ρ.interlacementGraph` | `ρ : Record`; "actual" (realizable) is not needed as a hypothesis: the supplied `C_H` and the conclusion's `D` are actual diagrams |
| "Suppose that for every component H an actual retained diagram C_H with exactly that restricted named cyclic record is supplied." | `BlockSupply.supplied` | `C : ConnectedComponent → Diagram`, record of `C H` ≅ `ρ.restrictCrossings H.supp` |
| "Then a finite succession of clean marked joins of these actual diagrams realizes the full record" | `realizes` | `∃ J, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ)` |
| "and every actual diagram with that full record has polynomial ∏_H P_{C_H}." | `product` | `∀ D, Nonempty (RecordIso D.record ρ) → P D = ∏ H, P (C H)` |
| "The joins preserve the sign of every crossing" | `sign_preserved` | for every `D` with the full record (iso `ι`) and every supplied identification `ιH`, every crossing occurrence `v` of `C_H` reappears in `D` as `ι.Φ.symm (ιH.Φ v).1` with `D.sign _ = (C H).sign v.1` ("Every old crossing is present once, with its old sign", 1681-1682) |
| "and the writhe is the sum of the writhes of C_H." | `writhe_additive` | `D.writhe = ∑ H, (C H).writhe` for every `D` with the full record |

Readings and ambiguities:
* "interlacement graph" of a record: the library's `Interlaces`/`interlacementGraph`
  (Interlacement.lean, InterlaceSupports.lean) live on a single polygon `LabelledTuple n`, not on a
  record; mp:blocks is stated for a record, so a record-level interlacement is defined here from the
  successor alone (alternation of the four occurrences around the one circle).  It is defined for every
  choice of the occurrences (`∀ v ∈ x, ∀ w ∈ y`); on a one-circle record the four choices agree
  (`{w, τw}` is split by the two arcs `arc(v, τv)`, `arc(τv, v)`), and `fromRel` only symmetrises a
  relation that is already symmetric there.  A prover will need the lemma "Interlaces is
  representative-independent and symmetric on one-circle records" if it wants a cleaner adjacency;
  the statement does not.
* "restricted named cyclic record": the record of the crossing subset with the SAME circle and the
  first-return successor (the sub-word of the cyclic occurrence word).  This is `Record.restrict`'s
  construction (LinkRecord.lean:1144) with the retained set `CrossKeep S` instead of `RestrictKeep B`.
* "realizes the full record" is a printed clause of the lemma (not surrounding prose), so it is a
  field; it is the only field whose proof needs the planar existence construction (1387-1425,
  1665-1676).  `JoinForest` uses `Set ι` (no decidability), marks arbitrary at each node ("using small
  disjoint crossing-free intervals in that gap", 1667-1668, is a proof choice), each block exactly once
  (`Set.univ` with disjoint unions).
* "actual retained diagram": read as "an actual diagram whose named record is exactly the restricted
  record" (the retained crossings are those of the block); no reference to the corner-state-sum
  carriers is made.
* Nonemptiness: with an empty crossing set there are no blocks and `∏ = 1`; the printed lemma excludes
  this ("nonempty crossing set"; proof 1683-1685 "No empty link is introduced"), hence `nonempty`.
* The `sign_preserved` field follows formally from `sgn_eq` of `ι` and `ιH` and
  `restrictCrossings_sgn`; it is kept because it is a printed clause.

## 4. lem:homflyrows (sm-4:230-238) → `HomflyRowsData`, `SM.homflyrows`

| printed clause | field | rendering |
|---|---|---|
| "For oriented knots K, J, H_{K#J} = H_K H_J" | `connected_sum` | knots = `LinkEquiv` classes of one-component diagrams `K, J`; `K # J` = any clean marked join `D` of marked representatives `K' ~ K`, `J' ~ J`; `homfly D = homfly K * homfly J` |
| "and H_{K⊔J} = (a − a⁻¹)/z H_K H_J" | `split_union` | `K ⊔ J` = any `IsSplitUnion K' J' D` of representatives; `homfly D = R.delta * (homfly K * homfly J)`, `δ = (a − a⁻¹) z⁻¹` |
| "For a two-component oriented link diagram D = D₁ ∪ D₂ with linking number lk, [z⁻¹]H_D = (a − a⁻¹)a^{−2lk}[z⁰](H_{D₁}H_{D₂})" | `two_component_row` | `c = 2`, `i ≠ j`, `D₁ = D.knotRestrict i`, `D₂ = D.knotRestrict j`, `2lk = twoLinking D i j`; `zRow (−1) (homfly D) = (aPow 1 − aPow (−1)) * aPow (−twoLinking D i j) * zRow 0 (homfly D₁ * homfly D₂)` — the `[z^0]` of the PRODUCT, as printed |

Readings:
* `H` is the lit:homfly witness `homfly` (not `P`); lp:core's `P_eq_homfly` (PolynomialBlock.lean:667)
  is what the printed proof uses to transfer mp:join / mp:stack / mp:lowest.
* Knot classes: the formal scope has no connected sum or split union OF CLASSES (Reidemeister's theorem
  is outside scope, LinkInterfaces header).  The printed proof says exactly how the class notation is
  meant: "Choose actual knot diagrams for K, J with clean marked intervals. The clean joining
  construction ... gives a diagram of their ordinary oriented connected sum ... Passing from these
  chosen representatives to the knot-class notation uses the full global source premise explicitly
  retained in Literature input lit:homfly" (240-249).  Rendering: `K, J` are diagrams standing for
  their `LinkEquiv` classes, the representatives `K', J'` are arbitrary `LinkEquiv`-related diagrams,
  and the connected sum / split union is any diagram with the corresponding record.  By
  `homfly_descent` this is equivalent to the representative-only form (`K' = K`, `J' = J`); the
  class form was chosen as the closer reading of "for oriented knots".
* Split union: rendered by blocks and "no crossing between the blocks" (mp:stack 1502-1503) rather than
  by disjoint page images; the printed proof reduces to exactly that hypothesis ("two one-component
  blocks and no mixed crossings", 246-247).  The block restrictions are identified with `K'`, `J'` by
  `RecordIso` (the same "compared only by lc:presentations" reading as for joins).  The library's
  `IsSplitCircleAddition` (LinkMoves.lean:1088) is the crossing-free special case and uses `Reparam`;
  it is not reused because `J` may have crossings.
* Linking number: "with the crossing signs of Definition def:positive-lift, exactly the lk in the
  statement" (254-256) — `D.sign` via `mixedSignSum`.

## 5. Not rendered as fields (recorded)

* mp:join prose 1387-1425 "These actual clean joins exist, including at an interior-face mark" and the
  planar construction: existence claims outside the theorem rows.  They are consumed by
  `BlocksData.realizes` (a printed clause of mp:blocks) and by the class-level reading of
  lem:homflyrows only through the existence of SOME clean join, which the fields quantify over rather
  than assert — except `realizes`, which asserts it for the block forest.
* "The two old marks in the separate factors remain distinguished during recursion; a smoothing selects
  the unique resulting component containing the relevant interval." (1378-1381): proof bookkeeping.
* "The operation is not defined as an unspecified ambient isotopy class." (1381-1382), "No assertion
  about a marked terminal tangle being ambient-trivial is needed." (1433-1434): negative remarks.
* mp:blocks proof 1683-1685 (empty product conventions): excluded by `nonempty`.

## 6. Open questions for the panel

1. `IsCleanMarkedJoin` via `RecordIso` to `joinRecord` (record-first) versus a geometric cut-and-splice
   definition: A takes the printed "finite data are precise" sentence as the definition; is the panel
   content that the row then quantifies over all diagrams with the join record (which the printed proof
   itself does)?
2. `Record.Interlaces` is stated with `∀ v ∈ x, ∀ w ∈ y`; an equivalent `∃`-form or a `Crossing.rep`
   form is possible.  Which does the prover of mp:blocks prefer?  (All agree on one-circle records.)
3. lem:homflyrows `connected_sum`/`split_union`: class-level (`LinkEquiv` representatives, chosen) vs
   representative-only; equivalent by `homfly_descent`.
4. `JoinForest` allows arbitrary marks at each node; the printed construction uses marks inside the
   gaps of the current partial join.  Existence is the same; should the statement fix the marks?
5. `BlockSupply` does not require `ρ` to be realizable ("actual ... record"); it is implied when the
   conclusion is applied and harmless otherwise.  Add `IsRealizable ρ` as a hypothesis?
6. mp:lowest `two_component_row` is a specialisation of `lowest_value` (the "For c = 2" sentence); keep
   as a field (panel method: one field per printed clause) or drop as redundant?
