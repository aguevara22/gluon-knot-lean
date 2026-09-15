# NOTES_FINAL — marked-product block (mp:join, mp:lowest, mp:blocks, lem:homflyrows), judge's synthesis

Judge: 2026-09-14.  Inputs: `Statements_A.lean` / `NOTES_A.md` (Designer A, record-first) and
`Statements_B.lean` / `NOTES_B.md` (Designer B, diagram-first).  Both files re-checked with
`lake env lean` from `work/lean`: no errors, exactly the four `sorry` warnings of the row theorems in each.
Output: `Statements_FINAL.lean` (compiles; four `sorry`s: `SM.join`, `SM.lowest`, `SM.blocks`,
`SM.homflyrows`; every other declaration is sorry-free and depends only on `propext`, `Classical.choice`,
`Quot.sound` — checked with `#print axioms` on a `/tmp` copy).  Source frame SM15, `reference/SM/`.

## 0. Verdict per row and what was grafted

| row | base | grafts / changes by the judge |
|---|---|---|
| mp:join (`JoinData`, `SM.join`) | **A** (record marks, `IsCleanMarkedJoin` = `RecordIso` to `Record.joinRecord`; three fields) | B's geometric mark kept only as the bridge predicate `MarkedDiagram.IsGeometric` (with `Diagram.IsGapOf`), not as data |
| mp:lowest (`LowestData`, `SM.lowest`) | **A** (two fields; `two_component_row` for any `i ≠ j`) | none (A and B agree up to `aPow` vs `aMinusAInv` and A's symmetric two-component form) |
| mp:blocks (`BlocksData`, `SM.blocks`) | **A** (abstract `ρ : Record`, `BlockSupply`, record-level interlacement, `restrictCrossings`, `JoinForest`) | `BlockSupply.actual : IsRealizable ρ` ADDED (printed "actual"); `sign_preserved` replaced by **B's** join-level form (bijection of crossings of every `JoinForest` result with `Σ H, (C H).Γ.Crossing`, signs preserved) |
| lem:homflyrows (`HomflyRowsData`, `SM.homflyrows`) | **A** (class-level: `LinkEquiv` representatives; `IsSplitUnion` by blocks) | none |

Why A as the base.  The record-level clean join is the accepted design decision D9
(work/reports/design-decision-diagram-record-20260913.md: "`IsMarkedJoin (A, I_A) (B, I_B) J : Prop :=
RecordIso J.record (joinRecord …)`; c(J) = c(A)+c(B)−1 is then a theorem; realization existence is a
separate lemma; mp:blocks' realization clause is an explicitly tracked sub-obligation") and the brief's
recommended reading.  A's definitions plug directly into the accepted `Record.joinRecord`
(SM/LinkRecord.lean:1513) and its transport `RecordIso.joinRecord` (SM/LinkRecordExtras.lean:553),
`componentCount_joinRecord`, `writhe_joinRecord`; B's `MarkedJoinData` restates the same finite data
on `D.record`'s components field by field and then needs a bridge (`markedJoin_record_statement`, a
Prop B left unproved, which itself needs the gap-uniqueness/existence lemmas) before any accepted
record lemma applies.  Nothing in B's diagram-first rendering is more faithful than A's: B's own
reading R1 says the clean join is determined by the finite data, i.e. by the record.

## 1. mp:join (sm-3:1427-1437; definitions 1362-1385) → `JoinData`

### Adopted reading, clause by clause

| printed | Lean |
|---|---|
| "A marked diagram is a nonempty actual diagram with a specified closed nonsingular oriented interval I on one component; I contains no crossing and is contained in a clean disc" (1363-1365) | `MarkedDiagram = ⟨D, μ : D.record.Mark⟩` (accepted `Record.Mark`, SM/LinkRecord.lean:1226: marked circle `comp`, gap occurrence `gap : Option M`, `gap = none` iff the marked circle is crossing-free).  The interval itself: `MarkedDiagram.IsGeometric` — `∃ I : Arc, IsMarkedInterval D I ∧ I.i = μ.comp ∧ ∀ v, μ.gap = some v ↔ D.IsGapOf I v` (accepted `IsMarkedInterval`, SM/LinkMoves.lean:1107, whose docstring cites these lines; `IsGapOf` = B's `IsGap`: the last occurrence of the component before `I.start`).  NOT used by any row. |
| "A marked join … cuts a smaller open interval inside each mark and joins the oriented ends crosswise, preserving the surviving collars. There are no additional crossings in the joining arcs. Its finite data are precise: concatenate the marked component cycles at their marked gaps, retain every other component, and keep exactly all old crossing pairings, bits and signs. The component number is c(A)+c(B)−1." (1370-1378) | `Record.joinRecord A.μ B.μ` (accepted): `M = M_A ⊕ M_B` (no new crossings), `succ = (s_A ⊕ s_B) ∘ gapSwap` (concatenation at the gaps; identity swap when a gap is `none`), `pair/isOver/sgn = Sum.elim` (old pairings, bits, signs), `comps = comps_A ⊕ Unmarked_B` (every other component retained); `componentCount_joinRecord` is the printed count (re-exported as the sanity lemma `IsCleanMarkedJoin.componentCount`). |
| "any actual clean marked join J(A,B) just specified" (1428-1429) | `IsCleanMarkedJoin A B J := Nonempty (RecordIso J.record (Record.joinRecord A.μ B.μ))` |
| "P_{J(A,B)} = P_A P_B" (mp:join-value) | `join_value : ∀ A B J, IsCleanMarkedJoin A B J → P J = P A.D * P B.D` |
| "This includes smoothing-created multi-component factors" | `multi_component_factors` (the identity under `1 < c(A) ∨ 1 < c(B)`; a specialisation recording the printed inclusion — a smoothing-created factor is just a diagram with more components) |
| "and an arbitrary crossing-free marked component." | `crossing_free_marked_component` (the identity under `A.μ.gap = none ∨ B.μ.gap = none`; `gap = none` ⇔ the marked circle carries no occurrence, by `Mark.gap_none` and `Mark.gap_comp`) |
| "No assertion about a marked terminal tangle being ambient-trivial is needed." (1433-1434); "The operation is not defined as an unspecified ambient isotopy class." (1381-1382) | negative remarks, no field; honoured (nothing about isotopy classes or tangles appears) |
| "These actual clean joins exist, including at an interior-face mark." + construction (1387-1425) | existence prose, NOT a field (per the brief).  Consumed only by mp:blocks' printed clause `realizes`. |

### Rejected and why

* B's `Diagram.Mark` (an `Arc` with `IsMarkedInterval`) as the DATA of a marked diagram, with
  `MarkedJoinData` stated on visits/successor/components of `A`, `B`, `J` (13 fields).  Same content as
  `RecordIso J.record (joinRecord …)` — B says so (R1, `markedJoin_record_statement`) — but detached
  from every accepted lemma about `joinRecord`; the `succ_gap_*` case split (gap/no gap on each side)
  re-implements `gapSwap`; and the bridge needs the lemmas "the gap occurrence of `I` exists iff the
  component has an occurrence" and "it is unique", which are pure bookkeeping.  Kept from B: the gap
  predicate (as `Diagram.IsGapOf`) inside the documentation predicate `IsGeometric`.
* Making `IsGeometric` a field of `MarkedDiagram` (literal printed scope).  Not done: the rows would
  then quantify over fewer marks with the same proof, `realizes` (mp:blocks) would additionally have to
  construct geometric intervals inside gaps of the partial joins, and D9 already accepted the record
  reading with the note "stronger than printed (provable, but must be noted)".  Left as fidelity risk 1.
* B's two-field bundle (dropping `multi_component_factors`): the printed sentence names two inclusions;
  the accepted method is one field per clause (cf. `StackData.split_union`, `SplitCircleData.crossing_free`).

### Fidelity risks for the executor

1. **Record marks ⊋ printed marks.**  Every printed marked diagram `(D, I)` gives a record mark (its
   component and gap), so every printed instance is covered; conversely a record mark whose gap holds no
   clean interval is not a printed marked diagram.  `join_value` is therefore (harmlessly) stronger than
   printed: the proof never uses the interval, only the gap.  If a referee insists on the literal scope,
   add `geometric : IsGeometric ⟨D, μ⟩` to `MarkedDiagram` — statements unchanged otherwise.
2. **`IsCleanMarkedJoin` quantifies over every diagram with the join record**, not only over
   cut-and-splice realizations.  Printed text: "Its finite data are precise" and "any other actual
   clean realization [is] compared only by Lemma lc:presentations" (1420-1421), and the printed proof
   itself uses "the actual smoothed diagram as the realization of J(A⁰,B), or apply lc:presentations
   to a newly chosen clean realization" (1477-1479).  Design decision D9.  Not weaker than printed
   (every geometric clean join has the record, 1375-1378); stronger only through lc:presentations
   (`SM.presentations`), which is accepted.
3. Nothing asserts that a clean join EXISTS for given `A`, `B` (existence prose, not a row).  Consumers
   needing existence (mp:blocks `realizes`) carry it themselves.

### Proof-lane sketch (consumes)

Statement: `∀ A B J, RecordIso J.record (joinRecord A.μ B.μ) → P J = P A.D * P B.D`.
* Reduce to a record-level induction on `A.D` with a based order putting the marked circle first and
  based at the gap, then on `B.D`: `skein_induction_based` (SM/PolynomialBlock.lean:551; predicate
  `Φ D B := ∀ μ (with comp/gap = the basing's first circle/base) B' J, RecordIso J.record (joinRecord μ μ') → P J = P D * P B'.D`),
  `Record.RBasing`, `IsBad`, `badCount`, `RUnderFirst` (:139-196), `badCount_switch` (:229),
  `badCount_rbasingSwitch` (:371).
* Base (`b = 0`, both factors UNDER-first at these bases): build an `RBasing` of `joinRecord` (marked
  circle first, base at `A`'s gap, then `A`'s other circles in order, then `B`'s unmarked circles);
  `RUnderFirst` of the join from `RUnderFirst` of the factors (printed 1445-1451: no mixed visits, the
  relative order of the two visits of an old crossing is unchanged) — NEW record lemma
  `rUnderFirst_joinRecord`; then `exists_underFirst_of_rUnderFirst` (:469) and `P_underFirst_init` (:683)
  on `J` (via `RBasing.map` along the iso) and on the factors; `componentCount_joinRecord`,
  `Diagram.record_componentCount`; `R.delta` exponent arithmetic `c(A)+c(B)−2 = (c(A)−1)+(c(B)−1)`.
* Step at a bad occurrence `a` of `A` (symmetrically `B`): switch — `switch_record` (SM/LinkDiagramRecord.lean:697),
  NEW `joinRecord_switch : (joinRecord μA μB).switch (inl a) ≅ joinRecord μA' μB` with `μA'` the same mark
  on `A.record.switch a` (marks are untouched by a switch), `P_recursion_pos/neg` (:693/:697) on `J`
  and on `A.D`; smoothing — `exists_smoothing_pair` (:845) / `exists_smoothing_record_visit`
  (SM/Smoothing.lean:8185) for `J` and `A.D`, NEW `joinRecord_smooth : (joinRecord μA μB).smooth (inl a) ≅ joinRecord (μA.smoothMark a) μB`
  where `Mark.smoothMark` re-chooses the gap as the occurrence now preceding the interval (the printed
  four cases 1462-1472: self/mixed × marked/unmarked; `RecordIso.smooth`, SM/LinkRecordExtras.lean:432,
  and `RecordIso.joinRecord` :553 transport the isos), then `presentations` (:1177) identifies the actual
  smoothing of `J` with any diagram having record `joinRecord (μA.smoothMark a) μB`.
* Algebra: the two solved recursions (`solvedR`, PolynomialBlock §0) and `P_skein` (:638).
Estimated NEW lemmas: `rUnderFirst_joinRecord`, `joinRecord_switch`, `Mark.smoothMark` + `joinRecord_smooth`
(the substantial one: it is the record-level "recombination at disjoint ends" of 1458-1462), and the
mark/basing bookkeeping.  No geometry beyond the accepted `exists_smoothing`.

## 2. mp:lowest (sm-3:1582-1596) → `LowestData`

### Adopted reading

| printed | Lean |
|---|---|
| "Let D be an actual diagram with c ≥ 1 tagged oriented components" | `D : Diagram`, `c = D.componentCount = D.Γ.c ≥ 1`, tags `Fin D.Γ.c` |
| "let D_i be their actual knot restrictions" | `D.knotRestrict i := D.restrict {i} _` (SM/LinkDiagram.lean:1082; sanity `knotRestrict_componentCount`) |
| "Define ℓ_ij = ½ Σ σ(x) using ALL mixed crossings between the original components i, j, and put Λ = Σ_{i<j} ℓ_ij" | `twoLinking D i j := mixedSignSum D i j` (accepted, SM/ZeroLink.lean:31 — ALL mixed crossings of the ORIGINAL diagram, decorated signs), `twoLambda D := Σ_i Σ_j [i<j] twoLinking D i j`; both are `2ℓ_ij`, `2Λ` — integers; `a^{−2Λ} = aPow (−twoLambda D)`.  No `½` and no division appear (the brief's remark); integrality of `ℓ_ij` itself is `SM.zero_link.half_sum_integer`. |
| "[z^{1−c}] P_D = a^{−2Λ}(a − a⁻¹)^{c−1} ∏_{i=1}^c [z^0] P_{D_i}" (mp:lowest-value) | `lowest_value`: an identity in `ℤ[a^{±1}]` via the accepted `zRow k : R → LaurentPolynomial ℤ` (SM/LinkLaurentRing.lean:335, whose docstring already names this row); `(aPow 1 − aPow (−1)) ^ (c − 1)` with natural subtraction (`c ≥ 1`); `∏ i : Fin D.Γ.c` |
| "For c = 2 this is the two-component mixed row; the two tagged restrictions are intrinsic knot diagrams while ℓ_12 is computed in their original common diagram." | `two_component_row`: `c = 2`, any `i ≠ j`: `zRow (−1) (P D) = aPow (−twoLinking D i j) * (aPow 1 − aPow (−1)) * (zRow 0 (P D_i) * zRow 0 (P D_j))` |

### Rejected and why

* B's `two_component` fixing the components `⟨0,_⟩`, `⟨1,_⟩` with `by omega` proofs inside the
  statement: the printed row has no index convention ("the two tagged restrictions", `ℓ_12 = ℓ_21`);
  the symmetric form is the literal one and costs only the lemma `mixedSignSum D i j = mixedSignSum D j i`
  (each mixed crossing is one ordered strand pair `(s, t)`; `{s, t} = {t, s}`).
* B's separate constant `aMinusAInv`: `aPow 1 − aPow (−1)` inline is the printed `a − a⁻¹`.
* The coefficientwise variant `∀ d, coeffAt d (1−c) (P D) = …`: equivalent by `LaurentPolynomial` extensionality
  and `coeff_zRow`; the row form is literal.

### Fidelity risks

4. `[z^k]` is read as the `a`-Laurent polynomial row (`zRow`), an equation in `ℤ[a^{±1}]`; this is the
   accepted rendering (its docstring cites mp:lowest).  No risk beyond that choice.
5. `two_component_row` is implied by `lowest_value` (with `twoLambda D = twoLinking D i j` for `c = 2`
   after symmetry); kept as a field because it is a printed sentence (method of the accepted bundles).

### Proof-lane sketch (consumes)

* mp:stack is ACCEPTED: `SM.stack : StackData` (SM/Stack.lean:1350, `StackData.stack` with
  `blockRestrict D blk hblk i`, `BlockOrdered`).  With `blk = id : Fin c → Fin c`,
  `blockRestrict D id _ i = D.restrict (univ.filter (· = i)) _` and `knotRestrict = D.restrict {i} _`:
  rewrite by `Finset.filter_eq'` (a `Diagram.restrict` congruence along equal finsets; or state
  `knotRestrict` directly as `blockRestrict D id _ i` if the executor prefers — the judge kept the
  literal singleton).
* Switching mixed crossings to `BlockOrdered`: `Diagram.switch`, `switch_record` (SM/LinkDiagramRecord.lean:697),
  `restrictRecordIso` (:1454) + `restrict_record` to see that `(D.switch x).knotRestrict i ≅ D.knotRestrict i`
  for a mixed `x` (self crossings untouched); `presentations` then gives `P` equality of the restrictions.
* Weight invariance: `P_skein`/`P_recursion_pos/neg` (SM/PolynomialBlock.lean:638-697) at a mixed
  crossing; the smoothed term has `c − 1` components, `P_support` (:765) / `InSupportM` (SM/LinkLaurentRing.lean:846)
  with `InSupportM.z_mul` (:913) shows `z · P_{D₀}` has no `z^{1−c}` row (`zRow_eq_zero_iff`); the sign
  change moves `twoLambda` by `∓2` (`mixedSignSum` of the switch: one summand flips; `sign` of
  `D.switch x` at `x` is the negative — `switch_record_sgn` :666).
* Final `Λ = 0`: `SM.zero_link.over_constant` (SM/ZeroLink.lean:1325) for each pair after ordering.
* Row extraction of `δ^{c−1} ∏ P_{D_i}`: `P_knot_support` (:815, knot rows are even nonnegative),
  `R.delta = (a − a⁻¹) z⁻¹`, `zRow_single`, `coeffAt_mul_of_max_weight` (SM/LinkLaurentRing.lean:719) or a
  direct lowest-`z`-row lemma for products of supported elements (NEW: `zRow_lowest_mul`).
* `c = 1`: no switches, `twoLambda = 0`, identity.

## 3. mp:blocks (sm-3:1624-1636) → `BlocksData`

### Adopted reading

Hypotheses = `BlockSupply ρ C` (fields `actual : IsRealizable ρ`, `one_circle : ρ.componentCount = 1`,
`nonempty : Nonempty ρ.M`, `supplied : ∀ H, Nonempty (RecordIso (C H).record (ρ.restrictCrossings H.supp))`).

| printed | Lean |
|---|---|
| "Let an actual oriented one-circle decorated record" | `ρ : Record`, `actual` (SM/LinkDiagramRecord.lean:718 `IsRealizable ρ := ∃ D, Nonempty (RecordIso D.record ρ)`), `one_circle` |
| "have a nonempty crossing set" | `nonempty : Nonempty ρ.M` |
| "partitioned into the connected components of its interlacement graph" | `ρ.interlacementGraph := SimpleGraph.fromRel ρ.Interlaces` on `ρ.Crossing`; `Interlaces x y := x ≠ y ∧ ∀ v ∈ x, ∀ w ∈ y, Xor (ArcBetween v w τv) (ArcBetween v τw τv)`, `ArcBetween v w u := 0 < steps v w < steps v u`, `steps` = forward `succ`-step count; blocks = Mathlib `ConnectedComponent` (local `Fintype` via `Fintype.ofFinite`), crossing set `H.supp` |
| "Suppose that for every component H an actual retained diagram C_H with exactly that restricted named cyclic record is supplied" | `C : ConnectedComponent → Diagram`, `supplied`; `restrictCrossings S` = same circle(s), occurrences of the crossings in `S`, `firstReturn` successor, old pairing/bits/signs (the accepted `Record.restrict` pattern, SM/LinkRecord.lean:1144) |
| "Then a finite succession of clean marked joins of these actual diagrams realizes the full record" | `realizes : ∃ J, JoinForest C Set.univ J ∧ Nonempty (RecordIso J.record ρ)`; `JoinForest` inductive: leaf `C i` on `{i}`, node = `IsCleanMarkedJoin ⟨A, μA⟩ ⟨B, μB⟩ J` of two forests on disjoint index sets (any record marks) |
| "and every actual diagram with that full record has polynomial ∏_H P_{C_H}" | `product : ∀ D, Nonempty (RecordIso D.record ρ) → P D = ∏ H, P (C H)` |
| "The joins preserve the sign of every crossing" | `sign_preserved : ∀ J, JoinForest C Set.univ J → ∃ φ : (Σ H, (C H).Γ.Crossing) ≃ J.Γ.Crossing, ∀ q, J.sign (φ q) = (C q.1).sign q.2` (B's form: about the joins, "Every old crossing is present once, with its old sign", 1681-1682) |
| "and the writhe is the sum of the writhes of C_H." | `writhe_additive : ∀ D, Nonempty (RecordIso D.record ρ) → D.writhe = ∑ H, (C H).writhe` |

### Rejected and why

* B's parametrisation by an actual one-circle diagram `D₀` with `ρ = D₀.record` and a DIAGRAM-level
  interlacement (`cycBetween` on `visitCoord`, `overVisit`/`underVisit`).  Equivalent to the abstract
  `ρ` with `IsRealizable ρ`, but every consumer applying the lemma to a record given up to `RecordIso`
  would first have to transport B's interlacement graph and `blockRecord` along the iso; A's
  record-level notions are `RecordIso`-invariant by construction (they use only `succ`, `pair`).
  B's `Diagram.Interlaces` also silently depends on `c = 1` for `visitCoord` to be one circle.
* A's original `sign_preserved` (for every `D` with the full record and every supplied `ιH`,
  `D.sign (ι.Φ.symm (ιH.Φ v).1).1 = (C H).sign v.1`): true and useful, but it is a statement about
  record isomorphisms (it follows from `sgn_eq` twice and `restrictCrossings_sgn`), whereas the printed
  clause is about THE JOINS.  B's forest-level bijection is the in-context reading and also carries
  "present once" (the bijection).  A's version is a one-line corollary for the consumer cb:products
  (positivity of every crossing of `D_A` from positivity of the `C_H`).
* A's omission of `actual`: printed hypothesis ("an actual … record"), so it is a field.  It is
  redundant once `realizes` is proved (the forest result is an actual diagram with record `ρ`), but a
  faithful hypothesis costs consumers nothing (`isRealizable_record D₀`).
* B's `Record.restrictOcc p hp` (general predicate) + `blockRecord`: A's `restrictCrossings S` is the
  same construction specialised to a crossing set, with the `pair`-invariance proved once
  (`crossKeep_pair_iff`) instead of carried as a hypothesis.

### Fidelity risks

6. **`realizes` needs the geometric existence of clean marked joins** (the prose 1387-1425 and the
   nested-gap construction 1646-1676) — the tracked sub-obligation of D9 (estimated ≥ 1500 lines: sphere
   chart change / ribbon / affine shrinking, or a direct polygonal construction).  It is a printed
   clause; never drop it silently.  NOTE (both designers understated this): `product` is NOT independent
   of `realizes` in the printed proof — "Repeated use of mp:join gives the product value for the
   constructed diagram. lc:presentations equates it with any actual diagram having the same full data"
   (1675-1677); a record-only route would need actual diagrams for the partial joins, i.e. realizability
   of the sub-forest records, which is the same geometric content.  So cb:products (which "only needs
   `product`") waits on the realization too, unless the executor finds a record-level argument
   (e.g. smoothing/deleting the other blocks inside an actual `D` with record `ρ` — not in the printed text).
7. `Record.Interlaces` is stated `∀ v ∈ x, ∀ w ∈ y` (A's open question 2).  On a one-circle record the
   four choices agree; the prover will want `interlaces_symm`/representative-independence lemmas and the
   bridge to the polygon-level accepted `SM.interlacementGraph hn hP` (SM/Interlacement.lean) for the
   consumer cb:products (`record_of_single_polygon`, SM/LinkDiagramRecord.lean:829, gives the data agreement).
8. `JoinForest` allows arbitrary record marks at each node (A's open question 4); the printed
   construction uses marks in the gaps of the partial join.  Existence is unaffected (the constructed
   forest is one witness); no clause fixes the marks, so nothing is claimed about them.
9. "actual retained diagram" is read as "an actual diagram whose named record is exactly the
   restricted record"; no link to the corner-state-sum carriers is made in this row (cb:products makes it).

### Proof-lane sketch (consumes)

* Combinatorics (1637-1663, record level, no geometry): for a block `A` and a chord `b ∉ A`, both ends
  of `b` lie in one cyclic gap of `A` (connectedness of `A` used along an interlacement path:
  `SimpleGraph.ConnectedComponent` induction on `Reachable`/`Walk`); two interlacing chords outside `A`
  share the gap; hence each other block lies in one gap of `A`.  Nested forest by recursion on the
  number of pending blocks (well-founded on `Finset.card`).  Record identity: `ρ ≅ joinRecord (…)` of
  the sub-forest records at the right gaps — NEW `restrictCrossings_joinRecord`: for a crossing set
  `S ⊔ T` with `T` inside one gap of `S`, `ρ.restrictCrossings (S ∪ T) ≅ joinRecord (μ_S) (μ_T)` with
  marks at that gap; `restrictCrossings Set.univ ≅ ρ` (cf. `restrictUnivIso`, SM/LinkRecord.lean).
* Geometry (`realizes`): existence of an actual diagram with record `joinRecord μA μB` for actual `A`,
  `B` and any record marks — NEW `exists_cleanMarkedJoin` (D9's separate lemma).  Nothing accepted
  covers it; `exists_smoothing` (SM/Smoothing.lean:8170) is the closest existing geometric construction
  and its disc-local machinery (`IsDisc`, `Clean`, `ArcCover`, SM/LinkMoves.lean) is the natural toolkit.
* `product`: from `realizes`, `JoinForest` induction with `SM.join.join_value`, then `presentations`.
* `sign_preserved`: `JoinForest` induction; at a node the iso `RecordIso J.record (joinRecord …)` gives
  `J.Γ.Visit ≃ A.Γ.Visit ⊕ B.Γ.Visit` respecting `pair` and `sgn`; pass to crossings (`crossingOf`,
  `Record.Crossing`, `record_pair_apply`, `record_sgn`); leaves by `Equiv.sigmaEquivProd`-style
  bookkeeping on `Set.univ` = disjoint union of singletons.
* `writhe_additive`: `RecordIso.writhe_eq`, `record_writhe` (SM/LinkDiagramRecord.lean:578),
  `writhe_joinRecord` (SM/LinkRecord.lean:1590) along the forest (`IsCleanMarkedJoin.writhe` is the
  one-step lemma, already proved in the FINAL file).

## 4. lem:homflyrows (sm-4:230-238) → `HomflyRowsData`

### Adopted reading

| printed | Lean |
|---|---|
| "For oriented knots K, J, H_{K#J} = H_K H_J" | `connected_sum`: `K, J` one-component diagrams standing for their `LinkEquiv` classes (SM/LinkMoves.lean:760 — lit:homfly's "the oriented link presented by D"); `K # J` = any clean marked join `D` of marked representatives `K' ~ K`, `J' ~ J`; `homfly D = homfly K * homfly J` |
| "and H_{K⊔J} = (a − a⁻¹)/z H_K H_J" | `split_union`: `K ⊔ J` = any `IsSplitUnion K' J' D` of representatives (two nonempty component blocks `B`, `Bᶜ`, no crossing between them, block restrictions `RecordIso` to `K'`, `J'`); `homfly D = R.delta * (homfly K * homfly J)`, `δ = (a − a⁻¹) z⁻¹` |
| "For a two-component oriented link diagram D = D₁ ∪ D₂ with linking number lk, [z⁻¹]H_D = (a − a⁻¹)a^{−2lk}[z⁰](H_{D₁}H_{D₂})" | `two_component_row`: `c = 2`, `i ≠ j`, `D₁ = D.knotRestrict i`, `D₂ = D.knotRestrict j`, `2lk = twoLinking D i j`; `zRow (−1) (homfly D) = (aPow 1 − aPow (−1)) * aPow (−twoLinking D i j) * zRow 0 (homfly D₁ * homfly D₂)` — the `[z^0]` of the PRODUCT, as printed |
| "Passing from these chosen representatives to the knot-class notation uses the full global source premise explicitly retained in lit:homfly; it is not a conclusion of the local construction alone." (247-250) | the `LinkEquiv` quantification; `homfly_descent` (SM/LinkInterfaces.lean:395) is that premise |

### Rejected and why

* B's representative-only `connected_sum` (`K`, `J` themselves marked, `S` any clean join of them) and
  B's `split_union` on a two-component diagram without mixed crossings with `K := D_0`, `J := D_1`.
  Both are special cases of A's fields (`K' = K`, `J' = J`; `B = {0}`) and equivalent to them by
  `homfly_descent` + `presentations`/`P_eq_homfly`; but the printed lemma is stated "for oriented
  knots", i.e. for classes, and the printed proof explicitly separates the representative computation
  from the class statement.  A's form records that separation; the well-definedness of `K # J` as a
  class is NOT claimed (D9/D10).
* Rendering `K ⊔ J` with `IsSplitCircleAddition`/`Reparam` (SM/LinkMoves.lean:1088): that relation is the
  crossing-free special case; `J` may have crossings.
* Rendering "disjoint page images" literally: for a generic polygonal shadow (`tail_off`, transverse
  double points only) two components meet only at mixed crossings, so "no crossing between the blocks"
  is exactly "disjoint page images"; the printed proof reduces to that hypothesis (246-247).

### Fidelity risks

10. Class-level vs representative-only (A's open question 3): equivalent via `homfly_descent`; the
    executor may prove B's form first and derive A's fields in two lines (`homfly_descent`, then
    `P_eq_homfly` + `presentations` for the block restrictions).
11. `H` is `homfly` (lit:homfly's witness), not `P`; the transfer is `lp_core.eq_homfly` (`P_eq_homfly`,
    SM/PolynomialBlock.lean:667).  `[z^0](H_{D₁} H_{D₂}) = [z^0]H_{D₁} · [z^0]H_{D₂}` is the printed
    last paragraph (257-265: knot rows are even and nonnegative), proved from `P_knot_support` (:815).

### Proof-lane sketch (consumes)

* `connected_sum`: `SM.join.join_value` on `K'`, `J'`, `D`; `P_eq_homfly` three times; `homfly_descent`
  for `K ~ K'`, `J ~ J'`.
* `split_union`: `SM.stack.split_union` (SM/Stack.lean, `StackData.split_union` with
  `blk := fun c => if c ∈ B then 0 else 1`, surjective by `hB`, `hB'`; the "no crossing between blocks"
  hypothesis is `IsSplitUnion`'s first conjunct), `blockRestrict` vs `D.restrict B` (`Finset.filter`
  congruence as in mp:lowest), `presentations` for the `RecordIso` to `K'`, `J'`, `P_eq_homfly`,
  `homfly_descent`.
* `two_component_row`: `SM.lowest.two_component_row` (or `lowest_value` with `c = 2`), `P_eq_homfly`,
  `P_knot_support` for the product-row identity `zRow 0 (f * g) = zRow 0 f * zRow 0 g` when `f, g` have
  only even nonnegative `z`-exponents (NEW small lemma, `coeff_zRow`, `coeffAt_mul_of_max_weight` or a
  direct `Finsupp` computation).

## 5. Not rendered as fields (recorded)

* mp:join prose 1387-1425 (existence and planar construction); 1378-1381 ("The two old marks … remain
  distinguished during recursion; a smoothing selects the unique resulting component containing the
  relevant interval" — proof bookkeeping, it is `Mark.smoothMark` in the proof lane); 1369-1370 ("All
  crossing discs used in a recursion are chosen disjoint from I" — proof choice).
* mp:lowest 1621-1622 ("No coefficient or whole polynomial has been assumed nonzero or divided out").
* mp:blocks 1673-1674 ("with no assumption that an arbitrary restricted word is realizable"),
  1683-1685 (empty-product conventions — excluded by `nonempty`; "No empty link is introduced").
* lem:homflyrows 264-265 ("No division by either knot polynomial or by a corner coefficient has been used").

## 6. Library reuse (unchanged, file:line)

`Diagram` (SM/LinkDiagram.lean:490), `Diagram.restrict` (:1082), `sign` (:552), `writhe` (:577),
`componentCount` (:580); `Diagram.record` (SM/LinkDiagramRecord.lean:500), `record_componentCount`
(:537), `record_writhe` (:578), `IsRealizable` (:718), `restrictRecordIso` (:1454), `cycBetween` (:78),
`visitCoord` (:181), `compOf` (:164); `Record` (SM/LinkRecord.lean:309), `Record.Crossing` (:461),
`crossingOf`/`crossingOf_pair` (:466-470), `RecordIso` (:539), `firstReturn` (:100), `Record.restrict`
(:1144), `Record.Mark` (:1226), `Record.joinRecord` (:1513), `componentCount_joinRecord` (:1560),
`writhe_joinRecord` (:1590); `RecordIso.joinRecord`, `Mark.map` (SM/LinkRecordExtras.lean:478-553);
`IsMarkedInterval` (SM/LinkMoves.lean:1107), `Arc` (:145), `LinkEquiv` (:760); `P` (SM/LocalPolynomial.lean:22);
`homfly` (SM/LinkInterfaces.lean:131), `homfly_descent` (:395); `R.delta` (SM/LinkLaurentRing.lean:193),
`coeffAt` (:286), `zRow` (:335), `coeff_zRow` (:338); `mixedSignSum`, `Shadow.MixedPair` (SM/ZeroLink.lean:25-31);
`SM.presentations` (SM/PolynomialBlock.lean:1177), `lp_core` (:1150), `P_eq_homfly` (:667),
`skein_induction_based` (:551); `SM.stack` (SM/Stack.lean:1350).  Mathlib: `LaurentPolynomial.T`,
`SimpleGraph.fromRel`, `SimpleGraph.ConnectedComponent` (+ `.supp`, `Finite` instance), `Xor`.
