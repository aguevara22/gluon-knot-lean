# CV-DOM unit U8 — REPORT (2026-09-14, prover subagent)

Deliverable: `work/drafts/cvdom/U8/CVTripleEvents.lean` (1,052 lines incl. docstrings; intended home
`work/lean/CV/TripleEvents.lean`; imports `CV.Events`, `SM.TripleVisitExchanges`, `SM.GeometricParameters`,
`SM.GeometricInterlacement` — all in work/lean, no Bridge, no RProof).
Companion: `work/drafts/cvdom/U8/ConsumerCheck.lean` (scratch: module + the statement file's `RProof`
definitions + `localization_from_U8`, see §4).

## 1. Status

* `cd work/lean && lake env lean ../drafts/cvdom/U8/CVTripleEvents.lean` — **no errors, no warnings,
  no `sorry`** (grep clean).
* `#print axioms` on `CV.Event.IsSimpleRIII.tripleEventData`, `…geometricTripleSides`,
  `…tripleUnchangedOrders`, `…exactTriangleParameterOrders`, `…triangleCrossParamExchanges_sides`,
  `…tie_center_iff`, `CV.emptyArcAdjacent_of_outside`, `CV.visitsAdjacent_emptyArc`,
  `CV.geometricTripleSides_of_tripleSides`, `CV.exactTriangleVisitOrders_of_parameters_of_geometry`:
  `[propext, Classical.choice, Quot.sound]` only.
* **No restated lemma is false on CV events**; no `CarrierGeometry` (tier 1) hypothesis was needed anywhere:
  every statement is on `CrossingGeometry` (tier 0) for the sides plus `CV.Generic` of the sides and the
  event's zero-set structure. No new hypothesis beyond `E.IsSimpleRIII e f g h3 h4e h4f h4g` (and, for the
  reusable core, the weaker `E.NoG2Zero`, see §2). No accepted name is redefined; all new names are in
  `CV` / `CV.Event`.
* **Stronger than the SM lane in one respect**: every clause holds on the WHOLE punctured interval
  `t ≠ 0`, `|t| < E.radius` (and the crossing-set constancy, the centre-vs-side order persistence and the
  outside condition even at `t = 0`). No radius `δ` appears; the localization unit can take
  `δ := E.radius`.

## 2. What replaces the SM ingredients (design)

| SM ingredient (accepted lane) | CV replacement in U8 |
|---|---|
| `SM.Generic` via `generic_edgeParameters_ne` | accepted `SM.geometric_edgeParameters_ne` (CrossingGeometry) and `CV.Generic.crossParam_ne` |
| `G1 g.center`, `g1_crossings_locally_constant`, `g1_center_side_crossings` | `Event.NoG2Zero` (no unconditional `G2` member in `Z`; immediate from `hE.1`) + CV:lem:guardconst ⇒ every `Crosses` activation is constant along the whole interval, centre included (`NoG2Zero.crosses_const`, event form of `Bridge.crosses_const`); `IsCrossing ↔ Crosses` at every time (`NoG2Zero.isCrossing_iff_crosses`) |
| `g1_center_side_parameter_order` (same-side order constancy) | `NoG2Zero.crossParam_lt_iff_side`: `crossParam` continuous along the event (`NoG2Zero.continuous_crossParam`), never tying on the connected generic side (IVT: `CV.lt_zero_iff_of_ne_zero`) |
| `concurrenceTriples = {{e,f,k}}`, `uniqueTriple_parameter_tie_iff`, `uniqueTriple_parameters_eq` | `IsSimpleRIII.tie_center_iff`: a centre tie on an active pair is a vanishing active `G4⟨i;j,k⟩`, hence a member of `Z` (`NoG2Zero.mem_zeroSet_of_active`), hence one of the three printed `G4`s (`IsSimpleRIII.g4_mem_iff`, injectivity of `Member.g4`); converse from the three centre ties (`IsSimpleRIII.tie_center`, the `G4` members of `Z` vanish) and the accepted `triple_support_six_orders` |
| `TripleAt`'s three `SignChanges` of parameter differences | `E.Transversal` on the three `G4` members (`IsSimpleRIII.signChanges_G4`) turned into parameter-difference sign changes through `CV.G4_factorization` and `K(t)K(t') > 0` (`NoG2Zero.dirProd_mul_pos`; the accepted `Bridge.B3` route read backwards) |
| `uniqueTriple_outside_persists` (eventually near the centre, continuity) | `IsSimpleRIII.otherCrossingsOutside_edge`: the differences `t_h − t_j`, `t_h − t_k` never vanish on the whole interval (centre: `tie_center_iff`; sides: `crossParam_ne`) and agree at the centre ⇒ `OutsidePair` at every time |
| `visitKey`/`gaussList`/`VisitsAdjacent` (G1-bound) | geometric positions `geometricVisitPosition`, keys `geometricVisitKey`, and the empty-arc predicate `CV.EmptyArcAdjacent` (body identical to `RProof.AdjacentVisits`) |

Two small IVT facts (`CV.lt_zero_iff_of_ne_zero`, `CV.mul_pos_of_ne_zero_of_preconnected`) duplicate
`Bridge.neg_iff_of_ne_zero` / `Bridge.mul_pos_of_ne_zero_const` so that a CV module does not import the
Bridge lane (Bridge imports CV). The assembler may instead import `Bridge.B1`/`B3` and delete them.

## 3. Lemma table (SM source → CV statement → status)

All under `namespace CV` (polygon level) or `CV.Event` (event level); `hE : E.IsSimpleRIII e f g h3 h4e h4f h4g`,
`hZ : E.NoG2Zero`. "Target" = exact body shape of the named `RProof.LocalizationData` field
(NOTES_FINAL.md §1); consumer check in §4.

| # | SM source (accepted) | CV statement (U8) | status |
|---|---|---|---|
| 0 | `Bridge.crosses_const`, `active_const`, `active_center_of_relevant` (B1/B2) | `Event.NoG2Zero`; `NoG2Zero.g2_ne_zero`, `.four_g2`, `.crosses_const (a b) (s t)`, `.isCrossing_iff_crosses (t) (a b)`, `.isCrossing_const (s t) (c)`, `.active_const`, `.active_center_of_relevant`, `.mem_zeroSet_of_active` | proved |
| 0' | `continuousAt_edgeParameter`, `continuousAt_edgeParameter_of_geometry` | `NoG2Zero.continuous_crossParam (hc : Crosses E.center i j) : Continuous fun t => crossParam (E.curve t) i j`; `.continuous_crossParam_sub`; `.crossParam_sub_ne_zero` | proved |
| 0'' | `WallGerm.g1_center_side_parameter_order` | `NoG2Zero.crossParam_lt_iff_side (hij hik : Crosses E.center …) (b : Bool) (s s' : E.SideParameter)`; `NoG2Zero.crossParam_lt_iff_of_center_ne (hne) (s t : E.Parameter)` (whole interval) | proved |
| 1 | `WallGerm.triple_sides_crossing_equiv` (sides) / `g1_center_side_crossings` | **Target `crossing_set_constant`**: `IsSimpleRIII.isCrossing_iff (t t') (s) : IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s` (all `t t'`, centre included) | proved |
| 1' | `uniqueTriple_crossings`, `Bridge.tripleAt_crosses_center` | **Target `triangle_crossings`**: `IsSimpleRIII.isCrossing (t) : IsCrossing {e,f} ∧ {e,g} ∧ {f,g}`; also `.crosses_center`, `.crosses (t)` | proved |
| 2 | `uniqueTriple_parameters_eq`, `uniqueTriple_parameter_tie_iff`, `uniqueTriple_outside_parameter_ne` | `IsSimpleRIII.tie_center`; `.g4_mem_iff`; `.support_eq_of_tie`; `.tie_of_support_eq`; `.tie_center_iff (hjk) (hij hik) : crossParam E.center i j = crossParam E.center i k ↔ {i,j,k} = {e,f,g}`; `.crossParam_ne_center` | proved |
| 3 | `uniqueTriple_other_orders_persist`, `WallGerm.triple_other_orders_sides` (`TripleUnchangedOrders`) | `IsSimpleRIII.crossParam_lt_iff_of_ne (hne : {i,j,k} ≠ {e,f,g}) (s t)`; `IsSimpleRIII.tripleUnchangedOrders (t) : TripleUnchangedOrders E.center (E.curve t) e f g` (accepted predicate; any `t`, not only sides); **Target `other_orders_persist`**: `IsSimpleRIII.other_orders_persist (t t') (h i j) (hhi hhj) (hnot : ¬ ({h,i} ∈ {{e,f},{e,g},{f,g}} ∧ {h,j} ∈ …))` (any `t t'`; `triangleSupports e f g` unfolds to the literal) | proved |
| 4 | `WallGerm.triple_order_exchanges`, `g1_parameter_signChange_sides`, `TriangleOrderExchanges` | `CV.TriangleCrossParamExchanges P Q e f g` (= printed twelve-term body of `order_reverses`; `triangleCrossParamExchanges_iff : … ↔ TriangleOrderExchanges P Q e f g`, `.symm`); `NoG2Zero.paramDiff_signChanges`, `.orders_reverse_of_signChanges`; `IsSimpleRIII.signChanges_G4`; `IsSimpleRIII.triangleCrossParamExchanges_sides (s t : E.SideParameter)`; **Target `order_reverses`**: `IsSimpleRIII.order_reverses (t t') (h : t.val * t'.val < 0) : TriangleCrossParamExchanges (E.curve t) (E.curve t') e f g` | proved |
| 4' | (implicit in the SM lane: side constancy) | **Target `order_same_side`**: `IsSimpleRIII.order_same_side (t t') (h : 0 < t.val * t'.val) (h i j) (hhi hhj)`; helpers `Event.opposite_sides_cases`, `Event.same_side_cases` | proved |
| 5 | `WallGerm.triple_exact_parameter_orders`, `triple_exact_visit_orders`, `exactTriangleVisitOrders_of_parameters` (G1) | `CV.exactTriangleVisitOrders_of_parameters_of_geometry (hP hQ : CrossingGeometry) (hs) (ho) : ExactTriangleVisitOrders P Q e f g hs` (G1 → geometric parameter identification); `IsSimpleRIII.exactTriangleParameterOrders (h : t.val*t'.val < 0) : ExactTriangleParameterOrders (E.curve t) (E.curve t') e f g`; **Target `gauss_words`**: `IsSimpleRIII.exactTriangleVisitOrders (h) (hs) : ExactTriangleVisitOrders (E.curve t) (E.curve t') e f g hs` | proved |
| 6 | `pairVisits_no_between`, `visit_between_same_edge`, `visitKey_lt_iff`, `pairVisits_adjacent`, `tripleSides_of_outside`, `uniqueTriple_outside_persists`, `triple_sides`, `TripleSides`, `VisitsAdjacent` | `CV.EmptyArcAdjacent hP v w` (body = `RProof.AdjacentVisits`); `CV.visitOfPair hc h hh` (= `visitOn (xPair hc) h hh`); `CV.geometricVisitKey_lt_iff`; `CV.geometric_visit_between_same_edge`; `CV.emptyArcAdjacent_of_outside (hP) (hjk) (hv hw : ·.2.val = i) (hvs : v.1.val = {i,j}) (hws : w.1.val = {i,k}) (hout : OtherCrossingsOutside P i j k)`; `IsSimpleRIII.otherCrossingsOutside_edge`, `.otherCrossingsOutside (t)` (all three edges, every `t`); **Target `adjacent`**: `IsSimpleRIII.adjacent (ht : t.val ≠ 0) (hef heg hfg) : EmptyArcAdjacent _ (visitOfPair hef e _) (visitOfPair heg e _) ∧ … f … ∧ … g …`; `CV.GeometricTripleSides hP i j k` (CV form of `SM.TripleSides`, distinct points via `crossingPoints_ne_of_geometry`), `IsSimpleRIII.geometricTripleSides (ht)` | proved |
| B | `VisitsAdjacent` (idxOf in `gaussList`) → empty arc; `sorted_indices_adjacent` | `CV.sorted_no_between_of_adjacent`, `CV.sorted_lt_of_idxOf_lt` (converse/order facts on `Finset.sort`); `CV.visitsAdjacent_emptyArc (hn) (hP : SM.Generic P) (hCG) (h : VisitsAdjacent hn hP v w) : EmptyArcAdjacent hCG v w`; `CV.geometricTripleSides_of_tripleSides (hn hP hCG) (h : SM.TripleSides hn hP i j k) : GeometricTripleSides hCG i j k` | proved (direction LocalizationData needs; the converse is FALSE in general: the first and last visits of `gaussList` are cyclically adjacent through the cut at label 0 but not index-adjacent) |
| + | `geometric_interlaces_transport`, `CrossingParameterOrderAgrees` | **Target `interlace_same_side`**: `IsSimpleRIII.crossingParameterOrderAgrees_same_side (h : 0 < t.val*t'.val)`; `IsSimpleRIII.interlace_same_side (ht ht') (h) (hs) (x y)` | proved (bonus, cheap) |
| Σ | — | `structure CV.Event.TripleEventData E e f g : Prop` (fields = the eight targets above with `t.val ≠ 0` / sign products in place of `Punctured`/`OppositeSides`/`SameSide`); `theorem IsSimpleRIII.tripleEventData : TripleEventData E e f g` | proved |

Not in U8 (unit L3): `interlace_toggle` (4) and its corollary `complement_on_triangle`. Route unchanged from
NOTES_FINAL §7: `gauss_words` + `adjacent` through `CV.geometricInterlaces_iff_unique`.

## 4. Consumer check (the `exact` discharge)

`ConsumerCheck.lean` (= module + verbatim `RProof` defs of the statement file) compiles with exactly one
`sorry` warning, from:

```lean
theorem localization_from_U8 … (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    LocalizationData E e f g E.radius := by
  have D := hE.tripleEventData
  exact {
    triangle_crossings := fun t _ => D.triangle_crossings t
    crossing_set_constant := fun t t' _ _ => D.crossing_set_constant t t'
    adjacent := fun t ht hef heg hfg => D.adjacent t ht.1 hef heg hfg
    order_reverses := fun t t' _ _ hop => D.order_reverses t t' hop
    order_same_side := fun t t' _ _ hss => D.order_same_side t t' hss
    other_orders_persist := fun t t' _ _ _ => D.other_orders_persist t t'
    gauss_words := fun t t' _ _ hop => D.gauss_words t t' hop
    interlace_toggle := sorry            -- L3
    interlace_same_side := fun t t' ht ht' hss => D.interlace_same_side t t' ht.1 ht'.1 hss
    complement_on_triangle := sorry }    -- L3
```

(`Punctured E δ t` is `t.val ≠ 0 ∧ |t.val| < δ`, `OppositeSides` is `t.val * t'.val < 0`, `SameSide` is
`0 < t.val * t'.val`; `AdjacentVisits`/`EmptyArcAdjacent`, `visitOn (xPair _) _ _`/`visitOfPair`,
`triangleSupports`/the literal, `geomAt E t _`/`(E.generic_punctured t _).crossingGeometry` unify by
δ-unfolding and proof irrelevance.) So `RProof.localization` reduces to L3's two fields with `δ := E.radius`.

## 5. Notes for the assembler / reviewers

* Header of the module explains the design; port with header only (as Bridge/B1, B3).
* `Event.NoG2Zero` is a new predicate (weaker than `IsSimpleRIII`); the reusable core (crossing constancy,
  continuity of `crossParam`, side constancy, parameter-difference sign change) is stated on it so that other
  event types with `G2 ∉ Z` (e.g. future RII / RI bundles) can reuse it. Silent events do NOT satisfy it.
* SM-germ consistency: for `Bridge.eventOfTriple hn g h` (which `RProof.isSimpleRIII_eventOfTriple` shows is
  `IsSimpleRIII`), `geometricTripleSides_of_tripleSides` + the accepted `triple_sides` give the same
  `GeometricTripleSides` as `IsSimpleRIII.geometricTripleSides` — two independent routes to the same
  statement (not formalised as an equality of proofs; both are Props).
* Nothing under work/lean was written; no API key involved.
