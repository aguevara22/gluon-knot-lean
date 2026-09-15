# U7b — REPORT (CV:lem:carriers, row 136, on the accepted geo layer)

Written 2026-09-14 (≈03:00–03:30 UTC / 11:00–11:30pm ET) by the U7b prover subagent (claude-fable-5-1) of the
pod executor, for the CV-DOM decision work/drafts/cvdom/DECISION_FINAL.md (§0 option (C), §2 fidelity + three
readings, §3 rulings R1–R5, §4 review-note template, §5 unit U7b, §6 order of rows step 2). Paths relative to the
package root /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.
Nothing under work/lean was written.

## 0. Deliverable and status

| item | value |
|---|---|
| file | `work/drafts/cvdom/U7b/CVCarriersLemma.lean` — 451 lines (≈100 lines module docstring, 4 trailing `#print axioms` lines removed at porting); intended home `work/lean/CV/CarriersLemma.lean` |
| imports | `CV.Carriers` (U7a, landed: `Piece`, `pieceOf`, `pieceLabels`, `piecesOn`, `residualGraph`, and through it `CV.CarrierBridges`, `SM.FlatCarriers`, `SM.GeoCarrierOrder`, Mathlib `SimpleGraph.Connectivity.Connected`), `SM.GeoCarrierCrossings` (U2a), `SM.GeoCarrierNoncrossing` (U2a). `SM.GeoCarrierCount` (U1a) arrives through `SM.GeoCarrierOrder`. `SM.GeoCornerPolygon` (U2b) is NOT imported: lem:carriers in the CV text has no corner clause (corners are def:wind's, row 138) |
| check | `cd work/lean && lake env lean ../drafts/cvdom/U7b/CVCarriersLemma.lean` → **exit 0**, no errors, no warnings |
| sorries | **none** (`grep -c sorry` = 0) |
| row theorem PROVED | `CV.carriers hD S hS : CV.CarriersData hD S hS` — `#print axioms CV.carriers` → `[propext, Classical.choice, Quot.sound]` (standard). Also standard: `CV.exists_unique_piece_carrier`, `CV.traversalEvaluation_eq_crossingPoint_iff`, `CV.visits_separated_iff` |
| `hn : 3 ≤ n` | absent from every declaration (ruling R5): the `hn`-free bodies of the §5 targets are used (`geoComponent_card_independent`, `geo_carriers_noncrossing_visits`, `geo_unselected_nonneighbor_both_visits_one_carrier`) |
| tier | the whole row is tier 0 (`hD.crossingGeometry`) except the setup sentence's fibre statement `traversalEvaluation_eq_crossingPoint_iff`, which uses tier 1 (`CarrierGeometry.ofDiagrammatic hD`, for `cg_crossingPoint_ne_vertex`) — inside the printed binder |
| accepted declarations modified / `geo*` names redefined | none (ruling R3) |
| new names (namespace `CV`) | `CarriersData`, `carriers` (row); `crossing_two_visits`, `traversalEvaluation_eq_crossingPoint_iff`, `card_visit_eq_two_mul_card_crossing`; `geoIndependent_of_mem_Ind`, `mem_geoSupportUnselected_of_mem_U`, `carriers_noncrossing`, `carriers_noncrossing_marks`, `carriers_nonadjacent_together`, `owner_eq_of_mem_U`, `visits_separated_iff`; `owner_eq_of_interlaces_mem_U`, `owner_eq_of_walk`, `owner_eq_of_same_piece`, `exists_unique_piece_carrier`, `pieceOwner` (def), `pieceOwner_spec`, `pieceOwner_unique`, `pieceOwner_pieceOf`, `mem_piecesOn_iff`, `piecesOn_eq`, `exists_unique_mem_piecesOn` |

## 1. Binder and conventions (DECISION_FINAL §2, §4)

* **Binder as printed** (d1_setup.tex:362–365 "Let P be diagrammatic … and S ∈ Ind(G_P) — genericity is not
  needed here and an earlier revision assumed it"): `(hD : CV.Diagrammatic P) (S : Finset (Crossing P))
  (hS : S ∈ CV.Ind hD.crossingGeometry)`. `hS` is a parameter of the bundle (it is the printed binder) and is
  consumed by (i)–(iv) through ruling R2's `CV.mem_Ind_iff_geoIndependent` (wrapped as
  `CV.geoIndependent_of_mem_Ind`). No `hn`.
* **Objects** are the accepted `SM.GeoCarrier` ones (def:flat-carriers) read through `hP := hD.crossingGeometry`:
  carriers `GeoComponent hP S`, "the visit `u` lies on the carrier `L`" = `geoOwner hP S (Sum.inr u) = L`. On
  SM-generic polygons these are def:smoothing's objects (`geoSmoothingSuccessor_eq_generic`,
  `geoComponentEquivGeneric`, FlatCarriersDefs.lean:638–724).
* **Ownership convention at a selected crossing** = SM conv:selected-visits (`SM.selected_visits_convention`, the
  same `selectedMarkPerm`): cited in the module docstring (review note, §4 template filled in) and in the
  docstring of `CarriersData`. The lemma's clauses (ii)–(iv) only ever read owners of UNselected visits, so the
  convention affects the row only through (i) (the count) and the companion `visits_separated_iff`.
* **The traversal circle** `Γ`: `TraversalPoint n` with the traversal map `traversalEvaluation P` and the strict
  oriented cyclic order `traversalBetween` — the only structure of `Γ` the statement reads ("no coordinate is
  placed on Γ": the model's coordinates `ZMod n × [0,1)` are never compared numerically in this row; every clause
  goes through `traversalBetween`, `geometricVisitPosition` and `geoOwner`). "in this cyclic order" is
  `traversalBetween u₁ u₂ u₃ ∧ traversalBetween u₃ u₄ u₁`, the shape of the accepted
  `SM.CarriersLemmaData.noncrossing`.

## 2. Clause → field map and proof sources

| printed clause (d1_setup.tex) | field of `CarriersData` | proved from |
|---|---|---|
| setup 365–370: "Let Γ be the traversal circle … the traversal map Γ → ℝ² that runs once around P, on which each double point of P has exactly two preimages, so that Γ carries 2m marked points. (… the crossing-free case m = 0 is allowed, with no marked points.)" | `traversal_circle` (4 conjuncts: fibre of the traversal map over `crossingPoint c` = the positions of the visits of `c`; `c` has exactly two visits; distinct visits have distinct positions; `|Visit P| = 2·|Crossing P|`) | `traversalEvaluation_eq_crossingPoint_iff` (new, tier 1: `edgePoint_injective` + `crossingParameter_spec` on an edge of `c`; on a third edge, `t = 0` gives a vertex = crossing point, against `cg_crossingPoint_ne_vertex (CarrierGeometry.ofDiagrammatic hD)`, and `0 < t` gives three concurrent edge interiors, against `CrossingGeometry` clause 3 = `hP.2.2`); `crossing_two_visits` (`crossing_visits_exist`, `visitTwin_ne`, `visit_eq_or_twin`); `geometricVisitPosition_injective`; `card_visit` + `card_crossing` (`m = 0` is just the case `Crossing P` empty — no hypothesis excludes it) |
| (i) 371 "the oriented smoothing of P along S has exactly |S|+1 carriers" | `count : Fintype.card (GeoComponent hP S) = S.card + 1` | `SM.GeoCarrier.geoComponent_card_independent hP hS'` (U1a; the `hn`-free body of the §5 target `geoComponent_card`) |
| (ii) 372–375 "the assignment of traversal points to carriers is non-crossing: there are no four points u₁,u₂,u₃,u₄ of Γ in this cyclic order, none of them a preimage of an element of S, with u₁,u₃ on one carrier and u₂,u₄ on a different carrier" | `noncrossing` (`¬ ∃ u₁ u₂ u₃ u₄ : Visit P, between u₁ u₂ u₃ ∧ between u₃ u₄ u₁ ∧ (u_k.1 ∉ S) ∧ own u₁ = own u₃ ∧ own u₂ = own u₄ ∧ own u₁ ≠ own u₂`) | `CV.carriers_noncrossing` ← `geo_carriers_noncrossing_visits` (U2a; the `hn`-free body of `geo_noncrossing`). The restriction `u_k.1 ∉ S` is printed and kept; the lane proves the clause WITHOUT it and for all marks (`CV.carriers_noncrossing_marks` ← `geoIndependent_noncrossingOwners`) |
| (iii) 376–377 "if c ∈ [m]∖S is non-adjacent in G_P to every element of S, then both occurrences of c lie on the same carrier" | `nonadjacent_together : ∀ c, c ∉ S → (∀ y ∈ S, ¬ GeometricInterlaces hP c y) → ∀ v w, v.1 = c → w.1 = c → own v = own w` (hypotheses literally as printed; `= c ∈ U hP S` by `CV.mem_U_iff`) | `CV.carriers_nonadjacent_together` ← `geo_unselected_nonneighbor_both_visits_one_carrier` (U2a §6; the `hn`-free body of `geo_nonneighbor_visits_together'`) via `mem_geoSupportUnselected_iff` |
| (iv) 378–380 "if H is a connected component of the induced graph G_P[[m]∖(S ∪ N_{G_P}(S))], then there is exactly one carrier on which both occurrences of every c ∈ H lie" | `piece_carrier : ∀ H : Piece hP S, ∃! q, ∀ c ∈ pieceLabels hP S H, ∀ v, v.1 = c → own v = q` (`Piece` = `ConnectedComponent` of `residualGraph hP S = G_P.induce ↑(U hP S)`, `U hP S = univ \ (S ∪ N hP S)`, row 139) | **new** (gap G3), `CV.exists_unique_piece_carrier`: §3 below |

### Clause (iv): the connectivity induction (gap G3), ≈ 110 lines

Follows the printed proof (d1:426–435) step for step:
1. `owner_eq_of_interlaces_mem_U`: for `c, c' ∈ U(S)` with `GeometricInterlaces hP c c'`, every visit of `c` and
   every visit of `c'` have the same owner. The accepted definition `GeometricInterlaces` (SM/GeometricInterlacement.lean:16)
   IS the alternation "their four occurrences alternate on Γ": it supplies `x₀ ≠ x₁`, `y₀, y₁` with
   `traversalBetween ⟨c,x₀⟩ ⟨c',y₀⟩ ⟨c,x₁⟩ ∧ traversalBetween ⟨c,x₁⟩ ⟨c',y₁⟩ ⟨c,x₀⟩`; (iii) (`owner_eq_of_mem_U`) gives
   `own⟨c,x₀⟩ = own⟨c,x₁⟩` and `own⟨c',y₀⟩ = own⟨c',y₁⟩`; (ii) in positive form (`geo_carriers_noncrossing_owner_eq`,
   U2a) gives `own⟨c,x₀⟩ = own⟨c',y₀⟩`; (iii) again transports to arbitrary visits `v` of `c`, `w` of `c'`. (The
   "exactly one visit between" characterisation `geo_interlaces_iff_unique` is not needed: the definition already
   carries the alternation.)
2. `owner_eq_of_walk`: induction on a `SimpleGraph.Walk` of `residualGraph hP S` (its `Adj` is `GeometricInterlaces`
   on the subtype `↑(U hP S)` by `Iff.rfl`, as U7a's `induced_adj`); `nil` is (iii), `cons` is step 1 followed by
   the induction hypothesis through any visit of the intermediate vertex (`crossing_visits_exist`).
3. `owner_eq_of_same_piece`: `pieceOf c = pieceOf c'` ⇒ `Reachable` (`SimpleGraph.ConnectedComponent.eq`) ⇒ a walk
   (`Reachable.elim`) ⇒ step 2.
4. `exists_unique_piece_carrier`: existence with `q := own⟨c₀, i⟩` for a label `c₀` of `H` (`pieceLabels_nonempty`)
   and step 3; uniqueness "because it is a function" (d1:435): any `q` satisfying the clause equals `own⟨c₀, i⟩`.
5. Auxiliaries for the later rows (§5 U7b "`CV.pieceOwner H`, `piecesOn_eq`"; consumed by def:X1 / lem:piececurve):
   `pieceOwner hP hS H := Classical.choose …` with `pieceOwner_spec`, `pieceOwner_unique`, `pieceOwner_pieceOf`
   (the carrier of the piece of `c ∈ U(S)` is the carrier of either visit of `c`), `mem_piecesOn_iff`
   (`H ∈ piecesOn hP S q ↔ pieceOwner hP hS H = q`), `piecesOn_eq`, `exists_unique_mem_piecesOn` (the `piecesOn q`
   partition the pieces). All on the CV binder `hS : S ∈ Ind hP` (ruling R2).

## 3. Readings the reviewer should confirm (none is a scope change)

1. **"points of Γ" in (ii)** are rendered as the marked points of `Γ`, the crossing visits (the sentence before
   says "Γ carries 2m marked points"; only marked points are "assigned to carriers" in the finite model). The
   model's further marks, the original vertices, satisfy the same clause: `CV.carriers_noncrossing_marks` (all
   `Mark P`, selected visits included) is provided as a companion theorem outside the bundle.
2. **"in this cyclic order"** = strict oriented cyclic order `traversalBetween u₁ u₂ u₃ ∧ traversalBetween u₃ u₄ u₁`
   (this implies the four points are distinct — `geo_ncx_cyclic_visits_distinct` — so no separate distinctness
   conjunct is added, unlike the SM bundle `CarriersLemmaData.noncrossing`, whose extra distinctness hypotheses only
   weaken the negated statement).
3. **"none of them a preimage of an element of S"** = `u_k.1 ∉ S`; kept because printed, although the lane's
   theorem does not need it (item 1).
4. **The setup sentence** is rendered as a field (`traversal_circle`) because it makes factual claims ("exactly two
   preimages", "2m marked points"); "no coordinate is placed on Γ" and "m = 0 is allowed" are properties of the
   statement (only `traversalBetween` is read; no nonemptiness hypothesis), noted in the docstring, not fields.
   "exactly two preimages" is proved in the strong sense (the fibre of the traversal map over the crossing point
   is exactly the two visit positions), which is where tier 1 (`hD`, no vertex on a non-incident edge) enters.
5. **(iii)'s hypothesis** is spelled as printed (`c ∉ S`, non-adjacent to every element of `S`) rather than as
   `c ∈ U hP S`; the two are `CV.mem_U_iff`. (iv) uses `U` through `Piece` because the printed (iv) names the
   induced graph on `[m]∖(S ∪ N(S))`, which is the accepted `CV.U`.

## 4. Not rendered (deliberately)

* The proof text 379–449 (induction on |S|, the arcs α, β, the closing remark on where distinct carriers can meet
  in the plane). The closing remark's mathematical content — distinct carriers meet only at dominated crossings
  — is offered as the companion theorem `CV.visits_separated_iff hP hS v : own v ≠ own (twin v) ↔ v.1 ∈ S ∨
  v.1 ∈ N hP S` (← `geo_selected_visits_separated`, `geo_neighbor_visit_owners_ne`, (iii)); it is not a field.
* The SM twin row's extra clauses (SM/CarriersLemma.lean: inherited cyclic order, corner polygons, self-intersections,
  neighbour separation) — they are SM lem:carriers' sentences, not CV lem:carriers'. The inherited order is CV
  lem:carrierword (row 137, U7b's second row — NOT in this file: this unit delivered row 136 only, as tasked);
  the corner turns are def:wind (138, U7a).

## 5. The bundle (from the compiled file, lines 384–444)

```lean
structure CarriersData (hS : S ∈ Ind hD.crossingGeometry) : Prop where
  /-- "Let `Γ` be the traversal circle: an abstract oriented circle together with the traversal map
  `Γ → ℝ²` that runs once around `P`, on which each double point of `P` has exactly two preimages,
  so that `Γ` carries `2m` marked points. (… in particular the crossing-free case `m = 0` is allowed,
  with no marked points.)": the preimages of a double point `c` under the traversal map are exactly
  the positions of its visits; `c` has exactly two visits; distinct visits have distinct positions;
  there are `2m` visits in all (`m = 0` included) -/
  traversal_circle :
    (∀ (c : Crossing P) (p : TraversalPoint n), traversalEvaluation P p = crossingPoint c ↔
      ∃ v : Visit P, v.1 = c ∧ p = geometricVisitPosition hD.crossingGeometry v) ∧
    (∀ c : Crossing P, ∃ v w : Visit P, v.1 = c ∧ w.1 = c ∧ v ≠ w ∧
      ∀ u : Visit P, u.1 = c → u = v ∨ u = w) ∧
    Function.Injective (geometricVisitPosition hD.crossingGeometry) ∧
    Fintype.card (Visit P) = 2 * Fintype.card (Crossing P)
  /-- "(i) the oriented smoothing of `P` along `S` has exactly `|S|+1` carriers" -/
  count : Fintype.card (GeoComponent hD.crossingGeometry S) = S.card + 1
  /-- "(ii) the assignment of traversal points to carriers is *non-crossing*: there are no four
  points `u₁, u₂, u₃, u₄` of `Γ` in this cyclic order, none of them a preimage of an element of `S`,
  with `u₁, u₃` on one carrier and `u₂, u₄` on a different carrier" (the points of `Γ` assigned to
  carriers are its marked points, the visits; "in this cyclic order" is the strict oriented cyclic
  order `traversalBetween u₁ u₂ u₃ ∧ traversalBetween u₃ u₄ u₁`) -/
  noncrossing :
    ¬ ∃ u₁ u₂ u₃ u₄ : Visit P,
      traversalBetween (geometricVisitPosition hD.crossingGeometry u₁)
        (geometricVisitPosition hD.crossingGeometry u₂)
        (geometricVisitPosition hD.crossingGeometry u₃) ∧
      traversalBetween (geometricVisitPosition hD.crossingGeometry u₃)
        (geometricVisitPosition hD.crossingGeometry u₄)
        (geometricVisitPosition hD.crossingGeometry u₁) ∧
      (u₁.1 ∉ S ∧ u₂.1 ∉ S ∧ u₃.1 ∉ S ∧ u₄.1 ∉ S) ∧
      geoOwner hD.crossingGeometry S (Sum.inr u₁) = geoOwner hD.crossingGeometry S (Sum.inr u₃) ∧
      geoOwner hD.crossingGeometry S (Sum.inr u₂) = geoOwner hD.crossingGeometry S (Sum.inr u₄) ∧
      geoOwner hD.crossingGeometry S (Sum.inr u₁) ≠ geoOwner hD.crossingGeometry S (Sum.inr u₂)
  /-- "(iii) if `c ∈ [m] ∖ S` is non-adjacent in `G_P` to every element of `S`, then both
  occurrences of `c` lie on the same carrier" -/
  nonadjacent_together : ∀ c : Crossing P, c ∉ S →
    (∀ y ∈ S, ¬ GeometricInterlaces hD.crossingGeometry c y) →
    ∀ v w : Visit P, v.1 = c → w.1 = c →
      geoOwner hD.crossingGeometry S (Sum.inr v) = geoOwner hD.crossingGeometry S (Sum.inr w)
  /-- "(iv) if `H` is a connected component of the induced graph `G_P[[m] ∖ (S ∪ N_{G_P}(S))]`,
  then there is exactly one carrier on which both occurrences of every `c ∈ H` lie" (`H : Piece`,
  the connected components of `residualGraph = G_P.induce (U S)`, `U S = univ \ (S ∪ N S)`;
  `c ∈ H` is `c ∈ pieceLabels H`) -/
  piece_carrier : ∀ H : Piece hD.crossingGeometry S, ∃! q : GeoComponent hD.crossingGeometry S,
    ∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
      geoOwner hD.crossingGeometry S (Sum.inr v) = q

/-- **Row 136, CV:lem:carriers**, on the printed binder `hD : Diagrammatic P`, `S ∈ Ind(G_P)`. -/
theorem carriers (hS : S ∈ Ind hD.crossingGeometry) : CarriersData hD S hS where
  traversal_circle :=
    ⟨traversalEvaluation_eq_crossingPoint_iff hD, crossing_two_visits,
      geometricVisitPosition_injective hD.crossingGeometry, card_visit_eq_two_mul_card_crossing⟩
  count := geoComponent_card_independent hD.crossingGeometry
    (geoIndependent_of_mem_Ind hD.crossingGeometry hS)
  noncrossing := carriers_noncrossing hD.crossingGeometry hS
  nonadjacent_together := carriers_nonadjacent_together hD.crossingGeometry hS
  piece_carrier := exists_unique_piece_carrier hD.crossingGeometry hS

end CarriersRow

end CV
```

## 6. Axioms

```
'CV.carriers' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.exists_unique_piece_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.traversalEvaluation_eq_crossingPoint_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.visits_separated_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```
