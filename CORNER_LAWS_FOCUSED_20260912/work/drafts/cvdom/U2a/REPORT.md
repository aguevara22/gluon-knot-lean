# CV-DOM unit U2a — REPORT (2026-09-14 ~03:15 UTC / 11:15pm ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5) and §5 row **U2a**. Nothing under work/lean was written. Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## Deliverables

| file | intended home | lines | status |
|---|---|---:|---|
| `work/drafts/cvdom/U2a/GeoCarrierCrossings.lean` | `work/lean/SM/GeoCarrierCrossings.lean` (new module, namespace `SM.GeoCarrier`, `open Carrier`, CV-free; single import `SM.GeoCarrierOrder`) | 686 | `cd work/lean && lake env lean ../drafts/cvdom/U2a/GeoCarrierCrossings.lean` → **exit 0, no output (no warnings), no `sorry`** (≈ 5 s) |
| `work/drafts/cvdom/U2a/GeoCarrierNoncrossing.lean` | `work/lean/SM/GeoCarrierNoncrossing.lean` (same conventions; single import `SM.GeoCarrierOrder`; independent of the first file — CarrierNoncrossing's proofs use nothing from CarrierCrossings / CarrierNeighborSeparation) | 410 | same command → **exit 0, no output, no `sorry`** (≈ 7 s) |
| `work/drafts/cvdom/U2a/port_u2a.py` | tooling only | — | port_lane.py + the residue rules (rename dictionary, binder rules, dropped shared declarations, the hand edits listed below); run from work/ → `/tmp/u2a/{crossings,noncrossing}_body.lean` |
| `work/drafts/cvdom/U2a/assemble_u2a.py` | tooling only | — | wraps the two bodies with the hand-written header, §0 (`N(S)`/`U(S)`), §8 (crossings of a carrier vs `U(S)`) and the §5 target blocks; reproduces both .lean files exactly |

62 declarations (46 + 16), **all tier 0** (`hP : CrossingGeometry P`); no lemma needed `CarrierGeometry` or
`WeakGeneric`. `grep -c sorry` = 0 in both files. `#print axioms` (on copies with the lines appended):
`geo_noncrossing`, `geo_neighbor_visits_separated`(`'`), `geo_nonneighbor_visits_together`(`'`), `mem_geoCarrierCrossings`,
`geoCarrierCrossings_subset_U`, `geoCarrierCrossings_disjoint`, `geoCarrierCrossingCount`, `sum_geoCarrierCrossingCount_eq_card_U`,
`geoSupportUnselected_eq_biUnion_geoCarrierCrossings`, `mem_geoCarrierCrossings_iff_U`, `geo_smoothing_corner_directions`,
`geo_vertex_corner_directions`, `geo_unselected_nonneighbor_exists_unique_carrier`, `geo_neighbor_not_mem_geoCarrierCrossings`,
`geoIndependent_noncrossingOwners`, `geo_carriers_noncrossing_owner_eq`, `geo_carriers_noncrossing_rotate`,
`geo_ncx_cyclic_visits_distinct` — each `[propext, Classical.choice, Quot.sound]` only (standard).

Name safety (ruling R3): each of the 62 declared names grepped against every declaration site under work/lean
(SM, CV, Bridge, RProof, Supplemental; `.lake` excluded) — zero hits; no accepted `geo*` name is re-declared
(`geoCarrierCrossings` and the eight FlatCarriers §3 direction lemmas are referenced, marked `-- [port]` in the file).
No `Generic`, `hP.1`, `hP.2`, `independentSupports`, `IsDecomposition` anywhere except header prose; `hn hP` occurs
only at the four calls of the accepted `hn`-taking FlatCarriers lemmas (`geo_visit_incoming_direction hn hP`, …).

## §5 U2a targets — all proved, exact shapes

The three `CarriersLemmaData` mirrors were checked **textually** (script in the compile log): the statement after
`(hS : GeoIndependent hP S) :` equals the accepted field text (SM/CarriersLemma.lean) under exactly
`owner hn hP S ↦ geoOwner hP S`, `visitPosition hn hP.1 ↦ geometricVisitPosition hP`, `supportNeighbors hn hP S ↦
geoSupportNeighbors hP S`, `supportUnselected hn hP S ↦ geoSupportUnselected hP S` (whitespace-normalised: IDENTICAL ×3).

| §5 target | draft (line) | statement | proof |
|---|---|---|---|
| `geo_noncrossing (hn) (hP) (hS)` | GeoCarrierNoncrossing.lean:396 | `¬ ∃ u₁ u₂ u₃ u₄ : Visit P, (six ≠) ∧ traversalBetween (geometricVisitPosition hP u₁) (… u₂) (… u₃) ∧ traversalBetween (… u₃) (… u₄) (… u₁) ∧ geoOwner hP S (Sum.inr u₁) = geoOwner hP S (Sum.inr u₃) ∧ geoOwner … u₂ = geoOwner … u₄ ∧ geoOwner … u₁ ≠ geoOwner … u₂` = `CarriersLemmaData.noncrossing` (CarriersLemma.lean:113–124) | `:= geo_carriers_noncrossing hP hS` (port of CarrierNoncrossing.lean:410) |
| `geo_neighbor_visits_separated (hn) (hP) (hS)` | GeoCarrierCrossings.lean:652 | `∀ x ∈ geoSupportNeighbors hP S, ∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v))` = `neighbor_visits_separated` | `geo_neighbor_visit_owners_ne hP hS hx v hv` (port of CarrierNeighborSeparation.lean:197) |
| `geo_neighbor_visits_separated' (hn) (hP) (hS)` | :661 | the §5 alternative form: `∀ x, (∃ y ∈ S, GeometricInterlaces hP x y) → ∀ v, v.1 = x → …` (= the RHS of `CV.mem_N_iff`) | via `mem_geoSupportNeighbors` |
| `geo_nonneighbor_visits_together (hn) (hP) (hS)` | :670 | `∀ x ∈ geoSupportUnselected hP S, ∀ v w : Visit P, v.1 = x → w.1 = x → geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr w)` = `nonneighbor_visits_together` | `geo_unselected_nonneighbor_both_visits_one_carrier` (port of CarrierCrossings.lean:433) |
| `geo_nonneighbor_visits_together' (hn) (hP) (hS)` | :678 | `∀ x, x ∉ S → (∀ y ∈ S, ¬ GeometricInterlaces hP x y) → ∀ v w, …` (= the RHS of `CV.mem_U_iff`) | via `mem_geoSupportUnselected_iff` |
| `mem_geoCarrierCrossings (hP) (S) (q) (x)` | :89 | `x ∈ geoCarrierCrossings hP S q ↔ x ∉ S ∧ ∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q` | `simp only` (port of CarrierCrossings.lean:66); fibre form `mem_geoCarrierCrossings_iff_fiber` :96 |
| `geoCarrierCrossings_subset_U (hP) (hS) (q)` | :591 | `geoCarrierCrossings hP S q ⊆ geoSupportUnselected hP S` | NEW (no source counterpart, 11 lines): both visits share the owner `q`, which `geo_neighbor_visit_owners_ne` forbids for a neighbour |
| `geoCarrierCrossings_disjoint (hP) (S) (hqr : q ≠ r)` | :124 | `Disjoint (geoCarrierCrossings hP S q) (geoCarrierCrossings hP S r)` | port of CarrierCrossings.lean:103 |
| `geoCarrierCrossingCount (hP) (S) (q) : ℕ` | :85 | `(geoCarrierCrossings hP S q).card` (= `m_Q`); `geoCarrierCrossingCount_eq_card` :134 (`rfl`) | port of CarrierCrossings.lean:62 |

Further counting / membership lemmas (§8, NEW unless marked): `mem_geoCarrierCrossings_iff_U (hP) (hS) (q) (x) : x ∈ geoCarrierCrossings hP S q ↔ x ∈ geoSupportUnselected hP S ∧ ∃ v, v.1 = x ∧ geoOwner hP S (Sum.inr v) = q` (:603);
`geoSupportUnselected_eq_biUnion_geoCarrierCrossings (hP) (hS) : geoSupportUnselected hP S = Finset.univ.biUnion (geoCarrierCrossings hP S)` (:617; the ⊆ half is the port `geoSupportUnselected_subset_biUnion_geoCarrierCrossings` :361);
`sum_geoCarrierCrossingCount_eq_card_U (hP) (hS) : ∑ q, geoCarrierCrossingCount hP S q = (geoSupportUnselected hP S).card` (:627; `∑ m_Q = |U(S)|`, from the port `sum_geoCarrierCrossingCount` :139);
`geoIsCrossingOf_iff_mem` (:634), `geo_neighbor_not_mem_geoCarrierCrossings (hP) (hS) (hx : x ∈ geoSupportNeighbors hP S) (q) : x ∉ geoCarrierCrossings hP S q` (:641; def:smoothing's last sentence on the accepted set);
`geo_unselected_nonneighbor_exists_unique_carrier (hP) (hS) (hx : x ∈ geoSupportUnselected hP S) : ∃! q, x ∈ geoCarrierCrossings hP S q` (:351, port).

Nothing left unproved; no obstacle; no lemma needed `SM.Generic` beyond `CrossingGeometry` (no tier-1/2 statement).

## `N(S)`, `U(S)` on the SM side (§0, new definitions — assembler please note)

The SM module must stay CV-free (U0's convention; `CV.*` is not in the closure of `SM.GeoCarrierOrder`, and CV imports SM),
so the §5 statements "`∀ x ∈ N hP S`" are realised on the ports of SM/InterlaceSupports.lean:49–75:
`def geoSupportNeighbors (hP) (S) : Finset (Crossing P) := Finset.univ.filter fun y => ∃ x ∈ S, GeometricInterlaces hP y x` (:48),
`def geoSupportUnselected (hP) (S) := Finset.univ \ (S ∪ geoSupportNeighbors hP S)` (:59), with `mem_geoSupportNeighbors` (:52),
`geoSupportUnselected_eq` (:63, `rfl`), `mem_geoSupportUnselected` (:67), `mem_geoSupportUnselected_iff` (:74, the RHS of `CV.mem_U_iff`).
These are the accepted `CV.N` / `CV.U` (CV/Events.lean:171, 177) word for word: **`CV.N hP S = geoSupportNeighbors hP S` and
`CV.U hP S = geoSupportUnselected hP S` are `rfl`** (checked: a copy of GeoCarrierCrossings.lean with `import CV.CarrierBridges`
prepended and the two `example … := rfl` appended compiles, exit 0). So U7b can state lem:carriers (ii)/(iii) on `CV.N`/`CV.U`
and apply `geo_neighbor_visits_separated` / `geo_nonneighbor_visits_together` directly (or through the primed forms via
`CV.mem_N_iff` / `CV.mem_U_iff`). Neither name exists anywhere under work/lean (R3 check above). If the executor prefers no new
SM definitions, replace the two defs by the primed target forms; every §8 lemma then needs the `mem_*_iff` rewrite.

## Declarations, source → geo name (46 + 16)

Status: "ported" = declared in the draft, proof verbatim modulo the substitutions; "accepted" = the `geo*` counterpart exists
in SM/FlatCarriers.lean (not re-declared); "shared" = hypothesis-free `SM.Carrier` declaration in the import closure, used as is.

**SM/CarrierCrossings.lean** (→ GeoCarrierCrossings.lean §1–§6)

| source (line) | geo name | status | draft line |
|---|---|---|---:|
| `carrierCrossings` (56) | `geoCarrierCrossings` | accepted (FlatCarriersDefs.lean:451) | — |
| `carrierCrossingCount` (62) | `geoCarrierCrossingCount` | ported | 85 |
| `mem_carrierCrossings` (66) | `mem_geoCarrierCrossings` | ported | 89 |
| `mem_carrierCrossings_iff_fiber` (73) | `mem_geoCarrierCrossings_iff_fiber` | ported | 96 |
| `selected_not_mem_carrierCrossings` (89) | `geo_selected_not_mem_carrierCrossings` | ported | 112 |
| `carrierCrossings_subset_compl` (95) | `geoCarrierCrossings_subset_compl` | ported | 117 |
| `carrierCrossings_disjoint` (103) | `geoCarrierCrossings_disjoint` | ported | 124 |
| `carrierCrossingCount_eq_card` (113) | `geoCarrierCrossingCount_eq_card` | ported | 134 |
| `sum_carrierCrossingCount` (118) | `sum_geoCarrierCrossingCount` | ported | 139 |
| `markSuccessor_symm_visit_edge` (130), `_vertex_edge` (143), `smoothingSegment_positive_direction_of_succ` (164), `smoothingSegment_incoming_positive_direction` (178) | `geo*` | accepted (FlatCarriers.lean:2892–2934) | — |
| `smoothingSegment_incoming_mem_edgeSegment` (188) | `geoSmoothingSegment_incoming_mem_edgeSegment (hP) (S) (a) {u} (hu0) (hu1)` | ported (no `hn`) | 159 |
| `visitTwin_snd_ne` (204), `visitTwin_edge_ne` (209), `visit_crossing_val_eq_pair` (216) | same names | shared | — |
| `visit_incoming_direction` (231), `selected_visit_outgoing_direction` (251), `unselected_visit_outgoing_direction` (270), `vertex_outgoing_direction` (281), `vertex_incoming_direction` (297) | `geo_*` (all take `hn`) | accepted (FlatCarriers.lean:2937–2991) | — |
| `visit_incoming_mem_edgeSegment` (242) | `geo_visit_incoming_mem_edgeSegment (hn) (hP) (S) (v) {u} …` | ported; `hn` kept (`geoMarkSuccessor_symm_visit_edge hn`) | 183 |
| `selected_visit_outgoing_mem_edgeSegment` (261) | `geo_selected_visit_outgoing_mem_edgeSegment (hP) (S) (v) (hv) {u} …` | ported (no `hn`) | 192 |
| `vertex_outgoing_mem_edgeSegment` (290) | `geo_vertex_outgoing_mem_edgeSegment (hP) (S) (i) {u} …` | ported (no `hn`) | 203 |
| `vertex_incoming_mem_edgeSegment` (307) | `geo_vertex_incoming_mem_edgeSegment (hn) (hP) (S) (i) {u} …` | ported; `hn` kept | 211 |
| `smoothing_corner_directions` (323) | `geo_smoothing_corner_directions (hn) (hP) (S) (q) (v) (hv) (hq)` | ported; `hn` kept (direction lemmas) | 227 |
| `vertex_corner_directions` (362) | `geo_vertex_corner_directions (hn) (hP) (S) (q) (i) (hq)` | ported; `hn` kept | 266 |
| `insert_unselected_mem_independentSupports` (399) | `geoIndependent_insert_unselected (hP) (hS) (hx) : GeoIndependent hP (insert x S)` | ported (renamed: the source name mentions `independentSupports`) | 302 |
| `unselected_nonneighbor_visit_owner_eq_twin` (419) | `geo_unselected_nonneighbor_visit_owner_eq_twin` | ported | 320 |
| `unselected_nonneighbor_both_visits_one_carrier` (433) | `geo_unselected_nonneighbor_both_visits_one_carrier` | ported | 333 |
| `unselected_nonneighbor_mem_carrierCrossings` (443) | `geo_unselected_nonneighbor_mem_carrierCrossings` | ported | 342 |
| `unselected_nonneighbor_exists_unique_carrier` (453) | `geo_unselected_nonneighbor_exists_unique_carrier` | ported | 351 |
| `supportUnselected_subset_biUnion_carrierCrossings` (464) | `geoSupportUnselected_subset_biUnion_geoCarrierCrossings` | ported | 361 |

**SM/CarrierNeighborSeparation.lean** (→ GeoCarrierCrossings.lean §7)

| source (line) | geo name | status | draft line |
|---|---|---|---:|
| `interlaces_twin_different_slices` (44) | `geo_interlaces_twin_different_slices (hP) (v w) (hint : GeometricInterlaces hP v.1 w.1) (k A B hrot)` | ported (`not_interlaces_iff_twin_same_arc hn hP → geo_not_interlaces_iff_twin_same_arc hP`, GeoCarrierCount.lean:1354; `markList_rotate_left_iff hn hP → geoMarkList_rotate_left_iff hP`) | 377 |
| `interlacing_pair_owners_ne_insert` (106) | `geo_interlacing_pair_owners_ne_insert` | ported (`smoothingSuccessor_insert_child_data → geoSmoothingSuccessor_insert_child_data`) | 439 |
| `interlacing_visit_owners_ne_insert_partial` (151) | `geo_interlacing_visit_owners_ne_insert_partial` | ported (`component_empty_subsingleton`, `inheritsMarkOrder_empty`, `independent_remaining_pair_owners`, `owner_insert_ne_of_ne`, `owner_eq_iff` → their `geo*`) | 484 |
| `neighbor_visit_owners_ne` (197) | `geo_neighbor_visit_owners_ne (hP) (hS) (hx : x ∈ geoSupportNeighbors hP S) (v) (hv)` | ported | 529 |
| `interlacing_visit_owners_ne` (212) | `geo_interlacing_visit_owners_ne (hP) (hS) (hsS) (v) (hint)` | ported | 544 |
| `neighbor_not_mem` (222) | `geo_neighbor_not_mem (hP) (hS) (hx) : x ∉ S` | ported (`(mem_independentSupports_iff …).mp hS → hS`; `omit [NeZero n]` dropped, see hand edits) | 553 |
| `IsCrossingOf` (232) | `GeoIsCrossingOf (hP) (S) (q) (x) : Prop` | ported | 563 |
| `neighbor_no_common_owner` (237) | `geo_neighbor_no_common_owner` | ported | 568 |
| `neighbor_not_isCrossingOf` (246) | `geo_neighbor_not_isCrossingOf` | ported | 577 |

**SM/CarrierNoncrossing.lean** (→ GeoCarrierNoncrossing.lean)

| source (line) | geo name | status | draft line |
|---|---|---|---:|
| `ncx_cyclic_mod_add_iff` (57), `ncx_sorted_rotate_getElem_cyclic_iff` (71), `ncx_mem_cons_of_mem_cons_filter` (191), `ncx_traversalBetween_ne` (330), `ncx_cyclic_four_iff` (341) | same names | shared (hypothesis-free; SM.CarrierNoncrossing is in the closure of SM.GeoCarrierOrder) | — |
| `ncx_markList_rotate_between_iff` (94) | `geo_ncx_markList_rotate_between_iff (hP) (k i j l) (hi hj hl)` | ported (`let _ := geoMarkLinearOrder hP`) | 47 |
| `ncx_rotate_index_left_child` (110) / `_right_child` (137) | `geo_ncx_rotate_index_left_child` / `_right_child` | ported | 63 / 90 |
| `ncx_split_alternation_false` (165) | `geo_ncx_split_alternation_false` | ported | 118 |
| `NoncrossingOwners` (202) | `GeoNoncrossingOwners (hP) (T) : Prop` | ported | 150 |
| `noncrossingOwners_empty` (213) / `_insert` (224) | `geoNoncrossingOwners_empty` / `_insert (hP) (T) (hI : GeoInheritsMarkOrder hP T) (v) (hv) (hc) (hN)` | ported (`owner_insert_eq_imp`, `owner_insert_iff_of_unaffected`, `smoothingSuccessor_insert_child_data` → `geo*`) | 161 / 172 |
| `independent_noncrossingOwners_partial` (300) / `independent_noncrossingOwners` (321) | `geoIndependent_noncrossingOwners_partial (hP) (hS) (T) (hTS)` / `geoIndependent_noncrossingOwners (hP) (hS)` | ported (`independent_partial_invariants → geoIndependent_partial_invariants`, GeoCarrierCount.lean) | 248 / 268 |
| `ncx_cyclic_visits_distinct` (354) | `geo_ncx_cyclic_visits_distinct (hP : CrossingGeometry P) (u₁ u₂ u₃ u₄) (h123) (h341)` | ported (`hP : G1 P`, `visitPosition hn hP` → `CrossingGeometry`, `geometricVisitPosition hP`) | 280 |
| `carriers_noncrossing_marks` (378) | `geo_carriers_noncrossing_marks` | ported | 304 |
| `carriers_noncrossing_visits` (395) | `geo_carriers_noncrossing_visits` | ported | 321 |
| `carriers_noncrossing` (410) | `geo_carriers_noncrossing (hP) (hS)` | ported | 336 |
| `carriers_noncrossing_owner_eq` (426) | `geo_carriers_noncrossing_owner_eq` | ported | 352 |
| `carriers_noncrossing_rotate` (442) | `geo_carriers_noncrossing_rotate` | ported | 368 |
| `carriers_noncrossing_of_isDecomposition` (462) | — | **not ported** (`IsDecomposition` is `SM.Generic`-bound; ruling R2) | — |

## Method and hand edits (everything else is the transformer's output, proofs verbatim)

1. `port_lane.py` on the three sources (250 / 103 / 254 substitutions), then `port_u2a.py`:
   (a) binder `(hS : S ∈ independentSupports hn hP) → (hS : GeoIndependent hP S)`, `(mem_independentSupports_iff hn hP S).mp hS → hS`
   (`GeoIndependent` is that clause, FlatCarriersDefs.lean:457), `insert x S ∈ independentSupports hn hP → GeoIndependent hP (insert x S)`
   and the now-empty `rw [mem_independentSupports_iff] at hS ⊢` removed; `(hn : 3 ≤ n) {P} (hP : G1 P) → {P} (hP : CrossingGeometry P)`,
   `visitPosition hn hP → geometricVisitPosition hP`;
   (b) rename dictionary for the names outside DEFMAP: `mem_carrierCrossings* → mem_geoCarrierCrossings*`, `carrierCrossingCount →
   geoCarrierCrossingCount`, `sum_carrierCrossingCount → sum_geoCarrierCrossingCount`, `IsCrossingOf → GeoIsCrossingOf`,
   `NoncrossingOwners → GeoNoncrossingOwners`, `noncrossingOwners_* → geoNoncrossingOwners_*`, `independent_noncrossingOwners* →
   geoIndependent_noncrossingOwners*`, `insert_unselected_mem_independentSupports → geoIndependent_insert_unselected`,
   `supportNeighbors/Unselected → geoSupportNeighbors/Unselected`, `mem_support* → mem_geoSupport*`, `Interlaces → GeometricInterlaces`,
   `interlaces_symm → geometricInterlaces_symm`, `not_interlaces_iff_twin_same_arc → geo_not_interlaces_iff_twin_same_arc`,
   `mem_markList → mem_geoMarkList`, `InheritsMarkOrder → GeoInheritsMarkOrder`, `inheritsMarkOrder_empty → geoInheritsMarkOrder_empty`,
   `component_empty_subsingleton → geoComponent_empty_subsingleton`, `independent_remaining_pair_owners / independent_partial_invariants /
   owner_insert_ne_of_ne / owner_insert_eq_imp / owner_insert_iff_of_unaffected / smoothingSuccessor_insert_child_data → geo*`
   (all in SM/GeoCarrierCount.lean, U1a), then the global ` hn hP → hP` on every `geo*`/`Geo*` application;
   (c) hypothesis-free declarations dropped and referenced under their `SM.Carrier` names (they are in the import closure, so a
   same-named re-declaration in `SM.GeoCarrier` would be ambiguous under `open Carrier`): `visitTwin_snd_ne`, `visitTwin_edge_ne`,
   `visit_crossing_val_eq_pair`, `ncx_mem_cons_of_mem_cons_filter`, `ncx_traversalBetween_ne`, `ncx_cyclic_four_iff`
   (+ `ncx_cyclic_mod_add_iff`, `ncx_sorted_rotate_getElem_cyclic_iff`, declared before the source's `noncomputable section`).
2. Hand edits (in `port_u2a.py: hand()`): `hn : 3 ≤ n` restored on `geo_visit_incoming_mem_edgeSegment`, `geo_vertex_incoming_mem_edgeSegment`,
   `geo_smoothing_corner_directions`, `geo_vertex_corner_directions` and at the calls of the accepted `hn`-taking lemmas
   (`geoMarkSuccessor_symm_visit_edge/_vertex_edge hn`, `geo_visit_incoming_direction hn`, `geo_selected_visit_outgoing_direction hn`,
   `geo_vertex_incoming/outgoing_direction hn`); the accepted `geoSmoothingSegment_mem_edgeSegment hP S a u hu0 hu1` has `u` explicit
   (3 call sites; the source's had it implicit); `owner_predecessor`/`owner_successor` in `rw` → `geoOwner_predecessor`/`geoOwner_successor`
   (bare names the transformer's `X hn hP` rule does not see); `omit [NeZero n] in` removed from `geoIndependent_insert_unselected` and
   `geo_neighbor_not_mem` (their statements now mention `geoSupportNeighbors/Unselected`, whose `Finset.univ : Finset (Crossing P)` needs
   `NeZero n` — the source's `supportNeighbors` built the instance from `hn` inside the definition); one indentation slip.
3. Hand-written blocks (`assemble_u2a.py`): §0 (`N(S)`/`U(S)`, 6 declarations, 30 lines), §8 (6 lemmas, 55 lines), §9 / §5 targets
   (5 aliases). Compile loop: 2 rounds (round 1: `omit` on the §0 defs illegal; a block-dropping bug in the script had deleted the
   theorem before the §3 header; the second file's shell lacked `env.sh`). Round 2: exit 0 ×2, no warnings.

Tiers: every declaration is tier 0; `hn` is genuinely needed only where the accepted FlatCarriers §3 lemmas take it (they use
`geoMarkSuccessor_position_cases hn`); on the five §5 target aliases it is unused and kept under `set_option linter.unusedVariables false in`
(the U1a/U1b treatment). The `hn`-free content is the un-aliased lemma named in each row above.

## Notes for the assembler and downstream units (U2c, U3, U7b, U7c)

- Import graph: `SM.GeoCarrierCrossings` and `SM.GeoCarrierNoncrossing` both import only `SM.GeoCarrierOrder`; neither imports the other
  (the assembler may keep them independent or let Noncrossing import Crossings; nothing requires it). CV-free.
- U7b (lem:carriers (ii)–(iv) on `CV.N`/`CV.U`): `CV.N hP S = geoSupportNeighbors hP S` and `CV.U hP S = geoSupportUnselected hP S` by `rfl`;
  (ii) restricted to unselected visits follows from `geo_noncrossing hn hP hS` by weakening; (iii) = `geo_neighbor_visits_separated` +
  `geo_nonneighbor_visits_together`; (iv)'s "exactly one carrier per piece" gets `geo_unselected_nonneighbor_exists_unique_carrier`,
  `mem_geoCarrierCrossings_iff_U` and `geo_carriers_noncrossing_owner_eq`.
- U7c / U2c: `geoSupportUnselected_eq_biUnion_geoCarrierCrossings`, `geoCarrierCrossings_disjoint`, `sum_geoCarrierCrossingCount_eq_card_U`
  give "pieces partition `U(S)`" and the writhe count; `geo_smoothing_corner_directions hn hP S q v hv hq` / `geo_vertex_corner_directions`
  are the corner-direction inputs of the self-intersection analysis (with the accepted `geo_*_direction` lemmas of FlatCarriers §3).
- Call shapes that differ from the source: `geoSmoothingSegment_mem_edgeSegment hP S a u hu0 hu1` (accepted, `u` explicit, no `hn`);
  `geoIndependent_insert_unselected hP hS hx` (renamed); the primed target forms take the unfolded memberships.
- Time: ≈ 2 h including reading the decision, the three sources, the accepted geo layer, U1a/U1b reports, the transformer runs, two compile
  rounds and the verification passes (axioms, name scan, textual shape check, CV agreement probe).
