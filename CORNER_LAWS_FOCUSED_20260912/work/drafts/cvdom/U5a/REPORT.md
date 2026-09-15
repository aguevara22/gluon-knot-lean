# CV-DOM unit U5a — REPORT (2026-09-14, ~04:45 UTC / 12:45am ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5) and §5 row **U5a** ("re-binding of CChamber.lean §1 … GeoMarkTransport hP hQ hs …; path
transport along CrossingGeometry families; CV-chamber record persistence → chamberinv(ii), lem:silence, R-lane G8").
Nothing under work/lean was written. Paths relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## 1. Deliverables

| file | intended home | lines | decls | `lake env lean` | axioms |
|---|---|---:|---:|---|---|
| `work/drafts/cvdom/U5a/GeoMarkTransport.lean` | `work/lean/SM/GeoMarkTransport.lean` (library, `SM.GeoCarrier`, `open Carrier Link`, CV-free; imports `SM.FlatCarriers`, `SM.GeometricRecords`, `SM.GeoCarriersLemma` (U3), `SM.GeoPositiveLift` (U4)) | 668 | 80 | **exit 0, no output** (no warnings), **no `sorry`** | all **standard** (`propext, Classical.choice, Quot.sound`; two helpers axiom-free) |
| `work/drafts/cvdom/U5a/GeoPathTransport.lean` | `work/lean/SM/GeoPathTransport.lean` (library, `SM.GeoCarrier`; imports `SM.GeoMarkTransport`, `SM.LinkMoves`, `SM.LinkInterfaces`, `SM.RotationContinuity`, `SM.WeakGeometry`, `Mathlib.Topology.LocallyConstant.Basic`) | 865 | 95 | **exit 0, no output, no `sorry`** | standard on 68; **standard + `SM.lit_homfly`** on the 27 HOMFLY declarations (`geo_homfly_positiveDiagram_single_of_family`, `homfly_geoCornerFamily`, `homfly_geoPositiveLift_eq_of_family/_of_path`, and the structures `GeoPathData`/`GeoWeakPathData` whose *type* mentions `homfly`, with their projections/constructors) — as expected for lit:homfly's planar clause |
| `work/drafts/cvdom/U5a/CVChamberInvII_partial.lean` | `work/lean/CV/ChamberInvII.lean` (row module of CV:prop:chamberinv (ii)) — imports `CV.ChamberInv`, `CV.Carriers`, `CV.CarrierBridges`, `CV.X1` (U7c, landed 04:34Z), `SM.GeoPathTransport` | 501 | 47 | **exit 0, no output, no `sorry`** | standard on 38; `SM.lit_homfly` on the 9 declarations whose statements mention `homfly`/`X1` (`chamber_geoWeakPathData`, `homfly_geoPositiveLift_eq_of_mem_chamber`, `PieceHomflyTransported`, `groupedPoly_eq_of_mem_chamber`, `Omega1_eq_of_mem_chamber`, `X1Summand`, `X1_eq_sum_X1Summand`, `X1Summand_eq_of_mem_chamber`, `X1_eq_of_mem_chamber_of_pieceHomfly`) |

Total 2,034 lines, 222 declarations (counting structure projections/constructors, excluding auto-generated
`rec/recOn/casesOn/mk/congr_simp`). `grep -c sorry` = 0 on all three. Compile times ≈ 7 s / 5 s / 6 s.

**How the second and third files were checked** (they import the first two, which are not modules of work/lean):
```
cd work/lean; LP="$(lake env printenv LEAN_PATH)"; LEANBIN="$(lake env which lean)"
mkdir -p /tmp/u5a_root/SM /tmp/u5a_olean/SM
for f in "$PWD"/.lake/build/lib/lean/SM/*.olean; do ln -s "$f" /tmp/u5a_olean/SM/ 2>/dev/null; done   # overlay: Lean picks the FIRST path entry owning an `SM` dir
cp ../drafts/cvdom/U5a/GeoMarkTransport.lean ../drafts/cvdom/U5a/GeoPathTransport.lean /tmp/u5a_root/SM/
lake env lean ../drafts/cvdom/U5a/GeoMarkTransport.lean                                              # file 1 as usual
LEAN_PATH="/tmp/u5a_olean:$LP" "$LEANBIN" --root=/tmp/u5a_root -o /tmp/u5a_olean/SM/GeoMarkTransport.olean /tmp/u5a_root/SM/GeoMarkTransport.lean
LEAN_PATH="/tmp/u5a_olean:$LP" "$LEANBIN" --root=/tmp/u5a_root -o /tmp/u5a_olean/SM/GeoPathTransport.olean /tmp/u5a_root/SM/GeoPathTransport.lean
LEAN_PATH="/tmp/u5a_olean:$LP" "$LEANBIN" ../drafts/cvdom/U5a/GeoPathTransport.lean                  # exit 0
LEAN_PATH="/tmp/u5a_olean:$LP" "$LEANBIN" ../drafts/cvdom/U5a/CVChamberInvII_partial.lean            # exit 0
```
Once the assembler ports files 1–2 into work/lean/SM, plain `lake env lean` works for all three. Axioms were
computed for every declaration of each file by a file-local `elab` calling `Lean.collectAxioms` on
`env.constants.map₂` (copies in /tmp/u5a_ax/*.lean, results /tmp/u5a_ax/*.txt; the lists are in §7 below).

## 2. Name safety (ruling R3)

Every new declaration's short name was grepped against every declaration head under work/lean (SM, CV, Bridge,
RProof, Supplemental; scan in the compile log). Two genuine collisions in the `CV` namespace were found and
**renamed**: `CV.mem_piecesOn_iff` → `CV.mem_piecesOn_transport_iff`, `CV.piecesOn_eq` → `CV.piecesOn_transport_eq`
(CV/CarriersLemma.lean, U7b, already owns those names for different statements). The remaining same-short-name
hits are in *other namespaces* and are not collisions: `component`, `component_owner`, `mem_support`,
`support_card`, `support_surjective`, `transportedCornerPolygon` (`SM.Carrier.MarkTransport.*`, CChamber.lean) vs
mine in `SM.GeoCarrier.GeoMarkTransport.*`; `marks`, `interlaces_iff`, `turn_eq` (`SM.SilentFamilyData.*`,
CSilent.lean) vs my structure fields; `of_family` (`SM.Link.Deform.of_family`) vs `GeoPathCore.of_family` etc.;
`sign_eq` (`SM.sign_eq`, FrontRecordBridge) vs the field `GeoMarkTransport.sign_eq`. None of these inner
namespaces is ever `open`ed in the library, so no ambiguity arises. No accepted or ported `geo*` name is
re-declared (grep of every new `geo*` prefix against work/lean: zero hits); the accepted FlatCarriers.lean geo
transport lemmas (`geoMarkSuccessor_markTransport`, `geoSmoothingSuccessor_markTransport`,
`geoOwner_markTransport_iff`, `geoComponentMarkList_markTransport`, `geoComponentCornerList_markTransport`,
`geoCornerCount_markTransport`, `geoMarkList_map_transport`, `geoIndependent_map_iff`, `sameCycle_of_equiv_conj`,
`visitTransport_visitTwin`, `mem_transportSupport_iff`) are **reused, not redone**.

Row modules are NOT imported (CChamber, CSilent, CS3). Their helpers that the port needs were copied under new
names: CChamber §0 `recastTuple` toolkit → `geoRecast`, `geoRecast_rfl/_apply`, `geo_zmod_val_cast`,
`geo_zmod_cast_cast(')`, `rotationNumber_geoRecast`, `regular_geoRecast`, `turn_geoRecast(_cast)`,
`forall_turn_geoRecast`, `polyComp_geoRecast`, plus the new `cornerSelector_geoRecast`, `cornerSelector_congr_turn`;
CS3 `getElem_congr_lists` → `geo_getElem_congr`; CChamber §2c / CS3 link-layer family lemmas →
`geo_positiveDiagram_congr`, `geo_single_isCrossing_iff_of_forall`, `geo_crossingGeometry_of_single_generic`,
`geo_deform_of_family`, `geo_isPositive_deform_of_family`, `geo_deform_positiveDiagram_single_of_family`,
`geo_homfly_positiveDiagram_single_of_family`; CSilent's `geoCornerMark_markTransport`,
`geoCarrierCrossings_markTransport`, `silentMarkPoint`/`silentCornerFamily` pattern → `GeoMarkTransport.geoCornerMark_eq`,
`.geoCarrierCrossings_eq`, `geoMarkPoint`, `geoCornerFamily`. (If the executor prefers importing CS3/CChamber, as
AUTHOR_NOTES 2026-09-14 ~03:58Z allows for U6, these copies can be deleted and the names redirected.)

## 3. File 1 — SM/GeoMarkTransport.lean (tier 0, + tier 2 turn data as a hypothesis)

`structure GeoMarkTransport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) : Prop`
with fields `marks : (geoMarkList hP).map (markTransport hs) = geoMarkList hQ`, `interlaces_iff`, `sign_eq`
(the geo form of CChamber's `Carrier.MarkTransport`: on the geo lane the identification of marks is the
*canonical* accepted `markTransport hs` — vertices by label, visits by `visitTransport hs` — so the transport is a
proposition and the mark list is carried literally, no rotation). Constructors: `ofOrderAgrees` (from
`CrossingParameterOrderAgrees` + signs, the local data of `geometric_records_persist`), `of_gaussList` (from the
Gauss-list clause: new bridge `lt_iff_of_sorted_map_eq` / `geometricVisitKey_lt_of_gaussList` /
`geoMarkKey_lt_transport_of_visitKey` / `geoMarkList_map_transport_of_visitKey`), `of_recordsAgree :
GeometricRecordsAgree hP hQ → ∃ hs, GeoMarkTransport hP hQ hs`, `geoTransport_of_recordsAgree (h) :
GeoMarkTransport hP hQ (recordsAgree_crossing_iff h)`, `congr_hs` (the identification is a `Subsingleton`).

Transports (`τ : GeoMarkTransport hP hQ hs`, `tS := transportSupport hs S`): `geoMarkSuccessor_eq`,
`geoSmoothingSuccessor_eq`, `geoOwner_iff`, `mem_support`, `support_card/_injective/_surjective/_bijective`,
`supportEquiv : Finset (Crossing P) ≃ Finset (Crossing Q)`, `geoIndependent_iff : GeoIndependent hQ tS ↔ GeoIndependent hP S`,
`interlacementIso : geometricInterlacementGraph hP ≃g geometricInterlacementGraph hQ`,
`component S : GeoComponent hP S ≃ GeoComponent hQ tS` (with `component_owner`/`owner_transport`/`component_symm_owner`, all `rfl`-level),
`geoComponentMarkList_eq`, `geoComponentCornerList_eq`, `geoCornerCount_eq`, `geoCornerMark_eq(')` (cast index),
`geoCarrierCrossings_eq` (= `Finset.map`), `card_geoCarrierCrossings_eq`, `mem_geoCarrierCrossings_iff`,
`transportedCornerPolygon S q : LabelledTuple (geoCornerCount hP S q)` with
`geoCornerPolygon_eq : geoCornerPolygon hQ tS (τ.component S q) = geoRecast _ (τ.transportedCornerPolygon S q)`,
`transportedCornerPolygon_eq`, `regular_transportedCornerPolygon_iff`, `rotationNumber_transportedCornerPolygon`
(= `geoCarrierRotation hQ tS (τ.component S q)`), `turn_transportedCornerPolygon_eq_turn_cast`;
given `hn : 3 ≤ n`, `hS : GeoIndependent hP S` and `hturn : ∀ i, turn Q i = turn P i` (tier 2 datum):
`turn_transportedCornerPolygon` (vertex corners by U2b `geoCornerPolygon_turn_vertex` + `hturn`, smoothing corners by
U2b `geoCornerPolygon_turn_visit` + `sign_eq`), `turn_geoCornerPolygon_cast`, `turn_geoCornerPolygon_eq`,
`geoCarrierUniform_iff`, `geoUniformSupport_iff`, `geoCarrierSelector_eq`, `geoCarrierWeight_eq`,
**`geoWind_eq : geoWind hQ tS = geoWind hP S`**, `geoCarrierLeftTurns_eq`; tier 1 (explicit `hGP hGQ : CarrierGeometry`):
`geoCarrierShadow_eq` (the shadow of the copy's positive lift is the one-component shadow of the transported
corner polygon), `single_generic_transportedCornerPolygon`.

## 4. File 2 — SM/GeoPathTransport.lean (families and paths)

* §1 `geoMarkPoint (R : LabelledTuple n) : Mark P → Plane` (vertex by label, visit by Cramer), `geoMarkPoint_eq`
  (= the point of the transported mark on the record domain), `geoMarkPoint_self`, `markTransport_self`,
  `continuousAt_geoMarkPoint` (Cramer, `continuousAt_edgeParameter_of_geometry`).
* §2 for `γ : unitInterval → LabelledTuple n`, `hγc : Continuous γ`, `hγ : ∀ t, CrossingGeometry (γ t)`:
  `geoFamily_crossing_iff (s t c) : IsCrossing (γ s) c ↔ IsCrossing (γ t) c`, `geoFamily_orderAgrees (s t) :
  CrossingParameterOrderAgrees (γ s) (γ t)`, `geoFamily_crossingSign_eq` — each locally constant by the accepted
  `crossing_support_persists_of_geometry` / `geometric_parameter_order_persists` /
  `crossingSign_locally_constant_of_geometry` and constant on the connected `unitInterval`
  (`IsLocallyConstant.apply_eq_of_preconnectedSpace`); **`geoFamily_transport (s t) : GeoMarkTransport (hγ s) (hγ t) _`**;
  `geoFamily_turn_eq (hne : ∀ t i, turn (γ t) i ≠ 0)`, `geoFamily_turn_eq_of_weak (hW : ∀ t, WeakGeneric (γ t))`.
* §3 `geoCornerFamily hP S q γ t : LabelledTuple (geoCornerCount hP S q)` (the corner polygon of a carrier of `P`
  read on `γ t`), `_eq_self`, `_eq_transported`, `_eq_recast`, `continuous_geoCornerFamily`; at tier 1
  (`hG : ∀ t, CarrierGeometry (γ t)`): `regular_geoCornerFamily`, **`rotationNumber_geoCornerFamily_const`**
  (accepted `rotationNumber_family_constant`, lem:rot (ii)), **`geoCarrierRotation_eq_of_family`**,
  `single_generic_geoCornerFamily`, **`homfly_geoCornerFamily`** (`geo_homfly_positiveDiagram_single_of_family`),
  `geoPositiveLift_eq_geoCornerFamily`, `geoPositiveLift_zero_eq_geoCornerFamily`,
  **`homfly_geoPositiveLift_eq_of_family`**.
* §4 endpoint packages, in two layers so that the combinatorial/rotation facts stay on standard axioms:
  `GeoPathCore hGP hGQ hs` (fields `transport`, `order_agrees`, `rotation_eq`; lemmas `congr_hs`, `rotation_eq'`,
  `rotationInt_eq`, `gaussList_eq`, `gaussWord_eq`, **`recordsAgree : GeometricRecordsAgree hGP.cg hGQ.cg`**,
  `card_geoCarrierCrossings_eq`, `of_family`, `of_path`), `GeoWeakPathCore extends GeoPathCore` (+ `turn_eq`;
  `geoCarrierUniform_iff`, `geoCarrierSelector_eq`, `geoWind_eq`, `turn_geoCornerPolygon_eq`, `of_family`,
  `of_path`), `GeoPathData hn extends GeoPathCore` (+ `homfly_eq`; `homfly_eq'`, `of_family`, `of_path`),
  `GeoWeakPathData hn extends GeoWeakPathCore` (+ `homfly_eq`; `toGeoPathData`, `homfly_eq'`, `of_family`, `of_path`).
  `of_path` takes `γ : Path P Q` and transfers the family result to the endpoints by generalising `P Q` and
  substituting `γ.source`/`γ.target` (the dependent-type obstacle of `Path P Q` is avoided this way).
* §4b **`geoWind_eq_of_path (hn) (γ : Path P Q) (hW : ∀ t, WeakGeneric (γ t)) (hP hQ) : ∃ hs, GeoMarkTransport hP hQ hs ∧ (∀ i, turn Q i = turn P i) ∧ ∀ S, GeoIndependent hP S → geoWind hQ (transportSupport hs S) = geoWind hP S`**
  (standard axioms); **`homfly_geoPositiveLift_eq_of_path (hn) (γ) (hG : ∀ t, CarrierGeometry (γ t)) (hGP hGQ) : ∃ hs, GeoMarkTransport … ∧ ∀ S hS hS' a, homfly (geoPositiveLift hn hGQ hS' (geoOwner _ _ (markTransport hs a))) = homfly (geoPositiveLift hn hGP hS (geoOwner _ S a))`**
  (standard + `SM.lit_homfly`); `geoCarrierRotation_eq_of_path` (standard).

Tiers (R1/R4): the transport and all of §2 are tier 0 (`CrossingGeometry`); regularity / rotation / HOMFLY are tier 1
(`CarrierGeometry`, via U2b `geoCornerPolygon_regular`, `three_le_geoCornerCount` and U4 `geoCarrierShadow_generic`);
only the vertex turn constancy is tier 2 (`turn ≠ 0` along the family, supplied by `WeakGeneric`). `hn : 3 ≤ n`
appears exactly where U2b/U4 need it (R5).

## 5. File 3 — CV/ChamberInvII (partial): the chamber ingredients of chamberinv (ii)

On the row binders `hn : 3 ≤ n`, `hP hQ : CV.Generic`, `h : Q ∈ CV.chamber P` (CV chambers, no SM fallback), with
`hs := crossing_iff_of_mem_chamber hn hP hQ h` and `τ := geoMarkTransport_of_mem_chamber hn hP hQ h`:
`generic_of_mem_chamber`, `exists_generic_path` (from the accepted `chamber_joinedIn`),
`chamber_geoWeakPathCore(_exists)` (standard axioms), `chamber_geoWeakPathData` (+ HOMFLY), `turn_eq_of_mem_chamber`,
`crossingParameterOrderAgrees_of_mem_chamber`, `crossingSign_eq_of_mem_chamber`,
**`geometricRecordsAgree_of_mem_chamber : GeometricRecordsAgree hP.crossingGeometry hQ.crossingGeometry`**,
`geometricInterlaces_iff_of_mem_chamber`, `mem_Ind_transport_iff`, **`Ind_eq_map : Ind hQ.cg = (Ind hP.cg).map (supportEquiv hs).toEmbedding`**
(the reindexing of the `X1` sum), `mem_N_transport_iff`, `N_transport`, `mem_U_transport_iff`, `U_transport`,
**`weight_eq_of_mem_chamber`, `wind_eq_of_mem_chamber (hS : S ∈ Ind hP.cg) : wind hQ.cg (transportSupport hs S) = wind hP.cg S`**
(CV:def:wind's objects; `CV.wind = geoWind`, `CV.weight = geoCarrierWeight` are `rfl`), `carrierUniform_iff_of_mem_chamber`,
`turn_geoCornerPolygon_eq_of_mem_chamber`, **`geoCarrierRotation_eq_of_mem_chamber`**,
`rotationNumber_geoCornerPolygon_eq_of_mem_chamber` (CV:def:rot's `R(L)` is a function of it),
`geoCarrierRotationInt_eq_of_mem_chamber`, **`homfly_geoPositiveLift_eq_of_mem_chamber`**,
`geoCarrierCrossings_eq_of_mem_chamber`, `card_geoCarrierCrossings_eq_of_mem_chamber`; pieces: `bijOn_U`,
`residualIso : residualGraph hP.cg S ≃g residualGraph hQ.cg tS` (`SimpleGraph.Iso.induce` of `τ.interlacementIso`),
**`pieceEquiv : Piece hP.cg S ≃ Piece hQ.cg tS`**, `pieceEquiv_pieceOf`, `pieceLabels_eq` (= `Finset.map`),
`pieceWrithe_eq`, `mem_piecesOn_transport_iff`, `piecesOn_transport_eq`; local form `Generic.eventually_mem_chamber`.

**§7 of the file — `X₁` on a chamber, modulo the piece polynomials** (added after CV/X1.lean landed at 04:34Z):
`groupedWrithe_eq_of_mem_chamber` (`w_{S,L}` carried), `carrierR_eq_of_mem_chamber` (`R(L) = |rot|` carried, via the
accepted `CV.rot_eq_rotationNumber` and the chamber constancy of the corner polygon's rotation number),
`def PieceHomflyTransported hn hP hQ h : Prop` (= `∀ S hS hS' H, pieceHomfly hn (hQ.diagrammatic hn) hS' (pieceEquiv … H) =
pieceHomfly hn (hP.diagrammatic hn) hS H`, **the one open hypothesis**), `groupedPoly_eq_of_mem_chamber`,
`slot_eq_of_mem_chamber`, `Omega1_eq_of_mem_chamber`, `X1Summand` / `X1_eq_sum_X1Summand` (the total-summand device of the
accepted `cornerStateSum_transport`), `X1Summand_eq_of_mem_chamber`, and
**`X1_eq_of_mem_chamber_of_pieceHomfly (hPH : PieceHomflyTransported hn hP hQ h) : X1 hn Q hQ = X1 hn P hP`** — CV:prop:chamberinv (ii)
modulo `PieceHomflyTransported`.

The crossing-set constancy along the chamber path is derived from the accepted `crossing_support_persists_of_geometry`
at every (CV-generic ⇒ `CrossingGeometry`) point rather than from `CV.guardconst`; both routes are available
(`Generic.eventually_crosses_iff` + `Generic.crosses_iff` would give the same).

## 6. What is left for chamberinv (ii)'s assembly (executor / U7c / U6)

`CV.X1` (row 146) landed in work/lean/CV/X1.lean during this unit (04:34Z), so the assembly was carried out here as far
as it goes: **`CV.X1_eq_of_mem_chamber_of_pieceHomfly` proves chamberinv (ii) from exactly one hypothesis,
`PieceHomflyTransported hn hP hQ h`** — the piece polynomials `P_H = pieceHomfly` are carried by the piece bijection
`pieceEquiv` of the chamber transport. Everything else (reindexing of the `Ind` sum, `wind`, the carrier product,
`w_{S,L}`, `R(L)`, the slot, `Ω₁` = `coeffAt slot 0 P_{S,L}`) is proved.

1. **Why `P_H` is not automatic.** `pieceDiagram hn hD hS H = geoPositiveLift hn (ofDiagrammatic hD) _ (pieceCarrier hD hS H)`
   on the support `S ∪ pieceSupport hD hS H`, where `pieceSupport` is `Classical.choose` of lem:piececurve's existential
   (CV/PieceCurve.lean:327). At `Q` the chosen support `K'` need not be the transport `tK` of the choice `K` at `P`.
   `homfly_geoPositiveLift_eq_of_mem_chamber` gives `homfly (lift of (S' ∪ tK, τ.component _ (pieceCarrier_P)))
   = homfly (lift of (S ∪ K, pieceCarrier_P)) = pieceHomfly_P H`; what is missing is the equality, **at the single polygon
   `Q`**, of the HOMFLY polynomials of the positive lifts of the two carriers carrying `H'` on the supports `S' ∪ K'` and
   `S' ∪ tK` — a choice-independence of `P_H`.
2. **Recommended route** (U7c/U6 territory, ≈ 250–400 lines): the accepted CV:ax:gausscode replacement
   `CV.gausscode_polynomial (D D') (hD hD' : componentCount = 1) (i : RecordIso D.record D'.record) : homfly D = homfly D'`
   (CV/Axioms.lean:260) reduces it to a record isomorphism between the two piece diagrams. Their records are determined
   by the restricted Gauss word: `pieceCarrier_gaussWord` (CV/PieceCurve.lean:411) identifies the `H`-visits of the piece
   carrier's Gauss list, in order, with the parent's `H`-visits; the over/under data is positivity at every crossing
   (`pieceDiagram_isPositive`) and the crossing signs are the parent's (`crossingSign` of the two edges, constant on the
   chamber by `crossingSign_eq_of_mem_chamber`). CV/RecordHomfly.lean's `recordIsoOfData` / `recordIso_iff`
   (`IsRecordIsoData`: `PreservesCyclicOrder`, `CarriesDoublePoints`, `CarriesOverUnder`) is the constructor to feed.
   Once `pieceHomfly_eq_of_pieceLabels_eq : pieceHomfly … H = pieceHomfly … H'` for two supports at one polygon (or the
   chamber form directly) exists, `PieceHomflyTransported` follows from `pieceLabels_eq` (mine) and
   `homfly_geoPositiveLift_eq_of_mem_chamber` (mine), and `CV.chamberinv_ii := X1_eq_of_mem_chamber_of_pieceHomfly _ hPH`.
   Alternative (definitional, U7c's call): make `pieceSupport` canonical (e.g. the transport-compatible minimal choice) —
   not recommended, the record route is the printed one (def:piecediagram reads `P_H` off the record).
3. `CV.chamberinv` row bundle = `chamberinv_i` (accepted) ∧ (ii); `CV.hyp_R` (R6) and `RProof.cv_R` then use (ii) with
   `Event.sideChamber_eq_at` / `curve_mem_sideChamber_pos/neg` (CV/Events.lean) to identify all positive (negative)
   parameters' values. Local constancy at a CV-generic `P` is `Generic.eventually_mem_chamber` + (ii).
4. **U5b (lem:silence)** can reuse: `GeoMarkTransport.of_recordsAgree` / `geoTransport_of_recordsAgree` (records at the
   silent centre), `geoCornerFamily` + `continuous_geoCornerFamily` + `rotationNumber_family_constant` on a family through
   the centre (§3 of file 2 is stated for an arbitrary base `P` and arbitrary `γ`; only the `geoFamily_*` lemmas need
   `CrossingGeometry` at every time), and `geo_homfly_positiveDiagram_single_of_family` once `WeakGeneric`-centre
   genericity of the corner shadow is supplied (CSilent's `single_generic_of_weak` lives in a row module; U5b must copy
   or reprove it).
5. **U6 / B4 `sides`** consumes `wind_eq_of_mem_chamber`, `geoCarrierRotation_eq_of_mem_chamber`,
   `homfly_geoPositiveLift_eq_of_mem_chamber` and (once `hPH` exists) `X1_eq_of_mem_chamber_of_pieceHomfly` with
   `Bridge.eventOfTriple`'s side chambers.

## 7. Port notes for the assembler

* Namespaces: files 1–2 `SM.GeoCarrier` (`open Carrier Link`), sub-namespaces `GeoMarkTransport`, `GeoPathCore`,
  `GeoWeakPathCore`, `GeoPathData`, `GeoWeakPathData` (dot notation); file 3 `CV` (`open SM SM.GeoCarrier SM.Carrier SM.Link`).
* `transportedCornerPolygon` takes the transport as an explicit (unused) proof argument `_τ` so that
  `τ.transportedCornerPolygon S q` reads as dot notation (`include τ` does not add an unused variable to a `def`).
* Tier-1 lemmas take `hGP hGQ : CarrierGeometry` **explicitly** (unification cannot recover them through `.cg`, a proof).
* `Set.mem_ofPred_eq` is the non-deprecated name of `Set.mem_setOf_eq` in this Mathlib pin (used twice in file 2).
* Temp artefacts: /tmp/u5a_root, /tmp/u5a_olean (symlink overlay + two oleans), /tmp/u5a_ax (axiom scans), /tmp/u5a_stub*.lean.

## 8. Declaration lists with axioms (from the `Lean.collectAxioms` scan; auto-generated `rec/recOn/casesOn/mk/congr_simp` omitted)

### GeoMarkTransport.lean

- `SM.GeoCarrier.GeoMarkTransport` — standard
- `SM.GeoCarrier.GeoMarkTransport.card_geoCarrierCrossings_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.casesOn` — standard
- `SM.GeoCarrier.GeoMarkTransport.component` — standard
- `SM.GeoCarrier.GeoMarkTransport.component_owner` — standard
- `SM.GeoCarrier.GeoMarkTransport.component_symm_owner` — standard
- `SM.GeoCarrier.GeoMarkTransport.congr_hs` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCarrierCrossings_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCarrierLeftTurns_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCarrierSelector_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCarrierShadow_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCarrierUniform_iff` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCarrierWeight_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoComponentCornerList_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoComponentMarkList_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCornerCount_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCornerMark_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCornerMark_eq'` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoCornerPolygon_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoIndependent_iff` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoMarkSuccessor_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoOwner_iff` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoSmoothingSuccessor_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoUniformSupport_iff` — standard
- `SM.GeoCarrier.GeoMarkTransport.geoWind_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.interlacementIso` — standard
- `SM.GeoCarrier.GeoMarkTransport.interlacementIso_apply` — standard
- `SM.GeoCarrier.GeoMarkTransport.interlaces_iff` — standard
- `SM.GeoCarrier.GeoMarkTransport.marks` — standard
- `SM.GeoCarrier.GeoMarkTransport.mem_geoCarrierCrossings_iff` — standard
- `SM.GeoCarrier.GeoMarkTransport.mem_support` — standard
- `SM.GeoCarrier.GeoMarkTransport.mk` — standard
- `SM.GeoCarrier.GeoMarkTransport.ofOrderAgrees` — standard
- `SM.GeoCarrier.GeoMarkTransport.of_gaussList` — standard
- `SM.GeoCarrier.GeoMarkTransport.of_recordsAgree` — standard
- `SM.GeoCarrier.GeoMarkTransport.owner_transport` — standard
- `SM.GeoCarrier.GeoMarkTransport.rec` — standard
- `SM.GeoCarrier.GeoMarkTransport.recOn` — standard
- `SM.GeoCarrier.GeoMarkTransport.regular_transportedCornerPolygon_iff` — standard
- `SM.GeoCarrier.GeoMarkTransport.rotationNumber_transportedCornerPolygon` — standard
- `SM.GeoCarrier.GeoMarkTransport.sign_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.single_generic_transportedCornerPolygon` — standard
- `SM.GeoCarrier.GeoMarkTransport.supportEquiv` — standard
- `SM.GeoCarrier.GeoMarkTransport.supportEquiv_apply` — standard
- `SM.GeoCarrier.GeoMarkTransport.support_bijective` — standard
- `SM.GeoCarrier.GeoMarkTransport.support_card` — standard
- `SM.GeoCarrier.GeoMarkTransport.support_injective` — standard
- `SM.GeoCarrier.GeoMarkTransport.support_surjective` — standard
- `SM.GeoCarrier.GeoMarkTransport.transportedCornerPolygon` — standard
- `SM.GeoCarrier.GeoMarkTransport.transportedCornerPolygon_apply` — standard
- `SM.GeoCarrier.GeoMarkTransport.transportedCornerPolygon_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.turn_geoCornerPolygon_cast` — standard
- `SM.GeoCarrier.GeoMarkTransport.turn_geoCornerPolygon_eq` — standard
- `SM.GeoCarrier.GeoMarkTransport.turn_transportedCornerPolygon` — standard
- `SM.GeoCarrier.GeoMarkTransport.turn_transportedCornerPolygon_eq_turn_cast` — standard
- `SM.GeoCarrier.cornerSelector_congr_turn` — standard
- `SM.GeoCarrier.cornerSelector_geoRecast` — standard
- `SM.GeoCarrier.forall_turn_geoRecast` — standard
- `SM.GeoCarrier.geoMarkKey_lt_transport_of_visitKey` — standard
- `SM.GeoCarrier.geoMarkList_map_transport_of_visitKey` — standard
- `SM.GeoCarrier.geoRecast` — standard
- `SM.GeoCarrier.geoRecast_apply` — standard
- `SM.GeoCarrier.geoRecast_rfl` — standard
- `SM.GeoCarrier.geoTransport_of_recordsAgree` — standard
- `SM.GeoCarrier.geo_getElem_congr` — (no axioms)
- `SM.GeoCarrier.geo_zmod_cast_cast` — standard
- `SM.GeoCarrier.geo_zmod_cast_cast'` — standard
- `SM.GeoCarrier.geo_zmod_val_cast` — standard
- `SM.GeoCarrier.geometricGaussList_pairwise_lt` — standard
- `SM.GeoCarrier.geometricVisitKey_lt_of_gaussList` — standard
- `SM.GeoCarrier.lt_iff_of_sorted_map_eq` — standard
- `SM.GeoCarrier.pairwise_lt_of_pairwise_le_nodup` — standard
- `SM.GeoCarrier.pairwise_lt_of_pairwise_le_nodup.match_1_1` — standard
- `SM.GeoCarrier.polyComp_geoRecast` — standard
- `SM.GeoCarrier.recordsAgree_crossing_iff` — standard
- `SM.GeoCarrier.regular_geoRecast` — standard
- `SM.GeoCarrier.rotationNumber_geoRecast` — standard
- `SM.GeoCarrier.turn_geoRecast` — standard
- `SM.GeoCarrier.turn_geoRecast_cast` — standard
- `SM.transportSupport.eq_1` — standard

### GeoPathTransport.lean

- `SM.GeoCarrier.GeoPathCore` — standard
- `SM.GeoCarrier.GeoPathCore.card_geoCarrierCrossings_eq` — standard
- `SM.GeoCarrier.GeoPathCore.casesOn` — standard
- `SM.GeoCarrier.GeoPathCore.congr_hs` — standard
- `SM.GeoCarrier.GeoPathCore.gaussList_eq` — standard
- `SM.GeoCarrier.GeoPathCore.gaussWord_eq` — standard
- `SM.GeoCarrier.GeoPathCore.mk` — standard
- `SM.GeoCarrier.GeoPathCore.of_family` — standard
- `SM.GeoCarrier.GeoPathCore.of_path` — standard
- `SM.GeoCarrier.GeoPathCore.order_agrees` — standard
- `SM.GeoCarrier.GeoPathCore.rec` — standard
- `SM.GeoCarrier.GeoPathCore.recOn` — standard
- `SM.GeoCarrier.GeoPathCore.recordsAgree` — standard
- `SM.GeoCarrier.GeoPathCore.rotationInt_eq` — standard
- `SM.GeoCarrier.GeoPathCore.rotation_eq` — standard
- `SM.GeoCarrier.GeoPathCore.rotation_eq'` — standard
- `SM.GeoCarrier.GeoPathCore.transport` — standard
- `SM.GeoCarrier.GeoPathData` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.casesOn` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.congr_hs` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.homfly_eq` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.homfly_eq'` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.mk` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.of_family` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.of_path` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.rec` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.recOn` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoPathData.toGeoPathCore` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathCore` — standard
- `SM.GeoCarrier.GeoWeakPathCore.casesOn` — standard
- `SM.GeoCarrier.GeoWeakPathCore.congr_hs` — standard
- `SM.GeoCarrier.GeoWeakPathCore.geoCarrierSelector_eq` — standard
- `SM.GeoCarrier.GeoWeakPathCore.geoCarrierUniform_iff` — standard
- `SM.GeoCarrier.GeoWeakPathCore.geoWind_eq` — standard
- `SM.GeoCarrier.GeoWeakPathCore.mk` — standard
- `SM.GeoCarrier.GeoWeakPathCore.of_family` — standard
- `SM.GeoCarrier.GeoWeakPathCore.of_path` — standard
- `SM.GeoCarrier.GeoWeakPathCore.rec` — standard
- `SM.GeoCarrier.GeoWeakPathCore.recOn` — standard
- `SM.GeoCarrier.GeoWeakPathCore.toGeoPathCore` — standard
- `SM.GeoCarrier.GeoWeakPathCore.turn_eq` — standard
- `SM.GeoCarrier.GeoWeakPathCore.turn_geoCornerPolygon_eq` — standard
- `SM.GeoCarrier.GeoWeakPathData` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.casesOn` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.congr_hs` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.homfly_eq` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.homfly_eq'` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.mk` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.of_family` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.of_path` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.rec` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.recOn` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.toGeoPathData` — standard + SM.lit_homfly
- `SM.GeoCarrier.GeoWeakPathData.toGeoWeakPathCore` — standard + SM.lit_homfly
- `SM.GeoCarrier.continuousAt_geoMarkPoint` — standard
- `SM.GeoCarrier.continuous_geoCornerFamily` — standard
- `SM.GeoCarrier.continuous_geoCornerFamily_zero` — standard
- `SM.GeoCarrier.geoCarrierRotation_eq_of_family` — standard
- `SM.GeoCarrier.geoCarrierRotation_eq_of_path` — standard
- `SM.GeoCarrier.geoCornerFamily` — standard
- `SM.GeoCarrier.geoCornerFamily_apply` — standard
- `SM.GeoCarrier.geoCornerFamily_eq_recast` — standard
- `SM.GeoCarrier.geoCornerFamily_eq_self` — standard
- `SM.GeoCarrier.geoCornerFamily_eq_transported` — standard
- `SM.GeoCarrier.geoCornerFamily_zero` — standard
- `SM.GeoCarrier.geoFamily_crossingSign_eq` — standard
- `SM.GeoCarrier.geoFamily_crossing_iff` — standard
- `SM.GeoCarrier.geoFamily_orderAgrees` — standard
- `SM.GeoCarrier.geoFamily_transport` — standard
- `SM.GeoCarrier.geoFamily_transport_zero` — standard
- `SM.GeoCarrier.geoFamily_turn_eq` — standard
- `SM.GeoCarrier.geoFamily_turn_eq_of_weak` — standard
- `SM.GeoCarrier.geoMarkPoint` — standard
- `SM.GeoCarrier.geoMarkPoint.match_1` — standard
- `SM.GeoCarrier.geoMarkPoint_eq` — standard
- `SM.GeoCarrier.geoMarkPoint_self` — standard
- `SM.GeoCarrier.geoMarkPoint_vertex` — standard
- `SM.GeoCarrier.geoMarkPoint_visit` — standard
- `SM.GeoCarrier.geoPositiveLift_eq_geoCornerFamily` — standard
- `SM.GeoCarrier.geoPositiveLift_zero_eq_geoCornerFamily` — standard
- `SM.GeoCarrier.geoWind_eq_of_path` — standard
- `SM.GeoCarrier.geo_crossingGeometry_of_single_generic` — standard
- `SM.GeoCarrier.geo_deform_of_family` — standard
- `SM.GeoCarrier.geo_deform_positiveDiagram_single_of_family` — standard
- `SM.GeoCarrier.geo_homfly_positiveDiagram_single_of_family` — standard + SM.lit_homfly
- `SM.GeoCarrier.geo_isPositive_deform_of_family` — standard
- `SM.GeoCarrier.geo_positiveDiagram_congr` — standard
- `SM.GeoCarrier.geo_single_isCrossing_iff_of_forall` — standard
- `SM.GeoCarrier.homfly_geoCornerFamily` — standard + SM.lit_homfly
- `SM.GeoCarrier.homfly_geoPositiveLift_eq_of_family` — standard + SM.lit_homfly
- `SM.GeoCarrier.homfly_geoPositiveLift_eq_of_path` — standard + SM.lit_homfly
- `SM.GeoCarrier.markTransport_self` — standard
- `SM.GeoCarrier.regular_geoCornerFamily` — standard
- `SM.GeoCarrier.rotationNumber_geoCornerFamily_const` — standard
- `SM.GeoCarrier.single_generic_geoCornerFamily` — standard

### CVChamberInvII_partial.lean

- `CV.Generic.eventually_mem_chamber` — standard
- `CV.Ind_eq_map` — standard
- `CV.N_transport` — standard
- `CV.Omega1_eq_of_mem_chamber` — standard + SM.lit_homfly
- `CV.PieceHomflyTransported` — standard + SM.lit_homfly
- `CV.U_transport` — standard
- `CV.X1Summand` — standard + SM.lit_homfly
- `CV.X1Summand_eq_of_mem_chamber` — standard + SM.lit_homfly
- `CV.X1_eq_of_mem_chamber_of_pieceHomfly` — standard + SM.lit_homfly
- `CV.X1_eq_sum_X1Summand` — standard + SM.lit_homfly
- `CV.bijOn_U` — standard
- `CV.card_geoCarrierCrossings_eq_of_mem_chamber` — standard
- `CV.carrierR_eq_of_mem_chamber` — standard
- `CV.carrierUniform_iff_of_mem_chamber` — standard
- `CV.chamber_geoWeakPathCore` — standard
- `CV.chamber_geoWeakPathCore_exists` — standard
- `CV.chamber_geoWeakPathData` — standard + SM.lit_homfly
- `CV.crossingParameterOrderAgrees_of_mem_chamber` — standard
- `CV.crossingSign_eq_of_mem_chamber` — standard
- `CV.crossing_iff_of_mem_chamber` — standard
- `CV.exists_generic_path` — standard
- `CV.generic_of_mem_chamber` — standard
- `CV.geoCarrierCrossings_eq_of_mem_chamber` — standard
- `CV.geoCarrierRotationInt_eq_of_mem_chamber` — standard
- `CV.geoCarrierRotation_eq_of_mem_chamber` — standard
- `CV.geoMarkTransport_of_mem_chamber` — standard
- `CV.geometricInterlaces_iff_of_mem_chamber` — standard
- `CV.geometricRecordsAgree_of_mem_chamber` — standard
- `CV.groupedPoly_eq_of_mem_chamber` — standard + SM.lit_homfly
- `CV.groupedWrithe_eq_of_mem_chamber` — standard
- `CV.homfly_geoPositiveLift_eq_of_mem_chamber` — standard + SM.lit_homfly
- `CV.mem_Ind_transport_iff` — standard
- `CV.mem_N_transport_iff` — standard
- `CV.mem_U_transport_iff` — standard
- `CV.mem_piecesOn_transport_iff` — standard
- `CV.pieceEquiv` — standard
- `CV.pieceEquiv_pieceOf` — standard
- `CV.pieceLabels_eq` — standard
- `CV.pieceWrithe_eq` — standard
- `CV.piecesOn_transport_eq` — standard
- `CV.residualIso` — standard
- `CV.rotationNumber_geoCornerPolygon_eq_of_mem_chamber` — standard
- `CV.slot_eq_of_mem_chamber` — standard
- `CV.turn_eq_of_mem_chamber` — standard
- `CV.turn_geoCornerPolygon_eq_of_mem_chamber` — standard
- `CV.weight_eq_of_mem_chamber` — standard
- `CV.wind_eq_of_mem_chamber` — standard
