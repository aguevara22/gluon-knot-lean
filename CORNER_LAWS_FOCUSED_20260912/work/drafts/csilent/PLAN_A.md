# PLAN_A — prop:C-silent (silence) `C(P₊) = C(P₋)` at a simple (E) or (C) wall

Architect A (record-first), 2026-09-14.  Target `SM.prop_C_silent : CSilentData`, statement FIXED in
`work/drafts/CSilent_statement.lean` (bundle `CSilentData` with fields `extension`, `cut`; copied byte-identical
at the end of the skeleton).  Source: reference/SM/sm-4-knotlaws.tex:101-105 (statement), 106-152 (proof).
Skeleton: `work/drafts/csilent/Skeleton_A.lean` — **592 lines, 56 declarations, 22 sorried leaves, 0 errors**
(`cd work/lean && lake env lean ../drafts/csilent/Skeleton_A.lean`); `#print axioms SM.prop_C_silent` =
`propext, sorryAx, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the three
registered literature interfaces of work/lean/axiom-policy.json `literature`; `lp_lm`, `lp_lm_uniqueness` enter
through `P_eq_homfly`/`presentations` of SM/PolynomialBlock.lean, exactly as the printed proof cites lc:presentations
and lp:core).  **`prop_C_silent` is PROVED from the chain**; every `sorry` is a leaf.

## 0. Route and why (R1, the printed proof)

The printed proof (sm-4:106-152) has three parts, and the skeleton follows them one-for-one.

1. **Records agree across the wall (lines 106-116).**  lem:wall-sides (E),(C) = accepted `silent_sides`
   (SM/SilentSides.lean:26, data `SilentSidesData` :15): on one interval `|t| < δ` every parameter is weakly
   generic with crossing geometry, and `GeometricRecordsAgree centre (P(t))` (same crossing supports, Gauss word,
   interlacement, crossing signs), `CrossingParameterOrderAgrees centre (P(t))`, `ChirotopesOutsideZerosAgree`.
   Composed through the centre this is `SilentPairData P(−s) P(+s)` (skeleton §2): `hs` (supports), `ho`
   (parameter order), `sign` (crossing signs), `turn` (vertex turns; the turn support `{i−1,i,i+1}` is never a
   point-zero triple of the centre since the centre's turns are nonzero, `silent_center_weak`).
   Exactly the hypotheses of the accepted `pathTransport` construction of prop:C-chamber (SM/CChamber.lean:953),
   with the path replaced by the wall data: `silentTransport : MarkTransport hn hP hQ` (§3, PROVED in the skeleton:
   `markList_transport` :908 gives the mark list literally, `geometric_interlaces_transport`
   (GeometricInterlacement.lean:69) the interlacement).  Then the accepted assembly
   `MarkTransport.cornerStateSum_transport` (CChamber.lean:503) reduces `C(P₊) = C(P₋)` to, per carrier:
   (a) uniformity read on the transported corner polygon, (b) equal corner coefficients, the latter by
   `cornerCoefficient_transport` (:481) from (b1) equal `carrierRotation` and (b2) equal `homfly` of the positive lifts.
   "The independent supports, their uniformity, `|S|` and the common prefactor now identify the two sums term by
   term" is literally that assembly.
2. **Carrier geometry (lines 118-131) is needed only for the rotation and the turn signs**, and the printed
   proof insists no generic-polygon lemma is applied at the centre.  We respect this by never forming a corner
   polygon at the centre at all:
   * turn signs (a): on each generic side the corner turn is `sign det(d_in, d_out)` of the parent in/out edge
     directions (`ccpCornerPolygon_turn_eq_sign`, CarrierCornerPolygon.lean:588); the labels are combinatorial
     and carried by the transport; a vertex corner gives the parent turn (`turn_det`), a selected-visit corner the
     crossing sign of the parent pair `{v.edge, twin.edge}` (`visit_crossing_val_eq_pair`); both agree across the
     wall by the pair data.  ("Every original and smoothing turn sign is constant", line 133.)
   * rotation (b1) = lem:rot (ii) "along the germ" (line 132): on a generic side
     `r_Q = (1/2π) Σ_corners ∠(d_in(c_j), d_out(c_j))` because each corner-polygon edge is a *positive* multiple
     of a parent direction (`ccpCornerPolygon_edge` :498, `_edge_pred` :517) and the principal angle is scale
     invariant (`principalAngle_smul`, AngleScaling.lean:12).  Read as a function of the germ parameter with the
     labels frozen (`cornerAngleSum`), this sum is continuous through the centre (`continuousAt_principalAngle`,
     RotationContinuity.lean:20; each parent pair is a regular pair at every parameter: vertex pairs by weak
     genericity, crossing pairs by transversality, `SilentInterval.weak/geom/cross`) and `2πℤ`-valued off the
     centre (at a generic parameter it is `2π r_Q` of the transported carrier, `carrierRotation_exists_int`,
     CornerStateSum.lean:67), hence equal at `±s` (`eq_of_continuous_int_valued_off_point`, an intermediate-value
     argument).  Only parent edge directions are used at the centre — the printed "carrier tuple is continuous,
     has nonzero segments, no antiparallel corner" is replaced by the (weaker, sufficient) regularity of the parent
     in/out pairs.
3. **`H⁺` by lc:presentations and lp:core "to corresponding carrier diagrams on the two generic sides"
   (lines 137-141)** (b2): `SM.presentations` (PolynomialBlock.lean:1177: `Nonempty (RecordIso D.record D'.record) →
   P D = P D'`) and `SM.P_eq_homfly` (:667) need a named-record isomorphism between the two positive lifts.
   It is built on the generic sides only (§3d-3e): the two corner polygons live on one index type (the transported
   corner polygon is the recast of the side's corner polygon, `ccpCornerPolygon_transport_of_markList_eq`
   CChamber.lean:382); their crossing pairs `{a, b}` coincide because both are characterised combinatorially
   — `{a,b}` is a crossing of the corner polygon iff an unselected crossing of the carrier has its two visits in
   the blocks of the corners `c_a`, `c_b` (`BlockWitness`; from the accepted block parametrisation
   `nonadjacent_meet` LinkPositiveLift.lean:443, `mark_block` :676, `block_mark_eq` :339, `consecutive_meet` :698,
   `ccpCornerPolygon_no_triple` :556, `carrier_selfIntersection_not_corner` CarrierSelfIntersections.lean:661) and
   block witnesses are carried by the transport.  The occurrence bijection is `singleVisitEquiv ∘ visitTransport ∘
   singleVisitEquiv⁻¹` (LinkDiagram.lean:1685, CrossingTransport.lean:18); pairing is the twin (`twin_unique`
   LinkDiagramRecord.lean:442); the over bit is `det(d_a, d_b) > 0` = a parent crossing sign ("its positive
   over/under designation is also constant", line 136); the cyclic order is the traversal-coordinate order
   (`nextVisit_comm_iff_visitBetween_iff` LinkDiagramRecord.lean:1119), which on one corner edge is the parent
   parameter order (`ho`).  Signs are all `+1` (`positiveLift_sign`).
4. **Reduction to one side parameter (lines 148-152)**: prop:C-chamber along each side,
   `cornerStateSum_side_const` (PROVED: `labelledSide_eq_at` GermSides.lean:39, `sideTuple_mem_labelledSide` :29,
   `cornerStateSum_eq_of_mem_labelledChamber` CChamber.lean:1366), then `s := δ/2`.

Why not R2 (a `Deform` of the positive lifts through the centre, as prop:C-chamber/thm:C-S3 do).  `Deform.of_family`
needs `Shadow.Generic` of the carrier polygon at *every* time, including the centre; the accepted proof of
`carrierShadow_generic` (LinkPositiveLift.lean:580) runs through the generic-parent self-intersection lane
(`csi_*`, `edgeSegment_param`, `carrier_no_triple_point`, `ccpCornerPolygon_injective`), all stated for `Generic P`.
At a silent centre the parent is not generic (a collinear triple), so R2 would re-derive tail-off/transversality/
no-triple-point of the carrier polygon at a weakly generic centre from scratch (the flat lane could avoid this because
its centre carriers are subdivisions of the *generic* deletion's carriers; there is no such generic stand-in here).
That is more work than R1's record isomorphism, and it is exactly the "generic-polygon lemma at the centre" the
printed proof forbids.  R1 also needs no `Deform`, no `Reparam`, and no centre corner polygon.

## 1. The chain (skeleton order; ✓ proved in Skeleton_A.lean, ◻ sorried leaf with its unit)

Context throughout: `namespace SM`, `open Link Carrier`, `Classical.propDecidable` local instance.

### §1 Elementary facts
| declaration | status | uses |
|---|---|---|
| `regularPair_of_det_ne_zero (hu : u ≠ 0) (hv : v ≠ 0) (hd : det u v ≠ 0) : RegularPair u v` | ✓ | `RegularPair` RegularPairs.lean:8, `det_smul_self` Segment.lean:32 |
| `weak_regularPair_turn (hw : WeakGeneric P) (i) : RegularPair (edge P (i-1)) (edge P i)` | ✓ | `WeakGeneric` WeakGeneric.lean:11, `turn_det` Chirotope.lean:87 |
| `geometry_regularPair_crossing (hg : CrossingGeometry P) (hc : IsCrossing P {e,f}) : RegularPair (edge P e) (edge P f)` | ✓ | `crossing_det_ne_zero_of_geometry` GeometricParameters.lean:11 |
| `eq_of_continuous_int_valued_off_point [PreconnectedSpace X] (hF : Continuous F) (u₀) (hint : ∀ u, u ≠ u₀ → ∃ k : ℤ, F u = k) (ha : a ≠ u₀) (hb : b ≠ u₀) : F a = F b` | ◻ U2 | Mathlib `intermediate_value_univ` |

### §2 Silent germ data
```lean
structure SilentPairData (P Q : LabelledTuple n) : Prop where
  hs : ∀ c, IsCrossing P c ↔ IsCrossing Q c
  ho : CrossingParameterOrderAgrees P Q
  sign : ∀ i j, IsCrossing P {i, j} → crossingSign Q i j = crossingSign P i j
  turn : ∀ i, turn Q i = turn P i
structure SilentInterval (hn : 3 ≤ n) (g : WallGerm n) (δ : ℝ) : Prop where
  pos : 0 < δ ; le : δ ≤ g.radius
  weak : ∀ t : g.Parameter, |t.val| < δ → WeakGeneric (g.curve t)
  geom : ∀ t : g.Parameter, |t.val| < δ → CrossingGeometry (g.curve t)
  cross : ∀ t : g.Parameter, |t.val| < δ → ∀ c, IsCrossing g.center c ↔ IsCrossing (g.curve t) c
  pair : ∀ t₁ t₂ : g.Parameter, |t₁.val| < δ → |t₂.val| < δ → SilentPairData (g.curve t₁) (g.curve t₂)
theorem exists_silentInterval (hn : 3 ≤ n) (g : WallGerm n) (h : g.Silent) : ∃ δ : ℝ, SilentInterval hn g δ   -- ◻ U1
theorem SilentInterval.sideTime_abs_lt (hI) (b) (hs : s.val < δ) : |(g.sideTime b s).val| < δ   -- ✓ (`sideTime_val_abs` FlatCarriers.lean:72)
theorem SilentInterval.sidePairData (hI) (hs : s.val < δ) : SilentPairData (g.sideTuple false s).val (g.sideTuple true s).val -- ✓
```
`exists_silentInterval` (≈60 lines): `obtain ⟨-, δ, hδ, hδr, hall⟩ := silent_sides hn g h` (SilentSides.lean:26; the
seven clauses at every `|t| < δ`: `ChirotopesOutsideZerosAgree g.center (g.curve t)` GermChiStability.lean:13,
`WeakGeneric`, `CrossingGeometry`, injectivity, `CrossingParameterOrderAgrees g.center (g.curve t)`
GeometricTransport.lean:10, `GeometricRecordsAgree … ` GeometricRecords.lean:55 whose fields are
`⟨hs, gaussList, gaussWord, interlaces, ∀ i j, IsCrossing centre {i,j} → crossingSign (curve t) i j = crossingSign centre i j⟩`).
`cross t := (hrec t).choose`; `pair t₁ t₂`: `hs c := (cross t₁ c).symm.trans (cross t₂ c)`; `ho i j k h₁ h₂ :=`
rewrite both `IsCrossing (curve t₁)` to the centre and compose the two `↔` of the centre's parameter order;
`sign i j h := (hsign₂ i j hc).trans (hsign₁ i j hc).symm` with `hc : IsCrossing centre {i,j}`; `turn i`: with
`hw0 := g.silent_center_weak hn h` (SilentCenter.lean:40), `hw0.2.1 i : turn g.center i ≠ 0`, so
`({i-1, i, i+1} : Finset _) ∉ pointZeroTriples g.center` by `mem_pointZeroTriples` (ZeroTriples.lean:44) and
`pointZeroTriple_iff (prev_ne_self i) (next_ne_self i).symm (prev_ne_next hn i)` (:29; Segment.lean:78; needs
`Nontrivial (ZMod n)` from `hn`), and `ChirotopesOutsideZerosAgree` gives `chi (curve tᵢ) (i-1) i (i+1) = chi centre …`
(`turn` unfolds to `chi P (i-1) i (i+1)`, Chirotope.lean:13).

### §3 The silent transport (variables `hn hP hQ (hd : SilentPairData P Q)`, `τ := silentTransport hn hP hQ hd`)
| declaration | status |
|---|---|
| `silentTransport : MarkTransport hn hP hQ` (vert `Equiv.refl`, cross/visit transports, `markList_rotated` by `markList_transport`, `interlaces_iff` by `geometric_interlaces_transport`, `turn_eq := hd.turn`) | ✓ |
| `silentTransport_toMark (a) : τ.toMark a = Sum.map id (visitTransport hd.hs) a`, `_inl`, `_inr` | ✓ |
| `silentTransport_markList : markList hn hQ = (markList hn hP).map τ.toMark` | ✓ |
| `ccpCornerPolygon_silentTransport (S q) : ccpCornerPolygon hn hQ (τ.support S) (τ.component S q) = recastTuple (τ.ccpCornerCount_transport S q) (τ.transportedCornerPolygon S q)` | ✓ (`ccpCornerPolygon_transport_of_markList_eq` CChamber.lean:382) |
| `ccpCornerList_silentTransport (S q) : ccpCornerList hn hQ (τ.support S) (τ.component S q) = (ccpCornerList hn hP S q).map τ.toMark` | ◻ U1 (copy `h1`,`h2` of CChamber.lean:382-403: `componentMarkList`/`ccpCornerList` unfold, `List.filter_map`, `List.filter_congr`, `component_owner` :249, `isTrueCorner_transport` :292) ≈20 |
| `ccpCornerMark_silentTransport (S q j) : ccpCornerMark hn hQ (τ.support S) (τ.component S q) (Equiv.cast (congrArg ZMod (τ.ccpCornerCount_transport S q).symm) j) = τ.toMark (ccpCornerMark hn hP S q j)` | ◻ U1 (`getElem_eq_map_of_eq` CChamber.lean:312, `zmod_val_cast` :82; template: the `funext j` step of :382-403) ≈20 |
| `ccpInEdge_silentTransport (a) : ccpInEdge hn hQ (τ.toMark a) = ccpInEdge hn hP a` | ◻ U1 (`ccpInEdge_vertex` CarrierCornerPolygon.lean:67, `ccpInEdge_visit` :71, `visitTransport_edge` CrossingTransport.lean:27) ≈10 |
| `ccpOutSlot_fst_silentTransport (S a) : (ccpOutSlot hn hQ (τ.support S) (τ.toMark a)).1 = (ccpOutSlot hn hP S a).1` | ◻ U1 (`ccpOutSlot_vertex` :49, `ccpOutSlot_selected` :53 + `τ.twin_eq` CChamber.lean:172 + `τ.mem_support` :157, `ccpOutSlot_unselected` :60 + `visitPosition_edge`) ≈25 |
| `cornerInLabel/cornerOutLabel hn hP S q j` (noncomputable abbrevs: `ccpInEdge hn hP (ccpCornerMark …)`, `(ccpOutSlot hn hP S (ccpCornerMark …)).1`) | ✓ |
| `cornerLabels_cases (S q j) : (∃ i, c_j = inl i ∧ in = i-1 ∧ out = i) ∨ (∃ v, c_j = inr v ∧ v.1 ∈ S ∧ in = v.2.val ∧ out = (visitTwin v).2.val)` | ◻ U1 (`ccpCornerMark_isTrueCorner` :375, `isTrueCorner_visit` CarrierTrueCorners.lean:53) ≈20 |
| `cornerLabels_isCrossing_of_visit (S q j v) (hj : c_j = inr v) : IsCrossing P {in_j, out_j}` | ◻ U1 (`visit_crossing_val_eq_pair` CarrierCrossings.lean:216, `v.1.property`) ≈10 |
| `corner_det_sign_silentTransport (S a) (ha : IsTrueCorner S a) : sign (det (edge Q (ccpInEdge hn hP a)) (edge Q (ccpOutSlot hn hP S a).1)) = sign (det (edge P …) (edge P …))` | ◻ U1 (cases `a`; vertex: `turn_det` both sides, `hd.turn`; visit: `ccpInEdge_visit`, `ccpOutSlot_selected`, `crossingSign` Crossings.lean:80 unfolds to `sign det`, `hd.sign` on `visit_crossing_val_eq_pair`) ≈40 |
| `turn_transportedCornerPolygon_silent (hS q j) : turn (τ.transportedCornerPolygon S q) j = turn (ccpCornerPolygon hn hP S q) j` | ◻ U1 (`ccpCornerPolygon_silentTransport`, `turn_recastTuple_cast` CChamber.lean:864 read backwards, `ccpCornerPolygon_turn_eq_sign` :588 on both sides with `hS`/`(τ.isDecomposition_transport S).mpr hS` :278, `ccpCornerMark_silentTransport`, both label transports, `corner_det_sign_silentTransport`) ≈40 |
| `uniform_silentTransport (hS q) : (∃ σ, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ) ↔ CarrierUniform hn hP S q` | ✓ from the previous (`CarrierUniform` UniformDefinition.lean:27) |
| `carrierRotation_eq_sum_principalAngle (hS q) : carrierRotation hn hP S q = (∑ j, principalAngle (edge P (in_j)) (edge P (out_j))) / (2 * Real.pi)` | ◻ U2 (`carrierRotation` UniformDefinition.lean:42 = `rotationNumber (ccpCornerPolygon …)`; `rotationNumber` RotationNumber.lean:10 = `(∑ principalTurn) / (2π)`, `principalTurn` RegularLocus.lean:15 = `principalAngle (edge (j-1)) (edge j)`; `ccpCornerPolygon_edge_pred` :517, `ccpCornerPolygon_edge` :498, `principalAngle_smul`) ≈30 |
| `carrierRotation_silentTransport_eq_sum (hS q) : carrierRotation hn hQ (τ.support S) (τ.component S q) = (∑ j, principalAngle (edge Q (in_j)) (edge Q (out_j))) / (2 * Real.pi)` (labels of `P`) | ◻ U2 (previous at `Q`, reindex `Fintype.sum_equiv (Equiv.cast …)`, `ccpCornerMark_silentTransport`, label transports) ≈40 |
| `BlockWitness hn hP S q w a b : Prop := w.1 ∈ carrierCrossings hn hP S q ∧ ∃ r r', (ρ_S^r) c_a = inr w ∧ BlockInterior hn hP S q a r ∧ (ρ_S^r') c_b = inr (visitTwin w) ∧ BlockInterior hn hP S q b r'` | ✓ def (`BlockInterior` LinkPositiveLift.lean:251) |
| `isCrossing_ccp_iff (hS q a b) : IsCrossing (ccpCornerPolygon hn hP S q) {a, b} ↔ ∃ w, BlockWitness hn hP S q w a b` | ◻ U3 ≈150 |
| `crossingPoint_ccp_eq (hS q) (hab : IsCrossing Φ {a,b}) (hw : BlockWitness … w a b) : crossingPoint ⟨{a,b}, hab⟩ = crossingPoint w.1` | ◻ U3 ≈30 |
| `blockWitness_silentTransport (hS q w a b) : BlockWitness hn hQ (τS) (τq) (visitTransport hd.hs w) (cast a) (cast b) ↔ BlockWitness hn hP S q w a b` | ◻ U3 ≈80 |
| `isCrossing_transportedCornerPolygon_silent (hS q c) : IsCrossing (τ.transportedCornerPolygon S q) c ↔ IsCrossing (ccpCornerPolygon hn hP S q) c` | ◻ U3 ≈50 |
| `transportedPolyComp hS q : PolyComp := ⟨k, ccpCornerCount_ge_three hn hP hS q, τ.transportedCornerPolygon S q⟩` | ✓ |
| `carrierPolyComp_silentTransport (hS q) : carrierPolyComp hn hQ (τS) (τq) hS' = transportedPolyComp …` | ✓ (`polyComp_recastTuple` CChamber.lean:108) |
| `transportedShadow_generic (hS q) : (Shadow.single (transportedPolyComp …)).Generic` | ✓ (`carrierShadow_generic` LinkPositiveLift.lean:580) |
| `transportedLift hS q : Diagram := (Shadow.single (transportedPolyComp …)).positiveDiagram _` | ✓ |
| `positiveLift_silentTransport_eq (hS q) : positiveLift hn hQ (τS) (τq) hS' = transportedLift …` | ✓ (`positiveDiagram_congr` CChamber.lean:567) |
| `liftVisitEquiv hS q : (positiveLift hn hP S q hS).Γ.Visit ≃ (transportedLift …).Γ.Visit := singleVisitEquiv.trans ((visitTransport hΦ).trans singleVisitEquiv.symm)` | ✓ def |
| `liftVisitEquiv_twin (v) : Φ (D₋.twin v) = D₊.twin (Φ v)` | ◻ U4 ≈40 |
| `liftVisitEquiv_overBit (v) : D₊.overBit (Φ v) = D₋.overBit v` | ◻ U4 ≈120 |
| `liftVisitEquiv_visitCoord_lt (v w) : D₊.visitCoord (Φ v) < D₊.visitCoord (Φ w) ↔ D₋.visitCoord v < D₋.visitCoord w` | ◻ U4 ≈180 |
| `liftVisitEquiv_nextVisit (v) : Φ (D₋.nextVisit v) = D₊.nextVisit (Φ v)` | ✓ (`nextVisit_comm_iff_visitBetween_iff` LinkDiagramRecord.lean:1119, `VisitBetween` :882, `cycBetween` :78 unfolds to a formula in `<`) |
| `liftRecordIso hS q : RecordIso (positiveLift hn hP S q hS).record (transportedLift …).record` | ✓ (`RecordIso` LinkRecord.lean:539; `record_succ_apply` LinkDiagramRecord.lean:522; signs `positiveDiagram_sign` LinkPositiveLift.lean:114, `positiveLift_sign` :622) |
| `homfly_positiveLift_silent (hS q) : homfly (positiveLift hn hQ (τS) (τq) hS') = homfly (positiveLift hn hP S q hS)` | ✓ (`P_eq_homfly` PolynomialBlock.lean:667, `presentations` :1177) |

### §4 Rotation across the wall (variables `hI : SilentInterval hn g δ`, `hs : s.val < δ`; `P₋ := (g.sideTuple false s).val`)
| declaration | status |
|---|---|
| `cornerAngleSum hn hP S q (T : LabelledTuple n) : ℝ := ∑ j, principalAngle (edge T (in_j)) (edge T (out_j))` | ✓ def |
| `sideTransport hn hI hs : MarkTransport hn (g.sideTuple false s).property (g.sideTuple true s).property := silentTransport hn _ _ (hI.sidePairData hs)` | ✓ |
| `cornerAngleSum_int_valued (hS q) (t : g.Parameter) (ht : \|t.val\| < δ) (ht0 : t.val ≠ 0) : ∃ k : ℤ, cornerAngleSum hn _ S q (g.curve t) = 2 * Real.pi * k` | ◻ U2 ≈35 |
| `cornerAngleSum_continuousAt (hS q) (t) (ht : \|t.val\| < δ) : ContinuousAt (fun u : g.Parameter => cornerAngleSum hn _ S q (g.curve u)) t` | ◻ U2 ≈50 |
| `carrierRotation_sideTransport (hS q) : carrierRotation hn (g.sideTuple true s).property (τ.support S) (τ.component S q) = carrierRotation hn (g.sideTuple false s).property S q` | ◻ U2 ≈60 |

### §5-6 Assembly, reduction, statement — all ✓
`cornerCoefficient_sideTransport` (`cornerCoefficient_transport` CChamber.lean:481), `cornerStateSum_side_pair`
(`cornerStateSum_transport` :503), `cornerStateSum_side_const`, `cornerStateSum_silent (h : g.Silent) (tp tm)`
(δ from `exists_silentInterval`, `s := δ/2`), `CSilentData` (verbatim), `prop_C_silent` (fields from
`cornerStateSum_silent` with `Or.inl ⟨M, a, hE⟩` / `Or.inr ⟨i, j, k, hC⟩ : g.Silent`, SilentCenter.lean:24).

## 2. Proof sketches of the leaves

**U1.**  All bookkeeping on the two generic sides, no geometry.  `ccpCornerList_silentTransport` and
`ccpCornerMark_silentTransport` are the `h1/h2/funext` steps of the accepted `ccpCornerPolygon_transport_of_markList_eq`
(CChamber.lean:382-403) with `silentTransport_markList`; state the mark version with `getElem_eq_map_of_eq`
(:312) and `zmod_val_cast` (:82).  The label lemmas are `cases a`; for the selected visit
`ccpOutSlot_selected hn hQ (τ.support S) (τ.visit v) ((τ.mem_support S _).mpr hv)` and `τ.twin_eq`
(`silentTransport_toMark_inr` makes `τ.toMark (inr v) = inr (visitTransport hd.hs v)` definitional; `τ.visit`
is `visitTransport hd.hs` by `rfl`).  `corner_det_sign_silentTransport`: vertex — `ccpInEdge_vertex`,
`ccpOutSlot_vertex`, `← turn_det`, `hd.turn`; visit — `ccpInEdge_visit`, `ccpOutSlot_selected`, then the goal is
`crossingSign Q v.edge twin.edge = crossingSign P …` (unfold `crossingSign`), `hd.sign _ _ hc` with
`hc := visit_crossing_val_eq_pair v ▸ v.1.property`.  `turn_transportedCornerPolygon_silent`: rewrite the LHS
with `(turn_recastTuple_cast (τ.ccpCornerCount_transport S q) _ j).symm` and `← ccpCornerPolygon_silentTransport`,
apply `ccpCornerPolygon_turn_eq_sign` at `Q` (index `Equiv.cast … j`) and at `P`, rewrite the corner mark by
`ccpCornerMark_silentTransport`, both labels by the transports, close with `corner_det_sign_silentTransport`.

**U2.**  `eq_of_continuous_int_valued_off_point`: obtain `ka, kb` from `hint a ha`, `hint b hb`; by
`lt_trichotomy`; if `ka < kb` then `ka + 1/2, ka + 1/4 ∈ Set.Icc (F a) (F b) ⊆ Set.range F`
(`intermediate_value_univ a b hF`), giving `u₁, u₂`; a real `ka + 1/2` is no integer (`k - ka` would be an integer
in `(0,1)`: `Int.cast_lt`, `Int.lt_iff_add_one_le`), so `u₁ = u₀ = u₂` by `hint`, whence `ka + 1/2 = ka + 1/4`;
symmetric for `kb < ka`.  (Alternative: `IsPreconnected.constant_of_mapsTo` with
`Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range`, as in `rotationNumber_family_constant`
RotationContinuity.lean:45, after showing `F u₀ ∈ range Int.cast` by closedness — needs a non-isolatedness
argument for `u₀`; the intermediate-value route avoids it.)
`carrierRotation_eq_sum_principalAngle`: `unfold carrierRotation rotationNumber; congr 1; refine Finset.sum_congr rfl
fun j _ => ?_`, `principalTurn` unfolds to `principalAngle (edge Φ (j-1)) (edge Φ j)`, obtain
`⟨c₁, hc₁, he₁⟩ := ccpCornerPolygon_edge_pred hn hP hS q j`, `⟨c₂, hc₂, he₂⟩ := ccpCornerPolygon_edge hn hP hS q j`,
`rw [he₁, he₂, principalAngle_smul hc₁ hc₂]`.  `carrierRotation_silentTransport_eq_sum`: apply the previous at
`Q` with `hS' := (τ.isDecomposition_transport S).mpr hS`, then
`Fintype.sum_equiv (Equiv.cast (congrArg ZMod (τ.ccpCornerCount_transport S q).symm))` and per index
`ccpCornerMark_silentTransport`, `ccpInEdge_silentTransport`, `ccpOutSlot_fst_silentTransport`.
`cornerAngleSum_int_valued`: `hd_t := hI.pair (g.sideTime false s) t (hI.sideTime_abs_lt false hs) ht`,
`τ_t := silentTransport hn _ (g.generic_punctured t ht0) hd_t`, then `carrierRotation_silentTransport_eq_sum`
gives `cornerAngleSum … (g.curve t) = 2π · carrierRotation …`, and `carrierRotation_exists_int hn _ hS' _`
(CornerStateSum.lean:67) gives `k`.  `cornerAngleSum_continuousAt`: `continuousAt_finset_sum`-style
(`ContinuousAt.finset_sum` / `continuousAt_finset_sum`), per corner `continuousAt_principalAngle` with
`hu := ((continuous_edge _).comp g.continuous_curve).continuousAt` (Polygon-level `continuous_edge`, used in
CChamber.lean:625-660) and the regular pair from `cornerLabels_cases`: vertex → `weak_regularPair_turn (hI.weak t ht) i`
after rewriting the labels; visit → `geometry_regularPair_crossing (hI.geom t ht) hc'` with
`hc' : IsCrossing (g.curve t) {in, out}` obtained from `cornerLabels_isCrossing_of_visit` at `P₋` through
`(hI.cross _ (hI.sideTime_abs_lt false hs) _).symm` and `hI.cross t ht _`.
`carrierRotation_sideTransport`: `X := Set.Icc (-s.val) s.val`, `haveI := Subtype.preconnectedSpace (isPreconnected_Icc)`,
`F : X → ℝ := fun u => cornerAngleSum … (g.curve ⟨u.val, _⟩)` (bounds from `|u| ≤ s < δ ≤ radius`),
`Continuous F` from `cornerAngleSum_continuousAt` (`continuous_iff_continuousAt`, `ContinuousAt.comp` with the
continuous `fun u : X => (⟨u.val, _⟩ : g.Parameter)`), `u₀ := ⟨0, …⟩`, `hint` from `cornerAngleSum_int_valued`
(`F u = 2π k` ⇒ `∃ k', F u / (2π) …` — state `hint` for `F / (2π)`), `a := ⟨-s.val, …⟩`, `b := ⟨s.val, …⟩`
(both `≠ u₀` since `s.val > 0`); `F a = cornerAngleSum … (g.sideTuple false s).val` and
`F b = … (g.sideTuple true s).val` by `congr`/`Subtype.ext` on the parameter (`sideTime` WallGerm.lean:31 is
`⟨±t.val, _⟩`); finish with `carrierRotation_eq_sum_principalAngle` at `P₋` and
`carrierRotation_silentTransport_eq_sum` at `P₊`, dividing by `2π ≠ 0`.

**U3.**  `isCrossing_ccp_iff` (⇐): from `hw : BlockWitness … w a b` with `r, r'`: `hown : owner (inr w) = q` and
`hown' : owner (inr (visitTwin w)) = q` from `mem_carrierCrossings` (CarrierCrossings.lean:66) since
`w.1 = (visitTwin w).1` (`visitTwin_crossing`); `mark_block hn hP S q hS (inr w) hown` gives `⟨j, r₀, hj, hbj, hpt⟩`,
`block_mark_eq hn hP S q hbj hw.a (hj.trans h.symm) : j = a ∧ r₀ = r` ⇒ `crossingPoint w.1 ∈ edgeSegment Φ a`
(`markPosition_evaluation_visit` CarrierMarks.lean:54); likewise on `b` for the twin.  `1 ≤ r`: else `inr w = c_a` is a
true corner (`ccpCornerMark_isTrueCorner`), i.e. `w.1 ∈ S`, contradicting `hw.1` (`mem_carrierCrossings … .1`); then
`hea : w.2.val = out_a` (`BlockInterior.visit_edge` LinkPositiveLift.lean:279) and `heb : (visitTwin w).2.val = out_b`.
`¬ adjacent a b` (`adjacent` Polygon.lean:63): `b - a = 0` ⇒ `a = b` ⇒ `w.2.val = (visitTwin w).2.val`, contradicting
`visitTwin_edge_ne` (CarrierCrossings.lean:209); `b - a = 1` ⇒ `b = a + 1` ⇒ `consecutive_meet hn hP S q hS a hxa hxb :
x = Φ (a+1)`, contradicting `(carrier_selfIntersection_not_corner hn hP S q hw.1).2.2.2 _ (ccpCornerMark_isTrueCorner …)`
(the crossing point is no corner point; `ccpCornerPolygon_apply`); `b - a = -1` symmetric.  Conclude
`⟨a, b, rfl, hab, ⟨x, hxa, hxb⟩⟩` (`IsCrossing` Crossings.lean:12, `remote := ¬ adjacent`).
(⇒): `obtain ⟨i, j, hab, hr, x, hxa, hxb⟩ := h`; identify `{i,j} = {a,b}` (Finset pair equality, wlog by
`Finset.pair_comm`/swapping the roles of `a`, `b`, which is harmless since `BlockWitness … w a b ↔ BlockWitness … (visitTwin w) b a`
by `visitTwin_involutive` CarrierVisitTwin.lean:65); `nonadjacent_meet hn hP S q hS hr hxa hxb` gives `c, w` with
`hcw : w.1 = c`, `hc : c ∈ carrierCrossings`, `hx : x = crossingPoint c`; `mark_block` for `inr w` and `inr (visitTwin w)`
gives blocks `a₁ (r), b₁ (r')` with `x ∈ edgeSegment Φ a₁ ∩ edgeSegment Φ b₁`.  `a₁ ≠ b₁` (edges differ as above).
`x` is interior to every closed edge of `Φ` containing it: `x ≠ Φ e` for all `e` (`carrier_selfIntersection_not_corner`),
so from `⟨t, ht0, ht1, rfl⟩ : x ∈ edgeSegment Φ e` the parameter is in `(0,1)` (`edgePoint_one` G1Consequences.lean:16 for
`t = 1`, `edgePoint P e 0 = P e` by `simp [edgePoint]` for `t = 0`).  `ccpCornerPolygon_no_triple hn hP S q hS`
(LinkPositiveLift.lean:556) then forces `a₁ ∈ {a, b}` (else `a, b, a₁` distinct with `x` interior to all three; `a ≠ b`
from `hr`) and `b₁ ∈ {a, b}`; with `a₁ ≠ b₁` get `(a₁, b₁) = (a, b)` or `(b, a)`; in the second case use `visitTwin w`
(`visitTwin_involutive`, `visitTwin_crossing`).  `crossingPoint_ccp_eq`: `crossingPoint_unique_of_geometry`
(CrossingGeometry.lean:41) on `Φ` with `crossingGeometry_of_single_generic _ (carrierShadow_generic …)`
(CChamber.lean:582; `carrierShadow` is `Shadow.single ⟨k, _, Φ⟩` by `rfl`), the common point being `crossingPoint w.1`
on both edges by the (⇐) computation (factor that computation out as `blockWitness_mem_edgeSegment (hw) :
crossingPoint w.1 ∈ edgeSegment Φ a ∧ crossingPoint (visitTwin w).1 ∈ edgeSegment Φ b`).
`blockWitness_silentTransport`: `τ.carrierCrossings_transport` (CChamber.lean:252) + `Finset.mem_map_equiv` for the
first clause; `(ρ_S(Q))^r (τ.toMark m) = τ.toMark ((ρ_S(P))^r m)` by induction on `r` from
`τ.smoothingSuccessor_transport` (:208) (the `hzpow` of :215-243 in `ℕ`-power form); `ccpCornerMark_silentTransport`;
`τ.toMark (inr w) = inr (τ.visit w)` and `τ.twin_eq`; `BlockInterior` at `Q` for `cast a` ↔ at `P` for `a`: unfold
(∀ i, 1 ≤ i → i ≤ r → ∃ v, (ρ^i) c = inr v ∧ v.1 ∉ S ∧ v.2.val = out), transport `v` by `τ.visit`/`τ.visit.symm`,
`τ.mem_support`, `visitTransport_edge`, `ccpOutSlot_fst_silentTransport`.  `isCrossing_transportedCornerPolygon_silent`:
a crossing support is a pair (`IsCrossing` gives `c = {i, j}`), so reduce to pairs; rewrite `IsCrossing (τ.transportedCornerPolygon S q) {a,b}`
through `ccpCornerPolygon_silentTransport` and `recastTuple`/`Equiv.cast` (`IsCrossing (recastTuple hk X) {cast a, cast b} ↔
IsCrossing X {a, b}` — prove by `subst hk; rfl`), apply `isCrossing_ccp_iff` on both sides, and
`blockWitness_silentTransport` with `(visitTransport hd.hs).surjective`.

**U4.**  Work at the SM level through `singleVisitEquiv` (LinkDiagram.lean:1685; `singleVisitEquiv_fst/snd`,
`singleCrossingEquiv_val`, `single_crossingPoint` :1703 with the two generic shadows).  `liftVisitEquiv_twin`:
`twin_unique` (LinkDiagramRecord.lean:442) at `D₊`: `(Φ (twin v)).1 = (Φ v).1` (same crossing: `visitTransport_crossing`,
`singleVisitEquiv_fst`) and `Φ (twin v) ≠ Φ v` (`twin_ne`, injectivity); template `singleDiagram_twin` :785 which
works for any diagram on `single C` (its `hP` is unused there).  `liftVisitEquiv_overBit`: `overBit_eq_true_iff` :472
and `isOver` LinkDiagram.lean:627; the over strand of `positiveDiagram` is the strand `s` with `0 < det (dir s) (dir (other s))`
(`positiveDiagram_det_pos` LinkPositiveLift.lean:105; uniqueness by `det_swap` and `eq_other_of_mem_of_ne`);
`single_dir` :1636 gives `dir ⟨0,a⟩ = edge Φ a`; with `x := singleCrossingEquiv v.1 : Crossing Φ₋` of support `{a, b}`
(`crossing_support_partner`), `isCrossing_ccp_iff` gives a block witness `w`, `BlockInterior.visit_edge` gives
`w.2.val = out_a`, `(visitTwin w).2.val = out_b`, `ccpCornerPolygon_edge` at `P` and at `Q` (through
`ccpCornerPolygon_silentTransport`/`turn_recastTuple`-style recast lemmas; add `edge_recastTuple_cast`) write
`edge Φ₋ a = c • edge P out_a`, `edge Φ₊ a = c' • edge Q out_a`, so `sign det(edge Φ₊ a, edge Φ₊ b) = sign det(edge Φ₋ a, edge Φ₋ b)`
by `hd.sign out_a out_b hc` (`hc : IsCrossing P {out_a, out_b}` from `visit_crossing_val_eq_pair w`), hence the same
strand is over on both sides.  `liftVisitEquiv_visitCoord_lt`: `visitCoord` :181 `= traversalKey (visitPt v).2`
`= (label).val + crossingParam` (`visitPt` LinkDiagram.lean:1435, `traversalKey` Traversal.lean:17, `traversalKey_lt_iff` :46);
labels are preserved (`visitTransport_edge`, `singleVisitEquiv_snd`), so reduce to: for two occurrences on the same
strand `⟨0, a⟩`, the crossing parameters compare alike.  `D.crossingParam x hs = crossingParameter (singleCrossingEquiv x) a _`
(proof of `singleDiagram_crossingParam` LinkDiagramRecord.lean:765: `edgePoint_injective (ccpCornerPolygon_edge_ne_zero …)`,
`crossingParam_spec` LinkDiagram.lean:1416, `single_crossingPoint`, `crossingParameter_spec` Crossings.lean:74), and by
`crossingPoint_ccp_eq` the point is `crossingPoint w.1 = edgePoint P out_a (visitParameter w)` (`crossingParameter_spec`
on `w`), while `Φ a = edgePoint P out_a λ_a` (`ccp_evaluation_eq_outSlot` CarrierCornerPolygon.lean:87) and
`edge Φ a = c • edge P out_a`; `edgePoint_injective (hP-edge ≠ 0)` gives `λ_a + u·c = visitParameter w`, i.e. `u = (μ − λ_a)/c`;
the same at `Q` with `λ'_a, c'` and `μ' = visitParameter (visitTransport hd.hs w)`; `visitParameter_eq_of_support_pair_of_geometry`
(GeometricParameters.lean:36) turns `μ, μ'` into `edgeParameter P/Q out_a f` (`f := (visitTwin w).2.val`), and `hd.ho out_a f₁ f₂`
compares them across the wall (both `{out_a, fᵢ}` are crossings of `P`).  Assemble `u₁ < u₂ ↔ μ₁ < μ₂ ↔ μ'₁ < μ'₂ ↔ u'₁ < u'₂`
(`div_lt_div_iff_of_pos_right`, `sub_lt_sub_iff_right`).

## 3. Accepted declarations used (verified by grep, file:line under work/lean/SM/)

WallGerm.lean:13 `WallGerm`, :31 `sideTime`, :47 `sideTuple`; GermSides.lean:29 `sideTuple_mem_labelledSide`, :39 `labelledSide_eq_at`;
NamedWallPredicates.lean:39 `ExtensionAt`, :46 `PureCutAt`; SilentCenter.lean:24 `WallGerm.Silent`, :40 `silent_center_weak`;
SilentSides.lean:15 `SilentSidesData`, :26 `silent_sides`; GeometricRecords.lean:55 `GeometricRecordsAgree`;
GermChiStability.lean:13 `ChirotopesOutsideZerosAgree`; GeometricTransport.lean:10 `CrossingParameterOrderAgrees`;
CrossingTransport.lean:12 `crossingTransport`, :15 `crossingTransport_support`, :18 `visitTransport`, :27 `visitTransport_edge`;
FlatCarriers.lean:72 `WallGerm.sideTime_val_abs`, :119 `visitTransport_visitTwin`; GeometricInterlacement.lean:36
`geometricInterlaces_iff_generic`, :69 `geometric_interlaces_transport`; WeakGeneric.lean:11 `WeakGeneric`; CrossingGeometry.lean:11
`CrossingGeometry`, :41 `crossingPoint_unique_of_geometry`, :52 `crossingParameter_interior_of_geometry`; GeometricParameters.lean:11
`crossing_det_ne_zero_of_geometry`, :36 `visitParameter_eq_of_support_pair_of_geometry`, :58 `continuousAt_edgeParameter_of_geometry`;
Chirotope.lean:10 `chi`, :13 `turn`, :87 `turn_det`; ZeroTriples.lean:29 `pointZeroTriple_iff`, :44 `mem_pointZeroTriples`;
Segment.lean:32 `det_smul_self`, :70 `next_ne_self`, :78 `prev_ne_next`; Crossings.lean:12 `IsCrossing`, :41 `crossingPoint`,
:70 `crossingParameter`, :74 `crossingParameter_spec`, :80 `crossingSign`, :88 `edgePoint_injective`, :113 `generic_crossingPoint_injective`;
Polygon.lean:49 `edge`, :51 `edgePoint`, :54 `edgeSegment`, :57 `edgeInterior`, :63 `adjacent`, :66 `remote`; RegularPairs.lean:8
`RegularPair`; RegularLocus.lean:12 `Regular`, :15 `principalTurn`; RotationNumber.lean:10 `rotationNumber`;
RotationContinuity.lean:20 `continuousAt_principalAngle`, :45 `rotationNumber_family_constant` (template); AngleScaling.lean:12
`principalAngle_smul`; CarrierMarks.lean:33 `Mark`, :37 `markPosition`, :54 `markPosition_evaluation_visit`, :99 `markList`;
CarrierVisitTwin.lean:34 `visitTwin`, :38 `visitTwin_crossing`, :41 `visitTwin_ne`, :60 `visitTwin_unique`, :65 `visitTwin_involutive`,
:83/:87 `selectedVisitTwin_of_mem/_not_mem`; CarrierSmoothing.lean:36 `selectedMarkPerm`, :82 `smoothingSuccessor`, :124 `Component`,
:130 `owner`, :134 `owner_eq_iff`; CarrierTrueCorners.lean:44 `IsTrueCorner`, :49 `isTrueCorner_vertex`, :53 `isTrueCorner_visit`;
CarrierCrossings.lean:56 `carrierCrossings`, :66 `mem_carrierCrossings`, :209 `visitTwin_edge_ne`, :216 `visit_crossing_val_eq_pair`;
CarrierIndependentOrder.lean:97 `independent_selected_pair_owners_ne`; CarrierSelfIntersections.lean:661
`carrier_selfIntersection_not_corner`; CarrierCornerPolygon.lean:49 `ccpOutSlot_vertex`, :53 `ccpOutSlot_selected`, :60
`ccpOutSlot_unselected`, :67 `ccpInEdge_vertex`, :71 `ccpInEdge_visit`, :87 `ccp_evaluation_eq_outSlot`, :317 `ccpCornerList`,
:341 `ccpCornerCount`, :350 `ccpCornerMark`, :357 `ccpCornerPolygon`, :375 `ccpCornerMark_isTrueCorner`, :498 `ccpCornerPolygon_edge`,
:517 `ccpCornerPolygon_edge_pred`, :588 `ccpCornerPolygon_turn_eq_sign`, :659 `ccpCornerPolygon_edge_ne_zero`, :679
`ccpCornerPolygon_regular`, :691 `ccpCornerCount_ge_three`, :728 `ccp_pow_owner`; UniformDefinition.lean:27 `CarrierUniform`,
:42 `carrierRotation`; DecompositionDefinition.lean:15 `IsDecomposition`; CornerStateSum.lean:67 `carrierRotation_exists_int`,
:98 `cornerCoefficient`, :167 `cornerStateSum`; CChamber.lean:76 `recastTuple`, :82 `zmod_val_cast`, :108 `polyComp_recastTuple`,
:122 `MarkTransport`, :145 `toMark`, :154 `support`, :157 `mem_support`, :172 `twin_eq`, :208 `smoothingSuccessor_transport`,
:245 `component`, :249 `component_owner`, :252 `carrierCrossings_transport`, :278 `isDecomposition_transport`, :292
`isTrueCorner_transport`, :312 `getElem_eq_map_of_eq`, :344 `ccpCornerCount_transport`, :365 `transportedCornerPolygon`, :382
`ccpCornerPolygon_transport_of_markList_eq`, :481 `cornerCoefficient_transport`, :503 `cornerStateSum_transport`, :567
`positiveDiagram_congr`, :573 `single_isCrossing_iff_of_forall`, :582 `crossingGeometry_of_single_generic`, :864
`turn_recastTuple_cast`, :908 `markList_transport`, :953 `pathTransport` (template), :1366 `cornerStateSum_eq_of_mem_labelledChamber`,
:1378 `prop_C_chamber`; LinkDiagram.lean:61 `PolyComp`, :83 `Shadow`, :96 `Strand`, :106 `dir`, :246 `IsCrossing`, :251 `Crossing`,
:256 `Visit`, :315 `other`, :394 `Generic`, :490 `Diagram`, :547 `IsPositive`, :552 `sign`, :627 `isOver`, :1413 `crossingParam`,
:1416 `crossingParam_spec`, :1435 `visitPt`, :1589 `Shadow.single`, :1594 `singleStrandEquiv`, :1636 `single_dir`, :1641
`single_isCrossing_iff`, :1661 `singleCrossingEquiv`, :1685 `singleVisitEquiv`, :1703 `single_crossingPoint`;
LinkDiagramRecord.lean:78 `cycBetween`, :164 `compOf`, :181 `visitCoord`, :258 `nextVisit`, :413 `twin`, :442 `twin_unique`,
:470 `overBit`, :472 `overBit_eq_true_iff`, :500 `Diagram.record`, :522 `record_succ_apply`, :765 `singleDiagram_crossingParam`
(template), :785 `singleDiagram_twin` (template), :882 `VisitBetween`, :1119 `nextVisit_comm_iff_visitBetween_iff`;
LinkRecord.lean:309 `Record`, :539 `RecordIso`; LinkPositiveLift.lean:73 `Generic.exists_positive_strand`, :93
`Shadow.positiveDiagram`, :105 `positiveDiagram_det_pos`, :114 `positiveDiagram_sign`, :128 `eq_positiveDiagram_of_isPositive`,
:160 `single_generic_of`, :211 `carrierPolyComp`, :218 `carrierShadow`, :251 `BlockInterior`, :279 `BlockInterior.visit_edge`,
:339 `block_mark_eq`, :353 `edgeSegment_param`, :410 `ccpCornerPolygon_injective`, :443 `nonadjacent_meet`, :556
`ccpCornerPolygon_no_triple`, :580 `carrierShadow_generic`, :596 `positiveLift`, :618 `positiveLift_isPositive`, :622
`positiveLift_sign`, :633 `eq_positiveLift_of_isPositive`, :676 `mark_block`, :698 `consecutive_meet`, :722 `carrierCrossing_edges`,
:799 `carrierCrossingEquiv`; LinkInterfaces.lean:131 `homfly`, :382 `homfly_planar`; LocalPolynomial.lean:22 `P`;
PolynomialBlock.lean:667 `P_eq_homfly`, :1177 `presentations`.  Mathlib: `intermediate_value_univ`, `Subtype.preconnectedSpace`,
`isPreconnected_Icc`, `Equiv.subtypeEquivRight`, `Fintype.sum_equiv`, `Real.isClosedEmbedding_intCast` (fallback only).

## 4. Unit split for parallel provers (each provable from Skeleton_A.lean alone; may assume the other units' statements)

| unit | leaves | may assume | est. lines |
|---|---|---|---|
| **U1 wall data and label transport** | `exists_silentInterval`, `ccpCornerList_silentTransport`, `ccpCornerMark_silentTransport`, `ccpInEdge_silentTransport`, `ccpOutSlot_fst_silentTransport`, `cornerLabels_cases`, `cornerLabels_isCrossing_of_visit`, `corner_det_sign_silentTransport`, `turn_transportedCornerPolygon_silent` | library only | 250 |
| **U2 rotation** | `eq_of_continuous_int_valued_off_point`, `carrierRotation_eq_sum_principalAngle`, `carrierRotation_silentTransport_eq_sum`, `cornerAngleSum_int_valued`, `cornerAngleSum_continuousAt`, `carrierRotation_sideTransport` | U1 statements (`ccpCornerMark_silentTransport`, label transports, `cornerLabels_cases`, `cornerLabels_isCrossing_of_visit`) | 260 |
| **U3 crossings of corner polygons** | `isCrossing_ccp_iff`, `crossingPoint_ccp_eq`, `blockWitness_silentTransport`, `isCrossing_transportedCornerPolygon_silent` | U1 statements (`ccpCornerMark_silentTransport`, `ccpOutSlot_fst_silentTransport`) | 310 |
| **U4 record isomorphism** | `liftVisitEquiv_twin`, `liftVisitEquiv_overBit`, `liftVisitEquiv_visitCoord_lt` | U3 statements (`isCrossing_ccp_iff`, `crossingPoint_ccp_eq`, `blockWitness_silentTransport`) + U1 label transports | 340 |

Dependency order for assembly: U1 → (U2, U3) → U4; total new ≈ 1160 lines; finished module ≈ 1750 lines
(prop:C-chamber's accepted module is 1387).

## 5. Risks and fallbacks

1. **U4 `liftVisitEquiv_visitCoord_lt` (long pole, dependent-type bookkeeping through `singleVisitEquiv`, `recastTuple`,
   `visitPt`).**  Mitigations: state and prove first `crossingParam_eq_crossingParameter` (the
   `singleDiagram_crossingParam` argument for the two lifts) and `edge_recastTuple_cast` / `edgeSegment_recastTuple`
   helpers; the SM-level statement "on one corner edge the crossing parameter is `(μ − λ_a)/c_a`"
   (`ccpCornerPolygon_crossingParameter_eq`) can be proved on a single generic polygon and applied twice.  Fallback: prove
   the order statement directly from the two `edgePoint` equations without solving for `u` (`edgePoint_injective`,
   then `λ + u·c < λ + u'·c ↔ u < u'` by `mul_lt_mul_left`).
2. **U3 `isCrossing_ccp_iff` (⇒)** needs the block of the visit found by `nonadjacent_meet`, which the accepted statement
   does not export (only the parent edge).  Two independent fallbacks: (a) the no-triple-point argument in §2 (all accepted
   inputs); (b) copy the accepted proof of `nonadjacent_meet` (LinkPositiveLift.lean:443-518, same generic setting) and
   export `r, r'` from its `hwa, hwb`.
3. **`eq_of_continuous_int_valued_off_point`** is pure Mathlib; if `intermediate_value_univ`'s form is awkward, use
   `IsPreconnected.intermediate_value` on `Set.univ`, or the `constant_of_mapsTo` route with `F u₀ ∈ range Int.cast` from
   `IsClosed.mem_of_tendsto` along `u ↦ ⟨s/(k+2), _⟩`.
4. **Axioms.**  The proof uses `SM.lp_lm` and `SM.lp_lm_uniqueness` (registered literature interfaces, through
   `P_eq_homfly`), in addition to `SM.lit_homfly`; SM/PolynomialBlock.lean is "under review but usable" per the task —
   if it is not accepted in time, the only alternative for `H⁺` is R2 (a `Deform` through the centre), which requires the
   new centre genericity of §0.  A cheaper partial fallback does not exist: `homfly` is only known through
   lit:homfly's invariances, and the two lifts sit on different sides of the wall.
5. **`SilentPairData.turn`** relies on `turn g.center i ≠ 0` at the centre (`silent_center_weak`); this is exactly clause
   "all original turns are nonzero" of the printed proof (line 108) and holds for both (E) and (C) uniformly (`g.Silent`).
6. **Interval bookkeeping** in `carrierRotation_sideTransport` (`Set.Icc (−s) s` inside `g.Parameter`): the two
   endpoints must be shown `≠ ⟨0, _⟩` (`s.property.1 : 0 < s.val`) and the side tuples identified with `F a`, `F b`
   by `Subtype.ext` (`sideTime` unfolds by `Bool` cases).  Low risk.
7. **Statement fidelity.**  `CSilentData` is byte-identical to CSilent_statement.lean; the two side parameters `tp, tm`
   are independent (reduced by prop:C-chamber, as the printed proof's last sentence says); no hypothesis was added.

## 6. What is NOT done here

No centre corner polygon, no `Deform`, no `Reparam`, no modification of any accepted file.  The geo-carrier machinery of
SM/FlatCarriersDefs.lean / FlatCarriers.lean (carriers on `CrossingGeometry`) is not needed on this route; it would be the
starting point of the R2 alternative (`geoCornerPolygon_edge_ne_zero`, `geoCornerPolygon_not_antiparallel_of_det`,
`traced_successor_of_transport`, `markPointOn`, `cornerFamily`, `rotationNumber_locally_constant`) if a judge prefers
the flat lane's shape for the rotation; R1's angle-sum argument is shorter and stays on the sides.
