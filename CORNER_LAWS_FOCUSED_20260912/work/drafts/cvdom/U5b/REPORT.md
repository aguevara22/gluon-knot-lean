# CV-DOM unit U5b — REPORT (2026-09-14, ~07:20 UTC / 3:20am ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md
§0, §3 (rulings R1–R5), §4 (review-note template), §5 row **U5b** ("CV/Silence.lean: `CV.silent_center_weakGeneric`
…, `CV.silent_curve_weakGeneric` …, records agree through the centre, rotation constant through `t = 0`, piece
polynomials constant, hence `theorem CV.silence`"), §6 item 7 ("151 CV:lem:silence (its own proof; no detour
through SM prop:C-silent)"). Row: **151 CV:lem:silence**, reference/R/CV/d1_setup.tex:1300–1418 (statement
1300–1302, proof 1303–1418, remark rem:silencenew 1420–1428). Nothing under work/lean was written. Paths relative
to the package root /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## 1. Deliverables

| file | intended home | lines | decls | check | axioms |
|---|---|---:|---:|---|---|
| `work/drafts/cvdom/U5b/CVPathX1Transport.lean` | `work/lean/CV/PathX1Transport.lean` (library, namespace `CV`; imports `CV.ChamberInvII`, `CV.PieceHomflyTransport`) | 413 | 41 | `cd work/lean && lake env lean ../drafts/cvdom/U5b/CVPathX1Transport.lean`: **exit 0, no output** (no warnings), ≈ 9 s; 0 occurrences of the forbidden placeholder word | standard + `SM.lit_homfly` on the 30 path-datum lemmas (their *type* mentions `homfly` through `GeoWeakPathData`, as in U5a); standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` on the 7 that reach `pieceHomfly`/`X1` (`pieceHomfly_eq_of_pathData`, `groupedPoly_eq_of_pathData`, `Omega1_eq_of_pathData`, `X1Summand_eq_of_pathData`, `X1_eq_of_geoWeakPathData`, `X1_eq_of_weakGeneric_path`, `X1_eq_of_weakGeneric_family`, `X1_eq_of_mem_chamber'`) — identical to the accepted `CV.chamberinv_ii` |
| `work/drafts/cvdom/U5b/CVSilence.lean` | `work/lean/CV/Silence.lean` (row module; imports `CV.PathX1Transport`, `CV.ChamberInvRow`) | 533 | 31 | overlay check (§1.1): **exit 0, no output**, ≈ 7 s; 0 occurrences of the placeholder word | **standard only** on the 25 centre / geometry / path declarations (`silent_center_weakGeneric`, `silent_curve_weakGeneric`, `parallel_segments_meet_endpoint`, `Crosses.eventually`, `Member.Active.eventually`, `Event.Silent.*`, `Event.paramSegment*`, `Event.curvePath*`); `SilenceData` standard + `SM.lit_homfly` (its type mentions `X1`); `CV.silence`, `silence_sides`, `silence_near`, `silence_sideChamber`: standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` (through `X1`, as expected) |

Total 946 lines, 72 declarations (structures counted once; fields/constructors not counted), no placeholder proof
term anywhere (grep count 0 on both files and on this report), no new axioms (file-wide scan of
all 72 declarations, /tmp/u5b_ax/allax.txt: the only non-standard constants are the three accepted literature
interfaces `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness`, all inherited through `homfly`/`X1`).

### 1.1 How the row module was checked (it imports a draft)

```
cd work/lean; LP="$(lake env printenv LEAN_PATH)"; LEANBIN="$(lake env which lean)"
mkdir -p /tmp/u5b_root/CV /tmp/u5b_olean/CV
for f in "$PWD"/.lake/build/lib/lean/CV/*.olean; do ln -sf "$f" /tmp/u5b_olean/CV/; done   # overlay: first LEAN_PATH root owning `CV/` wins
lake env lean ../drafts/cvdom/U5b/CVPathX1Transport.lean                                     # file 1 as usual, exit 0
cp ../drafts/cvdom/U5b/CVPathX1Transport.lean /tmp/u5b_root/CV/PathX1Transport.lean
LEAN_PATH="/tmp/u5b_olean:$LP" "$LEANBIN" --root=/tmp/u5b_root -o /tmp/u5b_olean/CV/PathX1Transport.olean /tmp/u5b_root/CV/PathX1Transport.lean
LEAN_PATH="/tmp/u5b_olean:$LP" "$LEANBIN" ../drafts/cvdom/U5b/CVSilence.lean                # exit 0, no output
```
Axioms: `/tmp/u5b_ax/CVSilence_ax.lean` (copy of the row module + `#print axioms` for the main declarations) and
`/tmp/u5b_ax/CVSilence_allax.lean` (+ `#print axioms` for all 72 full names of both files), compiled with the same
`LEAN_PATH`; results in `/tmp/u5b_ax/allax.txt`. Once the assembler ports file 1 into work/lean/CV, plain
`lake env lean` applies to file 2 (the `import CV.PathX1Transport` line is already the ported name).

## 2. The printed lemma, its fields, and the binder

**d1_setup.tex:1300–1302.** "**Lemma (`X_1` is unchanged across a silent event).** Let `t ↦ P(t)` be a silent
event. Then `X_1(P_+) = X_1(P_-)`."

| printed text (line) | Lean |
|---|---|
| "Let `t ↦ P(t)` be a silent event." (1301) | theorem binders `(E : Event n) (hE : E.Silent)` — the accepted CV:def:event (`CV.Event`, CV/Events.lean:411) and CV:def:silent (`CV.Event.Silent`, CV/Events.lean:1125); plus `hn : 3 ≤ n` because `X_1` carries it (reading (iii), DECISION_FINAL §2; ruling R6's `X1 hn (E.curve tp) …` shape) |
| "Then `X_1(P_+) = X_1(P_-)`." (1301–1302), `P_±` = the punctured sides `P((0,ε))`, `P((−ε,0))` (def:event 1073–1075) | field **`sides`**: `∀ (tp tm : E.Parameter) (hp : 0 < tp.val) (hm : tm.val < 0), X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') = X1 hn (E.curve tm) (E.generic_punctured tm hm.ne)` |
| the same, `P_±` read as "the two chambers of the event" (def:event 1080–1083) on which "`X_1` takes one value … which is what makes the jump across the event a well-defined number" (rem:eventvalues 1097–1104) | field **`chambers`**: `∀ Qp Qm (hQp : Generic Qp) (hQm : Generic Qm), Qp ∈ E.sideChamber true → Qm ∈ E.sideChamber false → X1 hn Qp hQp = X1 hn Qm hQm` (`E.sideChamber` = the accepted def:event rendering of the two chambers) |

```
structure CV.SilenceData (hn : 3 ≤ n) (E : Event n) : Prop  -- fields sides, chambers
theorem   CV.silence (hn : 3 ≤ n) (E : Event n) (hE : E.Silent) : SilenceData hn E
```
Corollaries kept beside the row: `CV.silence_sides` (the `sides` field as a bare theorem — the shape ruling R6 /
the R lane consume), `CV.silence_near` (the δ-form of DECISION_FINAL §5 row U5b, with `δ = E.radius`),
`CV.silence_sideChamber` (the `chambers` field as a bare theorem).

## 3. Route (the printed proof, paragraph by paragraph, and where each step lives)

The printed proof (1303–1418) lists the inputs of `X_1` and shows each constant "on the whole interval, `t = 0`
included", then runs "the path argument of Proposition prop:chamberinv (ii) … through the wall … printed rather
than cited because a silent wall lies inside no chamber" (1394–1397). The Lean proof has the same two halves:
**(A)** the centre is in the accepted weak locus (`SM.WeakGeneric`), so the whole event interval is; **(B)** the
U5a path transport (records, rotations, HOMFLY along a continuous family of weakly generic polygons) carries
every input of `X_1` from `P(t_-)` to `P(t_+)` along the event itself.

| printed step (d1_setup.tex lines) | Lean |
|---|---|
| "`X_1` is determined by the set of double points …, their order along each edge, the turn signs …, the absolute rotation `R(L)` …, and `P_H`" (1303–1307) | `CV.X1Summand` / `X1_eq_sum_X1Summand` (ChamberInvII §7) and the `_of_pathData` chain of CV/PathX1Transport §5: `X1` is a function of `Ind`, `wind`, `groupedWrithe`, `carrierR`, `groupedPoly` |
| "A double point … can appear or disappear only through … a `G2` predicate vanishing with the vertex on the segment … Definition def:silent excludes that" (1308–1319) | **(A)** `Event.Silent.vertex_not_mem_edge` (1313–1318: `G2_{e,k} ∉ Z` ⇒ nonzero at the centre by `guardconst`, so `p_k` off the line; `∈ Z` ⇒ off the segment by `Silent`); **(B)** `geoFamily_crossing_iff` (U5a): crossing supports locally constant on the crossing-geometry locus (`crossing_support_persists_of_geometry`) at every point of the path |
| "Nor do two double points on disjoint pairs of edges collide … an active (G3) … lies in `Z` … which def:silent forbids; otherwise … an unconditional `G2` vanishes with the vertex on the segment" (1319–1329) | **(A)** `Event.Silent.no_sorted_triple` / `no_remote_triple` / `g2_sm` (the (G3) case, 1320–1326: the three meetings are transverse interior crossings so `Member.g3` is *active* at the centre, hence — activation open (`Crosses.eventually`, `Member.Active.eventually`), curve continuous — active and relevant at some `t ≠ 0` (`Event.exists_punctured_relevant_of_active`); `G3 = 0` at the common point (`G3_eq_zero_of_common_point`); so it would be in `Z`, against `Silent.no_g3`); `Event.Silent.remote_transverse` (the collinear case, 1326–1329 and rem:silentclauses 1275–1292: `parallel_segments_meet_endpoint`, new, standard axioms) |
| "Two double points on a common edge exchange order only by colliding … `G4⟨e;f,g⟩` … does not vanish … no collision" (1330–1371, incl. the peer's parallel example 1347–1356 and the shared-vertex case 1358–1369) | **(B)** `geoFamily_orderAgrees` (U5a): the same-edge crossing-parameter order is the order clause of `geometric_records_persist` at every point of the path; the CV predicates (G4, `G2·G1`) are not re-read — see reading 6 |
| "The turn sign at a vertex is `sgn G1_i` … nonzero of constant sign … at a smoothing site … `G5_{e,f}`" (1373–1381) | **(A)** `Event.Silent.g1_ne_zero`, `turn_ne_zero` (1373–1376); `CrossingGeometry` clause 2 at the centre (`remote_transverse`) is the (G5) fact; **(B)** `geoFamily_turn_eq_of_weak`, `geoFamily_crossingSign_eq` (U5a) → `turn_eq_of_pathData`, `crossingSign_eq_of_pathData`, `wind_eq_of_pathData` |
| "The absolute rotation `R(L)` … each corner's turn determinant … nonzero through the wall … `rot(L(t))` … a continuous integer-valued function on the connected event interval, hence constant" (1383–1397) | **(B)** `regular_geoCornerFamily`, `rotationNumber_geoCornerFamily_const`, `GeoPathCore.rotation_eq` (U5a; `rotationNumber_family_constant`, the accepted lem:rot (ii)) → `geoCarrierRotation_eq_of_pathData`, `carrierR_eq_of_pathData` |
| "the common Gauss word identifies every residual piece … record isomorphism … Axiom ax:gausscode … the same `P_H`; `w(H) = |H|` unchanged" (1399–1416) | **(B)** `pieceEquiv_of_pathData`, `pieceLabels_eq_of_pathData`, `pieceWrithe_eq_of_pathData`; `pieceHomfly_eq_of_pathData` = the record route of CV/PieceHomflyTransport (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq` = CV:lem:pieceintrinsic + `gausscode_polynomial`) with the transported lift's polynomial from the `homfly_eq` clause of the datum (lit:homfly's planar clause along the corner family) |
| "Every input to `X_1` is therefore constant on `(−ε, ε)`, and `X_1(P_+) = X_1(P_-)`" (1417–1418) | `X1_eq_of_geoWeakPathData` (reindex the sum along `supportEquiv`, `Fintype.prod_equiv` along `d.transport.component`), `X1_eq_of_weakGeneric_path`; `silence_sides` = that theorem on `E.curvePath tm tp` (the affine parameter path `u ↦ t_- + u(t_+ − t_-)`, through `t = 0`) with `silent_curve_weakGeneric` at every point |

Centre lemma (the CV analogue of the accepted `SM.WallGerm.silent_center_weak`, SM/SilentCenter.lean:40–46):
```
theorem CV.silent_center_weakGeneric (E : Event n) (hE : E.Silent) : WeakGeneric E.center
theorem CV.silent_curve_weakGeneric   (E : Event n) (hE : E.Silent) (t : E.Parameter) : WeakGeneric (E.curve t)
```
The five clauses of `WeakGeneric` at the centre: edges nonzero (`center_polygon`); turns nonzero (`g1_ne_zero`);
vertices off non-incident closed edges (`vertex_not_mem_edge`); remote meetings transverse and unique
(`remote_transverse` + `transverse_segments_unique`); `SM.G2` (`g2_sm` via the accepted
`weak_base_g2_iff_no_remote_closed_triples`). Also `silent_center_crossingGeometry` (tier 0) and
`silent_center_diagrammatic (hn)` (CV:def:diagrammatic, via the accepted `diagrammatic_of_weak`).

## 4. Readings (for the reviewer)

1. **`P_+`, `P_-`.** Two readings of the one printed conclusion, one field each: at the parameters
   (`sides`; `P_+ = P(t)`, `t ∈ (0,ε)`, the punctured sides of def:event) and on the two chambers of the event
   (`chambers`; def:event 1080–1083, rem:eventvalues). `chambers` follows from `sides` and the accepted
   prop:chamberinv (ii) (`CV.chamberinv_ii`) at the base parameter `E.sideBase = ε/2` of each side; `sides`
   is the form the R lane and ruling R6 consume. No third reading is offered.
2. **No transversality.** The lemma holds for every silent event; def:event's "every named event … is required
   to be transversal" is neither a hypothesis nor used.
3. **`hn : 3 ≤ n`** appears exactly where `X_1` appears (`SilenceData`, `silence`, `silence_sides`,
   `silence_near`, `silence_sideChamber`, `silent_center_diagrammatic`); the centre lemmas are stated without it
   (ruling R5). The decision's sketch `silent_center_weakGeneric (hn) …` had `hn`; it is not needed.
4. **The centre has no printed clause.** The statement says nothing about `P(0)`; the centre facts are auxiliary
   theorems, not bundle fields (the SM row prop:C-silent has the same shape: `silent_center_weak` beside the row).
5. **Whole interval, no δ.** The decision's `silent_curve_weakGeneric : ∃ δ > 0, ∀ t, |t.val| < δ → …` is
   delivered in the stronger form `∀ t, WeakGeneric (E.curve t)`: off the centre the polygons are generic
   (def:event) hence weakly generic (`Generic.weakGeneric`), and at the centre by step (A). Hence `sides` is the
   **all-sides form directly**, without the detour "δ-form + chamberinv (ii)" foreseen in DECISION_FINAL §5;
   `silence_near` records the δ-form as a corollary (`δ = E.radius`).
6. **What replaces the predicate-by-predicate exclusions.** The printed proof rules out births, collisions and
   order changes through the wall by naming the CV predicate that would have to vanish (G2 with the vertex on
   the segment; active G3; the accessor G4⟨e;f,g⟩ with the peer's parallel example; `G2·G1` at a shared vertex;
   G5) and invoking def:silent + lem:guardconst. The Lean proof establishes one fact at `t = 0` — the centre is in
   the accepted weak locus — and then uses the accepted local constancy of the *geometric records* on the
   crossing-geometry locus (`crossing_support_persists_of_geometry`, `geometric_records_persist`; U5a's
   `geoFamily_*`) at every point of the path. Those records (crossing supports, same-edge parameter order,
   signs, vertex turns) are exactly the inputs the printed paragraphs protect; the (G4) paragraph *is* the order
   clause, the (G5) paragraph *is* `CrossingGeometry` clause 2. The predicate bookkeeping of def:silent is used
   only at `t = 0` (G1, G2 via `guardconst`'s first clause; G3 via activation openness). The peer's parallel
   example (1347–1356) is therefore not re-derived; it needs no separate treatment on this route.
7. **"By the proof of prop:chamberinv (ii)"** (1303, 1394): realised literally — CV/PathX1Transport is the chain
   of CV/ChamberInvII with the chamber datum replaced by a hypothesis; the chamber theorem is the special case
   `X1_eq_of_mem_chamber'` (kept as a cross-check against the accepted `chamberinv_ii`).
8. **Activation at the centre and the zero set's quantifier.** `Z` asks for relevance "at `P(t)` for some
   `t ≠ 0`" (def:event), not at the centre. The step "an active member is relevant, hence lies in `Z` if it
   vanishes at `t = 0`" (1323–1325) is therefore proved as: active at the centre ⇒ (activation is an open
   condition, the curve is continuous) active at every `t` in a neighbourhood ⇒ relevant at some `t ≠ 0`
   (`Event.exists_punctured_relevant_of_active`).

## 5. Fidelity risks

* **Statement.** None known: binder `E : CV.Event n`, `E.Silent` as printed; `X_1` = the accepted `CV.X1`; the
  two fields are the two accepted renderings of `P_±` (def:event). The genericity proofs in `sides` are the only
  ones available (`generic_punctured`) and `X1` is proof-irrelevant in that argument.
* **Proof route (internal, no statement change).** The route proves a stronger intermediate fact than the text
  states at `t = 0` (the centre is weakly generic — the text only argues each input constant). Every step of the
  text is nevertheless matched by a lemma (table §3). Reviewers who read "silent" as "the specific predicates in
  `Z` behave so" should check reading 6.
* **`parallel_segments_meet_endpoint`** is new real-plane geometry (two parallel closed segments with a common
  point contain an endpoint of one another); it is the content of rem:silentclauses ("they meet at a point that
  is an endpoint of at least one of them", 1288–1289). Standard axioms; 100 lines; proof by the convex-combination
  case split. It is what makes the centre's remote meetings transverse without any G5 member in hand.
* **`chambers`** uses `E.sideChamber`, which is defined through `E.sideBase = ε/2` (accepted def:event module);
  `curve_mem_sideChamber_pos/neg` show every punctured parameter lands in the right chamber.

## 6. Name safety (ruling R3)

Every new declaration's short name was grepped against every declaration head under work/lean (SM, CV, Bridge,
RProof, Supplemental). **No collision** (no same full name). Three same-short-name hits, all in *other*
namespaces that are never `open`ed: `CV.Event.Silent.turn_ne_zero` vs `CV.Generic.turn_ne_zero` (Setup.lean:1080);
`CV.Event.Silent.vertex_not_mem_edge` vs `CV.Generic.vertex_not_mem_edge` (Setup.lean:1123) and
`SM.CarrierGeometry.vertex_not_mem_edge` (GeoCarrierGeometry.lean:85); `CV.Event.Silent.g2_sm` vs
`CV.Generic.g2_sm` (Setup.lean:1159) — deliberately parallel names (the same facts at the silent centre instead
of at a generic polygon). `crosses_of_segments_meet` was so named to stay clear of `CV.crosses_of_meet`. No
`geo*` name is declared (nothing to check against FlatCarriers*). Suffix `_of_pathData` for the re-bound
ChamberInvII lemmas (distinct from U5a's `SM.GeoCarrier.*_eq_of_path`).

## 7. Declarations

**CVPathX1Transport.lean** (`CV`, section variables `hn hP hQ {hs} (d : GeoWeakPathData hn (ofCV hP) (ofCV hQ) hs)`):
`geoMarkTransport_of_pathData`, `turn_eq_of_pathData`, `crossingParameterOrderAgrees_of_pathData`,
`crossingSign_eq_of_pathData`, `geometricRecordsAgree_of_pathData`, `geometricInterlaces_iff_of_pathData`,
`mem_Ind_transport_iff_of_pathData`, `Ind_eq_map_of_pathData`, `mem_N_transport_iff_of_pathData`,
`N_transport_of_pathData`, `mem_U_transport_iff_of_pathData`, `U_transport_of_pathData`, `weight_eq_of_pathData`,
`wind_eq_of_pathData`, `carrierUniform_iff_of_pathData`, `turn_geoCornerPolygon_eq_of_pathData`,
`geoCarrierRotation_eq_of_pathData`, `rotationNumber_geoCornerPolygon_eq_of_pathData`,
`geoCarrierRotationInt_eq_of_pathData`, `homfly_geoPositiveLift_eq_of_pathData`, `geoCarrierCrossings_eq_of_pathData`,
`card_geoCarrierCrossings_eq_of_pathData`, `bijOn_U_of_pathData`, `residualIso_of_pathData` (def),
`pieceEquiv_of_pathData` (def), `pieceEquiv_of_pathData_pieceOf`, `pieceLabels_eq_of_pathData`,
`pieceWrithe_eq_of_pathData`, `mem_piecesOn_transport_iff_of_pathData`, `piecesOn_transport_eq_of_pathData`,
`pieceHomfly_eq_of_pathData`, `groupedWrithe_eq_of_pathData`, `carrierR_eq_of_pathData`, `groupedPoly_eq_of_pathData`,
`slot_eq_of_pathData`, `Omega1_eq_of_pathData`, `X1Summand_eq_of_pathData`; then
`X1_eq_of_geoWeakPathData`, `X1_eq_of_weakGeneric_path`, `X1_eq_of_weakGeneric_family`, `X1_eq_of_mem_chamber'`.

**CVSilence.lean** (`CV`): `exists_smul_of_det_eq_zero`, `parallel_segments_meet_endpoint`, `Crosses.eventually`,
`Member.Active.eventually`; `Event.exists_punctured`, `Event.exists_punctured_relevant_of_active`;
`Event.Silent.g1_ne_zero`, `.turn_ne_zero`, `.vertex_not_mem_edge`, `.vertex_not_mem_edge'`, `.remote_transverse`,
`.crosses_of_segments_meet`, `.no_sorted_triple`, `.no_remote_triple`, `.g2_sm`; `silent_center_weakGeneric`,
`silent_center_crossingGeometry`, `silent_center_diagrammatic`, `silent_curve_weakGeneric`;
`Event.paramSegment_mem`, `Event.paramSegment` (def), `Event.paramSegment_zero`, `Event.paramSegment_one`,
`Event.continuous_paramSegment`, `Event.curvePath` (def, `Path (E.curve tm) (E.curve tp)`), `Event.curvePath_apply`;
`silence_sides`, `SilenceData` (structure, fields `sides`, `chambers`), **`silence`**, `silence_near`,
`silence_sideChamber`.

## 8. Open items / notes for the assembler

1. **Port order:** `CV/PathX1Transport.lean` first (plain `lake env lean` passes now), then `CV/Silence.lean`
   (its imports are already the ported names). Both need only the "Ported …" header line.
2. `X1_eq_of_mem_chamber'` duplicates the accepted `chamberinv_ii` as a cross-check; it may be dropped at port.
3. DECISION_FINAL §6 item 7 ("SM prop:C-silent can then reuse U5a/U5b's WeakGeneric-centre transport"): not
   touched; `SM.prop_C_silent` is accepted as is. `X1_eq_of_weakGeneric_path` is the reusable statement.
4. The R lane's `cv_R_near`/`Punctured E δ t` shape is matched by `silence_near`; the all-sides form by
   `silence_sides`; both are theorems, not fields, beside the bundle.
5. Temp artefacts: /tmp/u5b_root, /tmp/u5b_olean (symlink overlay + one olean), /tmp/u5b_ax (axiom scans).
