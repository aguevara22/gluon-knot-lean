# DESIGN_A — the moves toolkit (D-RM-1): constructor architecture

Architect A, 2026-09-15 ≈ 18:10 UTC / 2:10pm ET. Sketch: `work/drafts/moves/Sketch_A.lean` — compiles
(`cd work/lean && lake env lean ../drafts/moves/Sketch_A.lean`: 0 errors, 8 `sorry` = the 8 statement
leaves named in §4; every `def` is real; every instantiation lemma of §1.3 is PROVED from the leaves;
imports: `RProof.GenericTransport`, `SM.MarkedProducts`, `CV.GroupedKnot`, `SM.Smoothing`, all accepted).
Read first: AUTHOR_NOTES "Reassessment note … D-RM-1" (17:24Z), U_S7G_REPORT §0, U_R174_REPORT §4,
U_R176_REPORT §5, U_R177_REPORT "What remains".

## 0. The one idea

All four consumers need local replacements on diagrams that are `(Shadow.single X).positiveDiagram` (or
that diagram switched at one crossing, or the accepted `smoothDiagram` of it). SM/Smoothing.lean is the
wrong model for a Reidemeister move: the smoothing changes the SHADOW TYPE (components joined or split,
`k_i + k_j + 4` vertices, seven strand kinds, a `SpliceModel`) and 8.2k lines go into the index laws and
the outside match across a re-typed shadow. A Reidemeister move never changes components. **G11**
(RProof/GenericTransport.lean, row 173) found the economical template and proved it feasible in 11k lines:

* subdivide the moved strand by FLAT vertices (a `Reparam`, homfly-neutral via `P_planar`;
  `G11_subdiv`, CS3 `reparam_positiveDiagram_single_appendVertex`), so that the vertex to move has
  short incident edges;
* move ONE vertex (`X₁ = Function.update X₀ mid apex`): the shadow type is unchanged
  (`Shadow.withVertices`), the strands are literally the same `Σ i, ZMod k`, the outside match is the
  IDENTITY on labels, the disc `U` is the homothetic enlargement `(1+r)·Δ` of the local triangle
  (`G11_discOf`, `G11_Params` with smallness clauses `theta_sub`, `disc_clear_edge`, `disc_clear_vertex`);
* the record of the moved diagram is the old record with the local transpositions (Unit E).

DESIGN_A generalises this to a **vertex-chain move** `Diagram.moveVertices` (Sketch §M: the accepted
`Diagram.deform` of LinkMoves with the crossing-set EQUALITY weakened to an inclusion — a deletion has
fewer crossings; over data pulled back on the surviving crossings, which are the SAME `Finset Strand`s),
inside `U = homothety c (1+η) '' conv{p, chain, q}` (`Shadow.chainHull`, `Shadow.chainDisc`), and puts
three LOCAL PATTERNS on the same frame:

| pattern | local picture in `U` | output | consumers |
|---|---|---|---|
| **B** bigon deletion | chain path crosses the remote strand twice, same over strand → chain moved to the near side, no crossing | `RIIData U D' D`, `D'.record ≅ D.record.eraseTwo x y` | 110 bigon (r=1), 174 G10 (r=1), 176 port (r=1), 177(6) (r=2, the smoothing arc), 110 curl via K |
| **K** kink insertion | crossing-free 2-chain → the two end edges cross once | `RIData U D D⁺`, `D⁺.record.eraseCrossing kink ≅ D.record` | 110 curl (avoidance of the RI DELETION on the smoothing, §1.4) |
| **T** triangle (G11) | one vertex over a crossing of two others | `RIII M₀ M₁` | 177(4), with G11 generalised from positive to arbitrary over data with a strict height order |

The record clause is ONE record operation `Record.erase S` (Sketch §R, real def, compiles): `M' = {v // v ∉ S}`
for a pair-closed `S`, `succ = firstReturn ρ.succ (· ∉ S)`, COMPONENTS KEPT (`comps := ρ.comps`) — the
accepted `Record.restrict` with a different keep predicate; `eraseTwo x y` is "the record minus the four
visits". Its diagram bridge is proved exactly as `Diagram.restrictRecordIso` (LinkDiagramRecord §J, 240
lines: `restrictVisit_nextVisit`, first return of the sorted cyclic successor = sorted successor of the
retained occurrences), and here it is EASIER: the moved diagram has the same visits with the SAME
traversal coordinates (`visitCoord` unchanged: outside the disc the labels and parameters are identical;
the chain edges carry no retained visit), so `VisitBetween` is preserved literally and
`nextVisit_comm_of_visitBetween_iff` / the §J first-return law close it.

## 1. Statements (all typechecked in Sketch_A.lean; names as there)

### 1.1 Record layer (§R)
```
Record.erase (ρ) (S : Finset ρ.M) (hS : ρ.PairClosed S) : Record          -- def, compiles
Record.eraseCrossing ρ x := erase {x, pair x};  Record.eraseTwo ρ x y := erase ({x,pair x} ∪ {y,pair y})
eraseTwo_componentCount : (ρ.eraseTwo x y).componentCount = ρ.componentCount   -- rfl
eraseTwo_crossingCount (y ≠ x) (y ≠ pair x) : (ρ.eraseTwo x y).crossingCount + 2 = ρ.crossingCount   -- leaf
eraseTwo_switch (hz : z ∉ …) : Nonempty (RecordIso ((ρ.switch z).eraseTwo x y) ((ρ.eraseTwo x y).switch ⟨z,hz⟩))  -- leaf
```
### 1.2 The generic constructors
```
structure BigonChain (D : Diagram)   -- §3 lists the fields
theorem exists_rii_deletion (D : Diagram) (B : BigonChain D) :
  ∃ (w : Fin B.r → Plane) hgen hcross (U : Set Plane),
    Nonempty (RIIData U (D.moveVertices (B.moved w) hgen hcross) D) ∧
    Nonempty (RecordIso (D.moveVertices (B.moved w) hgen hcross).record
      (D.record.eraseTwo (D.overVisit B.x) (D.overVisit B.y)))
theorem rii_of_bigonChain (D) (B) : ∃ D', RII D' D ∧ Nonempty (RecordIso D'.record (D.record.eraseTwo …))
theorem P_eq_of_bigonChain (D DL) (B) (hrec : Nonempty (RecordIso (D.record.eraseTwo …) DL.record)) : P D = P DL
theorem exists_subdivide_reparam (D) (e : D.Γ.Strand) (0<t<1) (hoff : ∀ s ≠ e, edgePt e t ∉ seg s) :
  ∃ D', D'.Γ = D.Γ.subdivide e t ∧ Reparam D D'                                          -- Unit S
theorem reparam_switch (h : Reparam D D') (x) : ∃ x', crossingPoint x' = crossingPoint x ∧ Reparam (D.switch x) (D'.switch x')
structure KinkSite (D : Diagram)     -- 2-chain, crossing-free, clear hull, requested sign
theorem exists_ri_insertion (D) (K : KinkSite D) : ∃ D⁺ U (M : RIData U D D⁺),
  D⁺.sign M.kink = K.sgn ∧ Nonempty (RecordIso (D⁺.record.eraseCrossing (D⁺.overVisit M.kink)) D.record)
structure HeightOrder (C : RProof.G11_Config k) (D : Diagram) (ι : ZMod k → D.Γ.Strand) : Prop
theorem exists_riii_of_heightOrder (C) (D) (hD : D.Γ = Shadow.single C.comp) (ι) (hι) (hH : HeightOrder C D ι) :
  ∃ M₀ M₁, Reparam D M₀ ∧ RIII M₀ M₁ ∧ homfly M₁ = homfly D                              -- Unit T
```
The deletion direction is the primary one (the insertion `RII D' D` is the same datum read backwards:
`RII` is symmetric, `RII.symm`). The kink is stated in the INSERTION direction on purpose (§1.4).

### 1.3 Instantiation lemmas (PROVED in the sketch from the leaves)
* **110** `inst_110_bigon (D) (x) (B : BigonChain (D.switch x)) (DL) (hrec : … eraseTwo … ≅ DL.record) :
  ∃ Dred, RII Dred (D.switch x) ∧ Nonempty (RecordIso Dred.record DL.record)` — literally `hR`, `hrec` of
  `s7g_switch_value_of_rii`. With the subdivision absorbed: `inst_110_bigon_subdivided (hiso : PlanarIsotopic
  (D.switch x) D₂) (B : BigonChain D₂) (hrec) : P (D.switch x) = P DL` (uses `P_planar`).
* **174** `inst_174_fulltwist_move (D_H D_L) (q) (D_H') (hiso : PlanarIsotopic (D_H.switch q) D_H') (B : BigonChain D_H')
  (hrec : … ≅ D_L.record) : ∃ D_L', ReflTransGen RII D_H' D_L' ∧ homfly D_L' = homfly D_L ∧ homfly (D_H.switch q) = homfly D_L`
  — `gsc_fulltwist_triple`'s third conjunct up to the planar-isotopic start (§5, FR-A-2).
* **176** `inst_176_port` — the same shape for `est_PortData.port` (§5, FR-A-1: the literal field is unrealisable).
* **177 (6)** `inst_177_rii_after_smoothing (D_H0 D_L0) (y_H y_L) (D_H' D_L') (hH hL : PlanarIsotopic …) (BH BL)
  (hrec : eraseTwo_H ≅ eraseTwo_L) : homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)` = `esc_rii_after_smoothing`.
* **177 (4)** `inst_177_switch_riii (C : G11_Config k) … (hH : HeightOrder C (D_H.switch x_H) ι)
  (hrec : ∀ M₀ M₁, Reparam (D_H.switch x_H) M₀ → RIII M₀ M₁ → Nonempty (RecordIso M₁.record (D_L.switch x_L).record)) :
  homfly (D_H.switch x_H) = homfly (D_L.switch x_L)` = `esc_switch_riii`.
In each, the SECOND hypothesis (`hrec`) is the consumer's record bookkeeping (U110-A persistent visit
orders; row 173's `ExactTriangleVisitOrders`/`GT_homfly_wall_gen` transport; G11 Unit F), not geometry.

### 1.4 Avoidances (typechecked)
* **The RI DELETION on `D_A` is avoided.** `inst_110_curl_avoidance (D₁) (S : KinkSite D₁) (hs : S.sgn = 1) (K)
  (hK : ∀ D⁺ U (M : RIData U D₁ D⁺), D⁺.sign M.kink = 1 → (D⁺.record.eraseCrossing … ≅ D₁.record) → Nonempty
  (RecordIso K.record D⁺.record)) : P K = P D₁`: insert the kink into the CLEAN polygonal lift `D₁` of the half
  contact carrier (explicit polygon, pattern K) and identify records with `K = component₁(D_A)`
  (`knotRestrict`; `restrictRecordIso` gives its record). The printed sentence (sm-4:491-503, "delete exactly
  that curl … Lemma rp:record-polynomial gives its value") is rendered with the move in the insertion
  direction — the same `lp_core.reidemeister_I` instance, read from `D₁` to `D₁⁺`. What is avoided is the
  geometry of a smoothing output (`OrientedSmoothingData`-only knowledge) — the worst-specified object in
  the lane. The MarkedProducts 323/381 check: `homflyrows.two_component_row` takes ANY two-component `D`
  and reads `zRow 0 (P (D.knotRestrict i))` with the curl INSIDE the restriction, so the row needs no
  deletion; but the ledger needs `[z⁰] P(knotRestrict 1) = [z⁰] Q₁` with `Q₁` the half-contact-carrier
  value, i.e. an RI identity somewhere — the enlarged-support reading (sm-4:857-866) is a reading of WHICH
  carrier `D₁` is, not a way around RI. So: RI stays, but on the polygon, in the insertion direction.
* **The flat subdivision costs nothing at the value level** (`P_planar`, CS3 pattern); consumers instantiate
  the bigon on the subdivided copy (`inst_*_subdivided` shapes) — see FR-A-2 for the two interfaces that
  currently forbid it.
* **Nothing else is avoided.** RII on the smoothing (177(6)) cannot be traded for record algebra (no
  record-level RII lemma; U_S7G §0.4a).

## 2. RIII through the wall for 177 (4): reuse of G11, one generalisation

G11 proves `RIII π.M₀ π.M₁` (`G11_Params.riii`, D8) for `M₀ = positiveDiagram X₀`, `M₁ = positiveDiagram X₁`
— BOTH sides positive, the height order read from `crossingSign` (`G11_Config.trans : ¬IsAlternating …`).
Row 177's diagram is `D_H.switch x_H`: positive except at `x_H`; the K3 over-order is cyclic and the switch
makes it transitive. What is reusable verbatim (≈ 70 % of the 11k): Unit A (`G11_Config`, clearance glue),
Unit B (`G11_subdiv`, `X₀_generic`, the Reparam), Units C–D (disc, `Clean`, arcs, `ArcCover`, `MoveMatch`,
`X₁_generic`, `X₁_cross_*`, the crossing points) — none reads over data. What must be generalised: the
RIIIData over clauses (`top_ab, top_ac, mid_bc, sep_*, same over/under bits`) and Unit E (the record of `M₁`
= record of `M₀` with three transpositions, `bit_eq`), now for `M₀ := (positiveDiagram X₀).withOver ov`,
`M₁ := M₀.deform …` (the accepted `deform` applies: the three crossing pairs `{m,p},{m,q},{p,q}` are the
same `Finset`s on both sides, so `hcross` is an equality — G11 proves it as `X₁_cross_*`). Statement:
`exists_riii_of_heightOrder` (Sketch §T; `HeightOrder` = "the over relation on `{m,p,q}` is transitive",
stated through a strand embedding `ι` so it applies to `Shadow.single` and to its switches alike).
Route: `D_H.switch x_H ≃_Reparam M₀ –RIII→ M₁`, then the consumer's `M₁.record ≅ (D_L.switch x_L).record`
(G11 Unit F pattern with the switched bit). Estimate 2–3k NEW lines (Unit T), mostly re-proving the six
height-order cases of D8 and Unit E's transposition bookkeeping with `overStrand` in place of `crossingSign`.
RISK: G11's D8 and Unit E are 4.3k lines written against `positiveDiagram_isPositive`; if they cannot be
made parametric in the over data by a local edit, Unit T is a partial rewrite (≈ 4k). Mitigation: the port
of G11 should first be refactored to take `(ov, hov : consistent, htrans : HeightOrder)` — a statement-neutral
refactor of an accepted module — before Unit T starts.

## 3. Geometric hypotheses and how the consumers supply them

`BigonChain D` (Sketch §B) — the EMPTY BIGON along a vertex chain of length `r ≥ 1` on component `i`:
`j` first chain vertex, `p = j−1`, `q = j+r` fixed neighbours, `hk : r + 3 ≤ k` (no wrap; the chain path is a
proper sub-path), `rem` the remote strand (not a chain-path edge), `x.val = {(i,j−1), rem}`,
`y.val = {(i, j+r−1), rem}` (crossings on the FIRST and LAST edges of the chain path), `same_over :
overStrand x = rem ↔ overStrand y = rem` (sm-3:1982-1984 "one common over-strand"), `inner_free` (the `r−1`
inner chain edges carry no crossing), `hull_clear` (every strand other than `rem` and the `r+1` chain-path
edges misses `K = conv{p, chain, q}`), `hull_vertex` (no vertex other than `p, chain, q` lies in `K`),
`end_clear_p/q` (the outer edges `(p−1,p)`, `(q,q+1)` touch `K` only at `p`, `q`), `interior_nonempty`.
Derived inside the constructor (NOT hypotheses): `rem ∩ K = [x, y]` (convexity: `rem` meets the sides
`[p,j]`, `[j+r−1,q]` at `x, y` and its endpoints are outside), `p, q` on one side of the line of `rem` and the
chain on the other (`inner_free` + the two crossings), non-collinearity of `p, j, q` for `r = 1`.
The constructor CHOOSES `w` (the chain moved onto a segment parallel to `[p, q]` at distance `δ` inside `K`
on the `p,q` side: turns tiny, no antiparallel edges, no crossing with `rem`), `c ∈ interior K`, `η` (small:
`K ⊆ interior U` by `Convex.subset_interior_image_homothety_of_one_lt`; `U` misses everything `K` misses by
compactness — `Set.Finite.isCompact_convexHull`, `IsCompact.exists_infDist_eq_dist`; the fixed neighbours'
outer edges cross `∂U` once). This is `G11_exists_params` again (U3 there).

How each consumer produces a `BigonChain`:
* **110 bigon** (U_S7G §0.2): corner polygon `X` of the half contact carrier at the wall, `M` the bigon vertex,
  edges `(M−1,M) ∋ x`, `(M,M+1) ∋ y`, remote strand `r`. Step 1 (Unit S twice, `reparam_switch`): insert
  `p ∈ (M−1, x)`, `q ∈ (y, M+1)` close to `x, y` (parameters below the next crossing on each edge — the
  accepted crossing-parameter order of the corner polygon gives the gap; the `hoff` clause is
  `crossingPoint_not_mem_seg`-type). Step 2: `hull_clear/hull_vertex` for `K = conv{p, M, q}` from the
  printed emptiness of the bigon triangle `conv{x, M, y}` (U110-A's wall data: no other edge or vertex in the
  triangle) plus continuity in `p → x`, `q → y` (choose them close enough: a compactness lemma of Unit E).
  `same_over`: after the switch at the positive `x`, `r` is over at both (or under at both) — `switch_overStrand_self`
  + positivity of `y` (`positiveLift_isPositive`) + the printed sign table. `r = 1`.
* **174 G10** (U_R174 §4.4): `D_H = carrierDiagram (τ qAB)`, the switched pair `x', w'` on the `E`-side lift:
  the bigon bounded by the `ℓ₂`-segment `[w(ℓ₂), x(ℓ₂)]` (adjacent visits, R-LOC (2) — this IS `inner_free`
  and `hull_clear` for the remote strand) and the corner path `[w(ℓ₃) → m-corner → x(ℓ₁)]`: `r = 1` with the
  `m`-corner as `j`; emptiness from R-LOC (2)–(4) / lem:guardconst (`GT_Endpoint`'s adjacency fields
  `adj1..3`, `G11_Config.clear_edge`-style glue already proved for the triangle in G11 Unit A — reuse
  `G11_preconnected_meets_frontier`). Subdivision as in 110.
* **176 port** (U_R176 §5.1): the empty bigon `q, r` between the two triangle-strand arcs after switching `y`
  on `carrierDiagram q₀'`: same shape as 174 (`r = 1`), the RIII disc "small enough to contain the whole
  resulting bigon and no outside strand, crossing, or vertex" = `hull_clear/hull_vertex`.
* **177 (6)** (U_R177 remains 2): on `smoothDiagram D_H x` switched at `y`, the bigon `{y, z}` is bounded by the
  remote strand `q` and the path cut-piece → smoothing arc `[s⁻, t⁺]` → cut-piece: `r = 2`, chain `{s⁻, t⁺}`
  (`StrandKind.arcST`'s tail and `cutEndT`'s tail; explicit points `pt − ε·es`, `pt + ε·et`, Smoothing §3),
  end edges `cutStartS ∋ y`, `cutEndT ∋ z` (the case `arcTS` when the parameter order is reversed).
  `hull_clear` for `K = conv{p', s⁻, t⁺, q'}` from the triangle's clearance (`G11_Config.clear_edge` on the
  contact carrier's polygon) and `SmallEps` (`r₁`-clearance of the smoothing disc): every strand of
  `smoothDiagram` is of one of seven kinds (`SpliceModel.kind`, `seg_eq`), so the check is a 7-case
  classification — the Smoothing §6 style, on explicit points. The two subdivision points `p', q'` on the cut
  pieces need Unit S on a TWO-component non-positive diagram: that is why Unit S is stated for arbitrary
  `Diagram`. This is the costliest instantiation (§4).
* **110 curl** (`KinkSite D₁`): a crossing-free stretch of the half contact carrier's lift `D₁` at the cyclic
  position of the curl (the position is fixed by the record identification `hK`; any crossing-free stretch
  works because `hK` quantifies over the kink's position only through the record): subdivide one edge by
  two flat vertices (Unit S ×2), `hull_clear` by the same compactness argument.

## 4. Architecture, units, estimates (lines / hours), waves, risks

Proof architecture of `exists_rii_deletion` (mirrors Smoothing §1–§6 and G11 Units B–E, with the identity
outside match replacing the splice model):
G1 parameters (`w, c, η`; the clearance radius = `infDist` of `K` to the finite union of the other closed
edge segments and vertices; `η` below it and below the exit distances of the outer edges) →
G2 genericity of the moved shadow (`regular`: the new turns; `tail_off`, `transverse`, `no_triple`: every
new-edge/old-edge pair is either adjacent, or misses `K ⊇ new edges`, or is `rem` on the far side) →
G3 crossing correspondence (`hcross`: a crossing of the moved shadow is a crossing of `D`: its strands are
not chain edges (those cross nothing) so its `Finset` is literally an old crossing; and the old crossings
other than `x, y` survive with the same double point) →
G4 the disc: `IsDisc`, `Clean U D`, `Clean U D'` (frontier met injectively: the four frontier crossings of the
outer edges and of `rem`; `exits`: every component has a point outside `U` — `hull_vertex` gives one), the
two arcs on each side (`IsArc`: ends on `∂U` at explicit parameters on `(p−1,p)`, `(q,q+1)`, `rem`), `ArcCover`
(`mem_iff`: a traversal point evaluates into `U` iff it is on one of the two arcs — by `hull_clear` +
`end_clear` + the segment/sphere intersection count), `Separates`, `OverOn`, `inner_iff'`, `no_inner` →
G5 `MoveMatch` (`φ = id` on labels: `Outside U D ≃ Outside U D'` because `eval` agrees off the chain edges
and the chain edges are inside `U`; `dir_pos/dir_pos_before` with `l = 1`; `ψ` = the G3 correspondence;
`e = Equiv.refl`) →
G6 assembly of `RIIData U D' D` →
R1 record: `D'.Visit ≃ {v : D.Visit // v ∉ {x, pair x, y, pair y}}` via G3, `visitCoord` equal,
`VisitBetween` equal, `overBit`/`sign` equal, `firstReturn = nextVisit` (§J law) → `RecordIso`.

| unit | content | lines | hours | depends |
|---|---|---|---|---|
| **U-R** record ops | `Record.erase` (done), `eraseTwo_crossingCount`, `eraseTwo_switch`, `erase` vs `smooth`/`restrict` transport, the diagram bridge `eraseRecordIso` for any `moveVertices` with `hcross` and no visit on the moved edges (§J pattern, coordinates identical) | 900–1300 | 12–16 | — |
| **U-S** subdivision Reparam | `exists_subdivide_reparam` on arbitrary `Diagram` (multi-component, any over data: CS3's `subdivPt` bijection, `traversalBetween_subdivPt`, `over_map/over_surj` via pulled-back over data), `reparam_switch`, iterate ×2 | 1000–1400 | 14–18 | — |
| **U-G** core geometry | G1–G5 above for a chain of length `r` (`ZMod.val` no-wrap arithmetic as Smoothing 7-pre / G11 U3 Block A) | 3500–4500 | 45–60 | — |
| **U-B** pattern B | G6 + `exists_rii_deletion`, `rii_of_bigonChain`, `P_eq_of_bigonChain` | 600–900 | 8–12 | U-G, U-R |
| **U-K** pattern K | the kink: the new crossing of `[p,w₀]`, `[w₁,q]` (one explicit segment intersection, `det` sign = requested `sgn`), `RIData` assembly, record clause | 1000–1400 | 14–18 | U-G, U-R |
| **U-T** pattern T | G11 generalised to `HeightOrder` (§2) | 2000–3000 | 30–40 | G11 port refactor |
| **U-E** parameter existence | the compactness/`infDist` lemma choosing `p, q` (subdivision parameters) and `w, c, η`; shared by all instantiations (G11 `G11_exists_params` pattern) | 800–1100 | 10–14 | U-G |
| **toolkit total** | | **9.8k–13.6k** | 133–178 | |
| I-110 | `BigonChain` on the subdivided switched lift at the wall; `KinkSite` on `D₁`; the two `hK`/`hrec` record identifications are U110-A/B/H material (not counted) | 1500–2200 | 20–28 | U-B, U-K, U-S, U-E |
| I-174 | the G10 site (`BigonChain` from `GT_Endpoint` + R-LOC) + the interface glue | 1200–1800 | 16–22 | U-B, U-S, U-E |
| I-176 | the port site (same shape) | 1000–1500 | 14–20 | U-B, U-S, U-E |
| I-177a | (4): `HeightOrder` from `CompleteLocal` + the switch; glue to `esc_switch_riii` | 800–1200 | 12–16 | U-T |
| I-177b | (6): `BigonChain (r=2)` on `smoothDiagram` switched at `y` — 7-kind classification of `hull_clear` | 2000–3000 | 28–40 | U-B, U-S, U-E |
| **instantiations** | | **6.5k–9.7k** | 90–126 | |

**Honest total for the MOVES the four rows need: 16k–23k lines / 220–300 h**, against the ≤ 12k target.
The toolkit alone fits the target only in its low estimate. What is NOT in these numbers and is NOT moves
(the consumers' own remaining obligations, as listed in their reports): 174 items 4.1–4.3, 4.5–4.6
(carrier bijections across supports, wall reads, smoothing identification, writhe count: 5–8k), 176 items
3–5 (owner map, (13)/(14)/(12): 3–5k), 177 `esc_FullSplitData` + `three_components`/`knot_after_two`
(3–6k), 110's record identifications `hrec`/`hK` (1–2k). Everything the four rows need ≈ 28k–44k lines.
If the executor insists on ≤ 12k: build U-R, U-S, U-G, U-B, U-E (≈ 7–9k) and I-110 + I-174 (≈ 3–4k) — this
closes the 110 bigon branch (given U110-A's `hrec`) and the G10 move of 174; defer U-K (110 curl), U-T and
I-177a/b, and report 176/177 "ledger proved, move stated" — the honest intermediate state the plans
anticipate. The one thing that must NOT be cut is U-G's chain generality `r ≥ 1` (otherwise 177(6) and
the curl need a second constructor later).

**Waves.** Wave 1 (parallel, 4 provers): U-R, U-S, U-G (split G1–G3 / G4–G5 between two provers), U-E.
Wave 2 (parallel): U-B, U-K, U-T (after the G11 refactor), I-110-site, I-174-site. Wave 3: I-176, I-177a,
I-177b, assembly. Judge's decisive test after wave 2: `inst_110_bigon`, `inst_174_fulltwist_move` sorry-free
with the leaves closed.

**Riskiest steps** (in order): (i) U-G G4 `ArcCover.mem_iff` for a chain of `r` edges (the multi-edge arc
`Inner` characterisation and the no-wrap arithmetic; Smoothing needed `traversalBetween_span_two` for 3
labels — here `r+3`); (ii) I-177b's `hull_clear` on `smoothDiagram` (the 7-kind case analysis against an
explicit quadrilateral — Smoothing-§6 style, 2–3k lines, the largest single instantiation); (iii) U-T's
dependence on refactoring G11's D8/Unit E to arbitrary over data (§2); (iv) U-S's `over_surj` for pulled-back
over data on a subdivided multi-component shadow (CS3 did it for positive `single`); (v) U-E's compactness
lemma must deliver the subdivision points BELOW the next crossing parameter on each edge — needs the
accepted crossing-parameter order lemmas of the corner polygon (`crossingParam_spec`, `Generic.edgePt_injective`).

## 5. Fidelity

The constructors are library material (namespace `SM.Link`, new module `SM/VertexMoves.lean` after
`SM.Smoothing`; the `Record.erase` op belongs in LinkRecord's family). No row statement changes. Interface
Props are the units' internal glue (D-F11), so the following EDITS are proposals to the consuming units, not
to rows:

* **FR-A-1 (176, `est_PortData.port`) — STRONGER THAN DELIVERABLE, indeed unrealisable.** The field is
  `Relation.ReflTransGen RII ((carrierDiagram q').switch y) (carrierDiagram q)` with the two lifts on
  DIFFERENT polygons (`E.curve t'` vs `E.curve t`). `RIIData` contains `OutsideMatch.eval_eq` (identical
  traced points outside the disc) — an RII chain never moves a trace, and the two lifts differ outside every
  disc. The same objection the 174 unit raised against the literal `ReflTransGen RII (D_H.switch q) D_L`
  (U_R174_REPORT §5, "FALSE as a target") applies; the 174 unit's reading through ax:gausscode is the correct
  one. Proposed field: `port : ∃ D₀', Relation.ReflTransGen RII D₊' D₀' ∧ homfly D₀' = homfly (carrierDiagram q)`
  with `D₊'` as in FR-A-2 (`inst_176_port`); the ledger (`est_omega1_eq_of_port`) reads `port` only through
  `CV.fulltwist_coefficient`'s homfly identity, which the weakened field still supplies.
* **FR-A-2 (174 `gsc_fulltwist_triple`, 176) — the RII chain must start at a planar-isotopic copy.** The
  constructor's `D` side is the SUBDIVIDED switched lift (the flat vertices `p, q` are inside the disc — the
  outside match is the identity on labels only because both sides have `k+2` labels). Two options:
  (a) one-line interface edit `∃ D_H', PlanarIsotopic (D_H.switch q) D_H' ∧ ReflTransGen RII D_H' D_L' ∧ homfly
  D_L' = homfly D_L` — value-neutral (`homfly_planar`), exactly `inst_174_fulltwist_move`'s conclusion;
  (b) keep the literal start and build the "reparametrising outside match" variant of U-G (`φ` rescales the
  parameters on the two subdivided edges outside the disc; +1.2–1.8k lines). Recommendation: (a); the
  printed lem:fulltwist (T2) says "carried to `D_L` by oriented Reidemeister-II moves" of a diagram already
  "defined modulo positive page isotopy" (lp:lm sm-3:935), so the planar isotopy is inside the printed reading.
* **FR-A-3 (177 `esc_MoveData`) — the `∀`-smoothing quantification is stronger than any constructor can
  deliver.** `rii_after_smoothing`, `knot_after_two`, `three_components` quantify over EVERY `D_H0` with
  `IsOrientedSmoothing D_H x_H D_H0`; the library has no theorem that an arbitrary relational smoothing has the
  record `D.record.smooth v` (only the constructed `smoothDiagram` does: `exists_smoothing_record_visit`; the
  design file's clause is stated, LinkMoves:1115, not proved), and the geometry of an arbitrary smoothing is
  unknown. The ledger (`esc_contact_identity`) obtains its smoothings from `exists_smoothing_record_visit`,
  i.e. WITH record isos. Proposed: add the hypothesis `Nonempty (RecordIso D_H0.record (D_H.record.smooth v))`
  (and the `L` twin) to the three fields, or quantify over `Smoothing.smoothDiagram` — the ledger is unchanged.
  `inst_177_rii_after_smoothing` is stated at that generality (the bigon is exhibited on planar-isotopic
  copies of the two switched smoothings; for `smoothDiagram` I-177b supplies them).
* **FR-A-4 (110) — none.** `s7g_switch_value_of_rii`/`s7g_value_of_ri` are exactly discharged
  (`inst_110_bigon`; the curl by `inst_110_curl_avoidance` through `P_reidemeister_I` in the insertion
  direction — the same literature clause `lp_core.reidemeister_I`, no new axiom). The record identification
  `hrec` (`(D.switch x).record.eraseTwo … ≅ D_L.record`) is U110-A's persistent-visit-order transport; the
  toolkit contributes `eraseTwo_switch` so the switch can be moved past the erase.
* **Record clause vs the printed words.** "The remaining diagram has the same complete decorated record as
  `D_L`" (sm-4:600-606) is rendered as `RecordIso D'.record (D.record.eraseTwo x y)` composed with the
  consumer's `≅ D_L.record`; `Record.erase` keeps every circle (no component is deleted by a move — sanity
  `eraseTwo_componentCount`), drops exactly the four occurrences (`eraseTwo_crossingCount`), and takes the
  first-return successor (def:gauss-record's "forward successor" on the retained occurrences).
* **Axioms.** The constructors are standard-axiom (as Smoothing, G11); the instantiation lemmas add
  `lp_lm` through `P_reidemeister_*`/`presentations` and `lit_homfly` through `homfly` — the accepted rows'
  footprint, no new literature clause.
