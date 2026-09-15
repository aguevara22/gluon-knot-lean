# CV lane plan — 2026-09-13 (scout report for provers)

Written 2026-09-13 by a Claude Code scout subagent (claude-fable-5-1) of the pod executor, after
reading CLAUDE.md, START_HERE.md, STATE_OF_WORK.md, PROOF_PLAN.md, OPEN_WORK.md,
R_ASSEMBLY_SPEC.md, blueprint/ORDER.md, blueprint/AXIOM_REGISTRY.md, GLOSSARY.md, the CV source
(reference/R/CV/d1_setup.tex in full, d3_floor.tex, d6_vertexedge.tex, d10_axioms.tex,
d8a_dictionary.tex), the eight RA files (reference/R/RA/*.md), reference/BRIDGE/BRIDGE.md, the
accepted SM library (work/lean/SM) and the Chapter-3 layer (work/lean/SM/Link*.lean, design in
work/reports/design-decision-diagram-record-20260913.md). Row numbers are those of
`python3 tools/claims.py --pending-only` (129–184). Nothing here is accepted; every claim below
about the library was checked against the files named. A type-level skeleton of the CV
definitions (Appendix A) was compiled with `lake env lean` against the built library (exit 0,
no warnings, no sorry) on 2026-09-13; provers should start from it.

## 0. Ground rules, names, places

- Modules: `work/lean/CV/*.lean` (lakefile glob `CV.+`), `work/lean/RProof/*.lean` (`RProof.+`),
  `work/lean/Bridge/*.lean` (`Bridge.+`). All three directories exist and are empty. Namespace
  `CV` for CV rows; the checker fixes these names (work/lean/axiom-policy.json `targets`):
  `CV.hyp_R` (CV:ax:R, a HYPOTHESIS row: a Prop to be *proved* by `RProof.cv_R`),
  `RProof.localization, parity, exterior, fibre_partition, availability_zero_one, generic_table,
  generic_selector, generic_transport, generic_selected, extreme_pair_zero, extreme_transport,
  extreme_selected, cv_R`, `Bridge.B1..B4`, `Bridge.sm_R`. The CV rows 129–165 have empty
  `declaration` fields in work/lean/lean-declarations.json; proposed names are given per row
  below (pattern `CV.<label>_definition` for DEFINE rows, `CV.<label>` for PROVE rows).
- Row mechanics (ACCEPT_CYCLE.md): a DEFINE row is one "data" declaration bundling the printed
  clauses (pattern: `SM.polygonData`, `SM.uniform_definition : UniformDefinitionData`); a PROVE
  row is one theorem. Statement hash comes from `tools/check_lean.py`; independent review of the
  statement against the CV excerpt (blueprint/STATEMENTS_AND_PROOFS.md has every CV row's
  extract, lines 9594–12560).
- CV objects live on *labelled tuples* (CV has no cyclic quotient: "a polygon is a tuple",
  d1_setup.tex:8–11). Every CV declaration is on `LabelledTuple n` with `[NeZero n]` and, where
  the source says n ≥ 3, `hn : 3 ≤ n`.
- Integer representatives {1,…,n} of def:guarded ("Normalization of cyclic aliases",
  d1_setup.tex:132–140): use `CV.rep (i : ZMod n) : ℕ := (i - 1).val + 1` (rep 1 = 1, rep 0 = n);
  injective by `ZMod.val_injective` (compiled, Appendix A). The member-valued accessor
  `G4⟨e;f,g⟩` and the orientation sign `ε(f,g)` (d1_setup.tex:142–160) are `CV.G4acc`, `CV.eps`.
- Literature: CV's five "axioms" are theorems to derive (OPEN_WORK.md). The only admissible
  axioms are `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness`, `SM.ng_finite_word`,
  `SM.src_contact` (blueprint/AXIOM_REGISTRY.md), none declared yet.

## 1. Library state relevant to this lane (2026-09-13 ~18:15Z)

Accepted (work/lean/lean-declarations.json): def:polygon `SM.polygonData` (LabelledTuple, shift,
Polygon, edge, edgeSegment, edgeInterior, incident, adjacent, remote), def:chirotope (`chi`,
`turn`, `leftTurns`), def:generic `SM.Generic = G1 ∧ G2` (G1: all vertex triples, G2: no three
edge interiors concur), def:crossings (`IsCrossing`, `Crossing`, `crossingPoint`,
`crossingParameter`, `crossingSign P i j = sign det(edge i, edge j)`), def:gauss (`Visit`,
`visitPosition`, `gaussList`, `gaussWord : Cycle (Crossing P)`), def:interlace (`Interlaces`,
`interlacementGraph`, `independentSupports = Ind(G_P)`, `supportNeighbors = N(S)`,
`supportUnselected = U(S)`), def:weak `WeakGeneric`, def:regular (`Regular`, `principalTurn`,
`RegularPair`, `PrincipalAngleSpec`), def:shift, lem:rot `SM.rotation_number` (rotationNumber =
Σ principalTurn / 2π; integer; constant along paths in the regular locus; subdivision; reversal
negates; n = 3 values; 2|rot| < n; shift-invariant), lem:uniformrot `SM.uniform_rotation`,
def:germ `WallGerm` (radius, curve, continuous, generic off 0, not at 0; `center`, `sideTuple`,
`side`, `SignChanges`, `pointZeros = Z_pt`, `concurrences = Z_c`), def:walls
(`WallGerm.TripleAt e f k := pointZeros = ∅ ∧ concurrences = {{e,f,k}} ∧ three
`SignChanges (edgeParameter · a b − edgeParameter · a c)`), lem:triple-sides, thm:relgp,
def:decomposition (`IsDecomposition`), def:smoothing (`SmoothingData`, Carrier lane:
`Carrier.Mark P = ZMod n ⊕ Visit P`, `markSuccessor`, `smoothingSuccessor hn hP S`,
`Component hn hP S` (cycles), `owner`, `carrierCrossings`, `carrierCrossingCount = m_Q`,
`IsTrueCorner`), conv:selected-visits, lem:carriers `SM.carriers_lemma : CarriersLemmaData`
(count = |S|+1; `component_cycle`/`inherited_order` (inherited cyclic order); corner polygons
`ccpCornerPolygon hn hP S q : LabelledTuple (ccpCornerCount …)` with Regular, ≥ 3 corners, edges
positive multiples of parent edges, turn at a vertex corner = `turn P i`, the two smoothing
corners of a selected crossing have turns `crossingSign P i j`, `crossingSign P j i`, one left
one right; `self_intersections` (self-intersections of a carrier = its `carrierCrossings`,
transverse, not at corners, no triple point); `neighbor_visits_separated`,
`nonneighbor_visits_together`; `noncrossing`), def:uniform (`CarrierUniform`,
`UniformDecomposition`, `carrierRotation = rotationNumber ∘ ccpCornerPolygon`,
`carrierLeftTurns`). Also `CrossingGeometry P` (SM/CrossingGeometry.lean: nonzero edges, remote
meetings interior and transverse, G2), `WeakGeneric → CrossingGeometry`,
`Generic → CrossingGeometry`, and a *geometric* Gauss/interlacement API on `CrossingGeometry`:
`geometricVisitPosition`, `geometricGaussList/Word`, `GeometricInterlaces`,
`geometricInterlacementGraph`, `geometricInterlaces_iff_generic`,
`geometricInterlacementGraph_eq_generic` (SM/GeometricVisits.lean, GeometricInterlacement.lean).

Chapter-3 layer, ported but no row points at it (work/lean/SM/LinkDiagram.lean,
LinkRecord.lean, LinkLaurentRing.lean; AUTHOR_NOTES 2026-09-13 ~18:15Z): `SM.Link.PolyComp`,
`Shadow`, `Strand`, `Shadow.Generic`, `Diagram` (overStrand), `IsPositive`, `sign`, `writhe`,
`switch`, `restrict`, `reverse`, `mirror`, `Basing`, `UnderFirst`, `Shadow.single`,
`singleCrossingEquiv : (single C).Crossing ≃ SM.Crossing C.P`, `singleVisitEquiv`;
`SM.Link.Record` (comps, M, succ, pair, isOver, sgn), `RecordIso` (e, Φ, succ/pair/bit/sgn
preserved), `Record.switch`, `Record.smooth`, `Record.restrict`, `joinRecord`; `Laurent₂`,
`R = ℤ[a^±,z^±]`, `T`, `coeffAt d k f = [a^d z^k] f`, `zRow`, `degA/mindegA`, `R.delta`.
Not yet present: `Diagram.record`, `positiveLift` of a carrier, the move predicates
(`PlanarIsotopic`, `RI/RII/RIII`, `IsOrientedSmoothing`, `IsSkeinTriple`, `LinkEquiv`), the three
axiom declarations, `homfly`, `cornerCoefficient`/`cornerStateSum` (def:C). These are "phase 2"
of the adopted design and gate most of this lane (section 6(b)).

## 2. Fidelity facts every prover of this lane must know

F1. **CV genericity is strictly weaker than SM genericity.** CV def:generic(A) (d1_setup.tex:220)
says: every *relevant* member of the guarded list 𝓖 is nonzero, where G1_i = det(d_{i−1}, d_i)
(consecutive triples only), G2_{e,i} = det(d_e, p_i − p_e) for i ∉ {e, e+1} (vertex off the
*line* of a non-incident edge), and the conditional G3/G4/G5 only when *active* (strict four-sign
crossing test, d1_setup.tex:58–63). SM def:generic (sm-1-polygons.tex:100) asks χ_ijk ≠ 0 for
*all* distinct triples (G1) and no three edge interiors concurrent (G2). Hence
`SM.Generic P → CV.Generic P` (this is Bridge B1(1); proof route in section 5) and the converse
fails from n = 6 (bench A's witness `((0,0),(8,−11),(2,0),(5,−9),(−7,0),(6,−11))`,
sm-1-polygons.tex:548–560, lem:fibres status note). Both imply `Regular`. Also
`CV.Generic → WeakGeneric → CrossingGeometry` (CV's G2 puts vertices off lines hence off
segments; active G5 ≠ 0 is transversality; active G3 ≠ 0 excludes triple points — prop:fidelity
d1_setup.tex:263–288 and the B1 text). Chambers: CV chambers are components of the *labelled*
locus 𝓤_n^CV (d1_setup.tex:232–238); SM chambers are components of the cyclic quotient of
𝓤_n^SM (`SM.chamber`). Neither locus equality nor chamber equality holds or is needed (BRIDGE.md
§0: "Neither equality of the generic loci nor equality of the chamber sets is assumed").

F2. **Domain decision for carrier-dependent CV rows (must be recorded in work/AUTHOR_NOTES.md
and independently reviewed before those rows are stated).** The Carrier lane is parametrized by
`hP : SM.Generic P` (360 direct `hP.1/hP.2` uses in 27 modules; the lemmas it draws from
`Generic` are `visitKey_injective`, `generic_crossingPoint_injective`, `g1`, `visitPosition_injective`,
`g1_edge_ne_zero`, `crossingParameter_interior`, `g1_vertex_off_edge_line`,
`g1_vertex_not_mem_edge`, `crossing_edgeParameter_det_ne_zero`, `crossingPoint_unique`,
`crossingPoint_interior` — every one of which has a `CrossingGeometry`/`WeakGeneric`
counterpart or follows from CV.Generic's G1 (turns ≠ 0) and G2 (vertex off lines)). CV's
def:wind, def:pieces, def:X1, lem:carriers, lem:carrierword, lem:piececurve, prop:chamberinv(ii),
lem:silence, selector_A, singleton_D_i, cor:groupedknot are printed on CV-generic (or
diagrammatic) polygons. Two options:
  (A) *Faithful domain*: re-parametrize the Carrier lane from `Generic P` to a Prop structure
  `SM.CarrierGeometry P` := WeakGeneric P ∧ (∀ e i, ¬ incident i e → det (edge P e) (P i − P e) ≠ 0)
  (equivalently `CV.Generic`'s consequences), proved from both `SM.Generic` and `CV.Generic`,
  rebuilding `visitPosition`/`gaussList` on the existing `geometricVisitPosition`/
  `geometricGaussList` (`geometricVisitPosition_eq_generic` etc. keep the accepted rows'
  statements intact). Cost: mechanical but wide — 27 files, ~2–3 prover-weeks; it also serves
  SM def:flat-carriers / lem:weak-carriers (sm-3:262), which the design report already flagged.
  (B) *Documented narrowing*: state the carrier-dependent CV rows and `CV.hyp_R` with the binder
  `hP : SM.Generic P` (events whose punctured sides are SM-generic), record in AUTHOR_NOTES that
  U_n^SM ⊊ U_n^CV and why the final theorem is unaffected: Bridge B1 lands every SM simple triple
  germ in exactly this class, so `Bridge.sm_R` needs `RProof.cv_R` only there. Cost: none now;
  the review of each such row must carry the note "domain narrowed to U_n^SM; printed domain is
  U_n^CV", and `CV.hyp_R` becomes a narrowed hypothesis row (a scope change under OPEN_WORK's
  last paragraph: "Any scope change is documented and independently reviewed").
  Recommendation: start with (B) so the R lane is not blocked; keep every CV declaration
  *parametric in the hypothesis* (take `hP` as a variable, never unfold it) so that (A) is a
  signature change later; schedule (A) as a tracked sub-obligation "CV-DOM" (section 6(d), G1).
  The rows that do NOT depend on this decision (polygon, regular, guarded, generic,
  diagrammatic, interlace (via `CrossingGeometry`), event, guardconst, silent, rot,
  turnlift(ii), uniformrot, chamberinv(i), B1, B2, B3) are stated on their printed domains now.

F3. **CV's "diagrammatic" class** (d1_setup.tex:315) is exactly the class where the Gauss word
exists: finitely many transverse interior double points, no shared image/preimage (no triple
point), none at a corner, no vertex on a non-incident edge. In SM vocabulary this is
`CrossingGeometry P ∧ (∀ i e, ¬ incident i e → P i ∉ edgeSegment P e)` — `WeakGeneric` minus the
nonzero-turn clause. The geometric Gauss/interlacement API on `CrossingGeometry` is therefore the
right carrier of CV:def:interlace; the Carrier lane is not (F2).

F4. **CV:ax:gausscode is not to be assumed** (OPEN_WORK.md). Every in-scope consumer
(lem:pieceintrinsic d6:56, prop:chamberinv(ii) d1:1040–1060, lem:silence d1:1381–1396,
cor:groupedknot(A)(B) d6:263, lem:curl(i) via RI, and the RA files R_GENERIC_COMMON_TRANSPORT
§1–2, R_GENERIC_SELECTED_COUPLE §3, R_EXTREME_SINGLETON_TRANSPORT §1–2, R_EXTREME_SELECTED_COUPLE
§2, R_ATTACHMENT_WARRANTS §4) concludes only *polynomial equality* from the record isomorphism.
The legitimate replacement is SM rp:record-polynomial (sm-3:1215, row 63) + lp:core (row 61):
`RecordIso (record D) (record D') → homfly D = homfly D'` for one-circle diagrams. The checker
requires the shipped row `CV:ax:gausscode`, so the replacement is a reviewed scope/checker change
(OPEN_WORK.md), not an alias; the proposed statement is in row 163 below.

F5. **CV:def:X1 versus SM def:C.** CV reads one coefficient of the *product over residual
pieces* P_{S,L} = ∏_H P_H (d1_setup.tex:908–930); SM def:C reads the same coefficient of the
HOMFLY polynomial of the *positive lift of the carrier* (sm-3:1688). Their equality is
cor:groupedknot(B) (d6:263) = SM cb:products (sm-3:4638, row 102), and the selector identity
wind(S) = (−1)^{ℓ(P)+|S|}·[S uniform] is SM lem:C-X1 (sm-3:1787, row 72). This is the whole
content of Bridge B4 (BRIDGE.md §2 B4, lines 637–1441). The per-piece polynomial P_H is
load-bearing for CV:singleton_D_i (its proof splits P_{S,A} = P_{S',Λ₁}P_{S',Λ₂}·P_{{c}} piece by
piece, d6:2900–2947), so P_H must exist as an object: define it through the piece curve of
lem:piececurve (row 143) or through SM cb:products' "actual positive carrier diagram of a block".

F6. **Smooth curves.** CV:lem:rounding, lem:curl and thm:carrierfloor(A)(B)(C) live on C^∞
regular closed curves and their diagrams; the polygonal `SM.Link.Diagram` type does not contain
them. The SM rows cf:def-turning (95), cf:lem-turnlift (96), cf:lem-rounding (97), cf:lem-curl
(98), cf:thm-carrierfloor (99) are verbatim transcriptions of the CV d3 chain (sm-3:3514–4310
say so in their status tags), so this lane must NOT prove them twice: the CV rows 152–155 are to
be stated as re-exports of the SM cf:* rows once those exist (section 4). Whoever models smooth
diagrams for cf:* decides for CV too.

## 3. The CV rows of d1_setup.tex (129–151)

Format per row: (1) printed statement, short, with file:line; (2) SM counterpart and the
equivalence to prove; (3) proposed Lean signature and proof route; (4) dependencies / blocking.
"Start now" = provable with the accepted library alone (plus the rows listed before it).

### 129 CV:def:polygon — d1_setup.tex:8–19 — START NOW
(1) "A polygon on n vertices is a tuple P = (p_1,…,p_n) ∈ (ℝ²)^n with p_{i+1} ≠ p_i for every i,
indices read cyclically modulo n. Its edges are the closed segments e_i = [p_i, p_{i+1}] and its
edge directions d_i = p_{i+1} − p_i ≠ 0. Two edges are consecutive if their index sets meet, and
remote otherwise. An edge is remote to a vertex p_M when it is remote to both edges incident to
M. det(u,v) = u_1v_2 − u_2v_1."
(2) ↔ `SM.LabelledTuple n` with the extra clause "nonzero edges" (SM def:polygon allows zero
edges, sm-1:47–51; BRIDGE.md §0 notes this). Edges ↔ `edge P i`, `edgeSegment P i`;
consecutive ↔ `adjacent i j` (j − i ∈ {−1,0,1}); remote ↔ `remote i j`; "remote to a vertex M"
(CV's *stronger* reading) ↔ `remoteToVertexAndEdges M j` (j ∉ {M−2, M−1, M, M+1}); det ↔ `det`
(same sign convention: `det u v = u.1*v.2 − u.2*v.1`, Polygon.lean:16). No quotient.
(3) `def CV.IsPolygon (P : LabelledTuple n) : Prop := ∀ i, edge P i ≠ 0` and
`def CV.polygon_definition (n) (hn : 3 ≤ n) := (CV.IsPolygon (n := n), edge (n := n),
edgeSegment (n := n), adjacent (n := n), remote (n := n), remoteToVertexAndEdges (n := n), det)`
(the review-aggregate pattern of `SM.polygonData`), plus the theorem
`CV.isPolygon_iff : CV.IsPolygon P ↔ ∀ i, P (i+1) ≠ P i` (`sub_ne_zero`).
(4) None. ~40 lines.

### 130 CV:def:regular — d1_setup.tex:22–40 — START NOW
(1) "(A) … The principal turn at q_i is the unique τ_i ∈ (−π,π) with cos τ_i = ⟨δ_{i−1},δ_i⟩/
(|δ_{i−1}||δ_i|) and sgn τ_i = sgn det(δ_{i−1},δ_i). It exists precisely when δ_i is not a
negative multiple of δ_{i−1} … (B) The regular locus 𝓡_n ⊆ (ℝ²)^n is the set of P with d_i ≠ 0
for all i and d_{i+1} ≠ −λ d_i for all i and λ > 0 … Equivalently, every principal turn exists."
(2) ↔ SM def:regular verbatim: (A) is `SM.PrincipalAngleSpec u v θ` (PrincipalAngles.lean:9:
(−π<θ<π) ∧ cos θ = planeDot u v/(|u||v|) ∧ sign θ = sign det u v) with existence/uniqueness
`principalAngle_existsUnique_iff` ↔ `RegularPair u v` (u ≠ 0 ∧ v ≠ 0 ∧ ¬∃ r<0, v = r•u),
value `principalTurn P i = principalAngle (edge P (i−1)) (edge P i)`; (B) is `SM.Regular P =
∀ i, RegularPair (edge P (i−1)) (edge P i)` with `regular_iff_edges` and
`regular_iff_principalTurns_exist` already proved (RegularLocus.lean:18,26). CV states (A) for a
polygon "L with corners q_0..q_{c−1}" of any length c — same type `LabelledTuple c`.
(3) `theorem CV.regular_definition (hn : 3 ≤ n) (P : LabelledTuple n) :
  (CV.Regular P ↔ SM.Regular P) ∧ (CV.Regular P ↔ ∀ i, edge P i ≠ 0 ∧ ¬∃ λ>0, edge P (i+1) =
  −λ • edge P i) ∧ (CV.Regular P ↔ ∀ i, ∃! θ, PrincipalAngleSpec (edge P (i−1)) (edge P i) θ) ∧
  (∀ i, CV.Regular P → principalTurn P i = 0 ↔ ∃ λ>0, edge P i = λ • edge P (i−1))` with
`CV.Regular := SM.Regular` (or a literal re-transcription proved equal by `regular_iff_edges`).
Route: `regular_iff_edges`, `regular_iff_principalTurns_exist`, `principalTurn_eq_zero_iff`.
(4) None. ~60 lines.

### 131 CV:def:guarded — d1_setup.tex:42–218 — START NOW (skeleton compiled, Appendix A)
(1) "The guarded list is a finite family of real polynomial functions on (ℝ²)^n, indexed once
and for all by combinatorial data … Unconditional members (G1) G1_i = det(d_{i−1},d_i);
(G2) G2_{e,i} = ℓ_e(p_i) = det(d_e, p_i − p_e), i ∉ {e,e+1}. Activation: two remote edges e,f
are *defined* to cross when G2_{e,f}·G2_{e,f+1} < 0 and G2_{f,e}·G2_{f,e+1} < 0 [strict
products]. Conditional members (G5) G5_{e,f} = det(d_e,d_f), remote, 1 ≤ e < f ≤ n as
representatives, active when e,f cross; (G3) G3_{e,f,g} = det of the three coefficient rows
(A_e,B_e,C_e) = (−d_{e,2}, d_{e,1}, d_{e,2}p_{e,1} − d_{e,1}p_{e,2}), pairwise remote, e<f<g,
active when e,f,g pairwise cross; (G4) G4_{e;f,g} = det(d_f,p_f−p_e)det(d_g,d_e) −
det(d_g,p_g−p_e)det(d_f,d_e), f,g remote to e, f<g, active when f and g both cross e." Plus the
accessor G4⟨e;f,g⟩ (member indexed by the ordered representatives), ε(f,g) = ±1, the oriented
value, and the display G4_{e;f̄,ḡ} = (t_f̄ − t_ḡ)det(d_f̄,d_e)det(d_ḡ,d_e) at active pairs.
(2) No SM counterpart as a *list*; SM has the ingredients: `chi`, `turn` (`turn_det`:
turn P i = sign det(edge (i−1)) (edge i), so sign G1_i = turn P i), `det_edge_line`
(Generic.lean:98, the affine form), `crossingSign P e f = sign G5_{e,f}`, `edgeParameter P e f =
cramerFirst …` (Chambers.lean:86) = CV's t_f along e (`crossingParameter_eq_edgeParameter`),
`SM.IsCrossing` (segments meet, remote). Equivalences to prove: (i) at a polygon with all
unconditional members nonzero, `CV.Crosses P e f ↔ IsCrossing P {e,f}` (the "two agree wherever
the four members are nonzero" sentence, d1:79–83; strict-sign segment test — use
`SM.crossing_test` (accepted lem:crossing-test, Crossings.lean:155) which is the chirotope form
of the same four-sign test under G1; here only the four G2 values are needed, so re-prove from
`det_edge_line` and the segment parametrization); (ii) the G4 factorization display; (iii)
`G4 P e f g = −G3 P e f g`, `G4 P f e g = G3 P e f g`, `G4 P g e f = −G3 P e f g` as polynomial
identities for the fixed ordering (d8a_dictionary.tex:429–435; consumed by B3) — expected to
close by `unfold; ring`.
(3) From Appendix A: `CV.G1 P i`, `CV.G2 P e i`, `CV.G5 P e f`, `CV.G4 P e f g`, `CV.row P e :
Fin 3 → ℝ`, `CV.det3`, `CV.G3 P e f g`, `CV.Crosses P e f`, `inductive CV.Member n` (g1 i | g2 e i
h | g5 e f h | g3 e f g h | g4 e f g h, index side-conditions as proof fields),
`Member.eval : Member n → LabelledTuple n → ℝ`, `Member.Unconditional`, `Member.Active P`,
`Member.Relevant P := Unconditional ∨ Active P`, `CV.G4acc e f g h : Member n`, `CV.eps f g : ℤ`,
`CV.orientedG4 P e f g := eps f g * (G4acc e f g h).eval P`. Row declaration
`CV.guarded_definition` bundles: `Member.eval` unfolds to the printed formulas (rfl lemmas), the
activation ↔ strict four-sign products (rfl), `eps_mul_self`, `orientedG4_antisymm`
(`G4 P e g f = −G4 P e f g` by `ring`), the factorization display, and the three d8a identities.
Also prove `Member.eval` continuous in P (`Continuous fun P => m.eval P`; from
`continuous_vertex`, `continuous_edge`, `continuousAt_det` in GenericTopology.lean) — needed by
149, 147(i), B2.
(4) None. ~250 lines (Appendix A is ~110 of them).

### 132 CV:def:generic — d1_setup.tex:220–238 — START NOW
(1) "(A) A member of 𝓖 is relevant at P if it is unconditional, or conditional and active at P.
A polygon P is generic if every member relevant at P is nonzero at P … 𝓤_n the set of generic
polygons. (B) A chamber is a connected component of 𝓤_n." (Also prop:fidelity d1:263: 𝓤_n =
𝓤_n^♭, the (G1)–(G4) locus; remark d1:240: what genericity excludes.)
(2) `CV.Generic P := IsPolygon P ∧ ∀ m : Member n, m.Relevant P → m.eval P ≠ 0` (Appendix A).
Relations to prove as theorems in the same module (all consumed later): `SM.Generic P →
CV.Generic P` (= Bridge B1 clause (1); route in section 5), `CV.Generic P → WeakGeneric P`
(F1), `CV.Generic P → CrossingGeometry P`, `CV.Generic P → Regular P`, `CV.Generic P →
Diagrammatic P` (row 133), and `CV.Generic P → ∀ e f, Crosses P e f ↔ IsCrossing P {e,f}`.
Chambers: `CV.chamber (P) (hP : CV.Generic P) : Set (LabelledTuple n) :=
connectedComponentIn {Q | CV.Generic Q} P` (labelled; no quotient).
(3) `theorem CV.generic_definition (hn : 3 ≤ n) (P : LabelledTuple n) :
  (CV.Generic P ↔ IsPolygon P ∧ (∀ m, m.Unconditional → m.eval P ≠ 0) ∧
     (∀ m, m.Active P → m.eval P ≠ 0)) ∧
  (∀ Q, CV.chamber P hP = connectedComponentIn {Q | CV.Generic Q} P) ∧ (SM.Generic P → CV.Generic P)`.
(4) 131. The SM → CV direction needs: G1 consecutive from `g1_turn_area`/`turn_det`; G2 from
`g1_vertex_off_edge_line` (Generic.lean:103); G5 active from `crossing_edgeParameter_det_ne_zero`
(Chambers.lean:123) after (i) of row 131; G3 active: three pairwise-crossing edges with G3 = 0
are concurrent at a point interior to all three, contradicting SM G2 — reuse
SM/LineConcurrence.lean, LinearConcurrenceCore.lean, ConcurrenceAffinity.lean (concurrency of
three lines ↔ vanishing 3×3 determinant); G4 active: a tie t_f = t_g on e is a common interior
point of e, f, g (SM G2) or, when f,g share a vertex M, puts M on e (excluded by
`g1_vertex_not_mem_edge`). ~300 lines, the G3/G4 cases dominating.

### 133 CV:def:diagrammatic — d1_setup.tex:315–344 — START NOW
(1) "A polygon P is diagrammatic if its self-intersections are finitely many, each an isolated
transverse crossing of two edges with exactly two preimages on the traversal circle, no two of
them sharing an image or a preimage, none of them at a corner, and no vertex of P lying on an
edge not incident to it." Every generic polygon is diagrammatic; so is the polygon at a simple
positive flat wall (middle vertex inside the segment).
(2) ↔ `CrossingGeometry P ∧ (∀ i e, ¬ incident i e → P i ∉ edgeSegment P e)` (F3); finiteness of
double points is automatic for polygons (`crossing_set_finite`). Prove `CV.Generic →
Diagrammatic`, `WeakGeneric → Diagrammatic`, `Diagrammatic → CrossingGeometry` (so
`geometricGaussWord` is the CV Gauss word on this class).
(3) `def CV.Diagrammatic (P) : Prop` as in Appendix A; `theorem CV.diagrammatic_definition (hn)
(P) : (Diagrammatic P ↔ CrossingGeometry P ∧ ∀ i e, ¬incident i e → P i ∉ edgeSegment P e) ∧
(CV.Generic P → Diagrammatic P) ∧ (∀ (g : WallGerm n) j, g.FlatAt j → Diagrammatic g.center)`.
The flat-centre clause is optional (it is not consumed by any selected row; the FlatAt centre's
weak genericity is in SM/FlatCrossingGeometry.lean:15).
(4) 131–132. ~150 lines.

### 134 CV:def:interlace — d1_setup.tex:346–353 — START NOW
(1) "The interlacement graph G_P has vertex set [m], with c ∼ c′ iff exactly one of the two
occurrences of c′ lies between the two occurrences of c in the Gauss word. Ind(G_P) the
independent sets (including ∅), N_{G_P}(S) the neighbours of S."
(2) ↔ `GeometricInterlaces hP` / `geometricInterlacementGraph (hP : CrossingGeometry P)` on the
diagrammatic class, and = `Interlaces hn hP` / `interlacementGraph` on SM-generic P
(`geometricInterlaces_iff_generic`, `geometricInterlacementGraph_eq_generic`). "Exactly one
occurrence between" ↔ the alternating form: `SM.alternating_visits_iff_unique`
(Interlacement.lean:48) and `interlaces_iff_unique`, `interlaces_iff_count` (InterlaceCount.lean).
Ind ↔ `independentSupports`, N ↔ `supportNeighbors`, U ↔ `supportUnselected` (SM-generic
binder; on `CrossingGeometry` define the same three by `Finset.filter` on
`geometricInterlacementGraph`).
(3) `theorem CV.interlace_definition (hn) (P) (hD : Diagrammatic P) :
  let G := geometricInterlacementGraph (diagrammatic_crossingGeometry hD);
  (∀ x y, G.Adj x y ↔ x ≠ y ∧ exactly one visit of y lies strictly between the two visits of x
     on the traversal circle [state with `traversalBetween` and `geometricVisitPosition`]) ∧
  (∀ S, S ∈ CV.Ind hD ↔ G.IsIndepSet ↑S) ∧ ∅ ∈ CV.Ind hD ∧ (∀ S x, x ∈ CV.N hD S ↔ ∃ s ∈ S, G.Adj x s)
  ∧ (∀ (hP : SM.Generic P), G = interlacementGraph hn hP ∧ CV.Ind hD = independentSupports hn hP)`.
(4) 133. ~120 lines; the "exactly one between" clause is `interlaces_iff_unique` transported to
the geometric positions (`geometricVisitPosition_eq_generic` for the SM-generic case; for the
weaker binder re-run the InterlaceCount argument on `geometricCrossingVisitBetween`).

### 135 CV:def:smoothing — d1_setup.tex:355–360 — START NOW under decision F2(B)
(1) "For S ∈ Ind(G_P), the oriented smoothing of P along S replaces, at each double point of S,
the two transversally crossing arcs by the two arcs that respect the orientation of P and do not
cross. The result is a disjoint union of closed oriented curves, called the carriers of S."
(2) ↔ accepted SM def:smoothing/conv:selected-visits (`SM.smoothing_definition`,
`SM.selected_visits_convention`): carriers = `Carrier.Component hn hP S` (cycles of
`smoothingSuccessor`), realized as closed polygons `ccpCornerPolygon hn hP S q` whose traces
equal the carriers' images (`ccpCornerPolygon_trace`, CarrierCornerPolygon.lean:778;
`CarriersLemmaData.corner_polygons.1`). CV's "carriers of S" are exactly these components; the
CV definition has no ownership convention for the two visits of a selected crossing — SM's
incoming-visit convention is a disambiguation (rem:selected-visits, sm-3:44–52) and must be
cited in the review as such.
(3) `theorem CV.smoothing_definition (hn) (P) (hP : SM.Generic P) (S) (hS : IsDecomposition hn hP S) :
  (∀ q : Component hn hP S, the trace of q = ⋃ j, edgeSegment (ccpCornerPolygon hn hP S q) j) ∧
  Fintype.card (Component hn hP S) = S.card + 1 ∧ (∀ v : Visit P, v.1 ∈ S →
     owner hn hP S (Sum.inr v) ≠ owner hn hP S (Sum.inr (visitTwin v)))` — i.e. re-export of
`carriers_lemma`'s `corner_polygons.1`, `count`, `selected_visits_separated` under the CV label.
(4) Domain decision F2 (binder `SM.Generic`). Immediate once the decision is recorded. ~40 lines.

### 136 CV:lem:carriers — d1_setup.tex:362–448 — (i)(ii)(iii) START NOW, (iv) short new proof
(1) "Let P be diagrammatic and S ∈ Ind(G_P) … (i) the oriented smoothing of P along S has exactly
|S|+1 carriers; (ii) the assignment of traversal points to carriers is non-crossing: no
u_1,u_2,u_3,u_4 in cyclic order, none a preimage of an element of S, with u_1,u_3 on one carrier
and u_2,u_4 on a different one; (iii) if c ∈ [m]∖S is non-adjacent to every element of S, both
occurrences of c lie on the same carrier; (iv) if H is a connected component of
G_P[[m]∖(S ∪ N(S))], there is exactly one carrier on which both occurrences of every c ∈ H lie."
(2) (i) ↔ `CarriersLemmaData.count`; (ii) ↔ `.noncrossing` (SM's clause is stated for all
visits including selected ones — stronger than CV's, which excludes preimages of S; weaken by
restricting); (iii) ↔ `.nonneighbor_visits_together`; (iv) has no accepted counterpart (SM's
cb:blocks, sm-3:4623, row 101, asserts it in one sentence: "An undominated crossing has both
visits on one carrier by lem:carriers; that carrier is its owner"). Proof of (iv): for adjacent
c, c′ ∈ H (both undominated), their four visits alternate (`interlaces_iff_unique`), each pair
of visits lies on one carrier by (iii), and distinct carriers would violate (ii); so `owner` is
constant along edges of the induced graph, hence on the connected component
(`SimpleGraph.ConnectedComponent.ind`/`Reachable` induction). Uniqueness: carriers partition
the marks (`owner` is a function).
(3) `theorem CV.carriers (hn) (P) (hP : SM.Generic P) (S) (hS : IsDecomposition hn hP S) :
  Fintype.card (Component hn hP S) = S.card + 1 ∧
  (¬ ∃ u₁ u₂ u₃ u₄ : Visit P, (∀ k, u_k.1 ∉ S) ∧ cyclic order ∧ owner u₁ = owner u₃ ∧
     owner u₂ = owner u₄ ∧ owner u₁ ≠ owner u₂) ∧
  (∀ c ∈ supportUnselected hn hP S, ∀ v w : Visit P, v.1 = c → w.1 = c → owner (inr v) = owner (inr w)) ∧
  (∀ H : ((interlacementGraph hn hP).induce ↑(supportUnselected hn hP S)).ConnectedComponent,
     ∃! q : Component hn hP S, ∀ c ∈ H.supp, ∀ v : Visit P, v.1 = c → owner hn hP S (inr v) = q)`.
Define `CV.pieceOwner hn hP S H : Component hn hP S := Classical.choose …` here (used by 139, 146).
(4) 135; domain F2. (i)–(iii) are re-exports; (iv) ~120 lines.

### 137 CV:lem:carrierword — d1_setup.tex:450–485 — START NOW (statement decision needed)
(1) "Let C be a closed curve with a traversal circle Γ_C and finitely many transverse double
points, and let S be a set of them no two of which interlace. Then each closed curve produced by
smoothing C along S traverses the marked points of Γ_C lying on it in the cyclic order they have
on Γ_C. In particular, taking C = P generic and S ∈ Ind(G_P), each carrier of S traverses the
marked points lying on it in the order induced from Γ."
(2) The "in particular" clause ↔ `CarriersLemmaData.inherited_order : InheritsMarkOrder hn hP S`
and `.component_cycle` (componentCycle q = markCycle filtered by owner = q). The general clause
("any closed curve", used by lem:piececurve Step 5 on curves obtained by smoothing) is
instantiated in this formalization on carriers only: every curve it is applied to is a carrier of
some independent S′ ⊇ S of P (smoothing more crossings), and the inherited order for S′ is again
induced from Γ — so state the refinement clause: for S ⊆ S′ both independent, every carrier of
S′ lies (as a mark set) inside one carrier of S and its mark order is the one induced from that
carrier's order. Record in AUTHOR_NOTES that the printed generality over arbitrary curves is
realized on polygon carriers (the only instances consumed).
(3) `theorem CV.carrierword (hn) (P) (hP) (S) (hS) : InheritsMarkOrder hn hP S ∧
  (∀ q, componentCycle hn hP S q = (markCycle hn hP).filter (fun m => decide (owner hn hP S m = q))) ∧
  (∀ S′ (hS′ : IsDecomposition hn hP S′), S ⊆ S′ → ∀ q′ : Component hn hP S′, ∃ q : Component hn hP S,
     ∀ m, owner hn hP S′ m = q′ → owner hn hP S m = q)`.
Route: first two clauses are re-exports; the refinement clause from `smoothingSuccessor`'s
definition (`selectedMarkPerm S′ ⊇ selectedMarkPerm S`) and `CarrierUnchangedComponent.lean`
(`smoothingSuccessor_insert_bijOn_owner`: inserting a crossing refines orbits) by induction on
S′ ∖ S (`Finset.induction_on`).
(4) 135; F2. ~150 lines for the refinement clause.

### 138 CV:def:wind — d1_setup.tex:487–512 — START NOW under F2(B)
(1) "Let P be generic and S ∈ Ind(G_P). A corner of a carrier of S is either a vertex p_i of P
traversed by it or a smoothing site of S traversed by it. At each corner the carrier turns left
or right according to the sign of the determinant of the incoming and outgoing directions, which
under genericity is nonzero … uniform if all its corners turn the same way and mixed otherwise.
wt(L) = +1 (uniform, all right), (−1)^{c(L)} (uniform, all left, c(L) = #corners), 0 (mixed);
wind(S) = ∏_L wt(L)."
(2) Corners ↔ `ccpCornerMark hn hP S q j` (`Sum.inl i` vertices, `Sum.inr v` with `v.1 ∈ S`
smoothing sites; `IsTrueCorner`); c(L) ↔ `ccpCornerCount hn hP S q`; turn sign ↔
`turn (ccpCornerPolygon hn hP S q) j` (SM turn = sign det(incoming, outgoing) by `turn_det`;
nonzero by `ccpCornerPolygon_turn_ne_zero`, CarrierCornerPolygon.lean:579 — this is CV's
"under genericity is nonzero"); left = `turn = 1`, right = `turn = −1`; uniform ↔
`CarrierUniform hn hP S q`; mixed ↔ `CarrierMixed`. The SM selector form wt/wind appears in
lem:C-X1 (sm-3:1787, row 72) with the same values.
(3) `noncomputable def CV.weight (hn) (hP) (S) (q) : ℤ := if ∀ j, turn (ccpCornerPolygon hn hP S q) j = −1
then 1 else if ∀ j, turn (…) j = 1 then (−1) ^ ccpCornerCount hn hP S q else 0`;
`CV.wind hn hP S : ℤ := ∏ q : Component hn hP S, CV.weight hn hP S q`;
`theorem CV.wind_definition … : (∀ q, CV.weight … q ≠ 0 ↔ CarrierUniform hn hP S q) ∧
  (∀ q j, turn (ccpCornerPolygon …) j ≠ 0) ∧ (CV.wind hn hP S ≠ 0 ↔ UniformDecomposition hn hP S) ∧
  (∀ q j i, ccpCornerMark … j = Sum.inl i → turn (…) j = turn P i) ∧ (∀ v, v.1 ∈ S → the two
  smoothing corners have turns crossingSign P v.2 (visitTwin v).2 and its negative)`.
Route: `Finset.prod_ne_zero_iff`, `carriers_lemma.corner_polygons`.
(4) 135; F2. ~120 lines.

### 139 CV:def:pieces — d1_setup.tex:514–520 — START NOW under F2(B)
(1) "For S ∈ Ind(G_P) put U(S) = [m]∖(S ∪ N(S)). The residual pieces of S are the connected
components H ∈ π_0(G_P[U(S)]) of the induced subgraph on U(S)."
(2) U(S) ↔ `supportUnselected hn hP S` (`supportUnselected_eq`); pieces ↔
`((interlacementGraph hn hP).induce ↑(supportUnselected hn hP S)).ConnectedComponent`; the SM
counterpart is cb:blocks (sm-3:4623, row 101: "blocks" and "owners"), pending. Piece label set
`H.supp : Set (Crossing P)` (finite; `Finset` via `Set.toFinset`).
(3) `abbrev CV.Piece hn hP S := ((interlacementGraph hn hP).induce ↑(supportUnselected hn hP S)).ConnectedComponent`,
`CV.pieceLabels (H : Piece) : Finset (Crossing P)`, `CV.piecesOn (q) : Finset (Piece)` := pieces
with `pieceOwner H = q` (row 136 (iv)); `theorem CV.pieces_definition : (∀ x, x ∈ supportUnselected
hn hP S ↔ x ∉ S ∧ x ∉ supportNeighbors hn hP S) ∧ (∀ H H′ : Piece, H ≠ H′ → Disjoint (labels H)
(labels H′)) ∧ (⋃ labels = U(S)) ∧ (∀ H, (labels H).Nonempty)`.
(4) 134–136; F2. ~100 lines.

### 140 CV:def:record — d1_setup.tex:522–550 — can start now on work/lean/SM/LinkRecord.lean (unreviewed layer)
(1) "A record consists of an oriented circle Γ; a finite subset V ⊂ Γ of marked points; a
partition of V into two-element sets, the double points; for each double point a designation of
one point as over and the other as under; and a sign in {±1}. The record of a link diagram …
A record isomorphism … is a bijection φ : V → V′ that (a) preserves the cyclic order, (b) carries
double points to double points, (c) over to over and under to under, (d) preserves signs.
Records are isomorphic when such φ exists; the relation is an equivalence."
(2) ↔ `SM.Link.Record` with one circle (`Fintype.card comps = 1`) and `SM.Link.RecordIso`
(LinkRecord.lean:309, 539; `refl`, `symm`, `trans` at 559–596 give the equivalence relation).
Differences to bridge: CV's V is a subset of an *oriented circle* with its cyclic order; the
Lean record carries the successor permutation `succ` instead — (a) "preserves the cyclic order"
↔ `succ_eq` (for ≥ 3 marks on the circle these are equivalent; for 1 or 2 marks (a) is vacuous
and `succ_eq` is automatic); (b) ↔ `pair_eq`; (c) ↔ `bit_eq`; (d) ↔ `sgn_eq`. "The record of a
link diagram" ↔ `Diagram.record` — NOT yet defined (phase 2).
(3) Define `Record.CyclicBetween (ρ) (u v w : ρ.M) : Prop := ∃ a b : ℕ, 0 < a ∧ a < b ∧ b <
orbit length ∧ (ρ.succ ^ a) u = v ∧ (ρ.succ ^ b) u = w`; `structure CV.RecordIso (ρ ρ′) extends
SM.Link.RecordIso ρ ρ′`; `theorem CV.record_definition : (∀ ρ ρ′ (Φ : ρ.M ≃ ρ′.M), 3 ≤ card ρ.M →
one circle → ((∀ u v w, ρ.CyclicBetween u v w → ρ′.CyclicBetween (Φ u) (Φ v) (Φ w)) ↔
∀ v, Φ (ρ.succ v) = ρ′.succ (Φ v))) ∧ Equivalence (fun ρ ρ′ => Nonempty (RecordIso ρ ρ′)) ∧
(∀ D : Diagram, D.componentCount = 1 → (D.record).componentCount = 1) [phase 2]`.
(4) The cyclic-order ↔ successor lemma is new (Gap G13, ~150 lines); `Diagram.record` blocks
the last clause. State the first two clauses now; the row itself waits for phase 2.

### 141 CV:def:homfly — d1_setup.tex:552–563 — BLOCKED (interfaces: `SM.lit_homfly` declaration)
(1) "P_H is normalized by P(○) = 1, aP(L_+) − a^{−1}P(L_−) = zP(L_0), and the consequence
P(L ⊔ ○) = (a − a^{−1})/z · P(L)."
(2) ↔ the two printed clauses of lit:homfly (AXIOM_REGISTRY: "takes the value 1 on the
crossing-free circle, and satisfies aH_{D+} − a^{−1}H_{D−} = zH_{D0} for every skein triple"),
read on `homfly := Classical.choose SM.lit_homfly : Diagram → R` (design decision 4). The third
identity is a theorem: apply the skein at a kink (RI-inserted crossing) of L: L_+, L_− are RI-
equivalent to L and L_0 = L ⊔ ○; needs RI invariance and the ability to insert a positive and a
negative kink on a polygonal diagram in a clean disc (Gap G12). `R.delta = (a − aInv) * zInv` is
in LinkLaurentRing.lean:193.
(3) `theorem CV.homfly_definition : (∀ D, D.IsCrossingFreeCircle → homfly D = 1) ∧
  (∀ D₊ D₋ D₀, IsSkeinTriple D₊ D₋ D₀ → R.a * homfly D₊ − R.aInv * homfly D₋ = R.z * homfly D₀) ∧
  (∀ D D′, IsSplitUnion D′ D (crossing-free circle) → homfly D′ = R.delta * homfly D)`.
(4) Phase-2 move predicates + axiom declaration; the third clause is G12 (do not block the row
on it: state the first two now as the row and file the third as a separately reviewed
theorem, per the source's own wording "the third is their consequence … displayed because it
fixes the reader's convention"). Consumers of the third clause in scope: CV:lem:homflyrows(i)/(iii)
only, which is itself a re-export of SM lem:homflyrows (row 157).

### 142 CV:def:piecediagram — d1_setup.tex:565–590 — BLOCKED (phase 2 + row 143)
(1) "For a diagrammatic parent P, the diagram of a residual piece H is the parent curve P with
every double point outside H erased … and every double point of H resolved by the divide
convention: the branch whose direction u_over satisfies det(u_over, u_under) > 0 passes over.
Under this convention every crossing is positive, so its writhe is w(H) = |H| … P_H(a,z) the
HOMFLY–PT polynomial of the link so presented … the datum is a word together with a rotation
system … To erase a double point is to omit it from that datum."
(2) In the polygonal `Diagram` type a double point of the underlying curve cannot be "erased";
the source itself says the diagram is the *datum* (restricted word + rotation system) realized by
the curve C_H of lem:piececurve. So in Lean: `CV.pieceDiagram hn hP S H : Diagram` := the positive
lift (`positiveLift`, phase 2; SM def:positive-lift row 55) of the piece curve `CV.pieceCurve hn
hP S H` (row 143), a one-component polygonal diagram whose crossings are exactly the labels of H
(row 143's conclusion). Divide convention ↔ `Diagram.IsPositive x := 0 < det (dir over) (dir
under)` (LinkDiagram.lean:547) — the same formula. Writhe ↔ `Diagram.writhe`; "w(H) = |H|" ↔
`(pieceDiagram H).writhe = (pieceLabels H).card`. P_H ↔ `homfly (pieceDiagram H)`.
(3) `theorem CV.piecediagram_definition … (H : Piece) : (∀ x, (pieceDiagram H).IsPositive x) ∧
  (pieceDiagram H).writhe = (pieceLabels H).card ∧ (pieceDiagram H).Γ.Crossing ≃ pieceLabels H ∧
  (pieceDiagram H).componentCount = 1` and `CV.P_H … := homfly (pieceDiagram H)`.
(4) 143, `positiveLift` (phase 2), `homfly`. Decision to record: P_H is defined on the piece
curve of lem:piececurve, which the source names as "the construction and not a description of
its result" (d1:602–611); the SM route (cb:products, row 102: "Every block H … admits an actual
positive carrier diagram") is the same object.

### 143 CV:lem:piececurve — d1_setup.tex:592–690 — BLOCKED on 136–137 (F2) and Gap G4
(1) "Let P be diagrammatic, S ∈ Ind(G_P), H a residual piece of S. Let C_H be the closed plane
curve that the proof's own route constructs: smooth every crossing of S so that the curve falls
into the |S|+1 carriers; take the one carrier that carries H (unique by lem:carriers(iv)); apply
Step 5's iteration, smoothing at each step one double point outside H and keeping the daughter
curve that carries H. Then C_H is a closed plane curve whose double points are exactly the
crossings of H and whose Gauss word is the parent word restricted to H in the parent's cyclic
order." (Steps 1–5 of the proof are part of the statement's construction.)
(2) In the Carrier lane: Step 5's iteration smooths a set K of crossings, each a double point of
the current retained carrier hence pairwise non-interlacing and non-interlacing with H and with
S; so C_H = `ccpCornerPolygon hn hP (S ∪ K) q_H` for the component q_H owning H, with
`carrierCrossings hn hP (S ∪ K) q_H = pieceLabels H`. Steps 1–2 ↔ `neighbor_visits_separated`,
`nonneighbor_visits_together`, `self_intersections`; Step 3 ↔ `inherited_order`; Step 4 is graph
theory on `Piece`; Step 5 is the greedy construction (Gap G4: define
`CV.pieceSupport hn hP S H : Finset (Crossing P)` by well-founded recursion on the number of
carrier crossings outside H, with invariants (a) `S ∪ K` independent, (b) H owned by one
component, (c) `carrierCrossings (S ∪ K) q_H ⊆ U(S) ∩ labels on the carrier`). The counter-
example word `d a a d b b` (d1:668) shows connectedness of H is used: keep it as a comment.
(3) `theorem CV.piececurve (hn) (P) (hP) (S) (hS) (H : Piece hn hP S) :
  ∃ (K : Finset (Crossing P)) (hK : IsDecomposition hn hP (S ∪ K)) (q : Component hn hP (S ∪ K)),
    Disjoint K (pieceLabels H) ∧ K ⊆ supportUnselected hn hP S ∧
    carrierCrossings hn hP (S ∪ K) q = pieceLabels H ∧
    (∀ c ∈ pieceLabels H, ∀ v : Visit P, v.1 = c → owner hn hP (S ∪ K) (Sum.inr v) = q) ∧
    InheritsMarkOrder hn hP (S ∪ K)` — the last clause is "Gauss word = parent word restricted".
Define `CV.pieceCurve hn hP S H : LabelledTuple (ccpCornerCount …) := ccpCornerPolygon hn hP (S ∪ K) q`
from the witness (Classical.choose), with `Regular`, ≥ 3 corners, transverse self-intersections =
`pieceLabels H`, no triple point — all from `carriers_lemma` at `S ∪ K`.
(4) 136 (iv), 137 refinement clause, 139; F2. New content G4: ~400–600 lines.

### 144 CV:def:rot — d1_setup.tex:726–787 — START NOW (definition) ; identification is 145(ii)
(1) "Let L ∈ 𝓡_c … Choose r ∈ ℝ² with det(r, δ_i) ≠ 0 for all i. Then rot(L) = Σ_i ε_i, ε_i =
+1 if det(δ_{i−1},δ_i) > 0, det(δ_{i−1},r) > 0, det(r,δ_i) > 0; −1 if all three < 0; 0 otherwise.
… The sum is independent of the admissible r … Direction loops and smooth curves: tw(T) =
(θ(1) − θ(0))/2π for a tangent-angle lift θ of a continuous T : ℝ/ℤ → S¹; for a closed C¹
regular curve γ, rot(γ) = tw(γ′/|γ′|). For either put R(L) = |rot(L)|."
(2) The polygon clause is a *computable formula* for `SM.rotationNumber` (lem:rot: Σ principal
turns / 2π); the identity is CV:lem:turnlift(ii) (row 145) and is the SM cf:lem-turnlift(ii)
(sm-3:3542) as well. The smooth clause ↔ SM cf:def-turning (sm-3:3514, row 95: "Transcribed from
CV def:rot, paragraph 'Direction loops and smooth curves'") — define once there (F6).
(3) `def CV.eps_i (L : LabelledTuple c) (r : Plane) (i : ZMod c) : ℤ := if 0 < det (edge L (i−1))
(edge L i) ∧ 0 < det (edge L (i−1)) r ∧ 0 < det r (edge L i) then 1 else if (all three < 0) then −1
else 0`; `def CV.Admissible L r : Prop := ∀ i, det r (edge L i) ≠ 0`;
`def CV.rotRay [NeZero c] (L) (r) : ℤ := ∑ i, eps_i L r i`; `theorem CV.exists_admissible (hL :
CV.IsPolygon L) : ∃ r, Admissible L r` (finitely many directions; pick r off the finitely many
lines — `Set.Finite` avoidance, or r := a rotation of Σ|edge| … simplest: choose r not parallel to
any of the c nonzero edge vectors by the pigeonhole on angles or `exists_ne` in `ℝ²/lines`);
`noncomputable def CV.rot (L) (hL : Regular L) : ℤ := rotRay L (Classical.choose (exists_admissible …))`;
`theorem CV.rot_definition : (∀ r r′, Admissible L r → Admissible L r′ → rotRay L r = rotRay L r′)
∧ (Regular L → (CV.rot L hL : ℝ) = rotationNumber L) ∧ (R L = |rot L|)` — the first two clauses ARE
turnlift(ii); prove them in row 145 and cite (the def row bundles the definitions and the
statements it needs proved later only as forward references if the checker allows; otherwise
split: def row = definitions + `exists_admissible`, and put independence into 145).
The counterexample polygon at d1:770–772 (returns −1 and 0 on a non-regular polygon) can be a
`decide`/`norm_num` test in the module.
(4) None for the definitions; the independence/identification is Gap G2 (row 145).

### 145 CV:lem:turnlift — d1_setup.tex:789–905 — (ii) START NOW (Gap G2); (i),(iii) ↔ SM cf:lem-turnlift (row 96)
(1) "(i) Every continuous direction loop has a tangent-angle lift; tw(T) is independent of lift
and seam, unchanged by orientation-preserving reparametrisation, constant under homotopy through
direction loops; rotation of a closed C¹ regular curve is regular-homotopy invariant and negated
by reversal. (ii) If L ∈ 𝓡_c has principal turns τ_i then 2π rot(L) = Σ τ_i; rotation is constant
along paths in 𝓡_c, unchanged by positive flat subdivision, negated by reversal; every regular
three-corner polygon has rotation ±1 according to the common sign of its turns. (iii) [rounding
and arc-replacement clauses for C¹ curves; GL⁺(2) invariance of Δ_c − Δ_b]."
(2) (ii) consequences ↔ accepted `SM.rotation_number` clauses (integer; path constancy; insert
vertex; reversal negates; n = 3). The new content of (ii) is the identity Σ ε_i(r) = Σ τ_i/2π
(the ray formula): printed proof d1:857–866 (β_i ∈ (ρ, ρ+2π) the edge directions' angles
relative to r; τ_i = β_i − β_{i−1} + 2π ε_i). SM tools: `principalAngle`, `cornerRotor`,
`principalAngle_coe_angle` (RotationNumber.lean:13: principal angle as a `Real.Angle` equals
arg(v) − arg(u)), `Real.Angle.toReal`, `Complex.arg`. (i),(iii) ↔ SM cf:lem-turnlift (row 96), a
pending SM row with identical text; F6.
(3) `theorem CV.turnlift_ii [NeZero c] (L : LabelledTuple c) (hL : Regular L) (r) (hr : Admissible L r) :
  (2 * Real.pi) * (CV.rotRay L r : ℝ) = ∑ i, principalTurn L i` — hence `rotRay L r =
rotationNumber L` (integer cast), independence of r, and all listed consequences from
`rotation_number`. Route: fix an angle ρ of r; for each edge let β_i := the representative of
arg(edge L i) in (ρ, ρ+2π) (`toIocMod`); show principalTurn L i = β_i − β_{i−1} + 2π·ε_i by the
three sign cases of ε_i (the three determinant signs decide whether β_i − β_{i−1} ∈ (−π,π),
> π, or < −π); telescope the β's. ~400–600 lines (the angle-branch bookkeeping is the cost).
(4) 144. Clauses (i),(iii): blocked with cf:lem-turnlift (F6).

### 146 CV:def:X1 — d1_setup.tex:908–930 — BLOCKED (142, 144–145, `homfly`; F2)
(1) "Let P be generic and S ∈ Ind(G_P). For a carrier L of S set P_{S,L} = ∏_{H carried by L}
P_H, w_{S,L} = Σ_{H carried by L} w(H) (empty product 1, empty sum 0). The slot of L is the
integer 1 − w_{S,L} − R(L), the factor Ω_1(S,L) = [a^{1−w_{S,L}−R(L)} z^0] P_{S,L}(a,z) — the
coefficient itself, with no sign gate and no zero-gate — and X_1(P) = Σ_{S ∈ Ind(G_P)} wind(S)
∏_L Ω_1(S,L), the inner product over the |S|+1 carriers of S."
(2) ↔ SM def:C (sm-3:1688) through lem:C-X1 (row 72) and cb:products (row 102) (F5). Ingredients
in Lean: `wind` (138), `piecesOn q` (139), `P_H` (142), `w(H) = (pieceLabels H).card` (142),
`R(L) = |rotationNumber (ccpCornerPolygon …)|` = `|carrierRotation …|` (accepted; integer by
`rotationNumber_integer`), coefficient `coeffAt d 0` (LinkLaurentRing.lean:286).
(3) `noncomputable def CV.groupedPoly hn hP S q : R := ∏ H ∈ piecesOn q, P_H H`;
`def CV.groupedWrithe … q : ℤ := ∑ H ∈ piecesOn q, (pieceLabels H).card`;
`noncomputable def CV.slot … q : ℤ := 1 − groupedWrithe q − |carrierRotationInt q|`;
`noncomputable def CV.Omega1 … q : ℤ := coeffAt (slot q) 0 (groupedPoly q)`;
`noncomputable def CV.X1 (hn) (P) (hP : SM.Generic P) : ℤ := ∑ S ∈ independentSupports hn hP,
  CV.wind hn hP S * ∏ q : Component hn hP S, CV.Omega1 hn hP S q` (the sum over Ind and the
product over the Fintype `Component` — `Fintype.card = |S|+1` by `carriers_lemma.count`);
`theorem CV.X1_definition : (empty conventions: piecesOn q = ∅ → groupedPoly q = 1 ∧ groupedWrithe q = 0)
∧ (Omega1 unfolds) ∧ (X1 unfolds)`. Also prove `groupedWrithe q = carrierCrossingCount hn hP S q`
(the labels of the pieces on q are exactly `carrierCrossings q`, by 136 (iv) and Step 2 of 143)
— consumed by B4 and by cor:groupedknot(B).
(4) 138, 139, 142, 144/145 (for R(L) one may use `carrierRotation` directly and cite 145(ii) for
the equality with CV's rot), `homfly`. F2.

### 147 CV:prop:chamberinv — d1_setup.tex:932–1070 — (i) START NOW after 132; (ii) BLOCKED (146; ↔ SM prop:C-chamber)
(1) "(i) 𝓤_n is open in (ℝ²)^n, and every chamber is open and path connected. (ii) X_1 is
constant on each chamber."
(2) (i): SM has the analogous facts for 𝓤_n^SM: `isOpen_Generic` (GenericTopology.lean:134),
`chambers_open_pathConnected`, `labelledChambers_open_pathConnected` (Chambers.lean:40,48; via
`genericTuple_locallyPathConnected`). For 𝓤_n^CV the printed proof is the "unconditional layer
controls activation" argument: on a neighbourhood where the finitely many unconditional members
keep their signs, the crossing status of every pair is constant (`Crosses` is a sign condition on
G2 values), hence the relevant set is constant; shrink so the relevant members keep sign
(`Member.eval` continuous, row 131; `Filter.Eventually` over the finite index type
`Fintype (Member n)` — derive `Fintype`/`Finite` for `Member n` from the finite index data, or
quantify over the finitely many index tuples directly). Components of an open subset of ℝ^{2n}
are open and path connected: `IsOpen.connectedComponentIn`, `isPathConnected_iff` via
`LocPathConnectedSpace` (Mathlib: open subsets of a normed space are locally path connected).
(ii): the printed proof is the SM prop:C-chamber proof (sm-4:36, "transcribed from CV
prop:chamberinv"); with X_1 = C (B4) it is a corollary; independently it needs the full constancy
of crossings/Gauss word/turn signs/rotations/piece polynomials along a path — the R-lane's
transport machinery (R:exterior) is the same. Route recommendation: prove (ii) as
`X1 P = X1 Q` for P, Q in one *SM*-labelled chamber from `prop_C_chamber` and B4 (F2(B)); the
printed CV-chamber version requires (A).
(3) `theorem CV.chamberinv_i (hn) : IsOpen {P : LabelledTuple n | CV.Generic P} ∧ ∀ P (hP), IsOpen
(CV.chamber P hP) ∧ IsPathConnected (CV.chamber P hP)`;
`theorem CV.chamberinv_ii (hn) (P Q) (hP hQ : SM.Generic P/Q) (h : Q ∈ labelledChamber ⟨P,hP⟩) :
CV.X1 hn P hP = CV.X1 hn Q hQ`.
(4) (i): 131–132; ~250 lines. (ii): 146, B4, SM prop:C-chamber (row 106).

### 148 CV:def:event — d1_setup.tex:1072–1105 — START NOW (skeleton compiled)
(1) "An event is a continuous path t ↦ P(t) of polygons on n vertices, t ∈ (−ε,ε), such that
P(t) is generic for every t ≠ 0 and P(0) is not. Its zero set Z = {g ∈ 𝓖 : g(P(0)) = 0 and g
relevant at P(t) for some t ≠ 0}. The two chambers of the event are the chambers containing
P((−ε,0)) and P((0,ε)). The event is transversal if every member of Z changes sign at t = 0."
(2) ↔ SM def:germ `WallGerm n` with `CV.Generic` in place of `SM.Generic` and the member zero set
in place of `pointZeros`/`concurrences`. `CV.Event n` in Appendix A mirrors `WallGerm` field for
field so that `Bridge.B1` can build an `Event` from a `WallGerm` by reusing `curve`,
`continuous_curve`, `radius`. Sign change ↔ `WallGerm.SignChanges` (GermSignChange.lean:10: ∃ δ,
∀ 0<t<δ, φ(P(t))·φ(P(−t)) < 0) — Appendix A's `Event.SignChanges` is the same formula.
"Chambers of the event" ↔ `connectedComponentIn {Q | CV.Generic Q} (E.curve t)` for t on either
side (constant in t by connectedness of the punctured image: `isConnected_range` of the
continuous side map, as in `GermSides.lean`).
(3) `structure CV.Event (n) [NeZero n]` (Appendix A), `Event.center`, `Event.zeroSet : Set (Member n)`,
`Event.SignChanges`, `Event.Transversal`, `Event.sideChamber (b : Bool) : Set (LabelledTuple n)`;
`theorem CV.event_definition : (∀ E, ∀ t, t.val ≠ 0 → CV.Generic (E.curve t)) ∧ (¬ CV.Generic E.center)
∧ (∀ m, m ∈ E.zeroSet ↔ m.eval E.center = 0 ∧ ∃ t, t.val ≠ 0 ∧ m.Relevant (E.curve t)) ∧
(∀ b, IsConnected (range of side b) ∧ ∀ t on side b, E.curve t ∈ E.sideChamber b) ∧
(E.Transversal ↔ ∀ m ∈ E.zeroSet, E.SignChanges m.eval)`. The tangency example d1:1092–1098
(p_2(t) = (2, −t²)) is a good `norm_num` test that Transversal is not automatic.
(4) 131–132. ~120 lines beyond the skeleton.

### 149 CV:lem:guardconst — d1_setup.tex:1107–1121 — START NOW
(1) "Let t ↦ P(t) be an event with zero set Z, and let g ∈ 𝓖 be relevant at P(t) for some t ≠ 0
and not a member of Z. Then g(P(0)) ≠ 0, and there is ε′ ∈ (0, ε] such that g is nonzero and of
constant sign on the whole of (−ε′, ε′)."
(2) No SM row; SM's `WallGerm`-side analogues live in GermChiStability.lean / GermG1Crossings.lean
(chi stays nonzero near the centre when nonzero there). Pure continuity.
(3) `theorem CV.guardconst (E : CV.Event n) (m : Member n) (hrel : ∃ t, t.val ≠ 0 ∧ m.Relevant (E.curve t))
(hZ : m ∉ E.zeroSet) : m.eval E.center ≠ 0 ∧ ∃ ε′, 0 < ε′ ∧ ε′ ≤ E.radius ∧
  ∀ t : E.Parameter, |t.val| < ε′ → m.eval (E.curve t) ≠ 0 ∧ sign (m.eval (E.curve t)) = sign (m.eval E.center)`.
Route: `hZ` + `hrel` give the first clause by definition of `zeroSet`; `(Member.eval_continuous m).comp
E.continuous_curve`, `ContinuousAt.eventually_ne`, `Metric.eventually_nhds_iff`, sign constancy
from `eventually_gt`/`eventually_lt` (or `SignType.sign` of a nonvanishing continuous function on
an interval, via IVT `intermediate_value_Icc` — the "constant sign" clause).
(4) 148. ~100 lines.

### 150 CV:def:silent — d1_setup.tex:1265–1272 — START NOW (skeleton compiled)
(1) "An event is silent if every member of its zero set Z is a predicate G2_{e,i} whose vanishing
at t = 0 places p_i on the line of e but not on the segment e. In particular no member of Z is a
turn (G1), a crossing-order predicate (G4), a concurrency (G3) or a direction determinant (G5)."
(2) ↔ SM def:walls type (E) "exterior extension" (`WallGerm.ExtensionAt M a`: μ_M(0) on the line
of E_a outside the closed segment) — CV silent = every member of Z is such a G2. SM's other
silent type (C) "pure cut" (three non-consecutive vertices collinear) is CV-*generic* at the
centre (CV's G1 only guards consecutive triples), so it is not a CV event at all: note this for
prop:C-silent's consumers (no CV counterpart is needed). `Event.Silent` in Appendix A.
(3) `theorem CV.silent_definition (E) : E.Silent ↔ ∀ m ∈ E.zeroSet, ∃ e i h, m = Member.g2 e i h ∧
(∃ t : ℝ, E.center i = edgePoint E.center e t) ∧ E.center i ∉ edgeSegment E.center e` (rfl) and
the "in particular" clause `E.Silent → ∀ m ∈ E.zeroSet, ¬(m is g1/g3/g4/g5)` (cases).
(4) 148. ~40 lines.

### 151 CV:lem:silence — d1_setup.tex:1300–1400 — BLOCKED (146); combinatorial half START NOW
(1) "Let t ↦ P(t) be a silent event. Then X_1(P_+) = X_1(P_−)."
(2) The printed proof has a combinatorial half (crossing set, order along each edge, Gauss word,
turn signs at vertices and smoothing sites constant through t = 0 — d1:1310–1372) and an
analytic half (rotations constant through the wall by `lem:turnlift(ii)` path constancy; piece
polynomials equal via record isomorphism + ax:gausscode → F4 replacement). SM's accepted
lem:wall-sides (E) clause and the modules SilentSides.lean (`silent_sides : SilentSidesData`),
SilentCenter.lean (`silent_curve_weak`: the whole silent germ lies in the weak locus),
GeometricRecords.lean (`geometric_records_persist`, `GeometricRecordsAgree`: the complete sorted
geometric Gauss record is locally constant along a `CrossingGeometry` family) already prove the
combinatorial half for SM exterior-extension germs. Rotation constancy through the wall ↔
`rotation_number` clause 3 applied to the carrier corner polygons along the (regular) family —
needs the carriers' corner polygons to vary continuously through the wall: F2(B) gives carriers
only at SM-generic points; on the silent centre the polygon is WeakGeneric, and the Carrier lane
is not available there (Gap G1/G8). Under (B) the route is: X_1 = C on both sides (B4) and SM
prop:C-silent (row 107, pending) for C.
(3) `theorem CV.silence (E : CV.Event n) (hE : E.Silent) (hSM : ∀ t, t.val ≠ 0 → SM.Generic (E.curve t))
: ∀ t₊ t₋, 0 < t₊ → t₋ < 0 → CV.X1 hn (E.curve t₊) _ = CV.X1 hn (E.curve t₋) _` (binder per F2(B);
drop `hSM` under (A)). Combinatorial half now: `theorem CV.silence_crossings (E) (hE : E.Silent) :
∃ δ>0, ∀ t t′, |t|,|t′| < δ → (∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t′) s) ∧
GeometricRecordsAgree …` from `guardconst` + `geometric_records_persist`.
(4) 146, B4, SM prop:C-silent; the combinatorial half only needs 148–150.

## 4. The CV rows of d3_floor.tex, d6_vertexedge.tex, d10_axioms.tex (152–165)

### 152 CV:lem:rounding — d3_floor.tex:31–118 — BLOCKED (F6: ↔ SM cf:lem-rounding, row 97)
(1) "Let L be a closed polygon with corners q_1..q_c and D an oriented diagram whose underlying
plane curve is L. Assume the principal turns of L all exist and are nonzero; L has finitely many
double points, all transversal, none a corner; no corner lies on a non-incident edge. Then there
is a clearance ε_0(L) > 0 such that for every ε ∈ (0, ε_0(L)) there is a C^∞ regular closed
plane curve L_ε and a diagram D_ε with (a) L_ε = L outside the ε-discs about the corners, (b)
strictly monotone tangent inside each disc sweeping exactly |τ_i|, immersive on the open junction
arc, flat to infinite order at the ends, (c) same double points, strands, over/under, signs,
writhe, (d) rot(L_ε) = rot(L), (e) the disc package."
(2) Verbatim = SM cf:lem-rounding (sm-3:3644), whose status tag names the CV lemma. One proof,
one Lean statement; the CV row is a re-export: `theorem CV.rounding := SM.cf_lem_rounding` with
the CV symbols (`CV.rot` for polygons = `rotationNumber` by 145(ii); for smooth curves the cf:def-
turning `rot`).
(3) Signature fixed by the SM row; the CV row adds only the identification of `R(L)`.
(4) SM rows 95–97; a model of C^∞ regular closed curves and their diagrams (Gap G5). Not to be
started in this lane.

### 153 CV:lem:uniformrot — d3_floor.tex:263–302 — START NOW after 144–145
(1) "(i) Let L be a closed polygon all of whose principal turns exist and are positive. Then
rot(L) ≥ 1, with equality if L has three corners; if all negative, rot(L) ≤ −1, equality in
absolute value for three corners. (ii) exactly one negative principal turn of magnitude
α ∈ (0,π), Π the sum of the positive ones: Π − α = 2π r with r = rot(L) an integer and r ≥ 1."
(2) ↔ accepted `SM.uniform_rotation` (UniformRotation.lean:64): all turns = 1 → 1 ≤ rot; all
= −1 → rot ≤ −1; one turn −1 and the rest 1 → 1 ≤ rot (and the mirror). Plus `rotation_number`:
Σ principalTurn / 2π = rot, integer, and n = 3 → rot = ±1. The CV hypothesis "principal turns
exist and are positive" ↔ `Regular L ∧ ∀ i, 0 < principalTurn L i` ↔ `Regular L ∧ ∀ i, turn L i = 1`
(`principalTurn_sign`, UniformRotation.lean:12: sign of the principal turn = turn). The
identity Π − α = 2π r is `rotation_number`'s first clause rearranged.
(3) `theorem CV.uniformrot [NeZero c] (L : LabelledTuple c) (hL : Regular L) :
  ((∀ i, 0 < principalTurn L i) → 1 ≤ CV.rot L hL ∧ (c = 3 → CV.rot L hL = 1)) ∧
  ((∀ i, principalTurn L i < 0) → CV.rot L hL ≤ −1 ∧ (c = 3 → CV.rot L hL = −1)) ∧
  (∀ a, principalTurn L a < 0 → (∀ i ≠ a, 0 ≤ principalTurn L i) →
     (∑ i ∈ univ.erase a, principalTurn L i) − |principalTurn L a| = 2 * π * CV.rot L hL ∧ 1 ≤ CV.rot L hL)`.
Note CV(ii) admits zero turns among the "positive ones" (d3:283–288: "the hypothesis names one
negative turn and admits turns equal to zero"), while SM's third conjunct assumes all other turns
= 1; SM's `rotationNumber_ge_one_of_other_left_zero` (UniformRotation.lean:29) covers the zero
case — check its exact hypothesis; if it is "turns ≠ −1 except at a", it is the CV form.
(4) 144, 145(ii) (to read `CV.rot`). ~80 lines. (Under F2 nothing; this is polygon geometry.)

### 154 CV:lem:curl — d3_floor.tex:304–702 — BLOCKED (F6: ↔ SM cf:lem-curl, row 98)
(1) "Let F be a connected C^∞ immersed circle … given with an oriented diagram, p a point where
the tangent is u, isolated, in an embedded arc with no double point along which the tangent turns
strictly positively. Then F may be modified inside a disc Δ meeting the rest of the diagram only
in that arc so that F′ (i) is again such a diagram with P_{F′} = P_F and the same double points
outside Δ with the same signs; (ii) no tangent u in Δ, exactly one −u; (iii) exactly one double
point inside Δ, negative; (iv) rot(F′) = rot(F) − 1 and w(F′) = w(F) − 1."
(2) Verbatim = SM cf:lem-curl (sm-3:3870, "transcribed from CV lem:curl"). Re-export. (i) uses RI
invariance of P (`homfly` + `RI` move — the rational model b(t), c(t) at d3:322–329).
(3)/(4) As 152; SM row 98; needs `RI` on smooth diagrams (G5).

### 155 CV:thm:carrierfloor — d3_floor.tex:736–1012 — (R),(A),(B),(C) BLOCKED (↔ SM cf:thm-carrierfloor, row 99); (D) START after 146, 153
(1) "(R) P_{−K} = P_K; reversing a diagram keeps crossing signs and writhe, negates rot. (A) the
rounding record Round(L,D,ε) is one curve and one diagram. (B) [diagrammatic polygon, nonzero
turns, all positive or exactly one negative]: there are u ∈ S¹ and ε_1 such that for every ε <
ε_1 the rounded curve has exactly R points with tangent u and exactly R with −u, each crossed
positively. (C) Let D be an oriented knot diagram, all crossings positive, writhe w, underlying
polygon L with all principal turns existing, nonzero, |τ| < π, finitely many transverse double
points, no triple points, none a corner, no corner on a non-incident edge; R = |rot|; after
reversal, all turns positive or exactly one negative. Then min deg_a P_D ≥ 1 − w − R, and the same
for f_D = [z^0]P_D when f_D ≠ 0. (D) Let P be generic, S ∈ Ind(G_P), L a carrier of S carrying no
residual piece (P_{S,L} = 1, w_{S,L} = 0), all turns nonzero, uniform or one-dissent after
reversal. Then R(L) ≥ 1 and min deg_a P_{S,L} = 0 ≥ 1 − w_{S,L} − R(L)."
(2) (R),(A),(B),(C) verbatim = SM cf:thm-carrierfloor (sm-3:4282) clauses (R),(A),(B),(C); the
proof of (C) consumes CV:ax:etnyre + CV:ax:slbound (= SM src:contact + fd:contact, rows 94, 92)
and (R) consumes the uniqueness clause of CV:ax:homfly (= lp:lm-uniqueness via lp:coefficient-
transport, row 60). (D) is a corollary of 153 + the empty conventions of 146: `R(L) ≥ 1` from
`uniformrot`, `mindegA 1 = 0` (LinkLaurentRing: `mindegAZ` of `1`), `0 ≥ 1 − 0 − R`.
(3) `theorem CV.carrierfloor_D (hn) (P) (hP) (S) (hS) (q) (hempty : piecesOn q = ∅)
(hτ : ∀ j, turn (ccpCornerPolygon …) j ≠ 0) (huni : CarrierUniform … q ∨ OneDissent … q) :
  1 ≤ |carrierRotationInt … q| ∧ mindegAZ (groupedPoly … q) = 0 ∧ 1 − groupedWrithe q − |rot| ≤ 0`.
The SM row 99's Lean statement (when written) is the (R)(A)(B)(C) part; `CV.carrierfloor` bundles
it with (D).
(4) (D): 146, 153, `mindegAZ` spec (LinkLaurentRing.lean, def:adeg row). Rest: SM rows 60, 92,
94, 95–99, and the interfaces.

### 156 CV:lem:pieceintrinsic — d6_vertexedge.tex:56–115 — BLOCKED (F4 replacement; 143; phase 2)
(1) "Let P be generic, S ∈ Ind(G_P), H a residual piece carried by L. Let D_L(H) be the diagram
obtained from L by retaining exactly the crossings of H (divide convention) and erasing all others;
D_P(H) the intrinsic piece diagram. Then the identity map on the visits of H is a record
isomorphism from the record of D_L(H) to the record of D_P(H). Consequently they present the same
oriented link (ax:gausscode), so P_{D_L(H)} = P_H, w(D_L(H)) = |H|."
(2) With P_H defined on the piece curve (142/143), D_L(H) and D_P(H) are both realized by
`pieceCurve` — the lemma's content becomes: the H-restricted record of the positive lift of the
carrier L (`Record.restrict` of `(positiveLift q).record` to the occurrences of H) is `RecordIso`
to `(pieceDiagram H).record`, via the identity on visits (both orders inherited from Γ:
`inherited_order` at S and at S ∪ K; over/under and sign both read from the same two edge
directions; `crossingSign`). Polynomial conclusion via the F4 replacement (rp:record-polynomial +
lp:core), not via link equivalence. SM counterpart: cb:products (row 102) "Every block H has one
owner and admits an actual positive carrier …".
(3) `theorem CV.pieceintrinsic … (H) : Nonempty (RecordIso (((positiveLift hn hP S q).record).restrictTo
(visits of H)) ((pieceDiagram hn hP S H).record)) ∧ (pieceDiagram H).writhe = (pieceLabels H).card`,
plus (after F4) `homfly (pieceDiagram H) = …`. Needs `Record.restrict` on an occurrence subset
(LinkRecord.lean has `restrict` — check whether it restricts to a component set or an occurrence
set; an occurrence-set restriction (`Record.restrictOcc`) may need adding: successor = first
return into the kept set, `firstReturn` machinery LinkRecord.lean:55–190).
(4) 142, 143, `Diagram.record`, `positiveLift` (phase 2). ~300 lines after the layer exists.

### 157 CV:lem:homflyrows — d6_vertexedge.tex:117–261 — BLOCKED (↔ SM lem:homflyrows, row 109)
(1) "(i) For oriented knots K, J: P_{K#J} = P_K P_J; for a knot K and a link J: P_{K⊔J} =
δ P_K P_J. (ii) For an oriented link diagram D with ordered components D_1, D_2 and linking
number λ: [z^{−1}]P_D = (a − a^{−1}) a^{−2λ} [z^0](P_{D_1}P_{D_2}). (iii) P_{K_1⊔…⊔K_n} = δ^{n−1}
P_{K_1}⋯P_{K_n}."
(2) Verbatim = SM lem:homflyrows (sm-4:230, "transcribed from CV lem:homflyrows via mp:join,
mp:stack, mp:lowest"), pending row 109 with dependencies def:positive-lift, lp:core, mp:join,
mp:lowest, mp:stack. Re-export. (ii) is the clause the R lane reads (R_GENERIC_SELECTED_COUPLE §4,
R_EXTREME_SINGLETON_TRANSPORT §3, R_EXTREME_SELECTED_COUPLE §3), together with the knot-parity
clause of CV:ax:homfly (`[z^0](Q_A Q_B) = [z^0]Q_A · [z^0]Q_B`).
(3) `theorem CV.homflyrows := SM.lem_homflyrows` with the "K#J" reading on marked diagrams and
the join relation (design decision 10); linking number ↔ half the sum of mixed-crossing signs
(`Diagram.sign` over crossings with strands in both components).
(4) SM rows 55, 61, 66, 67, 69, 109.

### 158 CV:cor:groupedknot — d6_vertexedge.tex:263–495 — BLOCKED (↔ SM cb:products, row 102; mp:blocks, row 70)
(1) "(A) L a carrier of S bearing at least one residual piece, W the union of their label sets =
the self-crossings of L (Step 2 of lem:piececurve); D(W) the diagram from L retaining W is L
carrying all its own crossings. With W = W_1 ⊔ … ⊔ W_k the connected components (the label sets
of the pieces): D(W) ≅ #_𝒯(D(W_1),…,D(W_k)) for a fixed ordered binary parenthesization 𝒯, and
P_{D(W)} = ∏ P_{D(W_i)}. (B) L bearing pieces H_1..H_k, k ≥ 1: the diagram obtained from L by
retaining exactly the crossings of H_1 ∪ … ∪ H_k is a knot diagram whose HOMFLY polynomial is
P_{S,L} = ∏ P_{H_i}, writhe w_{S,L} = Σ|H_i|, underlying curve L with no triple points."
(2) (B) is exactly SM cb:products' product clause (sm-3:4638: the positive carrier diagram's
polynomial is the product of its blocks' polynomials) read with `positiveLift q`: `homfly
(positiveLift hn hP S q) = ∏ H ∈ piecesOn q, P_H H` and `(positiveLift q).writhe = Σ (pieceLabels
H).card = carrierCrossingCount q`. (A)'s connected-sum tree ↔ mp:blocks (row 70) via the gap
lemma / closed-block tree (d6:296–330); design decision 10 says the *realization* clause of
mp:blocks is a tracked sub-obligation and only the product clause is consumed. Consumers in
scope read only the product and writhe identities (R files; 165).
(3) `theorem CV.groupedknot_B (hn) (P) (hP) (S) (hS) (q) (hne : (piecesOn q).Nonempty) :
  homfly (positiveLift hn hP S q) = groupedPoly hn hP S q ∧ (positiveLift …).writhe = groupedWrithe … q
  ∧ (positiveLift …).componentCount = 1 ∧ no triple point (from carriers_lemma.self_intersections)`.
(A): state the record-level block decomposition through `joinRecord` (LinkRecord.lean) and
mp:blocks' product clause; the "≅" is a `RecordIso` statement (F4), never link equivalence.
(4) 142, 143, 146, `positiveLift`, SM cb:products (needs lp:core, mp:blocks, rp:record-polynomial).

### 159 CV:lem:fulltwist — d6_vertexedge.tex:1981–2040 — BLOCKED only by the move predicates + `homfly` (then ~60 lines)
(1) "Let D_L, D_H, D_A be oriented diagrams and q a positive crossing of D_H such that (T1) the
oriented smoothing of D_H at q is D_A; (T2) switching q in D_H gives a diagram carried to D_L by
oriented Reidemeister-II moves. For any diagram put F_D = P_D; for a single-curve diagram put
d(D) = 1 − w(D) − R(Γ_D), Ω(D) = [a^{d(D)} z^0] F_D. Then F_H = a^{−2} F_L + a^{−1} z F_A. If
moreover d_H = d_L − 2, then Ω_H − Ω_L = [a^{d_L − 1} z^{−1}] F_A."
(2) Pure consequence of the skein and RII invariance; no SM row (the DAG removed its historical
reference to def:markeddata). `R(Γ_D)` for a one-component `Diagram` = `|rotationNumber (D.Γ.comp 0).P|`
(the component polygon is Regular by `Shadow.Generic.regular`; integer by
`rotationNumber_integer`).
(3) `theorem CV.fulltwist (D_L D_H D_A : Diagram) (q : D_H.Γ.Crossing) (hq : D_H.IsPositive q)
  (T1 : IsOrientedSmoothing D_H q D_A) (T2 : Relation.EqvGen RII (D_H.switch q) D_L) :
  homfly D_H = R.aInv * R.aInv * homfly D_L + R.aInv * R.z * homfly D_A ∧
  (∀ (hL : D_L.componentCount = 1) (hH : D_H.componentCount = 1),
    CV.d D_H hH = CV.d D_L hL − 2 → CV.Omega D_H hH − CV.Omega D_L hL = coeffAt (CV.d D_L hL − 1) (−1) (homfly D_A))`.
Route: skein at q (`IsSkeinTriple D_H (D_H.switch q) D_A`), RII-invariance (EqvGen induction),
multiply by `R.aInv` (`R.a_mul_aInv`), then `coeffAt` linearity (`coeffAt_add`, `coeffAt_sub`)
and `coeffAt d k (single (p,q) 1 * f) = coeffAt (d−p) (k−q) f` (a shift lemma to add to
LinkLaurentRing: `coeffAt_single_mul`).
(4) Phase-2 predicates `IsOrientedSmoothing`, `RII`, `IsSkeinTriple`, and `homfly` (declaration
of `SM.lit_homfly`). Independent of F2.

### 160 CV:ax:homfly — d10_axioms.tex:342–360 — BLOCKED (interfaces; ↔ lp:core, lp:coefficient-transport)
(1) "There is a unique map L ↦ P_L(a,z) ∈ ℤ[a^{±1},z^{±1}] from isotopy classes of oriented links
in S³ satisfying P_○ = 1 and aP_{L+} − a^{−1}P_{L−} = zP_{L0} for every skein triple. In
particular P_L is invariant under the Reidemeister moves. One consequence is consumed: P_K ∈
ℤ[a^{±1}, z²] for a knot K, so the z^0 coefficient of a product of knot polynomials is the product
of their z^0 coefficients."
(2) A theorem to derive (OPEN_WORK): existence/invariance/skein/unknot from `SM.lit_homfly`
(`homfly`); knot parity from lp:core (`InSupportM 1 (homfly D)` for `componentCount D = 1`,
sm-3:1052 "knot evaluations are polynomials in z²"); uniqueness among LinkEquiv-invariant maps
with skein and unknot value from lp:lm-uniqueness (over T) transported to R by
lp:coefficient-transport (row 60; the source struck R-uniqueness from lit:homfly, so this clause
must be *proved* through the transport — Gap G9: the competitor Q : Diagram → R must be carried to
a T-valued competitor; the printed lp:coefficient-transport (sm-3:981) does exactly this with
the ring isos φ, ψ over ℤ[i]; check its statement covers an arbitrary R-valued competitor).
The "z^0 of a product of knot polynomials" clause: from `InSupportM` closure (`InSupportM 1 f →
InSupportM 1 g → coeffAt d 0 (f*g) = Σ_{p} coeffAt p 0 f * coeffAt (d−p) 0 g`) — an
`AddMonoidAlgebra` coefficient-of-product lemma restricted to the z-degree-0 rows.
(3) `theorem CV.ax_homfly : (∀ D D′, LinkEquiv D D′ → homfly D = homfly D′) ∧ (∀ D, D.IsCrossingFreeCircle
→ homfly D = 1) ∧ (∀ D₊ D₋ D₀, IsSkeinTriple D₊ D₋ D₀ → R.a * homfly D₊ − R.aInv * homfly D₋ = R.z * homfly D₀)
∧ (∀ D, D.componentCount = 1 → InSupportM 1 (homfly D)) ∧ (∀ f g : R, InSupportM 1 f → InSupportM 1 g
→ zRow 0 (f * g) = zRow 0 f * zRow 0 g) ∧ (∀ Q : Diagram → R, (∀ D D′, LinkEquiv D D′ → Q D = Q D′)
→ (∀ D, IsCrossingFreeCircle D → Q D = 1) → (skein for Q) → Q = homfly)`.
(4) SM rows lit:homfly (axiom), lp:lm (axiom), lp:lm-uniqueness (axiom), lp:coefficient-transport
(60), lp:core (61). Phase-2 predicates.

### 161 CV:ax:etnyre — d10_axioms.tex:387–397 — BLOCKED (↔ `SM.src_contact` + def:transverse-front, row 92)
(1) "Let T be a front diagram of a transverse knot with no downward vertical tangency. Then
sl(T) equals the writhe of T."
(2) = the last clause of the literature interface src:contact (AXIOM_REGISTRY: "For a generic
positive transverse front (Definition def:transverse-front), self-linking equals its front
writhe"). CV:ax:etnyre is a re-export of that clause of `SM.src_contact` once def:transverse-front
(sm-3:3328) is defined (a smooth front with no downward vertical tangency and its transverse
lift — the lift construction is printed inside CV thm:carrierfloor(C), d3:930–987). The
interface must *declare* `sl` together with its properties (∃-form, as for `homfly`).
(3) `theorem CV.ax_etnyre : ∀ T, TransverseFront T → sl T = frontWrithe T` — exact form follows the
SM row's declaration (not this lane's decision).
(4) `SM.src_contact`, def:transverse-front, a smooth-front model (G5/G6).

### 162 CV:ax:slbound — d10_axioms.tex:399–425 — BLOCKED (↔ SM fd:contact, row 94)
(1) "Let T be a transverse knot in the standard contact ℝ³ and P_T its HOMFLY–PT polynomial (in
the normalization of ax:homfly). Then sl(T) ≤ −max deg_a P_T(a,z) − 1."
(2) = SM fd:contact (sm-3:3404, "the HOMFLY–PT bound on the self-linking number"), a theorem of
the SM chain ng:front-domain … ng:local-front-bound (73–83), fd:transverse-neighborhood …
fd:ng-bound (84–93), consuming `SM.ng_finite_word` and `SM.src_contact`. Re-export.
(3) `theorem CV.ax_slbound := SM.fd_contact` in CV notation (`degAZ`/`maxdegA` from LinkLaurentRing).
(4) SM rows 73–94. Longest pole of the project; not this lane's work.

### 163 CV:ax:gausscode — d10_axioms.tex:525–563 — REPLACEMENT ROW (F4); BLOCKED (rp:record-polynomial 63, lp:core 61)
(1) "Let D and D′ be oriented link diagrams, each of whose underlying plane curves is a connected
generic immersed circle in the sphere, and suppose there is an orientation-preserving record
isomorphism from the record of D to the record of D′. Then D and D′ present the same oriented
link."
(2) Not to be assumed or proved as link equivalence (OPEN_WORK.md, design decision 11). Every
in-scope consumer concludes polynomial equality only (F4 lists them with line numbers). The
replacement: `RecordIso (D.record) (D′.record) → homfly D = homfly D′` for `componentCount = 1`,
which is SM rp:record-polynomial (`F_D = F_{D′}`; sm-3:1215; stated for any component count with
the component bijection) composed with lp:core's identification `P_D = H_D` (sm-3:1041) and the
ring transport. The checker requires the shipped row id `CV:ax:gausscode`; the replacement
requires a reviewed scope/checker change: record in AUTHOR_NOTES (a) the printed statement, (b)
the replacement statement, (c) the list of consumers and the sentence of each that reads only
the polynomial (F4), (d) the review verdict; keep the row id and point it at
`CV.gausscode_polynomial`.
(3) `theorem CV.gausscode_polynomial (D D′ : Diagram) (hD : D.componentCount = 1) (hD′ : D′.componentCount = 1)
  (i : RecordIso D.record D′.record) : homfly D = homfly D′`.
(4) `Diagram.record` (phase 2), rows 63, 61.

### 164 CV:selector_A — d6_vertexedge.tex:1017–1020 (clause (A) of lem:selectorid) — START NOW under F2(B)
(1) "(A) Under the guards of Definition def:generic(A), every carrier of every support has at
least three corners." (Only clause (A) is commissioned: PROOF_PLAN step 5, DEPENDENCIES
`partial_clauses`.)
(2) ↔ accepted `Carrier.ccpCornerCount_ge_three` (CarrierCornerPolygon.lean:691) =
`carriers_lemma.corner_polygons.2.2.1`, on the `SM.Generic` binder. The printed proof (two
corners ⇒ overlapping segments ⇒ a G2 vanishes; one/zero corners ⇒ zero-length segment) is the
SM proof's content.
(3) `theorem CV.selector_A (hn) (P) (hP : SM.Generic P) (S) (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
  3 ≤ ccpCornerCount hn hP S q := ccpCornerCount_ge_three hn hP hS q` (check the exact argument
list). Under F2(A) the binder becomes `CV.Generic`.
(4) F2 decision only. ~10 lines. Consumed by R:generic_selector, R:extreme_transport,
R:extreme_selected ("a zero selector means mixed turns, and no one- or two-corner convention is
needed", d6:1052).

### 165 CV:singleton_D_i — d6_vertexedge.tex:2682–2687 (thm:s7universal (D)(i)) — BLOCKED (↔ SM cb:singleton, row 103)
(1) "(i) Let S ∈ Ind(G_P), A a uniform carrier of S, and {c} a singleton residual piece of S
carried by A. Then min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2, so the factor Ω_1(S,A) of def:X1 is
zero." Here f_A = [z^0] P_{S,A} (def:markeddata, d6:1157–1166: f_i(a) = [z^0]Q_i(a,z)).
(2) ↔ SM cb:singleton (sm-3:4697: "Let A be a uniform carrier of S and suppose one of its
self-crossing labels c interlaces no other self-crossing of A. Then c(A) = 0"), an explicit DAG
dependency of this row. CV's conclusion is stronger by the degree gap "+2" — required by
PROOF_PLAN ("requires only the stated degree gap and zero conclusion"). The printed CV proof
(d6:2890–2947): S′ = S ∪ {c} independent; pieces of S′ = pieces of S minus {c} (same label sets);
smoothing c splits A into Λ₁, Λ₂ carrying the pieces (lem:carriers(iv) at S′); P_{S,A} =
P_{S′,Λ₁}P_{S′,Λ₂}·1, w_{S,A} = w_{S′,Λ₁} + w_{S′,Λ₂} + 1 (a one-crossing curve is an unknot with
P = 1, writhe 1 — SM lc:single-crossing, row 65); knot parity ⇒ f_A = f_{Λ₁}f_{Λ₂}; rot(A) =
rot(Λ₁) + rot(Λ₂) with one loop uniform and one one-dissent (turnlift(ii), the two smoothing
corners have opposite turns `crossingSign`), uniformrot ⇒ same signs ⇒ R(A) = R(Λ₁) + R(Λ₂);
carrierfloor(C) on each loop (through groupedknot(B) or carrierfloor(D)) ⇒ min deg f_{Λ_i} ≥ 1 −
w_i − R_i; add. SM cb:singleton's proof is the same chain with cb:products/thm:floor.
(3) `theorem CV.singleton_D_i (hn) (P) (hP) (S) (hS) (q) (hq : CarrierUniform hn hP S q) (c : Crossing P)
  (hc : {c} is a piece on q: c ∈ supportUnselected hn hP S ∧ pieceOwner ⟨c⟩ = q ∧ ∀ c′ ∈ supportUnselected hn hP S,
        c′ ≠ c → ¬ Interlaces hn hP c c′) :
  (zRow 0 (groupedPoly hn hP S q) ≠ 0 → slot hn hP S q + 2 ≤ mindegAZ (zRow 0 (groupedPoly …))) ∧
  Omega1 hn hP S q = 0`.
Route (once the inputs exist): `IsDecomposition (insert c S)`; `carriers_lemma` at S ∪ {c}
(`count` gives the split into two components; `CarrierUnchangedComponent`/`CarrierInheritedInsert`
identify the other carriers); pieces transfer (139, 136(iv) at S′); rotation additivity via
`rotation_number` first clause + the two smoothing-corner turns (`corner_polygons` last clause)
+ `principalAngle` of opposite determinants; 153; 155(C)/(D); knot parity (160).
(4) 146, 153, 155(C), 157(ii)-style parity (160), 158(B), SM lc:single-crossing (65), thm:floor
(100) for the SM route. Consumed by R:extreme_pair_zero.

## 5. The R rows (166–178): what each supplied argument asserts, what it consumes, what is missing

Source of the specifications: OPEN_WORK.md items 1–4, R_ASSEMBLY_SPEC.md (fibre sums (1)–(4)),
reference/R/RA/R_ATTACHMENT_WARRANTS.md (R-LOC-2, R-PAR-v6, R-EXTERIOR-1) and the seven RA proof
files. The R rows have no printed statement; their Lean statements are set by the executor from
these texts (record each in AUTHOR_NOTES with the quotation it renders). Every R row is stated
for a simple transversal RIII event `E : CV.Event n` with `E.IsSimpleRIII e f g …` (Appendix A;
under F2(B) add `hSM : ∀ t ≠ 0, SM.Generic (E.curve t)`), with T = the three crossings
{e,f}, {e,g}, {f,g} (as `Crossing (E.curve t)` — identified across t by their edge pairs
`Finset (ZMod n)`, which is what "indexed by carrying edge pairs" means and what the accepted
`IsCrossing P s` on `Finset (ZMod n)` gives for free).

Standing notation for the statements: `P₊ := E.curve t₊`, `P₋ := E.curve t₋` for small
t₊ > 0 > t₋; the two sides share the crossing *supports* `s : Finset (ZMod n)` (R-LOC-2 (1)), so
supports S ⊆ crossings are compared as `Finset (Finset (ZMod n))` via `crossingSet`
(Crossings.lean:17) — `SM.Chambers.crossing_iff_of_chi_eq`, `TripleVisitExchanges.triple_sides_crossing_equiv`
(the accepted triple-wall lane already builds this identification for SM germs).

### 166 R:localization (R-LOC-2) — `RProof.localization`
Asserts (R_ATTACHMENT_WARRANTS.md:16–29): on a punctured neighbourhood of t = 0, (1) the crossing
set indexed by carrying edge pairs is constant; (2) on each of e, f, g the two crossings of T
carried by that edge occupy *adjacent* crossing-visits of the traversal circle and their order
along that edge is opposite on the two sides; (3) every other pair of crossings keeps its order
along every edge; (4) hence G⁺ = G⁻ △ binom(T,2): exactly the three internal pairs of T toggle
their interlacement. Corollary: G[T] maps to its complement (extreme orbit K₃ ↔ ∅, generic orbit
P₃ ↔ one edge + isolated vertex).
Consumes: CV:def:event, def:guarded (the factorization G4 = (t_f − t_g)·G5·G5), lem:guardconst,
the "no birth/death" argument of lem:silence's proof (a crossing appears only through a G2
vanishing with the vertex on the segment; no G2 is in the forced bundle).
Library: **largely present for SM triple germs** — the accepted thm:A-R3E lane:
`SM.TripleParameters` (`uniqueTriple_outside_persists`: every third crossing parameter stays
strictly outside the two selected ones on the common edge), `SM.TripleAdjacency`
(`pairVisits_adjacent`: the two triangle visits are consecutive in the Gauss list), `SM.TripleOrder`
(`uniqueTriple_other_orders_persist`, `uniqueTriple_parameter_tie_iff`: only the three triangle
comparisons can tie), `SM.TripleExchanges` (`triple_order_exchanges_local`: the three sign
changes give the three reversals), `SM.TripleSideExchanges` (`triple_order_exchanges`,
`triple_other_orders_sides`: fixed on both connected sides), `SM.TripleVisitExchanges`
(`triple_exact_visit_orders`: "exactly the triangle pairs reverse, every other pair retains its
order"), `SM.GaussAdjacencyTransport` (`generic_family_gaussVisitsAdjacent`), `SM.InterlaceCount`
(interlacement as a count of visits on an arc). Clause (4) (the graph toggles) is not stated
there as such; derive it from (2)–(3) via `interlaces_iff_count`.
Proposed: `theorem RProof.localization (E : CV.Event n) (hE : E.IsSimpleRIII e f g …) [+ hSM] :
∃ δ > 0, ∀ t t′ (ht : 0 < |t| < δ) (ht′ …), (∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t′) s) ∧
(same-sign t t′ → same visit order for every pair of crossings on every edge) ∧
(opposite signs → the order of {e,f},{e,g} on e reverses, likewise on f and g, all other orders equal
∧ VisitsAdjacent (the two T-visits on each of e,f,g)) ∧
(opposite signs → ∀ x y, Interlaces x y ↔ (Interlaces x′ y′ xor ({x,y} ⊆ T ∧ x ≠ y)))`.
Route under F2(B): transport the SM triple lane through B1/B2 (an SM `TripleAt` germ is the
event); under (A) redo the six lemmas on `CrossingGeometry` (the modules mostly already use
`edgeParameter`, not `Generic`). Difficulty: medium (port + assembly, ~500 lines). START NOW for
SM germs (via `WallGerm.TripleAt`), independently of X₁.

### 167 R:parity (R-PAR-v6) — `RProof.parity`
Asserts (WARRANTS:107–121): (P1) every crossing y ∉ T interlaces exactly 0 or exactly 2 of the
three crossings of T, and when 2, the pair is the two crossings sharing one bundle edge; (P2) for
any set S′ of crossings disjoint from T, avail(S′) = {x ∈ T : x interlaces no member of S′} has
size 3, 1 or 0, and is the same on both sides.
Consumes: R:localization (2) (the three "clumps" of adjacent visits), CV:def:interlace.
Proof is the 2-colouring of the three clumps by the two arcs cut by y's visits (WARRANTS:125–
147): pure cyclic-order combinatorics on `gaussList`/`traversalBetween`; (P2) is a union of
pairs argument (`Finset.card` case analysis on ≤ 3 elements — `decide` after abstracting to
`Fin 3`).
Proposed: `theorem RProof.parity … : (∀ t (ht), ∀ y : Crossing (E.curve t), y.val ∉ T →
  ((univ.filter fun x : T => Interlaces y x).card = 0 ∨ (… = 2 ∧ ∃ edge h ∈ {e,f,g}, the two
  interlaced elements are the two crossings on h))) ∧ (∀ S′ disjoint from T, (avail S′).card ∈ {0,1,3})
  ∧ (avail is the same Finset (Finset (ZMod n)) on both sides)`.
Difficulty: medium (~300 lines) once 166 is available. Can be developed NOW as an abstract lemma
on a cyclic word with three adjacent pairs (a `List`/`Cycle` lemma), then instantiated.

### 168 R:exterior (R-EXTERIOR-1) — `RProof.exterior`
Asserts (WARRANTS:154–184): fix an outside independent Q disjoint from T; for A ⊆ T with Q ∪ A
independent, a carrier of Q ∪ A is *triangle-disjoint* if it contains none of the six T-visits
(selected smoothing-site visits included). C_{Q,σ}(A) := ∏_{triangle-disjoint L} wt_σ(L)·
Ω_{1,σ}(Q ∪ A, L) is independent of A and equal on both sides (value C_Q, possibly 0); hence every
full-availability row factors τ_σ(A) = C_Q · ρ_σ(A) with ρ the product over triangle-touching
carriers.
Consumes: cor:groupedknot (piece polynomials of exterior carriers), lem:carrierword, R:parity,
def:wind, def:X1, lem:turnlift(ii) (rotation of an exterior carrier equal on both sides), the F4
replacement (equal restricted records ⇒ equal polynomials), lem:guardconst (corner signs).
Library: carrier stability under adding selected crossings elsewhere —
`SM.CarrierUnchangedComponent` (`smoothingSuccessor_insert_eqOn_owner`,
`smoothingSuccessor_insert_bijOn_owner`: a component avoiding the inserted crossing's visits is
unchanged), `SM.CarrierAmbientTransport` (`splitList_ambient_*`: cycles under a swap of two
marks), `SM.CarrierInheritedInsert`. Cross-wall identification of a carrier's corner polygon
(§4 of the warrant: erase the six T-visits, same marked word both sides) needs a transport of
`ccpCornerPolygon` along the event and `rotation_number` clause 3 (path constancy in `Regular`)
— Gap G8.
Proposed: `theorem RProof.exterior … (Q) (hQ : IsDecomposition Q ∧ Disjoint Q T) :
∃ C_Q : ℤ, ∀ σ ∈ {+,−}, ∀ A ⊆ T, IsDecomposition (Q ∪ A) →
  (∏ L ∈ triangleDisjoint (Q ∪ A), weight L * Omega1 (Q ∪ A) L) = C_Q ∧
  wind (Q ∪ A) * ∏ L, Omega1 (Q ∪ A) L = C_Q * ∏ L ∈ triangleTouching (Q ∪ A), weight L * Omega1 (Q ∪ A) L`.
Difficulty: hard (~1000+ lines); BLOCKED by 146 and G8.

### 169 R:fibre_partition — `RProof.fibre_partition`
Asserts (R_ASSEMBLY_SPEC.md (1)–(3)): with W the complement of T, every independent S decomposes
uniquely as Q = S ∩ W (independent in G[W]) and J = S ∩ T (independent in G[T] and ⊆ 𝓐(Q) =
{t ∈ T : no element of Q adjacent to t}), and conversely; hence
X₁(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q), Φ_±(Q) = Σ_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J), with F_±(S) the
complete summand wind(S)∏_L Ω₁(S,L).
Consumes: CV:def:X1 (the sum), R:parity (𝓐(Q) equal on both sides).
Proposed: state first as an ABSTRACT graph lemma (START NOW): `theorem RProof.indep_partition
{V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (F : Finset V → ℤ) :
∑ S ∈ univ.filter G.IsIndepSet, F S = ∑ Q ∈ (univ.filter fun Q => Q ⊆ Tᶜ ∧ G.IsIndepSet Q),
  ∑ J ∈ (univ.filter fun J => J ⊆ avail G T Q ∧ G.IsIndepSet J), F (Q ∪ J)` with
`avail G T Q := T.filter fun t => ∀ q ∈ Q, ¬ G.Adj q t` — proof by `Finset.sum_bij`/`sum_sigma`
on `S ↦ (S ∩ Tᶜ, S ∩ T)`. Then `RProof.fibre_partition` instantiates it with
`G := interlacementGraph`, `T := the triangle`, `F := fun S => wind S * ∏ Omega1 S` for each side
and uses 167 (P2) for the equality of 𝓐(Q) across the wall. Difficulty: easy (abstract, ~150
lines) + instantiation blocked by 146.

### 170 R:availability_0_1 — `RProof.availability_zero_one` (the "missing full-domain assembly", part 1)
Asserts (R_ASSEMBLY_SPEC.md after (4); OPEN_WORK item 2): for Q with |𝓐(Q)| = 0 the fibre is the
single support Q on both sides; for |𝓐(Q)| = 1 = {x} it is {Q, Q ∪ {x}} on both sides; in each
case Φ₊(Q) = Φ₋(Q). "At availability zero or one the local supports themselves correspond, but
that does not prove their summands agree. Prove the required carrier/record, selector, rotation
and coefficient transport." No RA file covers it (the four core proofs assume full availability).
Consumes: R:fibre_partition, R:exterior (transport of the triangle-disjoint carriers), and the
transport of the triangle-*touching* carriers when the T-visits are all unselected (|𝓐| = 0: all
three crossings dominated by Q — their six visits are auxiliary marks on carriers; the three
adjacent-visit transpositions of R-LOC-2 do not change the mark *sets* of the carriers
(`owner` is defined from `smoothingSuccessor`, which only reads selected visits — check:
`smoothingSuccessor = selectedMarkPerm S ∘ markSuccessor`, and `markSuccessor` changes by the
three transpositions), so the carriers' corner polygons are the same corner lists → equal wt, R;
the grouped diagrams differ by the RIII rearrangement of three dominated crossings → polynomial
equality via the F4 replacement is NOT available (records differ); needs an actual RIII move
between the two positive lifts (`RIII` predicate, phase 2) or the observation that dominated
crossings are mixed crossings of no piece … in fact a dominated crossing lies in no residual
piece, so P_{S,L} = ∏_H P_H ignores it: its two visits sit on different carriers and the piece
curves erase it — so the piece records are identical on the two sides at |𝓐| = 0, and the
transport is record-level; at |𝓐| = 1 the smoothed x contributes two corners whose signs are
`crossingSign`, constant across the wall by guardconst on the active G5; the other two crossings
are dominated → same argument). Gap G7.
Proposed: `theorem RProof.availability_zero_one … (Q) (hQ) (h01 : (avail Q).card ≤ 1) : Φ₊ Q = Φ₋ Q`.
Difficulty: hard-medium once 168's transport toolkit exists (~500 lines). BLOCKED by 146, 168.

### 171 R:generic_table — `RProof.generic_table`
Asserts (R_GENERIC_ORBIT_ACTUAL_TABLE.md): at full availability in the generic orbit, with the
three unchanged exterior gaps A, B, C between the RIII strand blocks, the local words are
P = a b A a c B b c C (edges ab, bc; centre b) and E = b a A c a B c b C (edge ac; b isolated);
the successor cycles for each local support (∅, a, b, c, ac on P; ∅, a, b, c, ab, bc on E) are as
tabulated (e.g. P-b : (126)[C](345)[AB]; E-b : (1)[C](23456)[AB]; P-ac : (14)[C](23)[A](56)[B]);
the local undominated sets (P: ∅→abc, a→c, b→∅, c→a, ac→∅; E: ∅→abc, a→b, b→ac (connected), c→b,
ab→∅, bc→∅); the sign-branch classification: six nonalternating strand-determinant triples are
generic, the two alternating ones extreme (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (1)–(3):
(q_e,q_f,q_g) = −δ(s_a s_b, s_a s_c, s_b s_c) and edge(a,b) present iff q_e = −1, edge(a,c) iff
q_f = +1, edge(b,c) iff q_g = −1).
Consumes: R:localization, R:parity, lem:carrierword.
Library: `smoothingSuccessor`, `Component`, `owner`, `componentCycle` — the table is a finite
computation on the six local marks plus three opaque gap strings; formalize as a lemma about
`smoothingSuccessor` restricted to the six T-visits ("local skeleton") — the exterior gaps are
handled by 168's fiber-stability. The sign-branch classification is the determinant algebra of
(1) in the NONSELECTED file: `t_ef − t_eg = −Δ/(D_ef D_eg)` etc. (Cramer; `edgeParameter`,
`cramerFirst`), pure `field_simp; ring`.
Proposed: two theorems: `RProof.generic_table_words` (the successor-cycle table on the six local
marks, both sides, both orbits — `decide`-able on `Fin 6` after abstracting) and
`RProof.generic_table_signs` (the (q) = −δ(…) identity and the orbit classification).
Difficulty: medium (~400 lines). The sign part can START NOW (it is polygon algebra on the CV
guards); the words part needs 166 and the Carrier lane (F2).

### 172 R:generic_selector — `RProof.generic_selector`
Asserts (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md): in the generic orbit, each of the two
*nonselected* local pair supports (those whose shared strand u is not separating: sgn det(u,v) =
sgn det(u,w)) has winding selector 0 on the side where it is present, for arbitrary exterior gaps
and outside Q: one carrier contains the intact u-arc between the two adjacent T-visits and both
of its smoothing corners, whose determinants det(v,u) = −det(u,v) and det(u,w) have opposite
signs (5)–(6), so that carrier is mixed and wind = 0 by def:wind. Which pair is selected: table
(4) (selected pair ↔ separating strand ↔ the degree-two vertex's complement).
Consumes: R:generic_table, CV:def:wind, CV:selector_A (a zero selector means mixed turns; no
1-/2-corner convention).
Library: `carriers_lemma.corner_polygons` (smoothing-corner turns = `crossingSign`),
`ccp_selected_crossing_two_corners`, `CarrierUniform`, `Finset.prod_eq_zero`. The "intact arc
carries both corners" step is R-LOC-2's adjacency (166) + `smoothingSuccessor` on the two
adjacent selected visits.
Proposed: `theorem RProof.generic_selector … (hgen : generic orbit) (J : the nonselected pair) (Q) :
CV.wind hn hP (Q ∪ J) = 0`. Difficulty: medium (~300 lines). BLOCKED by 138, 166, 171.

### 173 R:generic_transport — `RProof.generic_transport`
Asserts (R_GENERIC_COMMON_TRANSPORT_PROOF.md (2)): T_P(∅) = T_E(∅), T_P(a) = T_E(a), T_P(c) =
T_E(c) — the complete X₁ terms of Q ∪ ∅, Q ∪ {a}, Q ∪ {c} agree across the wall (in the canonical
sign branch (1) sgn det(u1,u2) = sgn det(u1,u3) = sgn det(u2,u3) = σ). Empty row: the
distinguished carrier bears the three undominated local crossings on both sides; grouped
polynomials agree by an actual oriented RIII move on the grouped diagrams (transitive over-order
by (1)) + record isomorphism + F4; weights and rotations agree along the guarded path. Endpoint
rows a, c: relabelling c ↦ b (resp. a ↦ b) is an isomorphism of undominated graphs preserving the
signed records (divide designation preserved by (4): sgn det(u2,u3) = sgn det(u1,u3) = σ), and the
E-only rows bc (resp. ab) are killed by 172.
Consumes: R:generic_table, R:exterior, cor:groupedknot, lem:turnlift(ii), the F4 replacement,
CV:ax:homfly's RIII invariance, and for the empty row an *actual RIII move* between two polygonal
positive lifts (Gap G11: exhibit `RIII D_P D′` for the concrete grouped diagrams — the phase-2
`RIII` predicate on `AgreeOutside` a disc, plus a clearance argument for the event disc).
Proposed: `theorem RProof.generic_transport … (Q) (hfull : avail Q = T) (hgen) : F₊ Q = F₋ Q ∧
F₊ (Q ∪ {a}) = F₋ (Q ∪ {a}) ∧ F₊ (Q ∪ {c}) = F₋ (Q ∪ {c})` (with `F_σ S := wind S * ∏ Omega1 S`, absent
supports read 0). Difficulty: hard (~800 lines + G11). BLOCKED.

### 174 R:generic_selected — `RProof.generic_selected`
Asserts (R_GENERIC_SELECTED_COUPLE_PROOF.md (GSC)): T_E(b) = T_P(b) + T_P(ac). Ledger (4)–(8):
wt(C_ac) = −σ wt(C_b), wt(A)wt(B) = σ wt(AB), wind_P(Q∪ac) = −wind_P(Q∪b), wind_E(Q∪b) =
wind_P(Q∪b), rot(C_ac) = rot(C_b), rot(A)+rot(B) = rot(AB), R(A)+R(B) = R(AB) when the selector is
live (uniformrot(i)); the full-twist triple (D_L, D_H, D_0) = (P-b AB carrier, E-b AB carrier,
smoothing of a) satisfies (T1),(T2) of lem:fulltwist with w_H = w_L + 2, d_H = d_L − 2 (9);
the two components of D_0 have polynomials Q_A, Q_B (record-level) with D = d_L + 2ℓ (10)–(11);
then by lem:fulltwist, lem:homflyrows(ii) and knot parity, Ω_H − Ω_L = [a^{D−2}]f_A f_B −
[a^{D}]f_A f_B (12), and the carrier floor kills the second term / identifies the first with the
pair row (the file continues past the excerpt read; the prover must read §4–5 in full).
Consumes: R:generic_table, R:generic_selector, R:exterior, CV:thm:carrierfloor(C)(D),
CV:lem:fulltwist, CV:lem:homflyrows(ii), knot parity (160), CV:lem:turnlift(ii),
CV:lem:uniformrot, cor:groupedknot, F4. Also an actual RII move ("switching a makes a,c an
empty oppositely signed RII pair; deleting that pair gives D_L") — Gap G10.
Difficulty: very hard (~1200 lines). BLOCKED.

### 175 R:extreme_pair_zero — `RProof.extreme_pair_zero`
Asserts (R_EXTREME_PAIR_ZERO_PROOF.md): in the extreme orbit at full availability, each local pair
support J = {x,y} is absent on the K₃ side and present on the empty side, and its complete X₁
term there is 0: S = Q ∪ J is independent; z is undominated and {z} is a singleton residual
piece (R-PAR (P1) quantified over every outside crossing: a neighbour of z is adjacent to x or y,
hence dominated); if wind(S) = 0 done, else every carrier is uniform and thm:s7universal(D)(i)
(= CV:singleton_D_i) gives Ω₁(S,A) = 0 for the carrier A owning {z}.
Consumes: R:parity, CV:singleton_D_i (165), CV:def:pieces, def:X1.
Proposed: `theorem RProof.extreme_pair_zero … (hext : extreme orbit) (Q) (hfull) (J : local pair) :
F_L (Q ∪ J) = 0`. Difficulty: easy once 165 and 167 exist (~150 lines). BLOCKED by 165.

### 176 R:extreme_transport — `RProof.extreme_transport`
Asserts (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md (2)): T_H(x) = T_L(x), T_H(y) = T_L(y), T_H(z) =
T_L(z) for the three singleton rows, with the canonical words H = x y A z x B y z C (K₃), L = y x A
x z B z y C (empty), sign ledger (3) s_x = σ, s_y = −σ, s_z = σ, the rowwise table (5) of common
and affected carriers, the full-twist triple (D_0, D_+, smooth_q D_+) with w_+ = w_0 + 2, R(D_+) =
R(D_0) (7), the component table (9)–(10) and the coefficient extraction (the file continues past
the excerpt read: §3).
Consumes: R:exterior, CV:lem:fulltwist, CV:selector_A, CV:thm:carrierfloor, lem:homflyrows(ii),
knot parity, uniformrot, F4, an actual RII move (G10).
Difficulty: very hard (~1000 lines). BLOCKED.

### 177 R:extreme_selected — `RProof.extreme_selected`
Asserts (R_EXTREME_SELECTED_COUPLE_PROOF.md (2)): T_H(∅) − T_L(∅) = T_L(xyz). Route: over-orders
(1b), the outer/central corner signs (1c) s_o = −σ; the grouped contact diagrams D_H, D_L with
common w, R, W (§1); two matched switches and two subtracted skeins (§2, (4)–(7): switch x on both
sides → RIII-related transitive diagrams with isomorphic full records → equal polynomials; smooth
x; switch y → an empty RII bigon on each side → two-component diagrams E_H, E_L related by an
ambient isotopy through the wall → (6); hence F_H − F_L = a^{−2}z²(P(D_H^{xy}) − P(D_L^{xy})) (7));
D_H^{xy} is a knot ([z^{−2}] = 0 by parity (8)), D_L^{xy} has three components with skeletons A,
C, z B z (9) whose lowest z-row is read off (§3, continues past the excerpt).
Consumes: R:exterior, CV:lem:homflyrows (multi-component lowest row), CV:selector_A,
CV:thm:carrierfloor, knot parity, uniformrot, F4, actual RIII and RII moves and an "ambient
isotopy through the wall" of the two-component diagrams (a `Deform`/`PlanarIsotopic` witness
crossing the RIII wall after the local pair is deleted — G10/G11).
Difficulty: very hard (~1200 lines). BLOCKED.

### 178 R:cv_theorem — `RProof.cv_R` (proves `CV.hyp_R`)
Asserts (R_ASSEMBLY_SPEC.md (3)–(4), OPEN_WORK item 4): sum the proved fibre identities Φ₊(Q) =
Φ₋(Q) over all Q ∈ Ind(G[W]) (169) — availability 0/1 by 170; availability 3 in the generic orbit
by 172 (the two nonselected pair rows are 0 on the side where present), 173 (∅, a, c rows), 174
(b/ac couple); in the extreme orbit by 175 (pair rows 0), 176 (three singleton rows), 177 (∅/xyz
couple) — with the exterior factor C_Q carried, never divided; then X₁(P₊) = X₁(P₋).
"Review that all source event-domain clauses survived the localization and assembly."
Proposed: `theorem RProof.cv_R : CV.hyp_R` where `CV.hyp_R : Prop := ∀ (n) [NeZero n] (hn : 3 ≤ n)
(E : CV.Event n) (e f g) (h…) , E.IsSimpleRIII e f g … → [hSM →] ∀ t₊ t₋ small, X1 (E.curve t₊) =
X1 (E.curve t₋)` (the printed ax:R, d10:18–24, with the domain per F2). The orbit dichotomy
(generic vs extreme) is 171's sign classification; "both complement graph orbits" = R-LOC-2's
corollary. Difficulty: assembly only (~200 lines) once 169–177 exist.

## 6. Bridge:B1–B4 and the bridge theorem (179–183)

Source: reference/BRIDGE/BRIDGE.md §2 (B1 at 159–446, B2 at 448–491, B3 at 493–635, B4 at
637–1441) and §3 (1443–1474); quotations are SM11 text re-aligned to SM15 in
provenance/BRIDGE_REALIGNMENT_SM15.json (46 exact, 11 relocated, 2 superseded — check the two
superseded spans before quoting them in a review). Coordinates: p_i = μ_i, d_i = edge P i, CV's
e_i = SM's E_i, one-based tails on both sides (BRIDGE.md §0, SM_MAP).

### 179 Bridge:B1 — `Bridge.B1` — START NOW after 132, 148
Asserts (BRIDGE.md:161–169): (1) 𝓤_n^SM ⊆ 𝓤_n^CV (labelled loci); (2) every SM wall germ with the
central conditions of type T (`WallGerm.TripleAt e f k`: pointZeros = ∅, concurrences = {{e,f,k}},
three parameter-difference sign changes) is a CV event — generic (CV) at every t ≠ 0 and
CV-nongeneric at t = 0 (the active G3 of the concurrent triple vanishes). Restricted to type T;
nothing is asserted about other SM wall types.
Consumes: CV:def:polygon, def:generic (the SM→CV theorem of row 132), def:event; SM def:polygon,
def:germ, def:walls (accepted).
Proposed: `theorem Bridge.B1 (hn : 3 ≤ n) : (∀ P : LabelledTuple n, SM.Generic P → CV.Generic P) ∧
  (∀ (g : WallGerm n) (e f k), g.TripleAt e f k → ∃ E : CV.Event n, E.radius = g.radius ∧
     (∀ t, E.curve t = g.curve t) ∧ ¬ CV.Generic g.center)` and the constructor
`Bridge.eventOfTriple (g) (h : g.TripleAt e f k) : CV.Event n := ⟨g.radius, g.radius_pos, g.curve,
g.continuous_curve, fun t ht => (B1.1 _ (g.generic_punctured t ht)), (center nongeneric)⟩`.
Route for the centre: `mem_concurrences_triple` gives a common interior point x of the three
edge interiors; `pointZeros = ∅` gives `G1 g.center` (`pointZeros_empty_iff`), hence pairwise
non-parallel directions at the concurrent triple (BRIDGE.md B1 text: parallel would force three
collinear vertices); each pair meets at an interior transverse point ⇒ the strict four-sign test
holds ⇒ the three pairs `Crosses` ⇒ `Member.g3 e f g` is active; its `det3` of the three
coefficient rows vanishes because the three lines contain x (concurrency ↔ `det3 = 0` — the
LineConcurrence lemmas) ⇒ not CV-generic. Difficulty: medium (~400 lines with row 132's SM→CV
theorem counted there).

### 180 Bridge:B2 — `Bridge.B2` — START NOW after 179
Asserts (BRIDGE.md:450–491): for the event of B1 with e < f < g as representatives, its CV zero
set is exactly Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}} (four indexed members). Proof:
the relevance quantifier ("relevant at some t ≠ 0" ⇔ active at the centre, because all
unconditional members are nonzero on the whole germ interval and continuous, so every crossing
activation is constant on the interval); forced bundle ⊆ Z (the three central crossings persist
on both sides — `lem:triple-sides` / `SM.triple_sides`; G3 vanishes at the concurrency; each G4
vanishes as a parameter tie); Z ⊆ forced bundle by exhausting the five families (G1, G2 nonzero
at the centre; active G5 nonzero; an active vanishing G3 is a concurrency of a pairwise-crossing
triple hence in Z_c = {{e,f,g}}; an active vanishing G4_{a;b,c} is a tie hence a point interior
to a, b, c, so {a,b,c} = {e,f,g} and b, c cannot be adjacent under central G1).
Consumes: 179, CV:def:guarded (member indexing; the accessor and representative order), SM
`triple_sides`, `TripleOrder.uniqueTriple_parameter_tie_iff`, `crossingParameter_eq_edgeParameter`.
Proposed: `theorem Bridge.B2 (hn) (g : WallGerm n) (e f k) (h : g.TripleAt e f k) :
  let E := Bridge.eventOfTriple g h; let (e′,f′,g′) := sorted representatives of {e,f,k};
  E.zeroSet = {Member.g3 e′ f′ g′ _, Member.g4 e′ f′ g′ _, Member.g4 f′ e′ g′ _, Member.g4 g′ e′ f′ _}`
(the side-condition proofs supplied by `TripleAt`'s pairwise remoteness, from
`mem_concurrences`). Difficulty: medium (~400 lines; the ⊆ direction is a 5-way case split on
`Member`).

### 181 Bridge:B3 — `Bridge.B3` — START NOW after 180 (pure algebra + SM sign changes)
Asserts (BRIDGE.md:495–635): the three SM parameter-difference sign changes of type T, with the
central conditions, imply CV transversality for Z: every member of Z changes sign at 0. Route:
G4_{e;f,g} = (t_f − t_g)·det(d_f,d_e)·det(d_g,d_e) (row 131's display; BRIDGE (4)–(7)), the two
direction determinants are nonzero and of constant sign near 0 (continuity + centre nonzero), and
`SignChanges (edgeParameter · e f − edgeParameter · e g)` is the SM hypothesis; then G3 = −G4_{e;f,g}
(d8a identities of row 131) inherits the sign change; the other two G4's likewise.
Consumes: 180, 131 (identities and factorization), `WallGerm.SignChanges` (GermSignChange.lean),
`crossing_edgeParameter_det_ne_zero`.
Proposed: `theorem Bridge.B3 (hn) (g) (e f k) (h : g.TripleAt e f k) : (Bridge.eventOfTriple g h).Transversal`
— i.e. `∀ m ∈ zeroSet, E.SignChanges m.eval`; with 180 this is four instances. Note the
identification `CV.Event.SignChanges (eventOfTriple g h) φ ↔ g.SignChanges φ` (same formula).
Difficulty: medium (~300 lines; `ring` for the identities, `Filter.Eventually` for constant signs).

### 182 Bridge:B4 — `Bridge.B4` — BLOCKED (def:C row 71, lem:C-X1 row 72, cb:products row 102; 146)
Asserts (BRIDGE.md:639–641, proof 747–1441): on every SM-generic labelled representative the two
state sums are equal, X₁(P) = C(P) (17); on either punctured side of a triple germ this identifies
the SM side value (constant on the SM chamber by prop:C-chamber) with the CV side value (constant
on the containing CV chamber by prop:chamberinv(ii)) (18). Content (F5): same crossings and
Gauss word (accepted def:gauss/def:interlace vs CV's on the same tuple — trivial under F2(B)
since both are `interlacementGraph hn hP`), same supports, carriers, corner counts, turn signs;
wind(S) = (−1)^{ℓ(P)+|S|} for uniform S and 0 otherwise (lem:C-X1's selector identity: each
vertex corner has turn τ_i, each selected crossing contributes one left and one right smoothing
corner — `carriers_lemma.corner_polygons`); Ω₁(S,L) = c(L) because P_{S,L} = ∏_H P_H equals the
HOMFLY of the positive lift (cor:groupedknot(B) = cb:products) and w_{S,L} = m_L, R(L) = |r_L|.
Proposed: `theorem Bridge.B4 (hn) (P) (hP : SM.Generic P) : CV.X1 hn P hP = SM.cornerStateSum hn hP` and
`Bridge.B4_sides (g) (h : g.TripleAt …) : ∀ b, value of C on g.side b = value of X1 on the CV side
chamber` (the latter follows from prop:C-chamber and 147(ii)). Difficulty: medium once 146, 158(B),
def:C exist (~400 lines: the selector identity is a `Finset.prod` over corners split by
`ccpCornerMark` into vertices and selected visits, using `leftTurns` and the two-corner clause).

### 183 Bridge:theorem — `Bridge.sm_R : SM.hyp_R` — assembly
Asserts (BRIDGE.md §3 (19)–(21)): RA's theorem in the CV ax:R form ⟹ for every SM simple triple
wall germ, C(P₊) = C(P₋). Proof: B1 makes the germ a CV event; B2 its zero set the forced bundle;
B3 transversal; so `RProof.cv_R` applies and gives X₁(P₊^CV) = X₁(P₋^CV); B4 replaces both sides by
C on the SM sides. `SM.hyp_R` (sm-4:1149: "At every simple triple wall, C(P₊) = C(P₋)") is the
explicit-parameter hypothesis of the checker (`axiom-policy.json` mode `explicit_parameter`); its
Lean form is fixed when def:C and the wall-law rows are stated: `SM.hyp_R : Prop := ∀ n hn (g :
WallGerm n) e f k, g.TripleAt e f k → C-value on g.side true = C-value on g.side false`.
Difficulty: ~100 lines once 178–182 exist.

## 7. Work lists

### (a) Rows that can START NOW with the accepted SM library only (in this order)
1. CV:def:polygon (129) — `CV.IsPolygon`; alias of `LabelledTuple` + nonzero edges. 40 lines.
2. CV:def:regular (130) — alias of `SM.Regular`/`PrincipalAngleSpec`. 60 lines.
3. CV:def:guarded (131) — Appendix A skeleton + d8a identities + continuity of `Member.eval`. 250 lines.
4. CV:def:generic (132) — `CV.Generic`, labelled chambers, and the theorems `SM.Generic → CV.Generic`
   (= B1(1)), `CV.Generic → WeakGeneric/CrossingGeometry/Regular`. 300 lines.
5. CV:def:diagrammatic (133) — `CV.Diagrammatic`, `CV.Generic → Diagrammatic → CrossingGeometry`. 150 lines.
6. CV:def:interlace (134) — on `geometricInterlacementGraph`; equivalences with the accepted
   `Interlaces`, `independentSupports`, `supportNeighbors`, `supportUnselected`. 120 lines.
7. CV:def:event (148), CV:lem:guardconst (149), CV:def:silent (150) — Appendix A + continuity. 260 lines.
8. Bridge:B1 (179) — needs 4 and 7; the centre nongenericity via LineConcurrence. 400 lines.
9. CV:prop:chamberinv(i) (147(i)) — openness of the CV locus; components open, path connected. 250 lines.
10. Bridge:B2 (180), Bridge:B3 (181) — zero set and transversality of the triple event. 700 lines.
11. CV:def:rot (144) — `rotRay`, `Admissible`, `exists_admissible`; then CV:lem:turnlift(ii) (145)
    — the ray formula 2π·rotRay = Σ principalTurn (Gap G2, 400–600 lines); then CV:lem:uniformrot
    (153) — alias of `uniform_rotation` + `rotation_number`. 80 lines.
12. After recording the F2 decision (B): CV:def:smoothing (135), CV:lem:carriers (136; (iv) new,
    120 lines), CV:lem:carrierword (137; refinement clause 150 lines), CV:def:wind (138),
    CV:def:pieces (139), CV:selector_A (164). ~450 lines total.
13. R-lane cores that need no X₁: R:localization (166) for SM triple germs from the accepted
    `Triple*` modules (~500 lines); R:parity's clump/2-colouring lemma (167, ~300 lines);
    R:fibre_partition's abstract graph lemma (169, ~150 lines); R:generic_table's sign
    classification (171, Cramer identities, ~200 lines).
14. CV:def:record (140) first two clauses (cyclic order ↔ successor, equivalence relation) on
    work/lean/SM/LinkRecord.lean — the layer is ported but unreviewed; do this only after the
    executor confirms LinkRecord.lean is frozen enough to cite. 150 lines.

### (b) Rows blocked by the diagram/record layer (phase 2: `Diagram.record`, `positiveLift`,
move predicates `PlanarIsotopic`/`RI`/`RII`/`RIII`/`IsOrientedSmoothing`/`IsSkeinTriple`/`LinkEquiv`,
and def:C `cornerStateSum`)
CV:def:record (140, last clause), CV:def:homfly (141), CV:def:piecediagram (142), CV:lem:piececurve
(143; also Gap G4), CV:def:X1 (146), CV:prop:chamberinv(ii) (147(ii)), CV:lem:silence (151),
CV:thm:carrierfloor(D) (155(D)), CV:lem:pieceintrinsic (156), CV:cor:groupedknot (158; also SM
cb:products/mp:blocks), CV:lem:fulltwist (159; immediate once RII/skein exist), Bridge:B4 (182),
R:exterior (168), R:fibre_partition instantiation (169), R:availability_0_1 (170), R:generic_table
words (171), R:generic_selector (172), R:generic_transport (173), R:extreme_pair_zero (175),
R:cv_theorem (178), Bridge:theorem (183).

### (c) Rows blocked by the literature interfaces (declarations `SM.lit_homfly`, `SM.lp_lm`,
`SM.lp_lm_uniqueness`, `SM.src_contact`, `SM.ng_finite_word`) and the SM rows that consume them
CV:def:homfly (141: needs `homfly`), CV:ax:homfly (160: lp:core 61, lp:coefficient-transport 60),
CV:ax:gausscode replacement (163: rp:record-polynomial 63, lp:core 61), CV:lem:homflyrows (157:
mp:join 66, mp:stack 67, mp:lowest 69, lp:core), CV:lem:rounding (152), CV:lem:curl (154),
CV:thm:carrierfloor (R)(A)(B)(C) (155: cf:* 95–99, fd:contact 94, src:contact), CV:ax:etnyre
(161: src:contact, def:transverse-front 92), CV:ax:slbound (162: fd:contact 94 and its chain
73–93, ng:finite-word), CV:singleton_D_i (165: cb:singleton 103, thm:floor 100, lc:single-crossing
65), R:generic_selected (174), R:extreme_transport (176), R:extreme_selected (177).

### (d) Gaps — facts with no library lemma (difficulty: E easy, M medium, H hard, VH very hard)
G1 (H, decision first) Domain of the Carrier lane: `SM.Generic` vs CV's guarded genericity (F2).
   Generalization to `CV.Generic` (or `WeakGeneric ∧ vertex-off-lines`) touches 27 modules / 360
   `hP.1/hP.2` uses; the geometric API (`CrossingGeometry`, `geometricVisitPosition`,
   `GeometricInterlaces`) exists. 2–3 prover-weeks. Until done, carrier-dependent CV rows and
   `CV.hyp_R` are stated on U_n^SM with a recorded, reviewed narrowing.
G2 (M) The reference-ray rotation formula: 2π·Σ ε_i(r) = Σ principalTurn (CV:lem:turnlift(ii),
   d1:857–866). Angle-branch bookkeeping with `Real.Angle`/`toIocMod`; 400–600 lines.
G3 (E) CV:lem:carriers(iv): a connected component of G[U(S)] lies on one carrier — connectivity
   induction from `noncrossing` + `nonneighbor_visits_together` + `interlaces_iff_unique`. 120 lines.
G4 (M–H) The piece curve (lem:piececurve Step 5): a greedy independent set K of undominated
   crossings outside H such that the carrier of S ∪ K owning H has double points exactly H;
   well-founded recursion with three invariants. 400–600 lines. Alternative: SM cb:products.
G5 (VH, not this lane) Smooth (C^∞) regular closed curves and their diagrams, RI/RII/RIII on
   them, rounding and the negative curl (CV d3 = SM cf:* rows 95–99).
G6 (VH, not this lane) Contact-geometric interface: transverse knots, fronts, `sl`, the transverse
   lift (CV:ax:etnyre/slbound = src:contact, def:transverse-front, fd:contact chain).
G7 (H) R:availability_0_1 — no printed proof; needs record-level transport of piece diagrams when
   the three triangle crossings are dominated (their visits are on different carriers and lie in
   no piece), plus the one-selected case. Depends on the decision that piece polynomials are
   record-determined (F4 replacement).
G8 (H) Cross-wall transport of an exterior carrier's corner polygon and rotation (R-EXTERIOR §4,
   lem:silence's rotation paragraph): continuity of `ccpCornerPolygon` in the parent along a
   guarded family and `rotation_number` clause 3; the Carrier lane has no "family" version yet
   (`CarrierAmbientTransport` is combinatorial, not geometric).
G9 (M) CV:ax:homfly's uniqueness over R from lp:lm-uniqueness over T: check the printed
   lp:coefficient-transport (sm-3:981) covers an arbitrary R-valued competitor; otherwise the
   Gaussian-ring detour of the design's ring layer (`R.toRG`, `phiEquiv`) must be extended.
G10 (H) Exhibiting actual RII moves between concrete polygonal positive lifts ("switching q makes
   an empty oppositely-signed RII bigon; deleting it gives D_L": lem:fulltwist (T2) instances in
   174, 176, 177) — needs a clearance argument that the bigon's lens contains no other strand
   (R-LOC-2 adjacency + the event disc) and the phase-2 `RII` predicate.
G11 (H) Exhibiting actual RIII moves between grouped diagrams (173 empty row, 177 §2) and the
   "ambient isotopy through the wall" of the two-component diagrams E_H, E_L (177 (6)) — a
   `Deform` witness whose intermediate shadows stay generic after the local pair is deleted.
G12 (M) The split-unknot identity P(L ⊔ ○) = δ·P(L) (CV:def:homfly third display): needs a
   polygonal kink insertion realizing an RI move in a clean disc.
G13 (E–M) `Record.CyclicBetween` and the lemma "successor preservation ⇔ cyclic-order preservation
   for ≥ 3 marks on one circle" (CV:def:record (a) vs `RecordIso.succ_eq`). 150 lines.
G14 (E) `coeffAt_single_mul` (shift of `[a^d z^k]` under multiplication by a monomial) and the
   z⁰-row product lemma for `InSupportM 1` factors (knot parity consequence) in LinkLaurentRing.
G15 (M) An occurrence-set restriction `Record.restrictOcc` (successor by first return into the
   kept set; `firstReturn` machinery exists at LinkRecord.lean:55–190) for 156 and 158(A).


## Appendix A. Compiled skeleton of the CV definitions (type level)

Checked 2026-09-13 with `source /workspace/envs/lean/env.sh; cd work/lean; lake env lean /tmp/cvscout/CVSkeleton.lean`
against the built library: exit 0, no warnings, no `sorry`, standard axioms. Copy into
`work/lean/CV/Guarded.lean` (rows 129–132) and `work/lean/CV/Event.lean` (rows 148, 150) and
add the row declarations described in section 3. Bodies are the printed formulas of
d1_setup.tex:42–218 (guards), 220–238 (generic), 315 (diagrammatic), 1072 (event), 1265 (silent),
d10_axioms.tex:18–24 (the forced RIII bundle).

```lean
import SM.Generic
import SM.RegularLocus
import SM.Chirotope
import SM.GermSignChange
import SM.Interlacement

/-! Scout skeleton for the CV lane (type-level only; bodies are the printed formulas). -/

namespace CV
open SM

variable {n : ℕ}

/-- CV def:polygon (d1_setup.tex:8): a tuple with `p_{i+1} ≠ p_i` for every `i`. -/
def IsPolygon (P : LabelledTuple n) : Prop := ∀ i, edge P i ≠ 0

/-- The integer representative in {1,…,n} of a cyclic edge index (def:guarded, "Normalization
of cyclic aliases"). -/
def rep [NeZero n] (i : ZMod n) : ℕ := (i - 1).val + 1

theorem rep_injective [NeZero n] : Function.Injective (rep (n := n)) := by
  intro a b h
  have h1 : (a - 1).val = (b - 1).val := Nat.succ_injective h
  have h2 := ZMod.val_injective n h1
  exact sub_left_injective h2

/-- `ℓ_e(x) = det(d_e, x − p_e)`. -/
def lineForm (P : LabelledTuple n) (e : ZMod n) (x : Plane) : ℝ := det (edge P e) (x - P e)

/-- G1_i = det(d_{i−1}, d_i). -/
def G1 (P : LabelledTuple n) (i : ZMod n) : ℝ := det (edge P (i - 1)) (edge P i)
/-- G2_{e,i} = ℓ_e(p_i). -/
def G2 (P : LabelledTuple n) (e i : ZMod n) : ℝ := lineForm P e (P i)
/-- G5_{e,f} = det(d_e, d_f). -/
def G5 (P : LabelledTuple n) (e f : ZMod n) : ℝ := det (edge P e) (edge P f)
/-- G4_{e;f,g}. -/
def G4 (P : LabelledTuple n) (e f g : ZMod n) : ℝ :=
  det (edge P f) (P f - P e) * det (edge P g) (edge P e)
    - det (edge P g) (P g - P e) * det (edge P f) (edge P e)
/-- The coefficient row (A_e, B_e, C_e) of the line of `e`. -/
def row (P : LabelledTuple n) (e : ZMod n) : Fin 3 → ℝ :=
  ![-(edge P e).2, (edge P e).1, (edge P e).2 * (P e).1 - (edge P e).1 * (P e).2]
/-- G3_{e,f,g} = det of the three coefficient rows. -/
def det3 (r s t : Fin 3 → ℝ) : ℝ :=
  r 0 * (s 1 * t 2 - s 2 * t 1) - r 1 * (s 0 * t 2 - s 2 * t 0) + r 2 * (s 0 * t 1 - s 1 * t 0)
def G3 (P : LabelledTuple n) (e f g : ZMod n) : ℝ := det3 (row P e) (row P f) (row P g)

/-- CV activation (def:guarded): two remote edges are *defined* to cross by the strict
four-sign test. -/
def Crosses (P : LabelledTuple n) (e f : ZMod n) : Prop :=
  remote e f ∧ G2 P e f * G2 P e (f + 1) < 0 ∧ G2 P f e * G2 P f (e + 1) < 0

/-- The guarded list 𝓖 as an indexed type: one constructor per family, the index data carrying
the printed side conditions (remoteness, `i ∉ {e, e+1}`, representative order). -/
inductive Member (n : ℕ) [NeZero n]
  | g1 (i : ZMod n)
  | g2 (e i : ZMod n) (h : i ≠ e ∧ i ≠ e + 1)
  | g5 (e f : ZMod n) (h : remote e f ∧ rep e < rep f)
  | g3 (e f g : ZMod n) (h : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
  | g4 (e f g : ZMod n) (h : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)

variable [NeZero n]

/-- The polynomial function of a member. -/
def Member.eval : Member n → LabelledTuple n → ℝ
  | .g1 i, P => G1 P i
  | .g2 e i _, P => G2 P e i
  | .g5 e f _, P => G5 P e f
  | .g3 e f g _, P => G3 P e f g
  | .g4 e f g _, P => G4 P e f g

def Member.Unconditional : Member n → Prop
  | .g1 _ => True | .g2 _ _ _ => True | _ => False

/-- Activation at `P` (conditional members only). -/
def Member.Active (P : LabelledTuple n) : Member n → Prop
  | .g1 _ => False
  | .g2 _ _ _ => False
  | .g5 e f _ => Crosses P e f
  | .g3 e f g _ => Crosses P e f ∧ Crosses P f g ∧ Crosses P e g
  | .g4 e f g _ => Crosses P e f ∧ Crosses P e g

def Member.Relevant (P : LabelledTuple n) (m : Member n) : Prop := m.Unconditional ∨ m.Active P

/-- CV def:generic (A): every relevant member is nonzero. -/
def Generic (P : LabelledTuple n) : Prop :=
  IsPolygon P ∧ ∀ m : Member n, m.Relevant P → m.eval P ≠ 0

/-- The member-valued accessor G4⟨e; f, g⟩ (returns the member indexed by the ordered
representatives) and the orientation sign ε(f,g). -/
noncomputable def G4acc (e f g : ZMod n) (h : remote e f ∧ remote e g ∧ f ≠ g) : Member n :=
  if hfg : rep f < rep g then .g4 e f g ⟨h.1, h.2.1, h.2.2, hfg⟩
  else .g4 e g f ⟨h.2.1, h.1, h.2.2.symm, by
    rcases lt_or_ge (rep g) (rep f) with hlt | hge
    · exact hlt
    · exfalso; exact hfg (lt_of_le_of_ne hge fun hEq => h.2.2 (rep_injective hEq))⟩
def eps (f g : ZMod n) : ℤ := if rep f < rep g then 1 else -1

/-- CV def:event (d1_setup.tex:1072): a continuous path, CV-generic off `0`, not at `0`. -/
structure Event (n : ℕ) [NeZero n] where
  radius : ℝ
  radius_pos : 0 < radius
  curve : Set.Ioo (-radius) radius → LabelledTuple n
  continuous_curve : Continuous curve
  generic_punctured : ∀ t, t.val ≠ 0 → Generic (curve t)
  nongeneric_center : ¬ Generic (curve ⟨0, by constructor <;> linarith [radius_pos]⟩)

namespace Event
variable (E : Event n)
def center : LabelledTuple n := E.curve ⟨0, by constructor <;> linarith [E.radius_pos]⟩
/-- The zero set Z. -/
def zeroSet : Set (Member n) :=
  {m | m.eval E.center = 0 ∧ ∃ t, t.val ≠ 0 ∧ m.Relevant (E.curve t)}
/-- Sign change of a real function at 0 (the germ form used by SM `WallGerm.SignChanges`). -/
def SignChanges (φ : LabelledTuple n → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ∀ t : ℝ, 0 < t → t < δ →
    ∀ (hp : t ∈ Set.Ioo (-E.radius) E.radius) (hm : -t ∈ Set.Ioo (-E.radius) E.radius),
      φ (E.curve ⟨t, hp⟩) * φ (E.curve ⟨-t, hm⟩) < 0
def Transversal : Prop := ∀ m ∈ E.zeroSet, E.SignChanges m.eval
/-- CV def:silent. -/
def Silent : Prop := ∀ m ∈ E.zeroSet, ∃ e i h, m = Member.g2 e i h ∧
  (∃ t : ℝ, E.center i = edgePoint E.center e t) ∧ E.center i ∉ edgeSegment E.center e
/-- The forced RIII bundle of CV ax:R. -/
def IsSimpleRIII (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ rep e < rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ rep e < rep f) : Prop :=
    E.zeroSet = {Member.g3 e f g h3, Member.g4 e f g h4e, Member.g4 f e g h4f, Member.g4 g e f h4g} ∧
    (∃ x, x ∈ edgeInterior E.center e ∧ x ∈ edgeInterior E.center f ∧ x ∈ edgeInterior E.center g) ∧
    E.Transversal
end Event

/-- CV def:diagrammatic, in the accepted SM vocabulary (finitely many transverse interior double
points, no shared image/preimage, none at a corner, no vertex on a non-incident edge). -/
def Diagrammatic (P : LabelledTuple n) : Prop :=
  IsPolygon P ∧
  (∀ i j, remote i j → (edgeSegment P i ∩ edgeSegment P j).Nonempty →
      det (edge P i) (edge P j) ≠ 0 ∧ ∀ x ∈ edgeSegment P i ∩ edgeSegment P j,
        x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j) ∧
  (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      ¬ ∃ x, x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧ x ∈ edgeInterior P k) ∧
  (∀ i e, ¬ incident i e → P i ∉ edgeSegment P e)

end CV
```
