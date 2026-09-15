import RProof.Cores
import CV.X1
import CV.ChamberInvII
import CV.SelectorA
import CV.HomflyRows
import CV.FullTwist
import SM.CornerStateSum

/-! # R lane, panel B (consumer-first) — statements of the nine remaining obligation rows

Rows (blueprint/ORDER.md; fixed names, work/lean/axiom-policy.json `targets`):
168 R:exterior → `RProof.exterior`; 170 R:availability_0_1 → `RProof.availability_zero_one`;
172 R:generic_selector → `RProof.generic_selector`; 173 R:generic_transport → `RProof.generic_transport`;
174 R:generic_selected → `RProof.generic_selected`; 175 R:extreme_pair_zero → `RProof.extreme_pair_zero`;
176 R:extreme_transport → `RProof.extreme_transport`; 177 R:extreme_selected → `RProof.extreme_selected`;
178 R:cv_theorem → `RProof.cv_R : CV.hyp_R` (CV:ax:R → `CV.hyp_R`, declared here in the R6 form of
work/drafts/cvdom/DECISION_FINAL.md §3).

Sources (frozen): R_ASSEMBLY_SPEC.md; OPEN_WORK.md items 2–4; reference/R/RA/R_ATTACHMENT_WARRANTS.md
("R-EXTERIOR-1 — the triangle-disjoint factor"); R_GENERIC_NONSELECTED_SELECTOR_PROOF.md;
R_GENERIC_COMMON_TRANSPORT_PROOF.md; R_GENERIC_SELECTED_COUPLE_PROOF.md; R_EXTREME_PAIR_ZERO_PROOF.md;
R_EXTREME_SINGLETON_TRANSPORT_PROOF.md; R_EXTREME_SELECTED_COUPLE_PROOF.md; CV d1_setup.tex def:X1 (908),
def:event (1072), prop:chamberinv (932); d10_axioms.tex ax:R (18). Companion notes: NOTES_B.md.

Foundation consumed (accepted): `RProof.Cores` (rows 164/167/171/172: `LocalizationData`, `ParityData`,
`FibrePartitionData`, `GenericTableData`, the vocabulary `triangleCrossings`, `xPair`, `avail`,
`outsideSupports`, `localFibre`, `fibreSum`, `strandSign`, `Selected*`, `Edge*`, `ExtremeLocal`,
`Punctured`, `OppositeSides`, `genericAt`, `geomAt`); `CV.X1` (row 146: `X1`, `Omega1`, `slot`,
`carrierR`, `groupedPoly`, `groupedWrithe`); `CV.ChamberInvII` (`X1Summand`, `X1_eq_sum_X1Summand`;
chamberinv (ii) modulo `PieceHomflyTransported`); `CV.Carriers` (def:wind `weight`/`wind`/`CarrierUniform`,
def:pieces `Piece`/`pieceOf`/`pieceLabels`/`piecesOn`); `SM.GeoCarrier` (`GeoComponent`, `geoOwner`,
`geoCornerTurn`); `Bridge.B1/B3` and `RProof.isSimpleRIII_eventOfTriple` (the consumer chain).

## Domain (F2(A), no narrowing)

Every row is on the CV event locus: `E : CV.Event n`, `E.IsSimpleRIII e f g h3 h4e h4f h4g`, sides
`E.curve t`, `0 < |t| < δ`, `hn : 3 ≤ n` (needed by `CV.X1`; CV fixes `n ≥ 3` globally, d1:932). The
"complete summand of CV def:X1 at `S` on that side" (R_ASSEMBLY_SPEC.md) is `CV.X1Summand hn (genericAt E t _) S`
(`= wind(S) ∏_L Ω₁(S,L)` when `S ∈ Ind(G_P)`, `0` otherwise — "absent rows being zero"), and the fibre sum
`Φ_±(Q)` is `fibreSum … (X1Summand …) Q`. Crossings are identified across the wall by their carrying edge
pairs (`crossingTransport hs`, `Finset.map`), exactly as in the accepted rows.

## Consumer-first shape (§"cv_R" below)

`Bridge.sm_R` applies `RProof.cv_R : CV.hyp_R` to `Bridge.eventOfTriple hn g h` at one pair of side
parameters and reads the two values through Bridge:B4 `pointwise` (`X1 = cornerStateSum` on SM-generic
polygons). So `CV.hyp_R` is the printed all-parameters form (R6). The R lane's own content is the punctured
form `CvRNear` (bundle `CvTheoremData`: (3) specialised to the complete summand, the outside-support
reindexing, the fibre identities (4) for every `Q`, and their finite sum). Two PROVED reductions exhibit the
consumption: `hyp_R_of_near_of_chamberinv : CvRNear → ChamberInvII → CV.hyp_R` and
`smR_shape_of_hyp_R : CV.hyp_R → (B4 pointwise) → C(P₊) = C(P₋)` on every SM simple triple germ
(the printed SM hyp:R, sm-4-knotlaws.tex:1149). `CvTheoremData.of_fibre_identities` (PROVED) shows that the
fibre identities of rows 170–177 plus the accepted rows 164/171 give the punctured form by finite summation. -/

namespace CV

open SM

/-- **CV:ax:R (`CV.hyp_R`)** in the printed chamber-value form (d10_axioms.tex:18–24, DECISION_FINAL.md R6):
"`X₁(P₊) = X₁(P₋)` across every simple Reidemeister III event, i.e. every event whose zero set is the
forced bundle `Z = {G3_{e,f,g}, G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}` for three pairwise remote edges with
`1 ≤ e < f < g ≤ n`, concurrent at `t = 0` at a point interior to all three, the event being transversal in
the sense of Definition def:event" — `P₊`, `P₋` the two chambers of the event (def:event d1:1080–1083),
rendered as the value of `X₁` at every positive and every negative parameter of the event. -/
def hyp_R : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ rep e < rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ rep e < rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g →
    ∀ (tp tm : E.Parameter) (hp : 0 < tp.val) (hm : tm.val < 0),
      X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') =
        X1 hn (E.curve tm) (E.generic_punctured tm hm.ne)

end CV

namespace RProof

open SM SM.Carrier SM.GeoCarrier CV

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-! ## Part 0 — vocabulary of the X₁-dependent rows -/

/-- "`F_±(S)`, the **complete** summand of CV def:X1 at `S` on that side, including the selector and
every carrier coefficient with the printed empty conventions" (R_ASSEMBLY_SPEC.md): `wind(S) ∏_L Ω₁(S,L)`
for `S ∈ Ind(G_{P(t)})`, `0` for an absent support (`CV.X1Summand`, the total-function summand of
`CV.X1_eq_sum_X1Summand`). -/
noncomputable def summandAt (hn : 3 ≤ n) (E : CV.Event n) (t : E.Parameter) (ht : t.val ≠ 0) :
    Finset (Crossing (E.curve t)) → ℤ :=
  CV.X1Summand hn (genericAt E t ht)

/-- "`Φ_±(Q) = Σ_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J)`" (R_ASSEMBLY_SPEC.md (2)) with `F_±` the complete summand:
`fibreSum` of the accepted row 171 at `summandAt`. -/
noncomputable def fibreTermAt (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (t : E.Parameter)
    (ht : t.val ≠ 0) (Q : Finset (Crossing (E.curve t))) : ℤ :=
  fibreSum (geomAt E t ht) e f g (summandAt hn E t ht) Q

/-- The support `Q` read on the other side of the wall by its carrying edge pairs (the accepted
`Finset.map (crossingTransport hs).toEmbedding` of rows 167/171). -/
abbrev wallMap {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) : Finset (Crossing Q) :=
  S.map (crossingTransport hs).toEmbedding

omit [NeZero n] in
theorem wallMap_eq_transportSupport {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) : wallMap hs S = transportSupport hs S := rfl

/-- `wallMap hs` as an embedding of supports (for reindexing sums over `Ind(G[W])`). -/
def wallMapEmb {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    Finset (Crossing P) ↪ Finset (Crossing Q) :=
  (Finset.mapEmbedding (crossingTransport hs).toEmbedding).toEmbedding

omit [NeZero n] in
@[simp] theorem wallMapEmb_apply {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) : wallMapEmb hs S = wallMap hs S :=
  Finset.mapEmbedding_apply

/-- "Full availability means that the availability set defined in R-PAR-v6 equals the three-element local
crossing set `T`" (R_ATTACHMENT_WARRANTS.md, preamble): `𝓐(Q) = T`. -/
def FullAvail {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    (Q : Finset (Crossing P)) : Prop :=
  avail hP e f g Q = triangleCrossings P e f g

/-- The `K₃` side of the extreme orbit: all three local edges present ("`H[T] = K3`"). -/
def LocalComplete {P : LabelledTuple n} (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : Prop :=
  EdgeAB hP hef heg ∧ EdgeAC hP hef hfg ∧ EdgeBC hP heg hfg

/-- The empty side of the extreme orbit: no local edge ("`L[T]` is empty"). -/
def LocalEmpty {P : LabelledTuple n} (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : Prop :=
  ¬ EdgeAB hP hef heg ∧ ¬ EdgeAC hP hef hfg ∧ ¬ EdgeBC hP heg hfg

/-- R-EXTERIOR-1: "A carrier of `S` is *triangle-disjoint* when it contains none of the six traversal
visits belonging to `T`, including a selected triangle crossing's smoothing-site visits": no visit mark of a
triangle crossing is owned by the carrier (`geoOwner` is defined on every mark, the smoothing-site visits of
a selected crossing included, by conv:selected-visits). -/
def TriangleDisjoint {P : LabelledTuple n} (hP : CrossingGeometry P) (e f g : ZMod n)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) : Prop :=
  ∀ v : Visit P, v.1.val ∈ triangleSupports e f g → geoOwner hP S (Sum.inr v) ≠ q

/-- R-EXTERIOR-1: "`C_{Q,σ}(A) = ∏_{triangle-disjoint carriers L} wt_σ(L) · Ω_{1,σ}(S,L)`", `S = Q ∪ A`. -/
noncomputable def exteriorFactor (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (e f g : ZMod n) : ℤ :=
  ∏ q ∈ (Finset.univ.filter fun q => TriangleDisjoint hG.crossingGeometry e f g S q),
    weight hG.crossingGeometry S q * Omega1 hn hG hS q

/-- R-EXTERIOR-1: "`ρ_σ(A)` is the product over the triangle-touching carriers" (of `wt · Ω₁`). -/
noncomputable def touchingFactor (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (e f g : ZMod n) : ℤ :=
  ∏ q ∈ (Finset.univ.filter fun q => ¬ TriangleDisjoint hG.crossingGeometry e f g S q),
    weight hG.crossingGeometry S q * Omega1 hn hG hS q

/-- The pair selected by the separating-strand test (4) of R_GENERIC_NONSELECTED_SELECTOR_PROOF.md ("Which
pair is selected": `ac` iff `s_a = s_c`, `ab` iff `s_a = −s_b`, `bc` iff `s_b = −s_c`; in the generic orbit
exactly one holds, `GenericTableData.selected_unique`), in the labels `a = x_ef`, `b = x_eg`, `c = x_fg`. By
`GenericTableData.selected_is_graph_selected` it is the graph-selected pair complementary to the degree-two
vertex of `P₃`. -/
noncomputable def selectedPair {P : LabelledTuple n} {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    Finset (Crossing P) :=
  if SelectedAC (strandSign P e f) (strandSign P f g) then {xPair hef, xPair hfg}
  else if SelectedAB (strandSign P e f) (strandSign P e g) then {xPair hef, xPair heg}
  else {xPair heg, xPair hfg}

/-- The complementary singleton: "the degree-two singleton of `P₃`" (`b` in the canonical labels). -/
noncomputable def selectedCentre {P : LabelledTuple n} {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : Crossing P :=
  if SelectedAC (strandSign P e f) (strandSign P f g) then xPair heg
  else if SelectedAB (strandSign P e f) (strandSign P e g) then xPair hfg
  else xPair hef

/-- R_ASSEMBLY_SPEC.md: "Prove the required carrier/record, selector, rotation and coefficient transport":
the two complete summands are matched carrier by carrier — the selector (`wind`, and `wt` per carrier), a
bijection of carriers `τ` carrying the record data `w_{S,L}` (`groupedWrithe`) and `P_{S,L}` (`groupedPoly`),
the rotation `R(L)` (`carrierR`) and the coefficient `Ω₁(S,L)` (`Omega1`). -/
def SummandTransport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic Q)
    {S : Finset (Crossing P)} {S' : Finset (Crossing Q)}
    (hS : S ∈ Ind hG.crossingGeometry) (hS' : S' ∈ Ind hG'.crossingGeometry) : Prop :=
  wind hG'.crossingGeometry S' = wind hG.crossingGeometry S ∧
  ∃ τ : GeoComponent hG.crossingGeometry S ≃ GeoComponent hG'.crossingGeometry S',
    ∀ q, weight hG'.crossingGeometry S' (τ q) = weight hG.crossingGeometry S q ∧
      carrierR hn hG' hS' (τ q) = carrierR hn hG hS q ∧
      groupedWrithe hG' (τ q) = groupedWrithe hG q ∧
      groupedPoly hn hG' hS' (τ q) = groupedPoly hn hG hS q ∧
      Omega1 hn hG' hS' (τ q) = Omega1 hn hG hS q

/-! ## Row 168 — R:exterior (R_ATTACHMENT_WARRANTS.md, "R-EXTERIOR-1 — the triangle-disjoint factor")

Printed statement: "Let `P₋` and `P₊` be the generic sides of a simple transversal RIII event, and let `T`
be the three crossings identified by their carrying edge pairs as in R-LOC-2. Fix an outside independent
set `Q`, disjoint from `T`. On either side `σ`, let `A` be any subset of `T` for which `S = Q ∪ A` is
independent. A carrier of `S` is *triangle-disjoint* when it contains none of the six traversal visits
belonging to `T`, including a selected triangle crossing's smoothing-site visits. Define
`C_{Q,σ}(A) = ∏_{triangle-disjoint L} wt_σ(L) · Ω_{1,σ}(S,L)`. Then `C_{Q,σ}(A)` is independent of `A`, and
its common value is the same for `σ = −` and `σ = +`. Write that single value as `C_Q`; it may be zero.
Consequently every full-availability row factors exactly as `τ_σ(A) = C_Q · ρ_σ(A)`, where `ρ_σ(A)` is the
product over the triangle-touching carriers." OPEN_WORK.md item 4: "Prove the common exterior factor without
division; handle absent supports, empty products, dead selectors, orientations, both directions and
arbitrary exterior geometry." -/

/-- **R-EXTERIOR-1**, clause by clause; `C_Q` is represented by the base row `A = ∅` (`Q ∈ Ind(G_P)`). -/
structure ExteriorData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Then `C_{Q,σ}(A)` is independent of `A`" — for any two `A, A' ⊆ T` with `Q ∪ A`, `Q ∪ A'`
  independent on the side `σ` ("absent supports" are excluded by the independence hypotheses; "empty
  products" and "dead selectors" are covered since `wt` may be `0` and no factor is divided). -/
  exterior_independent_of_A : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ A A' : Finset (Crossing (E.curve t)), A ⊆ triangleCrossings (E.curve t) e f g →
      A' ⊆ triangleCrossings (E.curve t) e f g →
      ∀ (hS : Q ∪ A ∈ Ind (geomAt E t ht.1)) (hS' : Q ∪ A' ∈ Ind (geomAt E t ht.1)),
        exteriorFactor hn (genericAt E t ht.1) hS e f g = exteriorFactor hn (genericAt E t ht.1) hS' e f g
  /-- "and its common value is the same for `σ = −` and `σ = +`" — across the wall, for any `A` on one side
  and `A'` on the other ("both directions", "arbitrary exterior geometry"). -/
  exterior_wall_invariant : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ (A : Finset (Crossing (E.curve t))) (A' : Finset (Crossing (E.curve t'))),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t') e f g →
      ∀ (hS : Q ∪ A ∈ Ind (geomAt E t ht.1)) (hS' : wallMap hs Q ∪ A' ∈ Ind (geomAt E t' ht'.1)),
        exteriorFactor hn (genericAt E t ht.1) hS e f g = exteriorFactor hn (genericAt E t' ht'.1) hS' e f g
  /-- "Consequently every full-availability row factors exactly as `τ_σ(A) = C_Q · ρ_σ(A)`": the complete
  summand at `Q ∪ A` is the exterior factor of the base row `Q` (the common value `C_Q`) times the product
  over the triangle-touching carriers; "including when either factor is zero. No cancellation and no
  division by `C_Q` is used." (`summandAt_eq_exterior_mul_touching` below is the algebraic half.) -/
  factorization : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q, ∀ hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      FullAvail (geomAt E t ht.1) e f g Q →
      ∀ A : Finset (Crossing (E.curve t)), A ⊆ triangleCrossings (E.curve t) e f g →
      ∀ hS : Q ∪ A ∈ Ind (geomAt E t ht.1),
        summandAt hn E t ht.1 (Q ∪ A) =
          exteriorFactor hn (genericAt E t ht.1) ((F1.mem_outsideSupports _ e f g Q).mp hQ).1 e f g *
            touchingFactor hn (genericAt E t ht.1) hS e f g

/-- **Row 168, R:exterior.** -/
theorem exterior (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExteriorData hn E e f g δ := by
  sorry

/-! ## Row 170 — R:availability_0_1 (R_ASSEMBLY_SPEC.md, paragraph after (4); OPEN_WORK.md item 2)

Specified text: "The local proof task, for each such `Q`, is `Φ₊(Q) = Φ₋(Q)` (4). At availability zero or
one the local supports themselves correspond, but that does **not** prove their summands agree. Prove the
required carrier/record, selector, rotation and coefficient transport. These cases cannot be omitted because
the four core proofs assume full availability." OPEN_WORK.md item 2: "Prove the fibre identities for
availability 0 and 1." -/

/-- **The availability-0/1 fibre identities**, clause by clause, for every outside independent `Q` with
`|𝓐(Q)| ∈ {0, 1}` (the sizes `≠ 3` of `FibrePartitionData.avail_card`). -/
structure AvailabilityZeroOneData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "At availability zero … the local supports themselves correspond": `Ind(G[𝓐(Q)]) = {∅}`. -/
  fibre_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, (avail (geomAt E t ht.1) e f g Q).card = 0 →
      localFibre (geomAt E t ht.1) e f g Q = {∅}
  /-- "At availability … one the local supports themselves correspond": `𝓐(Q) = {z}` and
  `Ind(G[𝓐(Q)]) = {∅, {z}}`. -/
  fibre_one : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∃ z : Crossing (E.curve t), avail (geomAt E t ht.1) e f g Q = {z} ∧
        localFibre (geomAt E t ht.1) e f g Q = {∅, {z}}
  /-- "the local supports themselves correspond" across the wall: the local fibre over `Q` on one side is
  carried onto the local fibre over `Q` on the other side by the carrying edge pairs. -/
  fibre_correspond : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      localFibre (geomAt E t' ht'.1) e f g (wallMap hs Q) =
        (localFibre (geomAt E t ht.1) e f g Q).map (wallMapEmb hs)
  /-- "but that does **not** prove their summands agree. Prove the required carrier/record, selector,
  rotation and coefficient transport": for every local support `J` of the fibre, the complete summands at
  `Q ∪ J` on the two sides are matched carrier by carrier (`SummandTransport`). -/
  summand_transport : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
      ∀ (hS : Q ∪ J ∈ Ind (geomAt E t ht.1)) (hS' : wallMap hs (Q ∪ J) ∈ Ind (geomAt E t' ht'.1)),
        SummandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS'
  /-- (4) "`Φ₊(Q) = Φ₋(Q)`" at availability zero or one. -/
  fibre_identity : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      fibreTermAt hn E e f g t ht.1 Q = fibreTermAt hn E e f g t' ht'.1 (wallMap hs Q)

/-- **Row 170, R:availability_0_1.** -/
theorem availability_zero_one (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AvailabilityZeroOneData hn E e f g δ := by
  sorry

/-! ## Row 172 — R:generic_selector (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md)

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the generic graph orbit
`P3 <-> (one edge plus one isolated vertex)`. Among the three one-sided local pair supports, one is the
graph-selected pair complementary to the degree-two singleton of `P3`. Each of the other two pair rows has
winding selector zero on the side where it is present. This holds for arbitrary exterior gaps and outside
independent support `Q`; no coefficient, exterior-factor division, or nonvanishing hypothesis is used."
Mechanism ("The mixed carrier"): "one carrier contains the entire arc and both of its endpoint smoothing
corners … The two corner determinants are therefore `det(v,u) = −det(u,v)` and `det(u,w)`. By (5), the signs
in (6) are opposite. The carrier is mixed regardless of all its other corners, so its weight is zero by
def:wind. The support's winding selector, a product containing this weight, is zero. Consequently its entire
X1 row is zero before any coefficient is read." -/

/-- **The generic nonselected pair rows are selector-dead**, clause by clause. -/
structure GenericSelectorData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Among the three one-sided local pair supports, one is the graph-selected pair complementary to the
  degree-two singleton of `P3`": on either side of the generic orbit, `selectedPair` is complementary to
  `selectedCentre`, and either the centre has degree two with the pair independent (`P₃`), or the pair is
  the one edge and the centre is isolated. -/
  graph_selected : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    insert (selectedCentre hef heg hfg) (selectedPair hef heg hfg) = triangleCrossings (E.curve t) e f g ∧
    selectedCentre hef heg hfg ∉ selectedPair hef heg hfg ∧ (selectedPair hef heg hfg).card = 2 ∧
    ((∀ x ∈ selectedPair hef heg hfg,
        GeometricInterlaces (geomAt E t ht.1) (selectedCentre hef heg hfg) x) ∧
      (∀ x ∈ selectedPair hef heg hfg, ∀ y ∈ selectedPair hef heg hfg, x ≠ y →
        ¬ GeometricInterlaces (geomAt E t ht.1) x y)) ∨
    ((∀ x ∈ selectedPair hef heg hfg,
        ¬ GeometricInterlaces (geomAt E t ht.1) (selectedCentre hef heg hfg) x) ∧
      (∀ x ∈ selectedPair hef heg hfg, ∀ y ∈ selectedPair hef heg hfg, x ≠ y →
        GeometricInterlaces (geomAt E t ht.1) x y))
  /-- "The mixed carrier": for a nonselected pair `J` present with `Q`, "one carrier contains the entire arc
  and both of its endpoint smoothing corners" — the two smoothing-site visits of the two crossings of `J`
  on their shared strand `u` are owned by one carrier — and "the signs in (6) are opposite": the two corner
  turns are nonzero and opposite, so "the carrier is mixed regardless of all its other corners". -/
  mixed_carrier : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      J ≠ selectedPair hef heg hfg → Q ∪ J ∈ Ind (geomAt E t ht.1) →
      ∃ v w : Visit (E.curve t), v.1 ∈ J ∧ w.1 ∈ J ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val ∧
        geoOwner (geomAt E t ht.1) (Q ∪ J) (Sum.inr v) = geoOwner (geomAt E t ht.1) (Q ∪ J) (Sum.inr w) ∧
        geoCornerTurn (geomAt E t ht.1) (Q ∪ J) (Sum.inr v) ≠ 0 ∧
        geoCornerTurn (geomAt E t ht.1) (Q ∪ J) (Sum.inr w) =
          -geoCornerTurn (geomAt E t ht.1) (Q ∪ J) (Sum.inr v) ∧
        CarrierMixed (geomAt E t ht.1) (Q ∪ J) (geoOwner (geomAt E t ht.1) (Q ∪ J) (Sum.inr v))
  /-- "so its weight is zero by def:wind. The support's winding selector, a product containing this weight,
  is zero": "Each of the other two pair rows has winding selector zero on the side where it is present." -/
  wind_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      J ≠ selectedPair hef heg hfg → Q ∪ J ∈ Ind (geomAt E t ht.1) →
      wind (geomAt E t ht.1) (Q ∪ J) = 0
  /-- "Consequently its entire X1 row is zero before any coefficient is read." -/
  row_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      J ≠ selectedPair hef heg hfg →
      summandAt hn E t ht.1 (Q ∪ J) = 0

/-- **Row 172, R:generic_selector.** -/
theorem generic_selector (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectorData hn E e f g δ := by
  sorry

/-! ## Row 173 — R:generic_transport (R_GENERIC_COMMON_TRANSPORT_PROOF.md, "Statement and canonical branch")

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the generic graph orbit and an
exterior independent support `Q`. Relabel the local crossings so `P = a b A a c B b c C` (edges ab, bc),
`E = b a A c a B c b C` (edge ac). … Write `T_ν(J)` for the complete X1 term of `Q ∪ J` on side `ν`. Then
`T_P(∅) = T_E(∅)`, `T_P(a) = T_E(a)`, `T_P(c) = T_E(c)` (2)." In the fixed labels `e < f < g` the endpoints
`a, c` of the path are the two members of the selected pair (`ac` in the displayed branch), and `b` is
`selectedCentre`; "Every generic branch can be put in this form by relabelling the strands in their
transitive angular order." -/

/-- **The generic common-row transports**, clause by clause. -/
structure GenericTransportData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- The selected pair is the same pair of carrying edge pairs on the two sides (the strand signs `s_a, s_b,
  s_c` do not change across the wall, `GenericTableData.chamber_change`), so "the two endpoint singleton
  rows" are well defined across the wall. -/
  selected_pair_invariant : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
      selectedPair ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) = wallMap hs (selectedPair hef heg hfg) ∧
      selectedCentre ((hs _).mp hef) ((hs _).mp heg) ((hs _).mp hfg) =
        crossingTransport hs (selectedCentre hef heg hfg)
  /-- (2) "`T_P(∅) = T_E(∅)`": the empty local row transports. -/
  empty_row : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      summandAt hn E t ht.1 Q = summandAt hn E t' ht'.1 (wallMap hs Q)
  /-- (2) "`T_P(a) = T_E(a)`, `T_P(c) = T_E(c)`": the two endpoint singleton rows — the singletons of the
  two members of the selected pair — transport. -/
  endpoint_rows : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ x ∈ selectedPair hef heg hfg,
      summandAt hn E t ht.1 (insert x Q) =
        summandAt hn E t' ht'.1 (insert (crossingTransport hs x) (wallMap hs Q))

/-- **Row 173, R:generic_transport.** -/
theorem generic_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ := by
  sorry

/-! ## Row 174 — R:generic_selected (R_GENERIC_SELECTED_COUPLE_PROOF.md, "Statement")

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the generic graph orbit and an
exterior independent support `Q`. Relabel the three local crossings so the exact local words are
`P = a b A a c B b c C` (edges ab, bc), `E = b a A c a B c b C` (edge ac). Thus `b` is the degree-two vertex
of the path, and `ac` is its complementary independent pair on `P`. If `T_ν(J)` denotes the complete X1
term of `Q ∪ J` on side `ν`, absent rows being zero, then `T_E(b) = T_P(b) + T_P(ac)` (GSC)." The side `P`
is the side on which the selected pair is independent (present) with `Q`. -/

/-- **The generic selected complementary couple**, clause by clause. -/
structure GenericSelectedData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Thus `b` is the degree-two vertex of the path, and `ac` is its complementary independent pair on
  `P`": on a side where `Q ∪ selectedPair` is independent, the centre interlaces both members of the pair. -/
  centre_is_degree_two : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      Q ∪ selectedPair hef heg hfg ∈ Ind (geomAt E t ht.1) →
      ∀ x ∈ selectedPair hef heg hfg,
        GeometricInterlaces (geomAt E t ht.1) (selectedCentre hef heg hfg) x
  /-- (GSC) "`T_E(b) = T_P(b) + T_P(ac)`", "absent rows being zero": with `t` the side `P` (the selected
  pair present) and `t'` the side `E`. -/
  couple : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      Q ∪ selectedPair hef heg hfg ∈ Ind (geomAt E t ht.1) →
      summandAt hn E t' ht'.1 (insert (crossingTransport hs (selectedCentre hef heg hfg)) (wallMap hs Q)) =
        summandAt hn E t ht.1 (insert (selectedCentre hef heg hfg) Q) +
          summandAt hn E t ht.1 (Q ∪ selectedPair hef heg hfg)

/-- **Row 174, R:generic_selected.** -/
theorem generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ := by
  sorry

/-! ## Row 175 — R:extreme_pair_zero (R_EXTREME_PAIR_ZERO_PROOF.md)

Printed statement: "Fix the two nearby generic chamber-side representatives of a simple RIII wall in the
extreme graph orbit `K3 <-> empty`, and fix a full-availability fiber. Each local pair support is absent on
the `K3` side and present on the empty-graph side. Its complete X1 term on the latter generic polygon is
zero, for arbitrary outside support and exterior geometry." Proof steps recorded as clauses: "The support
`S` is independent"; "`{z}` is a singleton residual piece"; "If `wind(S) = 0`, the X1 term is zero by
definition. Otherwise every carrier of `S` is uniform. Let `A` be the carrier owning `{z}`. The hypotheses of
`thm:s7universal(D)(i)` now hold, so `Ω₁(S,A) = 0`." -/

/-- **Every extreme one-sided pair row is zero**, clause by clause (`K₃` side = `LocalComplete`,
empty-graph side = `LocalEmpty`). -/
structure ExtremePairZeroData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Each local pair support is absent on the `K3` side". -/
  pair_absent_on_complete : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalComplete (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      Q ∪ J ∉ Ind (geomAt E t ht.1)
  /-- "and present on the empty-graph side": "The support `S` is independent. Indeed, `J` is independent
  because the local graph is empty, and full availability says every member of `T` is nonadjacent to every
  member of `Q`." -/
  pair_present_on_empty : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalEmpty (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      Q ∪ J ∈ Ind (geomAt E t ht.1)
  /-- "The remaining crossing `z` is undominated by `S` … Hence `{z}` is a singleton residual piece." -/
  third_singleton_piece : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalEmpty (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
    ∀ z ∈ triangleCrossings (E.curve t) e f g, z ∉ J →
      ∃ hz : z ∈ U (geomAt E t ht.1) (Q ∪ J),
        pieceLabels (geomAt E t ht.1) (Q ∪ J) (pieceOf (geomAt E t ht.1) (Q ∪ J) z hz) = {z}
  /-- "If `wind(S) = 0`, the X1 term is zero by definition. Otherwise every carrier of `S` is uniform. Let
  `A` be the carrier owning `{z}`. The hypotheses of `thm:s7universal(D)(i)` now hold, so `Ω₁(S,A) = 0`"
  (CV:singleton_D_i). -/
  singleton_factor_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalEmpty (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
    ∀ hS : Q ∪ J ∈ Ind (geomAt E t ht.1), wind (geomAt E t ht.1) (Q ∪ J) ≠ 0 →
    ∀ z ∈ triangleCrossings (E.curve t) e f g, z ∉ J →
    ∀ (hz : z ∈ U (geomAt E t ht.1) (Q ∪ J)) (q : GeoComponent (geomAt E t ht.1) (Q ∪ J)),
      pieceOf (geomAt E t ht.1) (Q ∪ J) z hz ∈ piecesOn (geomAt E t ht.1) (Q ∪ J) q →
      Omega1 hn (genericAt E t ht.1) hS q = 0
  /-- "Its complete X1 term on the latter generic polygon is zero, for arbitrary outside support and exterior
  geometry." -/
  row_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalEmpty (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      summandAt hn E t ht.1 (Q ∪ J) = 0

/-- **Row 175, R:extreme_pair_zero.** -/
theorem extreme_pair_zero (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ := by
  sorry

/-! ## Row 176 — R:extreme_transport (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md, "Statement and canonical data")

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the extreme graph orbit, an
outside support `Q`, and the canonical words `H = x y A z x B y z C` (local graph K3),
`L = y x A x z B z y C` (local graph empty). Full availability is part of the statement: every member of
`T = {x,y,z}` is nonadjacent to `Q`, so every `Q ∪ {j}` is independent on both sides. … Write `T_ν(J)` for
the complete X1 term of `Q ∪ J`, with an absent row read as zero. Then, separately and without a symmetry
assumption, `T_H(x) = T_L(x)`, `T_H(y) = T_L(y)`, `T_H(z) = T_L(z)` (2)." -/

/-- **The extreme singleton transports**, clause by clause. -/
structure ExtremeTransportData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "every member of `T = {x,y,z}` is nonadjacent to `Q`, so every `Q ∪ {j}` is independent on both
  sides". -/
  singletons_present : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ x ∈ triangleCrossings (E.curve t) e f g, insert x Q ∈ Ind (geomAt E t ht.1)
  /-- (2) "`T_H(x) = T_L(x)`, `T_H(y) = T_L(y)`, `T_H(z) = T_L(z)`", "separately and without a symmetry
  assumption": every singleton row transports. -/
  singleton_rows : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ x ∈ triangleCrossings (E.curve t) e f g,
      summandAt hn E t ht.1 (insert x Q) =
        summandAt hn E t' ht'.1 (insert (crossingTransport hs x) (wallMap hs Q))

/-- **Row 176, R:extreme_transport.** -/
theorem extreme_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ := by
  sorry

/-! ## Row 177 — R:extreme_selected (R_EXTREME_SELECTED_COUPLE_PROOF.md, "Statement")

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the extreme graph orbit. Let `H`
denote the side whose local graph is `K3`, let `L` denote the side whose local graph is empty, and fix the
outside support `Q`. … Full availability is a hypothesis of the statement, not merely scene-setting: it says
every member of `T = {x,y,z}` is nonadjacent to `Q`, and therefore makes `Q ∪ T` an independent support on
`L`. On `H`, `T` is not independent because its induced graph is `K3`. … Write `T_ν(J)` for the complete X1
term of `Q ∪ J` on side `ν`, with an absent row read as zero. Then `T_H(∅) − T_L(∅) = T_L(xyz)` (2)." -/

/-- **The extreme selected empty/full couple**, clause by clause (`H` = `LocalComplete` side `t`, `L` = the
opposite side `t'`). -/
structure ExtremeSelectedData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "it … makes `Q ∪ T` an independent support on `L`". -/
  full_present_on_empty : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalEmpty (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      Q ∪ triangleCrossings (E.curve t) e f g ∈ Ind (geomAt E t ht.1)
  /-- "On `H`, `T` is not independent because its induced graph is `K3`." -/
  full_absent_on_complete : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalComplete (geomAt E t ht.1) hef heg hfg →
    ∀ Q : Finset (Crossing (E.curve t)), Q ∪ triangleCrossings (E.curve t) e f g ∉ Ind (geomAt E t ht.1)
  /-- (2) "`T_H(∅) − T_L(∅) = T_L(xyz)`", "with an absent row read as zero". -/
  couple : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    LocalComplete (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      summandAt hn E t ht.1 Q - summandAt hn E t' ht'.1 (wallMap hs Q) =
        summandAt hn E t' ht'.1 (wallMap hs Q ∪ triangleCrossings (E.curve t') e f g)

/-- **Row 177, R:extreme_selected.** -/
theorem extreme_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ := by
  sorry

/-! ## Row 178 — R:cv_theorem (R_ASSEMBLY_SPEC.md (3)–(4) and the closing paragraph; OPEN_WORK.md item 4)

Specified text: "The finite bijection just established partitions the exact state sum, so
`X₁(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)` (3). … The local proof task, for each such `Q`, is `Φ₊(Q) = Φ₋(Q)` (4).
… Finally sum the proved identities (4) over the same finite outside-support set in (3). Equality is
preserved by finite summation, giving exactly CV ax:R. … Apply the independently proved bridge afterwards."
OPEN_WORK.md item 4: "Sum all fibre identities to prove CV ax:R on its entire printed simple/transversal
forced-bundle domain." -/

/-- **The CV theorem in its punctured (R-lane) form**, clause by clause. -/
structure CvTheoremData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- (3) "`X₁(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)`" with `F_±` the complete summand (the X₁ specialisation of
  `FibrePartitionData.state_sum_partition`; `state_sum_of_fibrePartition` below). -/
  state_sum : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    X1 hn (E.curve t) (genericAt E t ht.1) =
      ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g, fibreTermAt hn E e f g t ht.1 Q
  /-- "sum … over the same finite outside-support set in (3)": `Ind(G[W])` is the same set on the two sides
  (by the carrying edge pairs; `FibrePartitionData.graph_on_W_same`). -/
  outside_supports_transport : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      outsideSupports (geomAt E t' ht'.1) e f g =
        (outsideSupports (geomAt E t ht.1) e f g).map (wallMapEmb hs)
  /-- (4) "`Φ₊(Q) = Φ₋(Q)`" for every outside independent `Q` (rows 170–177 by availability and orbit). -/
  fibre_identities : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      fibreTermAt hn E e f g t ht.1 Q = fibreTermAt hn E e f g t' ht'.1 (wallMap hs Q)
  /-- "Equality is preserved by finite summation, giving exactly CV ax:R": `X₁(P₊) = X₁(P₋)` on the
  punctured neighbourhood. -/
  near : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
      X1 hn (E.curve t) (genericAt E t ht.1) = X1 hn (E.curve t') (genericAt E t' ht'.1)

/-- The R lane's punctured form of CV:ax:R ("`RProof.cv_R_near`" of DECISION_FINAL.md R6): for every simple
transversal RIII event, `CvTheoremData` on some punctured neighbourhood. -/
def CvRNear : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ CvTheoremData hn E e f g δ

/-- CV:prop:chamberinv (ii) (d1_setup.tex:932–940), "`X₁` is constant on each chamber", in the form
`CV.ChamberInvII` will take (pending row 147 (ii); `CV.X1_eq_of_mem_chamber_of_pieceHomfly` proves it modulo
`PieceHomflyTransported`). -/
def ChamberInvII : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : LabelledTuple n) (hP : CV.Generic P) (hQ : CV.Generic Q),
    Q ∈ chamber P → X1 hn P hP = X1 hn Q hQ

/-- **Row 178, R:cv_theorem: `RProof.cv_R : CV.hyp_R`** — CV:ax:R in its printed chamber-value form, "on its
entire printed simple/transversal forced-bundle domain". Proof shape (DECISION_FINAL.md R6):
`hyp_R_of_near_of_chamberinv (cv_R_near) (chamberinv_ii)`, where `cv_R_near : CvRNear` is
`CvTheoremData.of_fibre_identities` on the accepted rows 164/171 and the fibre identities of rows 170–177. -/
theorem cv_R : CV.hyp_R := by
  sorry

/-! ## Proved reductions (the consumer chain, and the algebraic halves of the rows) -/

/-- The algebraic half of `ExteriorData.factorization`: for an independent `S`, the complete summand is the
product over all carriers of `wt(L) · Ω₁(S,L)` (def:wind `wind(S) = ∏_L wt(L)`, def:X1), split into the
triangle-disjoint and the triangle-touching carriers. No hypothesis on `S` beyond independence. -/
theorem summandAt_eq_exterior_mul_touching (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (e f g : ZMod n) :
    X1Summand hn hG S = exteriorFactor hn hG hS e f g * touchingFactor hn hG hS e f g := by
  unfold X1Summand exteriorFactor touchingFactor
  rw [dite_eq_left hS, Finset.prod_filter_mul_prod_filter_not, Finset.prod_mul_distrib]
  rfl

/-- The X₁ specialisation of (3): from the accepted row 171 and `CV.X1_eq_sum_X1Summand`. -/
theorem state_sum_of_fibrePartition (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hF : FibrePartitionData E e f g δ) (t : E.Parameter) (ht : Punctured E δ t) :
    X1 hn (E.curve t) (genericAt E t ht.1) =
      ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g, fibreTermAt hn E e f g t ht.1 Q := by
  rw [X1_eq_sum_X1Summand]
  exact hF.state_sum_partition t ht (summandAt hn E t ht.1)

/-- "Finally sum the proved identities (4) over the same finite outside-support set in (3). Equality is
preserved by finite summation": the `near` clause from the other three clauses. -/
theorem near_of_fibre_identities (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hF : FibrePartitionData E e f g δ)
    (hout : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
      OppositeSides E t t' →
      ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
        outsideSupports (geomAt E t' ht'.1) e f g =
          (outsideSupports (geomAt E t ht.1) e f g).map (wallMapEmb hs))
    (hfib : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
      OppositeSides E t t' →
      ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
        fibreTermAt hn E e f g t ht.1 Q = fibreTermAt hn E e f g t' ht'.1 (wallMap hs Q))
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t') :
    X1 hn (E.curve t) (genericAt E t ht.1) = X1 hn (E.curve t') (genericAt E t' ht'.1) := by
  have hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s :=
    hL.crossing_set_constant t t' ht ht'
  rw [state_sum_of_fibrePartition hn hF t ht, state_sum_of_fibrePartition hn hF t' ht',
    hout t t' ht ht' hop hs, Finset.sum_map]
  exact Finset.sum_congr rfl fun Q hQ => by rw [wallMapEmb_apply]; exact hfib t t' ht ht' hop hs Q hQ

/-- The bundle of row 178 from the accepted rows 164/171 and the two wall clauses. -/
theorem CvTheoremData.of_fibre_identities (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hF : FibrePartitionData E e f g δ)
    (hout : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
      OppositeSides E t t' →
      ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
        outsideSupports (geomAt E t' ht'.1) e f g =
          (outsideSupports (geomAt E t ht.1) e f g).map (wallMapEmb hs))
    (hfib : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
      OppositeSides E t t' →
      ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
        fibreTermAt hn E e f g t ht.1 Q = fibreTermAt hn E e f g t' ht'.1 (wallMap hs Q)) :
    CvTheoremData hn E e f g δ where
  state_sum := state_sum_of_fibrePartition hn hF
  outside_supports_transport := hout
  fibre_identities := hfib
  near := near_of_fibre_identities hn hL hF hout hfib

/-- **`RProof.cv_R = cv_R_near + chamberinv(ii)`** (DECISION_FINAL.md R6): the punctured form and the chamber
constancy of `X₁` give the printed all-parameters form, since `P((0, ε))` and `P((−ε, 0))` each lie in one
CV chamber (def:event; `Event.curve_mem_sideChamber_pos/neg`). -/
theorem hyp_R_of_near_of_chamberinv (hnear : CvRNear) (hch : ChamberInvII) : CV.hyp_R := by
  intro n _ hn E e f g h3 h4e h4f h4g hE tp tm hp hm
  obtain ⟨δ, hδ, hδr, hD⟩ := hnear n hn E e f g h3 h4e h4f h4g hE
  have hr := E.radius_pos
  have hτ0 : 0 < δ / 2 := by positivity
  have hτδ : δ / 2 < δ := by linarith
  have hτr : δ / 2 < E.radius := by linarith
  let tp' : E.Parameter := ⟨δ / 2, by constructor <;> linarith⟩
  let tm' : E.Parameter := ⟨-(δ / 2), by constructor <;> linarith⟩
  have hp' : Punctured E δ tp' := ⟨hτ0.ne', by show |δ / 2| < δ; rw [abs_of_pos hτ0]; exact hτδ⟩
  have hm' : Punctured E δ tm' :=
    ⟨neg_ne_zero.mpr hτ0.ne', by show |-(δ / 2)| < δ; rw [abs_neg, abs_of_pos hτ0]; exact hτδ⟩
  have hop : OppositeSides E tp' tm' := by
    show δ / 2 * -(δ / 2) < 0
    nlinarith
  have hnear' := hD.near tp' tm' hp' hm' hop
  have h1 : E.curve tp ∈ chamber (E.curve tp') := by
    have a := E.curve_mem_sideChamber_pos tp hp
    have b := E.curve_mem_sideChamber_pos tp' hτ0
    unfold CV.Event.sideChamber at a b
    rw [chamber_eq_of_mem b]
    exact a
  have h2 : E.curve tm ∈ chamber (E.curve tm') := by
    have a := E.curve_mem_sideChamber_neg tm hm
    have b := E.curve_mem_sideChamber_neg tm' (by show -(δ / 2) < 0; linarith)
    unfold CV.Event.sideChamber at a b
    rw [chamber_eq_of_mem b]
    exact a
  calc X1 hn (E.curve tp) (E.generic_punctured tp hp.ne')
      = X1 hn (E.curve tp') (genericAt E tp' hp'.1) :=
        (hch n hn _ _ (genericAt E tp' hp'.1) (E.generic_punctured tp hp.ne') h1).symm
    _ = X1 hn (E.curve tm') (genericAt E tm' hm'.1) := hnear'
    _ = X1 hn (E.curve tm) (E.generic_punctured tm hm.ne) :=
        hch n hn _ _ (genericAt E tm' hm'.1) (E.generic_punctured tm hm.ne) h2

/-- **How `Bridge.sm_R` consumes `RProof.cv_R`** (BRIDGE.md §3, (19)–(21); DECISION_FINAL.md R6/R7): with
Bridge:B4's pointwise dictionary `X₁ = C` on SM-generic polygons (BRIDGE.md (17)), `CV.hyp_R` at the CV
event `Bridge.eventOfTriple hn g h` of an SM simple triple germ (Bridge:B1–B3, `isSimpleRIII_eventOfTriple`)
gives the printed SM hyp:R "At every simple triple wall, `C(P₊) = C(P₋)`" (sm-4-knotlaws.tex:1149–1150), here
at every side parameter `t`. The germ is named by its increasing representatives (`exists_sorted_tripleAt`),
which does not change the event. This is the shape of `Bridge.sm_R`, not the fixed row itself. -/
theorem smR_shape_of_hyp_R (hcv : CV.hyp_R)
    (hB4 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P),
      X1 hn P (generic_of_sm hn hP) = cornerStateSum hn hP) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
      ∀ t : g.SideParameter,
        cornerStateSum hn (g.sideTuple true t).2 = cornerStateSum hn (g.sideTuple false t).2 := by
  intro n _ hn g e f k h t
  obtain ⟨e', f', k', -, hef, hfk, h'⟩ := Bridge.exists_sorted_tripleAt g h
  have hE := isSimpleRIII_eventOfTriple hn g h' hef hfk
  have hp : 0 < (g.sideTime true t).val := by
    show 0 < (if (true : Bool) = true then _ else _ : g.Parameter).val
    simp only [ite_true]
    exact t.2.1
  have hm : (g.sideTime false t).val < 0 := by
    show (if (false : Bool) = true then _ else _ : g.Parameter).val < 0
    simp only [Bool.false_eq_true, ite_false]
    exact neg_neg_iff_pos.mpr t.2.1
  have key := hcv n hn (Bridge.eventOfTriple hn g h') e' f' k' _ _ _ _ hE
    (g.sideTime true t) (g.sideTime false t) hp hm
  exact (hB4 n hn _ (g.sideTuple true t).2).symm.trans
    (key.trans (hB4 n hn _ (g.sideTuple false t).2))

end RProof
