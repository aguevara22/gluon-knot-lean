import CV.CarrierWord
import CV.RecordHomfly
import SM.GeoPositiveLift


/-! Ported 2026-09-14 04:34Z from work/drafts/cvdom/U7c/CVPieceCurve.lean (CV-DOM unit U7c, report work/drafts/cvdom/U7c/REPORT.md; DECISION_FINAL.md §5/§7): rows CV:def:piecediagram (142, `CV.piecediagram_definition`, bundle PieceDiagramData) and CV:lem:piececurve (143, `CV.piececurve`, bundle PieceCurveData). Only this header added. -/
/-! Repaired 2026-09-14 (unit U7c-fix, report work/drafts/cvdom/U7c-fix/REPORT.md), row 143 only: the
review of `CV.piececurve` (NOT FAITHFUL, two refuters) found that the printed last sentence "the datum of
Definition def:piecediagram is the datum of `C_H`" (d1:608–609) names a word TOGETHER WITH a rotation
system (d1:577–585; proof d1:664–666) and that `PieceCurveData` rendered only the word. `PieceCurveData`
now has the field `rotation_system` (the second half of the datum) and its field `realizable` is a
crossing-point-preserving bijection instead of a bare `Nonempty (_ ≃ _)`; the supporting lemmas
`cornerPolygon_edge_of_crossingPoint_mem`, `pieceShadow_strand_dir`, `pieceShadow_rotationSystem`,
`pieceShadowCrossingEquiv_crossingPoint` are new (§6). Every other declaration of the module — in
particular row 142 (`PieceDiagramData`, `piecediagram_definition`) and everything `CV/X1.lean` uses — is
byte-identical to the 04:34Z port. -/
/-! # CV:lem:piececurve (row 143) and CV:def:piecediagram (row 142) on the accepted geo carrier layer

CV-DOM unit **U7c** (work/drafts/cvdom/DECISION_FINAL.md §0 option (C), §2 fidelity and the three
documented readings, §3 rulings R1–R5, §4 review-note template, §5 row U7c). Intended home:
`work/lean/CV/PieceCurve.lean`. Row 146 (CV:def:X1) is the companion module `CV/X1.lean`.

## Review note (DECISION_FINAL §4, filled in)

Stated on the printed binder `hD : CV.Diagrammatic P` (d1_setup.tex:565 "For a diagrammatic parent
`P`", 592–593 "Let `P` be diagrammatic"); no domain change (CV-DOM decision, AUTHOR_NOTES 2026-09-14).
The carriers, their marks, corners, corner polygons, turns and retained crossings are the accepted
`SM.GeoCarrier` objects (def:flat-carriers, SM/FlatCarriersDefs.lean) read through
`hD.crossingGeometry`; `Ind(G_P)` is the accepted `CV.Ind` (CV:def:interlace). On SM-generic polygons
these are the accepted def:smoothing / lem:carriers objects by `geoSmoothingSuccessor_eq_generic`,
`geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic` (FlatCarriersDefs.lean:638–724). The
ownership of the two visits of a selected crossing follows SM conv:selected-visits (the same
`selectedMarkPerm`), a disambiguation the CV text leaves implicit. The reviewer checks: same binder as
printed, same quantifiers, each printed sentence = one bundle field, and that the `geo*` object named
in each field is the one the sentence describes.

**def:piecediagram (additional sentence, §4):** "`CV.pieceDiagram H` is the positive lift
(`Shadow.positiveDiagram`, divide convention = `Diagram.IsPositive`, LinkDiagram.lean:547) of the piece
curve `C_H` of lem:piececurve (d1:602–611: 'the construction and not a description of its result');
'erasing' a double point is realised as smoothing it into the carrier of `S ∪ K_H`, whose Gauss word
is the parent word restricted to `H` (lem:piececurve's conclusion)."

**Reading (ii) (DECISION_FINAL §2, verbatim):** "(ii) def:piecediagram's 'parent curve with every
double point outside `H` erased' is the datum (restricted word + rotation system, d1:580–590) realised
by the piece curve `C_H` of lem:piececurve, so `CV.pieceDiagram H` is the positive lift (divide
convention = `Diagram.IsPositive`) of the carrier of `S ∪ K_H` that carries `H`".

**Reading (iii) (DECISION_FINAL §2, verbatim):** "(iii) `hn : 3 ≤ n` is carried where the geo lemmas
need it (CV fixes `n ≥ 3` globally, d1:932)". Here: the piece curve, its support `K_H` and its carrier
are `hn`-free (pure combinatorics of the geo layer); `hn` enters the *geometric* clauses (regular
corner polygon, generic shadow, self-intersections, the positive lift) through U2b/U2c/U4's
`three_le_geoCornerCount hn`, `geoCornerPolygon_regular hn`, `geo_self_intersections hn`,
`geoPositiveLift hn`, exactly as §5's shapes `CV.piececurve (hn) …`, `CV.piecediagram_definition (hn) …`
prescribe.

## The construction (lem:piececurve, d1:592–611, and its proof, 612–690)

The printed route: (1) smooth every crossing of `S` — of `S` only — so that the curve falls into the
`|S|+1` carriers of `S`; (2) take the one carrier that carries `H` (unique by lem:carriers (iv));
(3) apply Step 5's iteration: while the current carrier of `H` has a double point `d` outside `H`,
smooth `d` and keep the daughter curve that carries `H`. Step 5 shows the kept daughter is well
defined: `d` interlaces no member of `H` (Step 4: `H` is a connected component of `G_P[U(S)]`, so an
undominated crossing interlacing a member of `H` lies in `H`) and `H` is connected, so all of `H`
falls onto one of the two daughters. The counter-example word `d a a d b b` with `K = {a, b}` (d1:668)
shows the connectedness hypothesis is used.

On the geo layer (cv-lane plan §143 (2), Gap G4): the crossings smoothed by the iteration form a set
`K` with the **invariant** `StepInvariant`: `K ⊆ U(S)`, `K ∩ H = ∅`, `S ∪ K ∈ Ind(G_P)`. Under it
(§1–§2 below) every label of `H` is undominated at `S ∪ K` (`pieceLabels_subset_U_union`, Step 4)
and hence all visits of all labels of `H` lie on ONE carrier of `S ∪ K` (`exists_unique_piece_owner_of_subset`,
the connectivity induction of lem:carriers (iv) run at `S ∪ K` along the walks of `G_P[U(S)]` inside
`H`) — this is "keeping the daughter curve that carries `H`, which Step 5 shows is well defined".
A step (§3, `StepInvariant.insert`) smooths a double point `d` of that carrier outside `H`: `d` is
unselected and interlaces nothing selected (`geoCarrierCrossings_subset_U`), so `S ∪ insert d K` is
independent (`geoIndependent_insert_unselected`), `d ∈ U(S)` and `d ∉ H`. The iteration is a
well-founded recursion (`exists_pieceSupport_aux`, strong induction on the number of unselected
crossings `|[m] ∖ (S ∪ K)|`, which drops by one at every step — the printed measure "each step removes
at least one double point outside `K`" is bounded by it); it stops when the carrier of `H` has no
double point outside `H`, i.e. `geoCarrierCrossings (S ∪ K) q ⊆ H`, and then equality holds because
every label of `H` is an unselected crossing both of whose visits lie on `q`.

The piece curve `C_H` is the corner polygon `geoCornerPolygon (S ∪ K_H) q_H` of the terminal carrier
(`pieceCurve`), a regular closed polygon (U2b) whose self-intersections are exactly the crossing points
of `H` (U2c) and whose one-component shadow is generic (U4); `K_H`, `q_H` are fixed once by
`Classical.choose` from the existence theorem (§5 U7c: "`CV.pieceSupport`, `CV.pieceCarrier`
(Classical.choose)"). The choice of the double point smoothed at each step is the printed proof's own
free choice ("If `C` has a double point `d` outside `K`, smooth it"), so the terminal datum is
determined only up to that choice in the text as well; every admissible terminal `K` yields a curve
with double points exactly `H` and Gauss word the parent word restricted to `H`.

## The datum of def:piecediagram, both halves (row 143, last printed sentence; U7c-fix)

def:piecediagram (d1:577–585) fixes what "erased" means: the evaluator "builds a piece's datum as the
parent Gauss word restricted to the crossings of `H`, in the parent's cyclic order, together with the
parent's per-crossing counter-clockwise half-edge order restricted to the surviving half-edges … So the
datum is a word *together with a rotation system*, not a bare word". lem:piececurve ends (d1:608–609)
"In particular that restricted word is realizable, and the datum of Definition def:piecediagram is the
datum of `C_H`", and its proof closes (d1:664–666) "Its rotation system at each surviving crossing is the
carrier's, which is the parent's, since smoothing at other points does not disturb the half-edge order at
a survivor; that is the second half of the datum." The clause map of `PieceCurveData` for this sentence:

* **first half, the word — `realizable`:** `∃ e : (pieceShadow …).Crossing ≃ {c // c ∈ H}, ∀ x,
  crossingPoint x = crossingPoint (e x)` — the double points of the actual closed curve `C_H` are the
  crossings of `H`, each sitting at the parent's crossing point (not merely a cardinality statement:
  the bijection is the one that identifies the double point of `C_H` with the parent crossing it *is*);
  together with `gauss_word` this is "that restricted word is realizable". Proof:
  `pieceShadowCrossingEquiv` (U4 `geoCarrierCrossingEquiv` ∘ `pieceCarrier_geoCarrierCrossings`) and
  `pieceShadowCrossingEquiv_crossingPoint` (U4 `crossingPoint_geoCarrierCrossingEquiv`).
* **second half, the rotation system — `rotation_system`:** for every surviving crossing `c ∈ H` and
  every double point `x` of the shadow of `C_H` at `crossingPoint c`, a bijection
  `e : {s // s ∈ x.val} ≃ {i // i ∈ c.val}` between the two strands of `C_H` through `x` and the two
  parent edges of `c` with `dir s = t • edge P (e s)`, `t > 0`: each strand of `C_H` at the survivor is
  directed along the parent edge it survives from. The four half-edges of `C_H` at `x` (the two
  strands, each entering and leaving `x`) are therefore the parent's four half-edges at `c` with the
  same directions, so their counter-clockwise order is the parent's — "the carrier's, which is the
  parent's" — restricted to `H`. Proof (`pieceShadow_rotationSystem`): U2b `geoCornerPolygon_edge_smul`
  (every edge of the corner polygon is a positive multiple of the parent edge of its block), the block
  parametrisation `geo_edgeSegment_param` and U2c `geo_carrier_crossingPoint_parameters` (a carrier
  passes through `crossingPoint c` exactly at the visits of `c`), `GeoBlockInterior.visit_edge` (an
  interior block mark lies on the block's parent edge) and `geo_carrier_selfIntersection_not_corner`
  (no crossing point is a corner) give `cornerPolygon_edge_of_crossingPoint_mem`; injectivity of
  strand ↦ edge is U4's transversality `pieceShadow_generic.transverse` (two strands along one parent
  edge would be parallel), and the two-element counts make it a bijection.

## Tiers

§1–§5 (the support, the carrier, the words) are tier 0 (`hP : CrossingGeometry P`); the geometric
realisation §6 and the piece diagram §8 are tier 1 (`CarrierGeometry.ofDiagrammatic hD`, ruling R4)
through U2b/U2c/U4. No tier-2 fact (`WeakGeneric`) is used anywhere: the rows stay on the printed
`Diagrammatic` binder.

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U7c/CVPieceCurve.lean` (04:34Z port) and, for the
U7c-fix repair of row 143, `cd work/lean && lake env lean ../drafts/cvdom/U7c-fix/PieceCurve.lean`. -/

namespace CV

open SM SM.Carrier SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 1. Step 4: an undominated crossing interlacing a member of `H` lies in `H` -/

section StepFour

variable (hP : CrossingGeometry P) {S : Finset (Crossing P)}

/-- `U(·)` is antitone: enlarging the selected set can only dominate more crossings. -/
theorem U_subset_of_subset {T : Finset (Crossing P)} (hST : S ⊆ T) : U hP T ⊆ U hP S := by
  intro c hc
  rw [mem_U_iff] at hc ⊢
  exact ⟨fun h => hc.1 (hST h), fun x hx => hc.2 x (hST hx)⟩

/-- **Step 4** (d1:633–636): "`H` is a connected component of `G_P[U(S)]`, so an undominated crossing
interlacing a member of `H` lies in `H`." -/
theorem mem_pieceLabels_of_interlaces (H : Piece hP S) {c d : Crossing P}
    (hc : c ∈ pieceLabels hP S H) (hd : d ∈ U hP S) (hI : GeometricInterlaces hP c d) :
    d ∈ pieceLabels hP S H := by
  obtain ⟨hcU, hH⟩ := (mem_pieceLabels hP S H c).mp hc
  refine (mem_pieceLabels hP S H d).mpr ⟨hd, ?_⟩
  have hadj : (residualGraph hP S).Adj ⟨c, hcU⟩ ⟨d, hd⟩ := hI
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hH

/-- The labels of `H` stay undominated after smoothing any set `K ⊆ U(S)` disjoint from `H`: a label
of `H` is neither in `S` nor in `K`, interlaces nothing in `S` (it is in `U(S)`) and interlaces nothing
in `K` (Step 4: it would pull that element of `K` into `H`). -/
theorem pieceLabels_subset_U_union (H : Piece hP S) {K : Finset (Crossing P)}
    (hKU : K ⊆ U hP S) (hKH : Disjoint K (pieceLabels hP S H)) :
    pieceLabels hP S H ⊆ U hP (S ∪ K) := by
  intro c hc
  have hcU : c ∈ U hP S := pieceLabels_subset hP S H hc
  rw [mem_U_iff] at hcU ⊢
  refine ⟨fun h => ?_, fun x hx hI => ?_⟩
  · rcases Finset.mem_union.mp h with h | h
    · exact hcU.1 h
    · exact Finset.disjoint_left.mp hKH h hc
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact hcU.2 x hx hI
    · exact Finset.disjoint_left.mp hKH hx (mem_pieceLabels_of_interlaces hP H hc (hKU hx) hI)

end StepFour

/-! ## 2. The carrier of `H` at any refinement `T ⊇ S` keeping `H` undominated (Step 5's
"well defined")

The connectivity induction of lem:carriers (iv) (CV/CarriersLemma.lean §3, gap G3) run at `T`: the
walks of `G_P[U(S)]` between two labels of `H` stay inside `H` (every vertex of a walk from a vertex
of `H` is reachable from it), each edge is an interlacing of two crossings undominated at `T`, and
lem:carriers (ii)+(iii) at `T` (`owner_eq_of_interlaces_mem_U`) identify the owners along it. -/

section PieceOwnerAt

variable (hP : CrossingGeometry P) {S : Finset (Crossing P)}

/-- Along a walk of `G_P[U(S)]` starting in `H`, all visits of all vertices have one owner at `T`,
provided `T ∈ Ind(G_P)` and every label of `H` is undominated at `T`. -/
theorem owner_eq_of_walk_of_subset {T : Finset (Crossing P)} (hT : T ∈ Ind hP) (H : Piece hP S)
    (hHU : pieceLabels hP S H ⊆ U hP T) {x y : (↑(U hP S) : Set (Crossing P))}
    (p : (residualGraph hP S).Walk x y) :
    pieceOf hP S x.1 x.2 = H → ∀ v w : Visit P, v.1 = x.1 → w.1 = y.1 →
      geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr w) := by
  induction p with
  | @nil a =>
    intro hx v w hv hw
    have haH : a.1 ∈ pieceLabels hP S H := (mem_pieceLabels hP S H a.1).mpr ⟨a.2, hx⟩
    exact owner_eq_of_mem_U hP hT (hHU haH) v w hv hw
  | @cons a b _ hab _ ih =>
    intro hx v w hv hw
    have haH : a.1 ∈ pieceLabels hP S H := (mem_pieceLabels hP S H a.1).mpr ⟨a.2, hx⟩
    have hbH : pieceOf hP S b.1 b.2 = H :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab).symm.trans hx
    have hbH' : b.1 ∈ pieceLabels hP S H := (mem_pieceLabels hP S H b.1).mpr ⟨b.2, hbH⟩
    obtain ⟨i, -, -⟩ := crossing_visits_exist b.1
    have hI : GeometricInterlaces hP a.1 b.1 := hab
    calc geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr ⟨b.1, i⟩) :=
          owner_eq_of_interlaces_mem_U hP hT (hHU haH) (hHU hbH') hI v ⟨b.1, i⟩ hv rfl
      _ = geoOwner hP T (Sum.inr w) := ih hbH ⟨b.1, i⟩ w rfl hw

/-- **Step 5, "well defined"** (d1:640–650, "Connectedness of `K` therefore forces all of `K` into one
arc, hence onto one of the two curves"; d1:606–608 "`H` lies on one carrier before the iteration begins,
and each subsequent step preserves that"): at every `T ∈ Ind(G_P)` keeping the labels of `H`
undominated there is exactly one carrier of `T` on which both occurrences of every `c ∈ H` lie. -/
theorem exists_unique_piece_owner_of_subset {T : Finset (Crossing P)} (hT : T ∈ Ind hP)
    (H : Piece hP S) (hHU : pieceLabels hP S H ⊆ U hP T) :
    ∃! q : GeoComponent hP T, ∀ c ∈ pieceLabels hP S H, ∀ v : Visit P, v.1 = c →
      geoOwner hP T (Sum.inr v) = q := by
  obtain ⟨c₀, hc₀⟩ := pieceLabels_nonempty hP S H
  obtain ⟨hc₀U, hH₀⟩ := (mem_pieceLabels hP S H c₀).mp hc₀
  obtain ⟨i, -, -⟩ := crossing_visits_exist c₀
  refine ⟨geoOwner hP T (Sum.inr ⟨c₀, i⟩), ?_, ?_⟩
  · intro c hc v hv
    obtain ⟨hcU, hH⟩ := (mem_pieceLabels hP S H c).mp hc
    have hr : (residualGraph hP S).Reachable ⟨c, hcU⟩ ⟨c₀, hc₀U⟩ :=
      SimpleGraph.ConnectedComponent.eq.mp (hH.trans hH₀.symm)
    exact hr.elim fun p => owner_eq_of_walk_of_subset hP hT H hHU p hH v ⟨c₀, i⟩ hv rfl
  · intro q hq
    exact (hq c₀ hc₀ ⟨c₀, i⟩ rfl).symm

end PieceOwnerAt

/-! ## 3. The iteration: invariant, one step, termination (Gap G4) -/

section Iteration

variable (hP : CrossingGeometry P) (S : Finset (Crossing P)) (H : Piece hP S)

/-- The invariant of Step 5's iteration for the set `K` of double points smoothed so far (beyond `S`):
"smoothing at each step one double point outside `H`" of the current carrier — every smoothed point is
undominated with respect to `S` and outside `H`, and the smoothed set stays independent (cv-lane plan
§143 (2): invariants (a) `S ∪ K` independent, (b)–(c) follow, §2 and `geoCarrierCrossings_subset_U`). -/
structure StepInvariant (K : Finset (Crossing P)) : Prop where
  /-- every smoothed double point is undominated: `K ⊆ U(S)` -/
  subset_U : K ⊆ U hP S
  /-- every smoothed double point is outside `H` -/
  disjoint : Disjoint K (pieceLabels hP S H)
  /-- the smoothed set `S ∪ K` is independent: the daughters are carriers of `S ∪ K` -/
  indep : S ∪ K ∈ Ind hP

variable {hP S H}

/-- The start of the iteration: nothing smoothed beyond `S` ("The route above smooths nothing but `S`"). -/
theorem StepInvariant.empty (hS : S ∈ Ind hP) : StepInvariant hP S H ∅ where
  subset_U := Finset.empty_subset _
  disjoint := Finset.disjoint_empty_left _
  indep := by rw [Finset.union_empty]; exact hS

/-- Under the invariant the labels of `H` are undominated at `S ∪ K` (Step 4). -/
theorem StepInvariant.pieceLabels_subset_U {K : Finset (Crossing P)} (hK : StepInvariant hP S H K) :
    pieceLabels hP S H ⊆ U hP (S ∪ K) :=
  pieceLabels_subset_U_union hP H hK.subset_U hK.disjoint

/-- Under the invariant the carrier of `H` at `S ∪ K` is well defined (§2). -/
theorem StepInvariant.exists_unique_owner {K : Finset (Crossing P)}
    (hK : StepInvariant hP S H K) :
    ∃! q : GeoComponent hP (S ∪ K), ∀ c ∈ pieceLabels hP S H, ∀ v : Visit P, v.1 = c →
      geoOwner hP (S ∪ K) (Sum.inr v) = q :=
  exists_unique_piece_owner_of_subset hP hK.indep H hK.pieceLabels_subset_U

/-- **One step of the iteration** (d1:640–650): a double point `d` of a carrier `q` of `S ∪ K` outside
`H` may be smoothed: `d` is unselected and interlaces nothing selected (Step 1–2, `geoCarrierCrossings_subset_U`),
so `S ∪ insert d K` is independent; `d ∈ U(S)` and `d ∉ H`. "The hypotheses persist." -/
theorem StepInvariant.insert {K : Finset (Crossing P)} (hK : StepInvariant hP S H K)
    {q : GeoComponent hP (S ∪ K)} {d : Crossing P} (hd : d ∈ geoCarrierCrossings hP (S ∪ K) q)
    (hdH : d ∉ pieceLabels hP S H) : StepInvariant hP S H (insert d K) := by
  have hT' : GeoIndependent hP (S ∪ K) := geoIndependent_of_mem_Ind hP hK.indep
  have hdU : d ∈ geoSupportUnselected hP (S ∪ K) := geoCarrierCrossings_subset_U hP hT' q hd
  have hdUS : d ∈ U hP S :=
    U_subset_of_subset hP Finset.subset_union_left
      ((mem_U_iff hP (S ∪ K) d).mpr ((mem_geoSupportUnselected_iff hP (S ∪ K) d).mp hdU))
  exact
    { subset_U := Finset.insert_subset hdUS hK.subset_U
      disjoint := Finset.disjoint_insert_left.mpr ⟨hdH, hK.disjoint⟩
      indep := by
        rw [Finset.union_insert]
        exact (mem_Ind_iff_geoIndependent hP _).mpr (geoIndependent_insert_unselected hP hT' hdU) }

/-- The measure: a step strictly decreases the number of unselected crossings `|[m] ∖ (S ∪ K)|`
("Each step removes at least one double point outside `K`, so after finitely many steps …"). -/
theorem card_compl_insert_lt {K : Finset (Crossing P)} (hK : StepInvariant hP S H K)
    {q : GeoComponent hP (S ∪ K)} {d : Crossing P} (hd : d ∈ geoCarrierCrossings hP (S ∪ K) q) :
    (Finset.univ \ (S ∪ insert d K)).card < (Finset.univ \ (S ∪ K)).card := by
  have hT' : GeoIndependent hP (S ∪ K) := geoIndependent_of_mem_Ind hP hK.indep
  have hdT : d ∉ S ∪ K :=
    ((mem_geoSupportUnselected hP (S ∪ K) d).mp (geoCarrierCrossings_subset_U hP hT' q hd)).1
  rw [Finset.union_insert]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨d, Finset.mem_sdiff.mpr ⟨Finset.mem_univ d, hdT⟩,
      fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self d _)⟩
  · intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hx.1, fun h => hx.2 (Finset.mem_insert_of_mem h)⟩

/-- **Step 5's iteration, run to the end** (d1:638–655): from any admissible `K` there is an admissible
`K' ⊇ K` whose carrier of `H` has double points exactly `H`. Strong induction on the number of
unselected crossings. -/
theorem exists_pieceSupport_aux (m : ℕ) :
    ∀ K : Finset (Crossing P), (Finset.univ \ (S ∪ K)).card = m → StepInvariant hP S H K →
      ∃ (K' : Finset (Crossing P)) (_ : StepInvariant hP S H K') (q : GeoComponent hP (S ∪ K')),
        K ⊆ K' ∧ geoCarrierCrossings hP (S ∪ K') q = pieceLabels hP S H ∧
        (∀ c ∈ pieceLabels hP S H, ∀ v : Visit P, v.1 = c →
          geoOwner hP (S ∪ K') (Sum.inr v) = q) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro K hm hK
  obtain ⟨q, hq, -⟩ := hK.exists_unique_owner
  by_cases hsub : geoCarrierCrossings hP (S ∪ K) q ⊆ pieceLabels hP S H
  · -- the carrier of `H` has no double point outside `H`: stop
    refine ⟨K, hK, q, Finset.Subset.refl K, Finset.Subset.antisymm hsub ?_, hq⟩
    intro c hc
    rw [mem_geoCarrierCrossings]
    exact ⟨((mem_U_iff hP (S ∪ K) c).mp (hK.pieceLabels_subset_U hc)).1, hq c hc⟩
  · -- "If `C` has a double point `d` outside `K`, smooth it"
    obtain ⟨d, hdq, hdH⟩ := Finset.not_subset.mp hsub
    obtain ⟨K', hK', q', hKK', hcr, hown⟩ :=
      ih _ (hm ▸ card_compl_insert_lt hK hdq) (insert d K) rfl (hK.insert hdq hdH)
    exact ⟨K', hK', q', (Finset.subset_insert d K).trans hKK', hcr, hown⟩

end Iteration

/-! ## 4. The existence theorem behind lem:piececurve (§5 U7c's shape for row 143) -/

section Existence

variable (hP : CrossingGeometry P) {S : Finset (Crossing P)}

/-- **The piece curve exists** (§5 U7c, row 143's existential): an independent set `K` of undominated
crossings outside `H` such that the carrier `q` of `S ∪ K` owning `H` has double points exactly `H`,
with the inherited cyclic order (lem:carrierword). Tier 0. -/
theorem exists_pieceSupport (hS : S ∈ Ind hP) (H : Piece hP S) :
    ∃ (K : Finset (Crossing P)) (_ : S ∪ K ∈ Ind hP) (q : GeoComponent hP (S ∪ K)),
      Disjoint K (pieceLabels hP S H) ∧ K ⊆ U hP S ∧
      geoCarrierCrossings hP (S ∪ K) q = pieceLabels hP S H ∧
      (∀ c ∈ pieceLabels hP S H, ∀ v : Visit P, v.1 = c → geoOwner hP (S ∪ K) (Sum.inr v) = q) ∧
      GeoInheritsMarkOrder hP (S ∪ K) := by
  obtain ⟨K, hK, q, -, hcr, hown⟩ :=
    exists_pieceSupport_aux (hP := hP) (S := S) (H := H) _ ∅ rfl (StepInvariant.empty hS)
  exact ⟨K, hK.indep, q, hK.disjoint, hK.subset_U, hcr, hown, carrierword_inherits_order hP hK.indep⟩

end Existence

/-! ## 5. The piece support `K_H`, the piece carrier `q_H`, the piece curve `C_H` -/

section PieceCurveDefs

variable (hD : Diagrammatic P) {S : Finset (Crossing P)} (hS : S ∈ Ind hD.crossingGeometry)
  (H : Piece hD.crossingGeometry S)

/-- **`K_H`**: the double points smoothed by Step 5's iteration beyond `S` (fixed once by
`Classical.choose` from `exists_pieceSupport`; §5 U7c "`CV.pieceSupport` (Classical.choose)"). -/
noncomputable def pieceSupport : Finset (Crossing P) :=
  Classical.choose (exists_pieceSupport hD.crossingGeometry hS H)

theorem pieceSupport_spec :
    ∃ (_ : S ∪ pieceSupport hD hS H ∈ Ind hD.crossingGeometry)
      (q : GeoComponent hD.crossingGeometry (S ∪ pieceSupport hD hS H)),
      Disjoint (pieceSupport hD hS H) (pieceLabels hD.crossingGeometry S H) ∧
      pieceSupport hD hS H ⊆ U hD.crossingGeometry S ∧
      geoCarrierCrossings hD.crossingGeometry (S ∪ pieceSupport hD hS H) q =
        pieceLabels hD.crossingGeometry S H ∧
      (∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
        geoOwner hD.crossingGeometry (S ∪ pieceSupport hD hS H) (Sum.inr v) = q) ∧
      GeoInheritsMarkOrder hD.crossingGeometry (S ∪ pieceSupport hD hS H) :=
  Classical.choose_spec (exists_pieceSupport hD.crossingGeometry hS H)

/-- `S ∪ K_H ∈ Ind(G_P)`. -/
theorem pieceSupport_mem_Ind : S ∪ pieceSupport hD hS H ∈ Ind hD.crossingGeometry :=
  (pieceSupport_spec hD hS H).fst

/-- `S ∪ K_H` is independent in the geo lane's form (ruling R2). -/
theorem pieceSupport_geoIndependent : GeoIndependent hD.crossingGeometry (S ∪ pieceSupport hD hS H) :=
  geoIndependent_of_mem_Ind hD.crossingGeometry (pieceSupport_mem_Ind hD hS H)

/-- **`q_H`**: the carrier of `S ∪ K_H` that carries `H` — the piece curve as a carrier. -/
noncomputable def pieceCarrier : GeoComponent hD.crossingGeometry (S ∪ pieceSupport hD hS H) :=
  Classical.choose (pieceSupport_spec hD hS H).snd

theorem pieceCarrier_spec :
    Disjoint (pieceSupport hD hS H) (pieceLabels hD.crossingGeometry S H) ∧
    pieceSupport hD hS H ⊆ U hD.crossingGeometry S ∧
    geoCarrierCrossings hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) =
      pieceLabels hD.crossingGeometry S H ∧
    (∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
      geoOwner hD.crossingGeometry (S ∪ pieceSupport hD hS H) (Sum.inr v) = pieceCarrier hD hS H) ∧
    GeoInheritsMarkOrder hD.crossingGeometry (S ∪ pieceSupport hD hS H) :=
  Classical.choose_spec (pieceSupport_spec hD hS H).snd

/-- `K_H ∩ H = ∅`: the iteration smooths only double points outside `H`. -/
theorem pieceSupport_disjoint :
    Disjoint (pieceSupport hD hS H) (pieceLabels hD.crossingGeometry S H) :=
  (pieceCarrier_spec hD hS H).1

/-- `K_H ⊆ U(S)`: the iteration smooths only undominated crossings. -/
theorem pieceSupport_subset_U : pieceSupport hD hS H ⊆ U hD.crossingGeometry S :=
  (pieceCarrier_spec hD hS H).2.1

/-- The invariant holds at the terminal support. -/
theorem pieceSupport_stepInvariant : StepInvariant hD.crossingGeometry S H (pieceSupport hD hS H) :=
  ⟨pieceSupport_subset_U hD hS H, pieceSupport_disjoint hD hS H, pieceSupport_mem_Ind hD hS H⟩

/-- **The double points of `C_H` are exactly the crossings of `H`** (combinatorial form): the
crossings of the carrier `q_H` (def:smoothing; lem:carriers (iii)) are the labels of `H`. -/
theorem pieceCarrier_geoCarrierCrossings :
    geoCarrierCrossings hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) =
      pieceLabels hD.crossingGeometry S H :=
  (pieceCarrier_spec hD hS H).2.2.1

/-- `q_H` carries `H`: both occurrences of every `c ∈ H` lie on `q_H`. -/
theorem pieceCarrier_owns :
    ∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
      geoOwner hD.crossingGeometry (S ∪ pieceSupport hD hS H) (Sum.inr v) = pieceCarrier hD hS H :=
  (pieceCarrier_spec hD hS H).2.2.2.1

/-- `q_H` is THE carrier of `H` at `S ∪ K_H` (uniqueness of Step 5's "well defined"). -/
theorem pieceCarrier_unique (q : GeoComponent hD.crossingGeometry (S ∪ pieceSupport hD hS H))
    (hq : ∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
      geoOwner hD.crossingGeometry (S ∪ pieceSupport hD hS H) (Sum.inr v) = q) :
    q = pieceCarrier hD hS H :=
  (pieceSupport_stepInvariant hD hS H).exists_unique_owner.unique hq (pieceCarrier_owns hD hS H)

/-- The carriers of `S ∪ K_H` inherit the cyclic order of `Γ` (lem:carrierword at `S ∪ K_H`). -/
theorem pieceSupport_inheritsMarkOrder :
    GeoInheritsMarkOrder hD.crossingGeometry (S ∪ pieceSupport hD hS H) :=
  (pieceCarrier_spec hD hS H).2.2.2.2

/-- `q_H` traverses its traversal word (lem:carrierword clause 2 at `S ∪ K_H`). -/
theorem pieceCarrier_traced :
    TracedSuccessor hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) :=
  carrierword_traced hD.crossingGeometry (pieceSupport_mem_Ind hD hS H) (pieceCarrier hD hS H)

/-- **The Gauss word of `C_H` is the parent word restricted to `H` in the parent's cyclic order**: the
double-point subword of the traversal word of `q_H` (its visits of crossings of `H`, in the order `q_H`
traverses them) is `P`'s Gauss word (`geometricGaussList`, CV:def:gauss on the geometric domain)
restricted to the visits of `H`. -/
theorem pieceCarrier_gaussWord :
    (carrierGaussList hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H)).filter
        (fun v : Visit P => decide (v.1 ∈ pieceLabels hD.crossingGeometry S H)) =
      (geometricGaussList hD.crossingGeometry).filter
        (fun v : Visit P => decide (v.1 ∈ pieceLabels hD.crossingGeometry S H)) := by
  rw [carrierGaussList_eq_filter, List.filter_filter]
  apply List.filter_congr
  intro v _
  by_cases hv : v.1 ∈ pieceLabels hD.crossingGeometry S H
  · simp [hv, pieceCarrier_owns hD hS H v.1 hv v rfl]
  · simp [hv]

/-- **`C_H`**, the piece curve: the corner polygon of the carrier `q_H` of `S ∪ K_H` — the closed plane
curve that the printed route constructs. -/
noncomputable def pieceCurve :
    LabelledTuple (geoCornerCount hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H)) :=
  geoCornerPolygon hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H)

end PieceCurveDefs

/-! ## 6. `C_H` as a closed plane curve (tier 1, through U2b/U2c/U4) -/

section PieceCurveGeometry

variable (hn : 3 ≤ n) (hD : Diagrammatic P) {S : Finset (Crossing P)}
  (hS : S ∈ Ind hD.crossingGeometry) (H : Piece hD.crossingGeometry S)

include hn in
/-- `C_H` is a regular closed polygon (U2b `geoCornerPolygon_regular`, tier 1). -/
theorem pieceCurve_regular : SM.Regular (pieceCurve hD hS H) :=
  geoCornerPolygon_regular hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H)
    (pieceCarrier hD hS H)

include hn in
/-- `C_H` is a regular closed polygon in CV's sense (CV:def:regular, through `regular_iff_sm`). -/
theorem pieceCurve_cvRegular : CV.Regular (pieceCurve hD hS H) :=
  (regular_iff_sm _).mpr (pieceCurve_regular hn hD hS H)

/-- The one-component shadow of `C_H` (U4 `geoCarrierShadow`). -/
noncomputable abbrev pieceShadow : Shadow :=
  geoCarrierShadow hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H)
    (pieceCarrier hD hS H)

/-- `C_H` is a closed plane curve with finitely many transverse double points and no triple point
(the shadow is generic; U4 `geoCarrierShadow_generic`, tier 1). -/
theorem pieceShadow_generic : (pieceShadow hn hD hS H).Generic :=
  geoCarrierShadow_generic hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H)
    (pieceCarrier hD hS H)

include hn in
/-- **The double points of `C_H` are exactly the crossings of `H`** (geometric form): the
self-intersection points of the carrier `q_H` are exactly the crossing points of the labels of `H`
(U2c `geo_self_intersections`, clause 1, tier 1). -/
theorem pieceCurve_selfIntersections (x : Plane) :
    GeoIsSelfIntersection hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) x ↔
      ∃ c ∈ pieceLabels hD.crossingGeometry S H, x = crossingPoint c := by
  rw [← pieceCarrier_geoCarrierCrossings hD hS H]
  exact (geo_self_intersections hn (CarrierGeometry.ofDiagrammatic hD)
    (pieceSupport_geoIndependent hD hS H) (pieceCarrier hD hS H)).1 x

/-- The double points of the shadow of `C_H` correspond bijectively to the crossings of `H`
(U4 `geoCarrierCrossingEquiv` composed with `pieceCarrier_geoCarrierCrossings`). -/
noncomputable def pieceShadowCrossingEquiv :
    (pieceShadow hn hD hS H).Crossing ≃ {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H} :=
  (geoCarrierCrossingEquiv hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H)
    (pieceCarrier hD hS H)).trans
    (Equiv.subtypeEquivRight fun c => by rw [pieceCarrier_geoCarrierCrossings hD hS H])

/-- The bijection `pieceShadowCrossingEquiv` preserves the crossing point: every double point of the
shadow of `C_H` sits at the crossing point of the crossing of `H` it corresponds to (U4
`crossingPoint_geoCarrierCrossingEquiv`; the transport along `pieceCarrier_geoCarrierCrossings` keeps the
underlying crossing). -/
theorem pieceShadowCrossingEquiv_crossingPoint (x : (pieceShadow hn hD hS H).Crossing) :
    (pieceShadow hn hD hS H).crossingPoint x =
      crossingPoint (pieceShadowCrossingEquiv hn hD hS H x).1 :=
  (crossingPoint_geoCarrierCrossingEquiv hn (CarrierGeometry.ofDiagrammatic hD)
    (pieceSupport_geoIndependent hD hS H) (pieceCarrier hD hS H) x).symm

include hn in
/-- **An edge of a corner polygon through a crossing point is directed along a parent edge of that
crossing** (tier 1; U7c-fix). If the crossing point of a crossing `c` of the carrier `q` of an
independent `T` lies on the edge `k` of the corner polygon `Q` of `q`, then `edge Q k = t • edge P i`
with `t > 0` and `i` one of the two parent edges of `c`. U2b `geoCornerPolygon_edge_smul` gives the
parent edge of the block of `k` (the outgoing slot of the corner `c_k`); the crossing point is traced on
the edge `k` at a block parameter `(ρ_T^r c_k, u)` (`geo_edgeSegment_param`) which U2c
`geo_carrier_crossingPoint_parameters` identifies as `(w, 0)` for a visit `w` of `c`; `r ≠ 0` because
`c` is unselected and `c_k` is a true corner, so `w` is an interior block mark and lies on the block's
parent edge (`GeoBlockInterior.visit_edge`); the end corner `Q (k+1)` is excluded because no crossing
point is the plane point of a true corner (`geo_carrier_selfIntersection_not_corner`). -/
theorem cornerPolygon_edge_of_crossingPoint_mem (hG : CarrierGeometry P)
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)
    {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg T q) (k : ZMod (geoCornerCount hG.cg T q))
    (hk : crossingPoint c ∈ edgeSegment (geoCornerPolygon hG.cg T q) k) :
    ∃ i ∈ c.val, ∃ t : ℝ, 0 < t ∧ edge (geoCornerPolygon hG.cg T q) k = t • edge P i := by
  obtain ⟨t, ht, hedge⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q k
  refine ⟨(geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1, ?_, t, ht, hedge⟩
  have hcS : c ∉ T := ((mem_geoCarrierCrossings hG.cg T q c).mp hc).1
  rcases geo_edgeSegment_param hn hG.cg hT q k hk with ⟨r, u, hu0, hu1, hb, hx⟩ | hx
  · -- the crossing point is traced at a block parameter of the edge `k`: a visit `w` of `c`
    obtain ⟨w, hw, -, hp⟩ := (geo_carrier_crossingPoint_parameters hn hG T q c _).mp
      ⟨geoIsCarrierParameter_block hG.cg T q k r hu0 hu1, hx⟩
    have hmark : (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = Sum.inr w :=
      congrArg Prod.fst hp
    have hr : 1 ≤ r := by
      by_contra h
      have hr0 : r = 0 := by omega
      rw [hr0, pow_zero, Equiv.Perm.one_apply] at hmark
      have hcorner := isTrueCorner_geoCornerMark hG.cg T q k
      rw [hmark] at hcorner
      exact hcS (hw ▸ (isTrueCorner_visit T w).mp hcorner)
    rw [← hb.visit_edge hG.cg T q hr hmark, ← hw]
    exact w.2.property
  · -- the crossing point is the end corner `Q (k+1)`: impossible, no crossing point is a corner
    exfalso
    rw [geoCornerPolygon_apply] at hx
    exact (geo_carrier_selfIntersection_not_corner hG T q hc).2.2.2 _
      (isTrueCorner_geoCornerMark hG.cg T q (k + 1)) hx.symm

/-- Each strand of a double point `x` of the shadow of `C_H` lying at the crossing point of `c ∈ H` is
directed along one of the two parent edges of `c`, with a positive factor
(`cornerPolygon_edge_of_crossingPoint_mem` at `q_H`, through `pieceCarrier_geoCarrierCrossings`). -/
theorem pieceShadow_strand_dir {c : Crossing P} (hc : c ∈ pieceLabels hD.crossingGeometry S H)
    (x : (pieceShadow hn hD hS H).Crossing)
    (hx : (pieceShadow hn hD hS H).crossingPoint x = crossingPoint c)
    {s : (pieceShadow hn hD hS H).Strand} (hs : s ∈ x.val) :
    ∃ i ∈ c.val, ∃ t : ℝ, 0 < t ∧ (pieceShadow hn hD hS H).dir s = t • edge P i := by
  have hc' : c ∈ geoCarrierCrossings hD.crossingGeometry (S ∪ pieceSupport hD hS H)
      (pieceCarrier hD hS H) := by
    rw [pieceCarrier_geoCarrierCrossings hD hS H]
    exact hc
  have hk : crossingPoint c ∈ edgeSegment
      (geoCornerPolygon hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H)) s.2 := by
    rw [← hx]
    exact (pieceShadow hn hD hS H).crossingPoint_mem x hs
  exact cornerPolygon_edge_of_crossingPoint_mem hn (CarrierGeometry.ofDiagrammatic hD)
    (pieceSupport_geoIndependent hD hS H) (pieceCarrier hD hS H) hc' s.2 hk

/-- **The rotation system of `C_H` at a surviving crossing is the parent's** (d1:664–666 "Its rotation
system at each surviving crossing is the carrier's, which is the parent's, since smoothing at other
points does not disturb the half-edge order at a survivor"): at a double point `x` of the shadow of
`C_H` lying at the crossing point of `c ∈ H`, the two strands of `x` correspond bijectively to the two
parent edges of `c`, each strand directed along its parent edge with a positive factor. Injectivity of
strand ↦ parent edge is the transversality of the generic shadow (two strands along the same parent edge
would have `det = 0`); both sides have two elements. -/
theorem pieceShadow_rotationSystem {c : Crossing P} (hc : c ∈ pieceLabels hD.crossingGeometry S H)
    (x : (pieceShadow hn hD hS H).Crossing)
    (hx : (pieceShadow hn hD hS H).crossingPoint x = crossingPoint c) :
    ∃ e : {s // s ∈ x.val} ≃ {i // i ∈ c.val},
      ∀ s : {s // s ∈ x.val}, ∃ t : ℝ, 0 < t ∧
        (pieceShadow hn hD hS H).dir s.1 = t • edge P (e s).1 := by
  let f : {s // s ∈ x.val} → {i // i ∈ c.val} := fun s =>
    ⟨Classical.choose (pieceShadow_strand_dir hn hD hS H hc x hx s.2),
      (Classical.choose_spec (pieceShadow_strand_dir hn hD hS H hc x hx s.2)).1⟩
  have hf : ∀ s : {s // s ∈ x.val}, ∃ t : ℝ, 0 < t ∧
      (pieceShadow hn hD hS H).dir s.1 = t • edge P (f s).1 :=
    fun s => (Classical.choose_spec (pieceShadow_strand_dir hn hD hS H hc x hx s.2)).2
  have hinj : Function.Injective f := by
    intro s s' hss'
    by_contra hne
    have hne' : s.1 ≠ s'.1 := fun h => hne (Subtype.ext h)
    obtain ⟨hna, hmeet⟩ := (pieceShadow hn hD hS H).crossing_pair_spec x s.2 s'.2 hne'
    have hdet := (pieceShadow_generic hn hD hS H).transverse s.1 s'.1 hna hmeet
    obtain ⟨t, -, ht⟩ := hf s
    obtain ⟨t', -, ht'⟩ := hf s'
    apply hdet
    rw [ht, ht', hss']
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_coe, Fintype.card_coe, (pieceShadow hn hD hS H).crossing_card_two x,
      SM.crossing_card_two c]
  exact ⟨Equiv.ofBijective f hbij, hf⟩

end PieceCurveGeometry

/-! ## 7. Row 143 — CV:lem:piececurve (d1_setup.tex:592–611), the bundle -/

section PieceCurveRow

variable (hn : 3 ≤ n) (hD : Diagrammatic P) (S : Finset (Crossing P))
  (hS : S ∈ Ind hD.crossingGeometry) (H : Piece hD.crossingGeometry S)

/-- CV:lem:piececurve (d1_setup.tex:592–611) as printed, one field per printed sentence, on the printed
binder `hD : Diagrammatic P`, `S ∈ Ind(G_P)`, `H` a residual piece of `S`. `C_H` is `pieceCurve hD hS H`,
the corner polygon of the carrier `pieceCarrier` of `S ∪ pieceSupport` (reading (ii)); `hn : 3 ≤ n` is
carried for the geometric clauses only (reading (iii), §5 shape `CV.piececurve (hn) …`). The last printed
sentence (d1:608–609) names the datum of def:piecediagram, "a word together with a rotation system"
(d1:577–585); it is rendered by two fields, `realizable` (the word) and `rotation_system` (the rotation
system), see the module docstring's clause map (U7c-fix). -/
structure PieceCurveData : Prop where
  /-- "smooth every crossing of `S` — of `S` *only* — so that the curve falls into the `|S|+1` carriers
  of `S`" (lem:carriers (i)) -/
  carriers_of_S : Fintype.card (GeoComponent hD.crossingGeometry S) = S.card + 1
  /-- "take the one carrier that carries `H`, which is unique by Lemma lem:carriers (iv)" — "The route
  above smooths nothing but `S`, so `H` lies on one carrier before the iteration begins" -/
  initial_carrier : ∃! q₀ : GeoComponent hD.crossingGeometry S,
    ∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
      geoOwner hD.crossingGeometry S (Sum.inr v) = q₀
  /-- "and apply to it Step 5's iteration, smoothing at each step one double point outside `H`": a step
  smooths a double point `d ∉ H` of the current carrier `q` of `H`; the smoothed set stays admissible
  (`StepInvariant`: undominated, outside `H`, independent) -/
  step : ∀ K : Finset (Crossing P), StepInvariant hD.crossingGeometry S H K →
    ∀ q : GeoComponent hD.crossingGeometry (S ∪ K),
      ∀ d ∈ geoCarrierCrossings hD.crossingGeometry (S ∪ K) q,
        d ∉ pieceLabels hD.crossingGeometry S H → StepInvariant hD.crossingGeometry S H (insert d K)
  /-- "and keeping the daughter curve that carries `H`, which Step 5 shows is well defined" — "and each
  subsequent step preserves that": at every admissible stage exactly one carrier carries `H` -/
  step_well_defined : ∀ K : Finset (Crossing P), StepInvariant hD.crossingGeometry S H K →
    ∃! q : GeoComponent hD.crossingGeometry (S ∪ K),
      ∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
        geoOwner hD.crossingGeometry (S ∪ K) (Sum.inr v) = q
  /-- the iteration terminates: the smoothed set `K_H = pieceSupport` is admissible and its carrier
  `q_H = pieceCarrier` is the carrier of `H` ("after finitely many steps the curve `C_H` …") -/
  terminal : StepInvariant hD.crossingGeometry S H (pieceSupport hD hS H) ∧
    (∀ c ∈ pieceLabels hD.crossingGeometry S H, ∀ v : Visit P, v.1 = c →
      geoOwner hD.crossingGeometry (S ∪ pieceSupport hD hS H) (Sum.inr v) = pieceCarrier hD hS H)
  /-- "Then `C_H` is a closed plane curve": `C_H = pieceCurve`, the corner polygon of `q_H`, is a regular
  closed polygon whose one-component shadow is generic (finitely many transverse double points, no
  triple point) -/
  closed_plane_curve : SM.Regular (pieceCurve hD hS H) ∧ (pieceShadow hn hD hS H).Generic
  /-- "whose double points are exactly the crossings of `H`": the crossings of the carrier `q_H` are the
  labels of `H`, and the self-intersection points of `C_H` are exactly their crossing points -/
  double_points :
    geoCarrierCrossings hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) =
      pieceLabels hD.crossingGeometry S H ∧
    ∀ x : Plane,
      GeoIsSelfIntersection hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) x ↔
        ∃ c ∈ pieceLabels hD.crossingGeometry S H, x = crossingPoint c
  /-- "and whose Gauss word is the parent word restricted to `H` in the parent's cyclic order": `q_H`
  traverses its marks in the order inherited from `Γ` (lem:carrierword at `S ∪ K_H`), and its
  double-point word — the visits of `H` in the order along `C_H` — is `P`'s Gauss word restricted to `H` -/
  gauss_word : GeoInheritsMarkOrder hD.crossingGeometry (S ∪ pieceSupport hD hS H) ∧
    TracedSuccessor hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) ∧
    (carrierGaussList hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H)).filter
        (fun v : Visit P => decide (v.1 ∈ pieceLabels hD.crossingGeometry S H)) =
      (geometricGaussList hD.crossingGeometry).filter
        (fun v : Visit P => decide (v.1 ∈ pieceLabels hD.crossingGeometry S H))
  /-- "In particular that restricted word is realizable, and the datum of Definition def:piecediagram is
  the datum of `C_H`" — the **first half of the datum, the word** (d1:577–580 "the parent Gauss word
  restricted to the crossings of `H`, in the parent's cyclic order"): the restricted word is read off an
  actual closed plane curve — the double points of the shadow of `C_H` are in bijection with `H`, each
  double point of the shadow sitting at the crossing point of the crossing of `H` it corresponds to -/
  realizable : ∃ e : (pieceShadow hn hD hS H).Crossing ≃
      {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H},
    ∀ x : (pieceShadow hn hD hS H).Crossing,
      (pieceShadow hn hD hS H).crossingPoint x = crossingPoint (e x).1
  /-- "and the datum of Definition def:piecediagram is the datum of `C_H`" — the **second half of the
  datum, the rotation system** (d1:580–585: "together with the parent's per-crossing counter-clockwise
  half-edge order restricted to the surviving half-edges … So the datum is a word *together with a
  rotation system*, not a bare word"; proof d1:664–666: "Its rotation system at each surviving crossing
  is the carrier's, which is the parent's, since smoothing at other points does not disturb the
  half-edge order at a survivor; that is the second half of the datum"): at every surviving crossing
  `c ∈ H`, the two strands of `C_H` through `crossingPoint c` are the two parent edges of `c` — for the
  double point `x` of the shadow of `C_H` at `crossingPoint c`, a bijection between the strands of `x`
  and the two edges of `c` under which each strand is directed along its parent edge with a positive
  factor (`dir s = t • edge P i`, `t > 0`). Hence the four half-edges of `C_H` at `x` are the parent's
  four half-edges at `c`, in the same counter-clockwise order: the parent's rotation system at `c`,
  restricted to `H` -/
  rotation_system : ∀ c ∈ pieceLabels hD.crossingGeometry S H,
    ∀ x : (pieceShadow hn hD hS H).Crossing,
      (pieceShadow hn hD hS H).crossingPoint x = crossingPoint c →
        ∃ e : {s // s ∈ x.val} ≃ {i // i ∈ c.val},
          ∀ s : {s // s ∈ x.val}, ∃ t : ℝ, 0 < t ∧
            (pieceShadow hn hD hS H).dir s.1 = t • edge P (e s).1

/-- **Row 143, CV:lem:piececurve** (d1_setup.tex:592–611), on the printed binder. -/
theorem piececurve : PieceCurveData hn hD S hS H where
  carriers_of_S := (carriers hD S hS).count
  initial_carrier := exists_unique_piece_carrier hD.crossingGeometry hS H
  step := fun _ hK _ _ hd hdH => hK.insert hd hdH
  step_well_defined := fun _ hK => hK.exists_unique_owner
  terminal := ⟨pieceSupport_stepInvariant hD hS H, pieceCarrier_owns hD hS H⟩
  closed_plane_curve := ⟨pieceCurve_regular hn hD hS H, pieceShadow_generic hn hD hS H⟩
  double_points := ⟨pieceCarrier_geoCarrierCrossings hD hS H, pieceCurve_selfIntersections hn hD hS H⟩
  gauss_word := ⟨pieceSupport_inheritsMarkOrder hD hS H, pieceCarrier_traced hD hS H,
    pieceCarrier_gaussWord hD hS H⟩
  realizable := ⟨pieceShadowCrossingEquiv hn hD hS H, pieceShadowCrossingEquiv_crossingPoint hn hD hS H⟩
  rotation_system := fun _ hc x hx => pieceShadow_rotationSystem hn hD hS H hc x hx

end PieceCurveRow

/-! ## 8. Row 142 — CV:def:piecediagram (d1_setup.tex:565–591): the piece diagram and `P_H` -/

section PieceDiagramDefs

variable (hn : 3 ≤ n) (hD : Diagrammatic P) {S : Finset (Crossing P)}
  (hS : S ∈ Ind hD.crossingGeometry) (H : Piece hD.crossingGeometry S)

/-- **The diagram of the residual piece `H`** (reading (ii)): the positive lift — every double point
resolved by the divide convention `det(u_over, u_under) > 0` (`Diagram.IsPositive`) — of the piece
curve `C_H` of lem:piececurve, i.e. of the carrier `q_H` of `S ∪ K_H` (U4 `geoPositiveLift`, tier 1). -/
noncomputable def pieceDiagram : Diagram :=
  geoPositiveLift hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H)
    (pieceCarrier hD hS H)

/-- **`P_H(a, z)`**: "the HOMFLY–PT polynomial of the link so presented, normalized as in
Definition def:homfly" — `homfly` (CV:ax:homfly / lit:homfly) of the piece diagram. -/
noncomputable def pieceHomfly : R := homfly (pieceDiagram hn hD hS H)

@[simp] theorem pieceDiagram_Γ : (pieceDiagram hn hD hS H).Γ = pieceShadow hn hD hS H := rfl

theorem pieceDiagram_componentCount : (pieceDiagram hn hD hS H).componentCount = 1 := rfl

/-- The curve of the piece diagram is the piece curve `C_H`. -/
theorem pieceDiagram_comp (i : Fin 1) : ((pieceDiagram hn hD hS H).Γ.comp i).P = pieceCurve hD hS H :=
  rfl

theorem pieceDiagram_isPositive (x : (pieceDiagram hn hD hS H).Γ.Crossing) :
    (pieceDiagram hn hD hS H).IsPositive x :=
  geoPositiveLift_isPositive hn _ _ _ x

theorem pieceDiagram_sign (x : (pieceDiagram hn hD hS H).Γ.Crossing) :
    (pieceDiagram hn hD hS H).sign x = 1 :=
  geoPositiveLift_sign hn _ _ _ x

/-- `w(H) = |H|`: the writhe of the piece diagram is the number of crossings of `H`. -/
theorem pieceDiagram_writhe :
    (pieceDiagram hn hD hS H).writhe = ((pieceLabels hD.crossingGeometry S H).card : ℤ) := by
  rw [pieceDiagram, geoPositiveLift_writhe, pieceCarrier_geoCarrierCrossings]

theorem pieceDiagram_writhe_eq_pieceWrithe :
    (pieceDiagram hn hD hS H).writhe = pieceWrithe hD.crossingGeometry S H :=
  pieceDiagram_writhe hn hD hS H

/-- The crossings of the piece diagram are the crossings of `H`. -/
noncomputable def pieceDiagramCrossingEquiv :
    (pieceDiagram hn hD hS H).Γ.Crossing ≃ {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H} :=
  pieceShadowCrossingEquiv hn hD hS H

/-- The piece diagram is the unique diagram on the shadow of `C_H` all of whose crossings are positive
(the divide convention determines it). -/
theorem eq_pieceDiagram_of_isPositive (D : Diagram) (hΓ : D.Γ = pieceShadow hn hD hS H)
    (hpos : ∀ x, D.IsPositive x) : D = pieceDiagram hn hD hS H :=
  eq_geoPositiveLift_of_isPositive hn _ _ _ D hΓ hpos

/-- The record of the piece diagram (CV:def:record) is that of a single circle. -/
theorem pieceDiagram_singleCircle_record : SingleCircle (pieceDiagram hn hD hS H).record :=
  singleCircle_record (pieceDiagram_componentCount hn hD hS H)

end PieceDiagramDefs

section PieceDiagramRow

variable (hn : 3 ≤ n) (hD : Diagrammatic P) (S : Finset (Crossing P))
  (hS : S ∈ Ind hD.crossingGeometry) (H : Piece hD.crossingGeometry S)

/-- CV:def:piecediagram (d1_setup.tex:565–591) as printed, one field per printed sentence, on the
printed binder `hD : Diagrammatic P` ("For a diagrammatic parent `P`"). The diagram is
`pieceDiagram hn hD hS H`, the positive lift of the piece curve `C_H` (reading (ii)); `hn : 3 ≤ n` is
reading (iii) (§5 shape `CV.piecediagram_definition (hn) …`). -/
structure PieceDiagramData : Prop where
  /-- "the diagram of a residual piece `H` is the parent curve `P` with every double point outside `H`
  erased — the two strands drawn as passing without interaction —" (reading (ii)): the diagram's curve
  is the piece curve `C_H` of lem:piececurve — one closed curve (the shadow of `q_H`) whose double
  points are exactly the crossings of `H`; every double point of `P` outside `H` has been smoothed away
  (`pieceCarrier_geoCarrierCrossings`) -/
  erased : (pieceDiagram hn hD hS H).Γ = pieceShadow hn hD hS H ∧
    (pieceDiagram hn hD hS H).componentCount = 1 ∧
    (∀ i : Fin 1, ((pieceDiagram hn hD hS H).Γ.comp i).P = pieceCurve hD hS H) ∧
    Nonempty ((pieceDiagram hn hD hS H).Γ.Crossing ≃
      {c : Crossing P // c ∈ pieceLabels hD.crossingGeometry S H})
  /-- "and every double point of `H` resolved by the divide convention: the branch whose direction
  `u_over` satisfies `det(u_over, u_under) > 0` passes over" (`Diagram.IsPositive x :=
  0 < det (dir (overStrand x)) (dir (underStrand x))`, the same formula) -/
  divide_convention : ∀ x : (pieceDiagram hn hD hS H).Γ.Crossing, (pieceDiagram hn hD hS H).IsPositive x
  /-- "Under this convention every crossing of the diagram is positive," -/
  positive : ∀ x : (pieceDiagram hn hD hS H).Γ.Crossing, (pieceDiagram hn hD hS H).sign x = 1
  /-- "so its writhe is `w(H) = |H|`, the number of double points of `H`." -/
  writhe : (pieceDiagram hn hD hS H).writhe = pieceWrithe hD.crossingGeometry S H ∧
    pieceWrithe hD.crossingGeometry S H = ((pieceLabels hD.crossingGeometry S H).card : ℤ)
  /-- "We write `P_H(a,z)` for the HOMFLY–PT polynomial of the link so presented, normalized as in
  Definition def:homfly": `P_H = homfly (pieceDiagram H)`, and `homfly` satisfies the two normalising
  identities of def:homfly, `P(○) = 1` and `aP(L₊) − a⁻¹P(L₋) = zP(L₀)` (CV:ax:homfly `unknot`, `skein`) -/
  piece_polynomial : pieceHomfly hn hD hS H = homfly (pieceDiagram hn hD hS H) ∧
    (∀ D : Diagram, D.IsCrossingFreeCircle → homfly D = 1) ∧
    (∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
      R.a * homfly Dp - R.aInv * homfly Dm = R.z * homfly D0)
  /-- "*What 'erased' means* … the datum is a word *together with a rotation system*, not a bare word,
  and the definition above is to be read as naming that pair. To erase a double point is to omit it from
  that datum.": the datum is that of the actual closed curve `C_H` (reading (ii)) — its word is the
  parent word restricted to `H` in the parent's cyclic order (lem:piececurve), and its rotation system
  is the plane geometry of `C_H` itself: the diagram is the unique diagram on the shadow of `C_H` whose
  crossings are all positive -/
  datum : (carrierGaussList hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H)).filter
        (fun v : Visit P => decide (v.1 ∈ pieceLabels hD.crossingGeometry S H)) =
      (geometricGaussList hD.crossingGeometry).filter
        (fun v : Visit P => decide (v.1 ∈ pieceLabels hD.crossingGeometry S H)) ∧
    ∀ D : Diagram, D.Γ = pieceShadow hn hD hS H → (∀ x, D.IsPositive x) → D = pieceDiagram hn hD hS H
  /-- "The combinatorial shadow of the datum — the word with its over/under and signs and nothing else —
  is Definition def:record.": the record (`Diagram.record`, CV:def:record) of the piece diagram is that
  of a single circle -/
  record_shadow : SingleCircle (pieceDiagram hn hD hS H).record

/-- **Row 142, CV:def:piecediagram** (d1_setup.tex:565–591), on the printed binder. -/
theorem piecediagram_definition : PieceDiagramData hn hD S hS H where
  erased := ⟨rfl, rfl, fun _ => rfl, ⟨pieceDiagramCrossingEquiv hn hD hS H⟩⟩
  divide_convention := pieceDiagram_isPositive hn hD hS H
  positive := pieceDiagram_sign hn hD hS H
  writhe := ⟨pieceDiagram_writhe_eq_pieceWrithe hn hD hS H, rfl⟩
  piece_polynomial := ⟨rfl, fun _ h => homfly_circle h, fun _ _ _ h => homfly_skein h⟩
  datum := ⟨pieceCarrier_gaussWord hD hS H, eq_pieceDiagram_of_isPositive hn hD hS H⟩
  record_shadow := pieceDiagram_singleCircle_record hn hD hS H

end PieceDiagramRow

end CV
