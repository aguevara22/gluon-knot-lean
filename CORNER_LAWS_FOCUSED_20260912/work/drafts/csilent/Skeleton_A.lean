import SM.CChamber
import SM.WallSides
import SM.PolynomialBlock
import SM.FlatCarriers
import SM.AngleScaling
import SM.LinkDiagramRecord

/-! # Skeleton A — prop:C-silent (silence), record-first route

Architect A, 2026-09-14.  Target `SM.prop_C_silent : CSilentData` (statement FIXED in
work/drafts/CSilent_statement.lean, copied verbatim at the end).  Source: reference/SM/sm-4-knotlaws.tex:101-152.
Plan: work/drafts/csilent/PLAN_A.md.

Route (the printed proof, R1).  The two sides `P₋ = P(−s)`, `P₊ = P(+s)` at one small side parameter `s`
are generic; by lem:wall-sides (E),(C) (`silent_sides`) their crossing supports, same-edge parameter orders,
crossing signs and vertex turns agree through the centre (`SilentPairData`).  This gives a
`Carrier.MarkTransport` from `P₋` to `P₊` exactly as `pathTransport` of the accepted prop:C-chamber, with the
sorted mark list carried literally (`markList_transport`).  The accepted `cornerStateSum_transport` then
reduces `C(P₊) = C(P₋)` to two facts per carrier `q` of a decomposition `S`:
* uniformity: the corner turns are `sign det(in, out)` of the parent in/out directions at the corner
  (`ccpCornerPolygon_turn_eq_sign`), parent turns and crossing signs agree across the wall;
* the corner coefficient: `|rot|` agrees (lem:rot (ii) along the germ: the rotation is `(1/2π) Σ` of the
  principal angles between the parent in/out directions at the corners, a continuous, `2πℤ`-valued-off-the-centre
  function of the parameter — no generic-polygon lemma is applied at the centre, only parent edge directions),
  and `H⁺` agrees by lc:presentations (`SM.presentations`) + lp:core (`P_eq_homfly`) on a named-record
  isomorphism of the two positive lifts, built on the generic sides only: the crossings of a carrier polygon
  are its unselected crossings read at block positions (`nonadjacent_meet`, `mark_block`, `block_mark_eq`),
  the visit order on a corner edge is the parent parameter order, over bits are crossing signs.
The two side parameters of the statement are reduced to one by prop:C-chamber along each side
(`cornerStateSum_eq_of_mem_labelledChamber`).  Only the generic sides carry state sums.

Every `sorry` below is a leaf of the chain; `prop_C_silent` is proved from the chain. -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

/-! ## §1. Two small elementary facts -/

/-- Two nonzero vectors with nonzero determinant form a regular pair (they are not antiparallel). -/
theorem regularPair_of_det_ne_zero {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (hd : det u v ≠ 0) :
    RegularPair u v :=
  ⟨hu, hv, fun ⟨r, _, hr⟩ => hd (by rw [hr, det_smul_self])⟩

/-- On a weakly generic polygon every vertex is a regular corner (nonzero edges, nonzero turn). -/
theorem weak_regularPair_turn {n : ℕ} {P : LabelledTuple n} (hw : WeakGeneric P) (i : ZMod n) :
    RegularPair (edge P (i - 1)) (edge P i) := by
  refine regularPair_of_det_ne_zero (hw.1 _) (hw.1 _) ?_
  have h := hw.2.1 i
  rw [turn_det] at h
  exact sign_ne_zero.mp h

/-- On the geometric record domain the two edges of a crossing form a regular pair. -/
theorem geometry_regularPair_crossing {n : ℕ} {P : LabelledTuple n} (hg : CrossingGeometry P)
    {e f : ZMod n} (hc : IsCrossing P {e, f}) : RegularPair (edge P e) (edge P f) :=
  regularPair_of_det_ne_zero (hg.1 _) (hg.1 _) (crossing_det_ne_zero_of_geometry hg hc)

/-- A continuous real function on a preconnected space whose values off one point `u₀` are integers
takes the same value at any two points other than `u₀` (intermediate values: two distinct non-integers
between `F a` and `F b` would both have to be taken at `u₀`). -/
theorem eq_of_continuous_int_valued_off_point {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {F : X → ℝ} (hF : Continuous F) (u₀ : X) (hint : ∀ u, u ≠ u₀ → ∃ k : ℤ, F u = k)
    {a b : X} (ha : a ≠ u₀) (hb : b ≠ u₀) : F a = F b := by
  sorry

/-! ## §2. The record data of a silent wall, composed across the centre -/

section SilentGerm

variable {n : ℕ} [NeZero n]

/-- The record identification of two polygons on one silent interval (lem:wall-sides (E),(C) composed
across the centre): same crossing supports, same same-edge parameter orders, same crossing signs, same
vertex turns.  This is all the wall data the transport needs. -/
structure SilentPairData (P Q : LabelledTuple n) : Prop where
  hs : ∀ c, IsCrossing P c ↔ IsCrossing Q c
  ho : CrossingParameterOrderAgrees P Q
  sign : ∀ i j, IsCrossing P {i, j} → crossingSign Q i j = crossingSign P i j
  turn : ∀ i, turn Q i = turn P i

/-- One common small interval on which every parameter is weakly generic with crossing geometry, has the
centre's crossing supports, and any two parameters have the pair data. -/
structure SilentInterval (hn : 3 ≤ n) (g : WallGerm n) (δ : ℝ) : Prop where
  pos : 0 < δ
  le : δ ≤ g.radius
  weak : ∀ t : g.Parameter, |t.val| < δ → WeakGeneric (g.curve t)
  geom : ∀ t : g.Parameter, |t.val| < δ → CrossingGeometry (g.curve t)
  cross : ∀ t : g.Parameter, |t.val| < δ → ∀ c, IsCrossing g.center c ↔ IsCrossing (g.curve t) c
  pair : ∀ t₁ t₂ : g.Parameter, |t₁.val| < δ → |t₂.val| < δ →
    SilentPairData (g.curve t₁) (g.curve t₂)

/-- **lem:wall-sides (E),(C) read for the transport.**  From `silent_sides`: the record clauses at every
`|t| < δ` (`GeometricRecordsAgree`, `CrossingParameterOrderAgrees`, `ChirotopesOutsideZerosAgree`, weak
genericity, crossing geometry) composed through the centre; vertex turns are constant because the turn
support `{i−1, i, i+1}` is never a point-zero triple of the centre (`turn g.center i ≠ 0`, weak genericity
of the centre, `pointZeroTriple_iff`). -/
theorem exists_silentInterval (hn : 3 ≤ n) (g : WallGerm n) (h : g.Silent) :
    ∃ δ : ℝ, SilentInterval hn g δ := by
  sorry

theorem SilentInterval.sideTime_abs_lt {hn : 3 ≤ n} {g : WallGerm n} {δ : ℝ}
    (hI : SilentInterval hn g δ) (b : Bool) {s : g.SideParameter} (hs : s.val < δ) :
    |(g.sideTime b s).val| < δ := by
  rw [g.sideTime_val_abs]
  exact hs

/-- The pair data of the two sides at one small side parameter. -/
theorem SilentInterval.sidePairData {hn : 3 ≤ n} {g : WallGerm n} {δ : ℝ}
    (hI : SilentInterval hn g δ) {s : g.SideParameter} (hs : s.val < δ) :
    SilentPairData (g.sideTuple false s).val (g.sideTuple true s).val :=
  hI.pair _ _ (hI.sideTime_abs_lt false hs) (hI.sideTime_abs_lt true hs)

end SilentGerm

/-! ## §3. The silent transport between two generic polygons with the pair data -/

section Transport

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P) (hQ : Generic Q)
  (hd : SilentPairData P Q)

/-- The mark transport of the silent wall: vertices fixed, crossings and visits through the canonical
transports, the sorted mark list carried literally (`markList_transport`), interlacement through
`geometric_interlaces_transport`, turns by the pair data.  Word for word `pathTransport` of prop:C-chamber
with the path replaced by the wall data. -/
noncomputable def silentTransport : MarkTransport hn hP hQ where
  vert := Equiv.refl _
  cross := crossingTransport hd.hs
  visit := visitTransport hd.hs
  visit_fst := fun _ => rfl
  markList_rotated := by
    rw [markList_transport hn hP hQ hd.hs hd.ho]
    exact List.IsRotated.refl _
  interlaces_iff := fun x y =>
    (geometric_interlaces_transport (generic_crossingGeometry hn hP)
      (generic_crossingGeometry hn hQ) hd.hs hd.ho x y).symm
  turn_eq := fun i => hd.turn i

theorem silentTransport_toMark (a : Mark P) :
    (silentTransport hn hP hQ hd).toMark a = Sum.map id (visitTransport hd.hs) a := by
  cases a <;> rfl

theorem silentTransport_toMark_inl (i : ZMod n) :
    (silentTransport hn hP hQ hd).toMark (Sum.inl i) = Sum.inl i := rfl

theorem silentTransport_toMark_inr (v : Visit P) :
    (silentTransport hn hP hQ hd).toMark (Sum.inr v) = Sum.inr (visitTransport hd.hs v) := rfl

/-- The sorted mark list is carried literally (no rotation). -/
theorem silentTransport_markList :
    markList hn hQ = (markList hn hP).map (silentTransport hn hP hQ hd).toMark := by
  rw [markList_transport hn hP hQ hd.hs hd.ho]
  congr 1

/-- The corner polygon of the transported carrier is the transported corner polygon (recast). -/
theorem ccpCornerPolygon_silentTransport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerPolygon hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q) =
      recastTuple ((silentTransport hn hP hQ hd).ccpCornerCount_transport S q)
        ((silentTransport hn hP hQ hd).transportedCornerPolygon S q) :=
  (silentTransport hn hP hQ hd).ccpCornerPolygon_transport_of_markList_eq
    (silentTransport_markList hn hP hQ hd) S q

/-! ### 3a. Corner marks and their in/out edge labels are carried (unit U1) -/

/-- The corner list is carried literally (the `h2` of `ccpCornerPolygon_transport_of_markList_eq`). -/
theorem ccpCornerList_silentTransport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerList hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q) =
      (ccpCornerList hn hP S q).map (silentTransport hn hP hQ hd).toMark := by
  sorry

/-- The `j`-th corner mark is carried to the `j`-th corner mark (indices identified by the cast along
`ccpCornerCount_transport`). -/
theorem ccpCornerMark_silentTransport (S : Finset (Crossing P)) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    ccpCornerMark hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q)
        (Equiv.cast (congrArg ZMod
          ((silentTransport hn hP hQ hd).ccpCornerCount_transport S q).symm) j) =
      (silentTransport hn hP hQ hd).toMark (ccpCornerMark hn hP S q j) := by
  sorry

/-- The incoming original edge at a mark is a label: carried (`ccpInEdge_vertex`, `ccpInEdge_visit`,
`visitTransport_edge`). -/
theorem ccpInEdge_silentTransport (a : Mark P) :
    ccpInEdge hn hQ ((silentTransport hn hP hQ hd).toMark a) = ccpInEdge hn hP a := by
  sorry

/-- The outgoing original edge at a mark is a label: carried (`ccpOutSlot_vertex`, `ccpOutSlot_selected`
with `twin_eq`, `ccpOutSlot_unselected`, `mem_support`). -/
theorem ccpOutSlot_fst_silentTransport (S : Finset (Crossing P)) (a : Mark P) :
    (ccpOutSlot hn hQ ((silentTransport hn hP hQ hd).support S)
      ((silentTransport hn hP hQ hd).toMark a)).1 = (ccpOutSlot hn hP S a).1 := by
  sorry

/-- The parent in/out edge labels at the `j`-th corner of a carrier (the labels of
`ccpCornerPolygon_turn_eq_sign`). -/
noncomputable abbrev cornerInLabel {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) : ZMod n :=
  ccpInEdge hn hP (ccpCornerMark hn hP S q j)

noncomputable abbrev cornerOutLabel {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) : ZMod n :=
  (ccpOutSlot hn hP S (ccpCornerMark hn hP S q j)).1

/-- At a corner the in/out labels are consecutive edges `(i−1, i)` of an original vertex `i`, or the two
edges `(v.edge, twin.edge)` of a selected crossing (`ccpCornerMark_isTrueCorner`, `ccpInEdge_vertex/visit`,
`ccpOutSlot_vertex/selected`). -/
theorem cornerLabels_cases (S : Finset (Crossing P)) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) :
    (∃ i : ZMod n, ccpCornerMark hn hP S q j = Sum.inl i ∧
      cornerInLabel hn hP S q j = i - 1 ∧ cornerOutLabel hn hP S q j = i) ∨
    (∃ v : Visit P, ccpCornerMark hn hP S q j = Sum.inr v ∧ v.1 ∈ S ∧
      cornerInLabel hn hP S q j = v.2.val ∧ cornerOutLabel hn hP S q j = (visitTwin v).2.val) := by
  sorry

/-- The parent pair `{in, out}` at a selected-visit corner is a crossing of `P`. -/
theorem cornerLabels_isCrossing_of_visit (S : Finset (Crossing P)) (q : Component hn hP S)
    (j : ZMod (ccpCornerCount hn hP S q)) (v : Visit P) (hj : ccpCornerMark hn hP S q j = Sum.inr v) :
    IsCrossing P {cornerInLabel hn hP S q j, cornerOutLabel hn hP S q j} := by
  sorry

/-! ### 3b. Uniformity is carried: every corner turn is `sign det(in, out)` of parent directions -/

/-- The sign of the parent in/out determinant at a true corner is the same on both sides: a vertex corner
by `turn_det` and the turn data, a selected-visit corner by the crossing-sign data
(`visit_crossing_val_eq_pair`). -/
theorem corner_det_sign_silentTransport (S : Finset (Crossing P)) (a : Mark P) (ha : IsTrueCorner S a) :
    SignType.sign (det (edge Q (ccpInEdge hn hP a)) (edge Q (ccpOutSlot hn hP S a).1)) =
      SignType.sign (det (edge P (ccpInEdge hn hP a)) (edge P (ccpOutSlot hn hP S a).1)) := by
  sorry

/-- The turns of the transported corner polygon are the turns of the corner polygon
(`ccpCornerPolygon_silentTransport`, `turn_recastTuple_cast`, `ccpCornerPolygon_turn_eq_sign` on both
sides, the label transports, `corner_det_sign_silentTransport`). -/
theorem turn_transportedCornerPolygon_silent {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (j : ZMod (ccpCornerCount hn hP S q)) :
    turn ((silentTransport hn hP hQ hd).transportedCornerPolygon S q) j =
      turn (ccpCornerPolygon hn hP S q) j := by
  sorry

theorem uniform_silentTransport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    (∃ σ : SignType, σ ≠ 0 ∧
        ∀ j, turn ((silentTransport hn hP hQ hd).transportedCornerPolygon S q) j = σ) ↔
      CarrierUniform hn hP S q := by
  simp only [turn_transportedCornerPolygon_silent hn hP hQ hd hS q]
  rfl

/-! ### 3c. The rotation as a sum of parent angles (unit U2, side identities) -/

/-- **lem:rot read on the parent directions.**  `r_Q = (1/2π) Σ_j ∠(d_in(c_j), d_out(c_j))`: each corner
polygon edge is a positive multiple of the parent direction of its outgoing slot (`ccpCornerPolygon_edge`,
`ccpCornerPolygon_edge_pred`), and the principal angle is invariant under positive scaling
(`principalAngle_smul`). -/
theorem carrierRotation_eq_sum_principalAngle {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    carrierRotation hn hP S q =
      (∑ j : ZMod (ccpCornerCount hn hP S q),
        principalAngle (edge P (cornerInLabel hn hP S q j)) (edge P (cornerOutLabel hn hP S q j))) /
        (2 * Real.pi) := by
  sorry

/-- The same for the transported carrier, indexed by the corners of the original carrier and its labels
(`Fintype.sum_equiv` along the cast, `ccpCornerMark_silentTransport`, the label transports). -/
theorem carrierRotation_silentTransport_eq_sum {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    carrierRotation hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q) =
      (∑ j : ZMod (ccpCornerCount hn hP S q),
        principalAngle (edge Q (cornerInLabel hn hP S q j)) (edge Q (cornerOutLabel hn hP S q j))) /
        (2 * Real.pi) := by
  sorry

/-! ### 3d. The crossings of a corner polygon are its unselected crossings at block positions (unit U3) -/

/-- A *block witness* for the pair of corner-polygon edges `{a, b}`: an unselected crossing of the carrier
whose visit `w` lies in the block of the corner `c_a` and whose twin lies in the block of `c_b`
(`BlockInterior` of `SM.LinkPositiveLift`). -/
def BlockWitness (S : Finset (Crossing P)) (q : Component hn hP S) (w : Visit P)
    (a b : ZMod (ccpCornerCount hn hP S q)) : Prop :=
  w.1 ∈ carrierCrossings hn hP S q ∧
  ∃ r r' : ℕ,
    (smoothingSuccessor hn hP S ^ r) (ccpCornerMark hn hP S q a) = Sum.inr w ∧
    BlockInterior hn hP S q a r ∧
    (smoothingSuccessor hn hP S ^ r') (ccpCornerMark hn hP S q b) = Sum.inr (visitTwin w) ∧
    BlockInterior hn hP S q b r'

/-- **The crossings of the corner polygon.**  `{a, b}` is a crossing of `Q = ccpCornerPolygon` iff it has a
block witness.  (⇐) the block points lie on the edges `a`, `b` (`mark_block` + `block_mark_eq`), `a ≠ b`
(`BlockInterior.visit_edge`, `visitTwin_edge_ne`), `a`, `b` not consecutive (`consecutive_meet`, the crossing
point is no corner: `carrier_selfIntersection_not_corner`).  (⇒) `nonadjacent_meet` gives the crossing
`c` and visit `w`; `mark_block` places `w`, `twin w` in blocks `a₁`, `b₁`; the crossing point is interior to
the edges `a, b, a₁, b₁`, so by `ccpCornerPolygon_no_triple` `{a₁, b₁} = {a, b}` (swap `w ↔ twin w` if
needed). -/
theorem isCrossing_ccp_iff {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (a b : ZMod (ccpCornerCount hn hP S q)) :
    IsCrossing (ccpCornerPolygon hn hP S q) {a, b} ↔ ∃ w : Visit P, BlockWitness hn hP S q w a b := by
  sorry

/-- The crossing point of the corner-polygon crossing `{a, b}` is the parent crossing point of its block
witness (`crossingPoint_unique_of_geometry` on the corner polygon, `crossingGeometry_of_single_generic`
+ `carrierShadow_generic`). -/
theorem crossingPoint_ccp_eq {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) {a b : ZMod (ccpCornerCount hn hP S q)}
    (hab : IsCrossing (ccpCornerPolygon hn hP S q) {a, b}) {w : Visit P}
    (hw : BlockWitness hn hP S q w a b) :
    crossingPoint (⟨{a, b}, hab⟩ : Crossing (ccpCornerPolygon hn hP S q)) = crossingPoint w.1 := by
  sorry

/-- Block witnesses are carried by the transport (`smoothingSuccessor_transport` iterated,
`ccpCornerMark_silentTransport`, `carrierCrossings_transport`, `twin_eq`, and `BlockInterior` through the
label transports). -/
theorem blockWitness_silentTransport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (w : Visit P) (a b : ZMod (ccpCornerCount hn hP S q)) :
    BlockWitness hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q) (visitTransport hd.hs w)
        (Equiv.cast (congrArg ZMod ((silentTransport hn hP hQ hd).ccpCornerCount_transport S q).symm) a)
        (Equiv.cast (congrArg ZMod ((silentTransport hn hP hQ hd).ccpCornerCount_transport S q).symm) b) ↔
      BlockWitness hn hP S q w a b := by
  sorry

/-- **The crossing pairs of the two corner polygons agree** (on the common index type of the transported
corner polygon). -/
theorem isCrossing_transportedCornerPolygon_silent {S : Finset (Crossing P)}
    (hS : IsDecomposition hn hP S) (q : Component hn hP S) (c : Finset (ZMod (ccpCornerCount hn hP S q))) :
    IsCrossing ((silentTransport hn hP hQ hd).transportedCornerPolygon S q) c ↔
      IsCrossing (ccpCornerPolygon hn hP S q) c := by
  sorry

/-! ### 3e. The named records of the two positive lifts agree (unit U4) -/

/-- The polygon component of the transported carrier, on the index type of the original carrier. -/
noncomputable abbrev transportedPolyComp {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) : PolyComp :=
  ⟨ccpCornerCount hn hP S q, ccpCornerCount_ge_three hn hP hS q,
    (silentTransport hn hP hQ hd).transportedCornerPolygon S q⟩

theorem carrierPolyComp_silentTransport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    carrierPolyComp hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q)
        (((silentTransport hn hP hQ hd).isDecomposition_transport S).mpr hS) =
      transportedPolyComp hn hP hQ hd hS q := by
  unfold carrierPolyComp transportedPolyComp
  rw [ccpCornerPolygon_silentTransport hn hP hQ hd S q]
  exact polyComp_recastTuple _ _ _ _

theorem transportedShadow_generic {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) : (Shadow.single (transportedPolyComp hn hP hQ hd hS q)).Generic := by
  have h := carrierShadow_generic hn hQ ((silentTransport hn hP hQ hd).support S)
    ((silentTransport hn hP hQ hd).component S q)
    (((silentTransport hn hP hQ hd).isDecomposition_transport S).mpr hS)
  unfold carrierShadow at h
  rw [carrierPolyComp_silentTransport hn hP hQ hd hS q] at h
  exact h

/-- The positive lift of the transported carrier, read on the original index type. -/
noncomputable def transportedLift {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) : Diagram :=
  (Shadow.single (transportedPolyComp hn hP hQ hd hS q)).positiveDiagram
    (transportedShadow_generic hn hP hQ hd hS q)

theorem positiveLift_silentTransport_eq {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    positiveLift hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q)
        (((silentTransport hn hP hQ hd).isDecomposition_transport S).mpr hS) =
      transportedLift hn hP hQ hd hS q := by
  unfold positiveLift transportedLift
  exact positiveDiagram_congr (congrArg Shadow.single (carrierPolyComp_silentTransport hn hP hQ hd hS q))
    _ _

/-- The occurrence bijection of the two lifts: through `Shadow.singleVisitEquiv` on both sides and the
canonical `visitTransport` along the common crossing pairs of the two corner polygons. -/
noncomputable def liftVisitEquiv {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    (positiveLift hn hP S q hS).Γ.Visit ≃ (transportedLift hn hP hQ hd hS q).Γ.Visit :=
  (Shadow.singleVisitEquiv (carrierPolyComp hn hP S q hS)).trans
    ((visitTransport (fun c => (isCrossing_transportedCornerPolygon_silent hn hP hQ hd hS q c).symm)).trans
      (Shadow.singleVisitEquiv (transportedPolyComp hn hP hQ hd hS q)).symm)

/-- The bijection preserves the pairing (`twin_unique` at the diagram level, `visitTransport_visitTwin`,
`singleDiagram_twin`-style argument). -/
theorem liftVisitEquiv_twin {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (v : (positiveLift hn hP S q hS).Γ.Visit) :
    liftVisitEquiv hn hP hQ hd hS q ((positiveLift hn hP S q hS).twin v) =
      (transportedLift hn hP hQ hd hS q).twin (liftVisitEquiv hn hP hQ hd hS q v) := by
  sorry

/-- The bijection preserves the over/under bit: the over strand of a positive lift is the strand `s` with
`det(dir s, dir other) > 0`; the directions are positive multiples of the parent out-edge directions of the
two blocks (`ccpCornerPolygon_edge`), the parent pair is a crossing of `P` (block witness,
`BlockInterior.visit_edge`), and its sign is carried (`SilentPairData.sign`). -/
theorem liftVisitEquiv_overBit {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (v : (positiveLift hn hP S q hS).Γ.Visit) :
    (transportedLift hn hP hQ hd hS q).overBit (liftVisitEquiv hn hP hQ hd hS q v) =
      (positiveLift hn hP S q hS).overBit v := by
  sorry

/-- The bijection preserves the traversal-coordinate order: strands (edge labels) are preserved, and on
one corner edge `a` the crossing parameter of an occurrence is an increasing affine function
`(μ − λ_a)/c_a` of the parent parameter `μ = edgeParameter P e f` of its block witness on the parent edge
`e = out_a` (`ccp_evaluation_eq_outSlot`, `ccpCornerPolygon_edge`, `crossingPoint_ccp_eq`,
`edgePoint_injective`), whose order is the same on both sides (`SilentPairData.ho`). -/
theorem liftVisitEquiv_visitCoord_lt {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (v w : (positiveLift hn hP S q hS).Γ.Visit) :
    (transportedLift hn hP hQ hd hS q).visitCoord (liftVisitEquiv hn hP hQ hd hS q v) <
        (transportedLift hn hP hQ hd hS q).visitCoord (liftVisitEquiv hn hP hQ hd hS q w) ↔
      (positiveLift hn hP S q hS).visitCoord v < (positiveLift hn hP S q hS).visitCoord w := by
  sorry

/-- Successor preservation from cyclic-order preservation (`nextVisit_comm_iff_visitBetween_iff`, one
component, `cycBetween` is a formula in `<`). -/
theorem liftVisitEquiv_nextVisit {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) (v : (positiveLift hn hP S q hS).Γ.Visit) :
    liftVisitEquiv hn hP hQ hd hS q ((positiveLift hn hP S q hS).nextVisit v) =
      (transportedLift hn hP hQ hd hS q).nextVisit (liftVisitEquiv hn hP hQ hd hS q v) := by
  have hcomp : ∀ v w : (positiveLift hn hP S q hS).Γ.Visit,
      (transportedLift hn hP hQ hd hS q).compOf (liftVisitEquiv hn hP hQ hd hS q v) =
          (transportedLift hn hP hQ hd hS q).compOf (liftVisitEquiv hn hP hQ hd hS q w) ↔
        (positiveLift hn hP S q hS).compOf v = (positiveLift hn hP S q hS).compOf w :=
    fun v w => iff_of_true (Subsingleton.elim (α := Fin 1) _ _) (Subsingleton.elim (α := Fin 1) _ _)
  refine ((positiveLift hn hP S q hS).nextVisit_comm_iff_visitBetween_iff
    (liftVisitEquiv hn hP hQ hd hS q) hcomp).mpr ?_ v
  intro v w u _ _
  unfold Diagram.VisitBetween cycBetween
  simp only [liftVisitEquiv_visitCoord_lt hn hP hQ hd hS q]

/-- **The named-record isomorphism of the two positive lifts** (lc:presentations' hypothesis). -/
noncomputable def liftRecordIso {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    RecordIso (positiveLift hn hP S q hS).record (transportedLift hn hP hQ hd hS q).record where
  e := Equiv.refl _
  Φ := liftVisitEquiv hn hP hQ hd hS q
  comp_eq := fun _ => Subsingleton.elim (α := Fin 1) _ _
  succ_eq := fun v => by
    rw [Diagram.record_succ_apply, Diagram.record_succ_apply]
    exact liftVisitEquiv_nextVisit hn hP hQ hd hS q v
  pair_eq := fun v => liftVisitEquiv_twin hn hP hQ hd hS q v
  bit_eq := fun v => liftVisitEquiv_overBit hn hP hQ hd hS q v
  sgn_eq := fun v => by
    show (transportedLift hn hP hQ hd hS q).sign _ = (positiveLift hn hP S q hS).sign _
    rw [positiveLift_sign]
    exact Shadow.positiveDiagram_sign _ _ _

/-- **lc:presentations + lp:core on the two sides**: equal `H⁺` polynomials. -/
theorem homfly_positiveLift_silent {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    homfly (positiveLift hn hQ ((silentTransport hn hP hQ hd).support S)
        ((silentTransport hn hP hQ hd).component S q)
        (((silentTransport hn hP hQ hd).isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn hP S q hS) := by
  rw [positiveLift_silentTransport_eq hn hP hQ hd hS q, ← P_eq_homfly, ← P_eq_homfly]
  exact (presentations _ _ ⟨liftRecordIso hn hP hQ hd hS q⟩).symm

end Transport

/-! ## §4. The rotation across the wall (unit U2, germ part) -/

section Rotation

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)

/-- The sum of the principal angles between the parent in/out directions at the corners of the carrier
`q` of `P`, read on an arbitrary polygon `T` (the function of the parameter of the printed limit
argument). -/
noncomputable def cornerAngleSum (S : Finset (Crossing P)) (q : Component hn hP S)
    (T : LabelledTuple n) : ℝ :=
  ∑ j : ZMod (ccpCornerCount hn hP S q),
    principalAngle (edge T (cornerInLabel hn hP S q j)) (edge T (cornerOutLabel hn hP S q j))

variable {g : WallGerm n} {δ : ℝ} (hI : SilentInterval hn g δ) {s : g.SideParameter} (hs : s.val < δ)

/-- The side transport from `P(−s)` to `P(+s)`. -/
noncomputable def sideTransport :
    MarkTransport hn (g.sideTuple false s).property (g.sideTuple true s).property :=
  silentTransport hn _ _ (hI.sidePairData hs)

/-- Off the centre the angle sum is `2π` times an integer: at a generic parameter `t` the sum is `2π r_Q`
of the transported carrier (`carrierRotation_silentTransport_eq_sum` for the pair `(P(−s), P(t))`,
`carrierRotation_exists_int`). -/
theorem cornerAngleSum_int_valued {S : Finset (Crossing (g.sideTuple false s).val)}
    (hS : IsDecomposition hn (g.sideTuple false s).property S)
    (q : Component hn (g.sideTuple false s).property S) (t : g.Parameter) (ht : |t.val| < δ)
    (ht0 : t.val ≠ 0) :
    ∃ k : ℤ, cornerAngleSum hn (g.sideTuple false s).property S q (g.curve t) = 2 * Real.pi * k := by
  sorry

/-- The angle sum is continuous on the silent interval: each corner's parent pair is a regular pair at
every parameter (vertex corners by `weak_regularPair_turn`, selected-visit corners by
`geometry_regularPair_crossing` with the crossing carried to `t` through the centre), and
`continuousAt_principalAngle` (`continuous_edge`, `g.continuous_curve`). -/
theorem cornerAngleSum_continuousAt {S : Finset (Crossing (g.sideTuple false s).val)}
    (hS : IsDecomposition hn (g.sideTuple false s).property S)
    (q : Component hn (g.sideTuple false s).property S) (t : g.Parameter) (ht : |t.val| < δ) :
    ContinuousAt (fun u : g.Parameter => cornerAngleSum hn (g.sideTuple false s).property S q (g.curve u))
      t := by
  sorry

/-- **lem:rot (ii) across the wall.**  The rotation of a carrier is the same on both sides: on the
preconnected `Set.Icc (−s) s` the angle sum is continuous and `2πℤ`-valued off the centre
(`eq_of_continuous_int_valued_off_point`), and at `±s` it is `2π r_Q` (`carrierRotation_eq_sum_principalAngle`,
`carrierRotation_silentTransport_eq_sum`). -/
theorem carrierRotation_sideTransport {S : Finset (Crossing (g.sideTuple false s).val)}
    (hS : IsDecomposition hn (g.sideTuple false s).property S)
    (q : Component hn (g.sideTuple false s).property S) :
    carrierRotation hn (g.sideTuple true s).property ((sideTransport hn hI hs).support S)
        ((sideTransport hn hI hs).component S q) =
      carrierRotation hn (g.sideTuple false s).property S q := by
  sorry

end Rotation

/-! ## §5. Assembly -/

section Assembly

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {g : WallGerm n} {δ : ℝ} (hI : SilentInterval hn g δ)
  {s : g.SideParameter} (hs : s.val < δ)

/-- The corner coefficients agree (`cornerCoefficient_transport` with the rotation and `H⁺` identities). -/
theorem cornerCoefficient_sideTransport {S : Finset (Crossing (g.sideTuple false s).val)}
    (hS : IsDecomposition hn (g.sideTuple false s).property S)
    (q : Component hn (g.sideTuple false s).property S) :
    cornerCoefficient hn (g.sideTuple true s).property ((sideTransport hn hI hs).support S)
        ((sideTransport hn hI hs).component S q)
        (((sideTransport hn hI hs).isDecomposition_transport S).mpr hS) =
      cornerCoefficient hn (g.sideTuple false s).property S q hS :=
  (sideTransport hn hI hs).cornerCoefficient_transport hS q (carrierRotation_sideTransport hn hI hs hS q)
    (homfly_positiveLift_silent hn _ _ (hI.sidePairData hs) hS q)

include hI hs in
/-- `C(P(+s)) = C(P(−s))` at one small side parameter (`cornerStateSum_transport`). -/
theorem cornerStateSum_side_pair :
    cornerStateSum hn (g.sideTuple true s).property = cornerStateSum hn (g.sideTuple false s).property :=
  (sideTransport hn hI hs).cornerStateSum_transport
    (fun S hS q => uniform_silentTransport hn _ _ (hI.sidePairData hs) hS q)
    (fun S hS q => cornerCoefficient_sideTransport hn hI hs hS q)

end Assembly

section Reduction

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g : WallGerm n)

/-- prop:C-chamber along one side: the state sum does not depend on the side parameter
(`labelledSide_eq_at`, `sideTuple_mem_labelledSide`, `cornerStateSum_eq_of_mem_labelledChamber`). -/
theorem cornerStateSum_side_const (b : Bool) (t t' : g.SideParameter) :
    cornerStateSum hn (g.sideTuple b t).property = cornerStateSum hn (g.sideTuple b t').property := by
  have h : g.sideTuple b t' ∈ labelledChamber (g.sideTuple b t) := by
    rw [← g.labelledSide_eq_at b t]
    exact g.sideTuple_mem_labelledSide b t'
  exact cornerStateSum_eq_of_mem_labelledChamber hn h

/-- prop:C-silent for a silent germ, at every pair of side parameters. -/
theorem cornerStateSum_silent (h : g.Silent) (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property := by
  obtain ⟨δ, hI⟩ := exists_silentInterval hn g h
  have hδr : δ / 2 < g.radius := by linarith [hI.pos, hI.le]
  let s : g.SideParameter := ⟨δ / 2, by constructor <;> linarith [hI.pos]⟩
  have hs : s.val < δ := by
    show δ / 2 < δ
    linarith [hI.pos]
  rw [cornerStateSum_side_const hn g true tp s, cornerStateSum_side_const hn g false tm s]
  exact cornerStateSum_side_pair hn hI hs

end Reduction

/-! ## §6. The fixed statement (verbatim from work/drafts/CSilent_statement.lean) -/

/-- prop:C-silent as printed: at a simple silent wall the corner state sums of the two sides agree. -/
structure CSilentData : Prop where
  /-- (E): "At a simple exterior-extension wall … `C(P₊) = C(P₋)`." -/
  extension : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n), g.ExtensionAt M a →
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property
  /-- (C): "… or a simple pure cut, `C(P₊) = C(P₋)`." -/
  cut : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (i j k : ZMod n), g.PureCutAt i j k →
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property

theorem prop_C_silent : CSilentData where
  extension := fun n _ hn g M a hE tp tm => cornerStateSum_silent hn g (Or.inl ⟨M, a, hE⟩) tp tm
  cut := fun n _ hn g i j k hC tp tm => cornerStateSum_silent hn g (Or.inr ⟨i, j, k, hC⟩) tp tm

end SM

#print axioms SM.prop_C_silent
