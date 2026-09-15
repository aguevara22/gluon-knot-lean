import SM.CornerStateSum
import SM.Chambers
import SM.ChamberPaths
import SM.CyclicChambers
import SM.CrossingTransport
import SM.GeometricInterlacement
import SM.RotationContinuity
import SM.LinkMoves
import SM.VisitRelabel
import SM.InterlaceRelabel

/-! # Skeleton B for prop:C-chamber (chamber constancy of the corner state sum)

Route (work/drafts/cchamber/PLAN_B.md): a *mark transport* `Carrier.MarkTransport hn hP hQ` between
two generic polygons (a bijection of vertices, crossings and visits, commuting with the visit twin,
carrying the sorted mark list to a rotation of the sorted mark list, and preserving interlacement,
vertex turns and smoothing-corner signs) transports the whole Carrier lane: the smoothing successor,
the carriers (`Component`), their crossings, `m_Q`, the true corners, the corner list (up to rotation),
uniformity, and the index set `uniformDecompositions`.  Two instances: (i) `pathTransport γ s t`
along a `Path` in `GenericTuple n` (from accepted `SM.chambers`: constant chirotope, crossing set and
parameter orders), where in addition the corner polygons form a continuous family of *regular* tuples
(so `carrierRotation` is constant by `rotationNumber_family_constant`) and the positive lifts are
related by a `Deform` (so `homfly` agrees by `homfly_planar`); (ii) `shiftTransport a` for the cyclic
relabelling `shift a P`, where the corner polygons are literally cyclic shifts of each other (so
`carrierRotation` agrees by `rotationNumber_shift`) and the positive lifts are related by a `Reparam`.
Then the descent: `chamber (polygonProjection P) = polygonProjection '' labelledChamber P`
(accepted `projection_labelledChamber_eq_chamber`), and labelled chambers are path connected.

Every lemma of the chain is stated with `sorry`; `SM.C_chamber` is proved from them. -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

/-! ## 0. Re-indexing a labelled tuple along an equality of sizes -/

/-- A labelled `k`-tuple read as a labelled `k'`-tuple along `hk : k' = k`. All invariants below
are proved by `subst hk`. -/
def recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) : LabelledTuple k' :=
  fun j => f (Equiv.cast (congrArg ZMod hk) j)

theorem recastTuple_rfl {k : ℕ} (f : LabelledTuple k) : recastTuple rfl f = f := rfl

theorem rotationNumber_recastTuple {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k)
    (f : LabelledTuple k) : rotationNumber (recastTuple hk f) = rotationNumber f := by
  sorry

theorem regular_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) :
    Regular (recastTuple hk f) ↔ Regular f := by
  sorry

theorem turn_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (j : ZMod k') :
    turn (recastTuple hk f) j = turn f (Equiv.cast (congrArg ZMod hk) j) := by
  sorry

theorem forall_turn_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (τ : SignType) :
    (∀ j, turn (recastTuple hk f) j = τ) ↔ ∀ j, turn f j = τ := by
  sorry

/-- The one-component shadow data is unchanged by a recast. -/
theorem polyComp_recastTuple {k k' : ℕ} (hk : k' = k) (h : 3 ≤ k) (h' : 3 ≤ k')
    (f : LabelledTuple k) : (PolyComp.mk k' h' (recastTuple hk f)) = PolyComp.mk k h f := by
  sorry

namespace Carrier

variable {n : ℕ} [NeZero n]

/-! ## 1. Mark transports: the combinatorial equivalence of two generic marked traversals -/

/-- A *mark transport* from the generic polygon `P` to the generic polygon `Q`: compatible bijections
of vertex labels, crossings and visits which commute with the visit twin, carry the sorted mark list
of `P` to a rotation of the sorted mark list of `Q` (hence commute with `markSuccessor`), preserve
interlacement, vertex turn signs and the smoothing-corner signs `sgn det(d_i, d_j)`. -/
structure MarkTransport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P) (hQ : Generic Q) where
  /-- vertex relabelling -/
  vert : ZMod n ≃ ZMod n
  /-- crossing bijection -/
  cross : Crossing P ≃ Crossing Q
  /-- visit bijection -/
  visit : Visit P ≃ Visit Q
  /-- visits are carried over their crossings -/
  visit_fst : ∀ v, (visit v).1 = cross v.1
  /-- the visit twin is carried to the visit twin -/
  twin_eq : ∀ v, visit (visitTwin v) = visitTwin (visit v)
  /-- the sorted mark list of `Q` is a rotation of the transported sorted mark list of `P` -/
  markList_rotated :
    (markList hn hQ).IsRotated ((markList hn hP).map (Sum.map vert visit))
  /-- interlacement is preserved -/
  interlaces_iff : ∀ x y, Interlaces hn hQ (cross x) (cross y) ↔ Interlaces hn hP x y
  /-- vertex turn signs are preserved -/
  turn_eq : ∀ i, turn Q (vert i) = turn P i
  /-- the smoothing-corner signs are preserved -/
  sign_eq : ∀ v : Visit P,
    crossingSign Q (visit v).2.val (visit (visitTwin v)).2.val =
      crossingSign P v.2.val (visitTwin v).2.val

namespace MarkTransport

variable {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
  (τ : MarkTransport hn hP hQ)

/-- The induced bijection of marks. -/
def toMark : Mark P ≃ Mark Q := Equiv.sumCongr τ.vert τ.visit

theorem toMark_apply (m : Mark P) : τ.toMark m = Sum.map τ.vert τ.visit m := rfl

/-- The transported support. -/
noncomputable def support (S : Finset (Crossing P)) : Finset (Crossing Q) :=
  S.map τ.cross.toEmbedding

theorem mem_support (S : Finset (Crossing P)) (x : Crossing P) :
    τ.cross x ∈ τ.support S ↔ x ∈ S := by
  simp only [support, Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem support_card (S : Finset (Crossing P)) : (τ.support S).card = S.card :=
  Finset.card_map _

theorem support_surjective (S' : Finset (Crossing Q)) : ∃ S, τ.support S = S' :=
  ⟨S'.map τ.cross.symm.toEmbedding, by
    simp [support, Finset.map_map]⟩

/-! ### 1a. The successor and the smoothing successor -/

/-- The cyclic successor commutes with the transport (from `markList_rotated` through
`List.isRotated_next_eq` and the `getElem` formula `markSuccessor_getElem`). -/
theorem markSuccessor_transport (m : Mark P) :
    markSuccessor hn hQ (τ.toMark m) = τ.toMark (markSuccessor hn hP m) := by
  sorry

theorem selectedMarkPerm_transport (S : Finset (Crossing P)) (m : Mark P) :
    selectedMarkPerm (τ.support S) (τ.toMark m) = τ.toMark (selectedMarkPerm S m) := by
  sorry

theorem smoothingSuccessor_transport (S : Finset (Crossing P)) (m : Mark P) :
    smoothingSuccessor hn hQ (τ.support S) (τ.toMark m) =
      τ.toMark (smoothingSuccessor hn hP S m) := by
  sorry

theorem sameCycle_transport (S : Finset (Crossing P)) (a b : Mark P) :
    (smoothingSuccessor hn hQ (τ.support S)).SameCycle (τ.toMark a) (τ.toMark b) ↔
      (smoothingSuccessor hn hP S).SameCycle a b := by
  sorry

/-! ### 1b. Carriers, their crossings, decompositions, true corners -/

/-- The carriers of `S` correspond to the carriers of the transported support. -/
noncomputable def component (S : Finset (Crossing P)) :
    Component hn hP S ≃ Component hn hQ (τ.support S) :=
  Quotient.congr τ.toMark (fun a b => (τ.sameCycle_transport S a b).symm)

theorem component_owner (S : Finset (Crossing P)) (m : Mark P) :
    τ.component S (owner hn hP S m) = owner hn hQ (τ.support S) (τ.toMark m) := rfl

theorem carrierCrossings_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossings hn hQ (τ.support S) (τ.component S q) =
      (carrierCrossings hn hP S q).map τ.cross.toEmbedding := by
  sorry

theorem carrierCrossingCount_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierCrossingCount hn hQ (τ.support S) (τ.component S q) =
      carrierCrossingCount hn hP S q := by
  sorry

theorem isDecomposition_transport (S : Finset (Crossing P)) :
    IsDecomposition hn hQ (τ.support S) ↔ IsDecomposition hn hP S := by
  sorry

theorem isTrueCorner_transport (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner (τ.support S) (τ.toMark m) ↔ IsTrueCorner S m := by
  sorry

/-! ### 1c. The corner list and the corner polygon -/

/-- The mark list of the transported carrier is a rotation of the transported mark list. -/
theorem componentMarkList_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    (componentMarkList hn hQ (τ.support S) (τ.component S q)).IsRotated
      ((componentMarkList hn hP S q).map τ.toMark) := by
  sorry

theorem ccpCornerList_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    (ccpCornerList hn hQ (τ.support S) (τ.component S q)).IsRotated
      ((ccpCornerList hn hP S q).map τ.toMark) := by
  sorry

theorem ccpCornerCount_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerCount hn hQ (τ.support S) (τ.component S q) = ccpCornerCount hn hP S q := by
  sorry

/-- The corner marks correspond up to a rotation `r` of the corner indices. -/
theorem exists_ccpCornerMark_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ r : ZMod (ccpCornerCount hn hP S q), ∀ j : ZMod (ccpCornerCount hn hP S q),
      ccpCornerMark hn hQ (τ.support S) (τ.component S q)
          (Equiv.cast (congrArg ZMod (τ.ccpCornerCount_transport S q).symm) j) =
        τ.toMark (ccpCornerMark hn hP S q (j + r)) := by
  sorry

/-- The corner polygon of the carrier `q` of `P` read at the geometry of `Q`: the vertex at the
corner mark `c_j` of `q` is the plane point of `Q` at the transported mark. -/
noncomputable def transportedCornerPolygon (S : Finset (Crossing P)) (q : Component hn hP S) :
    LabelledTuple (ccpCornerCount hn hP S q) :=
  fun j => traversalEvaluation Q (markPosition hn hQ.1 (τ.toMark (ccpCornerMark hn hP S q j)))

/-- The corner polygon of the transported carrier is the transported corner polygon, up to a
cyclic re-indexing. -/
theorem exists_ccpCornerPolygon_transport (S : Finset (Crossing P)) (q : Component hn hP S) :
    ∃ r : ZMod (ccpCornerCount hn hP S q),
      ccpCornerPolygon hn hQ (τ.support S) (τ.component S q) =
        recastTuple (τ.ccpCornerCount_transport S q) (shift r (τ.transportedCornerPolygon S q)) := by
  sorry

/-- When the mark list is carried literally (no rotation), so is the corner polygon. -/
theorem ccpCornerPolygon_transport_of_markList_eq
    (h : markList hn hQ = (markList hn hP).map τ.toMark)
    (S : Finset (Crossing P)) (q : Component hn hP S) :
    ccpCornerPolygon hn hQ (τ.support S) (τ.component S q) =
      recastTuple (τ.ccpCornerCount_transport S q) (τ.transportedCornerPolygon S q) := by
  sorry

/-! ### 1d. Turn signs, uniformity, the index set, the prefactor -/

/-- The turn of the transported carrier at the transported corner is the turn of `q` at the
corner (vertex corners by `turn_eq`, smoothing corners by `sign_eq` and `twin_eq`, through the
accepted `ccpCornerPolygon_turn_vertex` / `ccpCornerPolygon_turn_smoothing`). -/
theorem exists_turn_ccpCornerPolygon_transport {S : Finset (Crossing P)}
    (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    ∃ r : ZMod (ccpCornerCount hn hP S q), ∀ j : ZMod (ccpCornerCount hn hP S q),
      turn (ccpCornerPolygon hn hQ (τ.support S) (τ.component S q))
          (Equiv.cast (congrArg ZMod (τ.ccpCornerCount_transport S q).symm) j) =
        turn (ccpCornerPolygon hn hP S q) (j + r) := by
  sorry

theorem carrierUniform_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    CarrierUniform hn hQ (τ.support S) (τ.component S q) ↔ CarrierUniform hn hP S q := by
  sorry

theorem uniformDecomposition_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) :
    UniformDecomposition hn hQ (τ.support S) ↔ UniformDecomposition hn hP S := by
  sorry

theorem mem_uniformDecompositions_transport (S : Finset (Crossing P)) :
    τ.support S ∈ uniformDecompositions hn hQ ↔ S ∈ uniformDecompositions hn hP := by
  sorry

theorem leftTurns_transport : leftTurns Q = leftTurns P := by
  sorry

/-! ### 1e. The state sum under a transport with equal corner coefficients -/

theorem cornerSlot_transport {S : Finset (Crossing P)} (q : Component hn hP S)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q) :
    cornerSlot hn hQ (τ.support S) (τ.component S q) = cornerSlot hn hP S q := by
  sorry

theorem cornerCoefficient_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q)
    (hH : homfly (positiveLift hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS)) = homfly (positiveLift hn hP S q hS)) :
    cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS := by
  sorry

theorem cornerProduct_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (hcoef : ∀ q : Component hn hP S,
      cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerProduct hn hQ (τ.support S) ((τ.isDecomposition_transport S).mpr hS) =
      cornerProduct hn hP S hS := by
  sorry

/-- The corner state sum is carried by a mark transport whose corner coefficients agree. -/
theorem cornerStateSum_transport
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerStateSum hn hQ = cornerStateSum hn hP := by
  sorry

end MarkTransport

/-! ## 2. Transport along a path of generic polygons -/

section PathTransport

/-- The mark order is determined by the crossing set and the same-edge parameter orders
(vertex/vertex by label, vertex/visit by label and strict interiority, visit/visit by
`geometric_visitKey_lt_transport`). -/
theorem markKey_lt_transport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P)
    (hQ : Generic Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) (a b : Mark P) :
    markKey hn hQ.1 (Sum.map id (visitTransport hs) a) <
        markKey hn hQ.1 (Sum.map id (visitTransport hs) b) ↔
      markKey hn hP.1 a < markKey hn hP.1 b := by
  sorry

/-- Both sorted mark lists are sorted by keys whose order agrees: they are literally carried. -/
theorem markList_transport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P)
    (hQ : Generic Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) :
    markList hn hQ = (markList hn hP).map (Sum.map id (visitTransport hs)) := by
  sorry

theorem visitTransport_twin {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (v : Visit P) : visitTransport hs (visitTwin v) = visitTwin (visitTransport hs v) := by
  sorry

variable {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]

/-- The crossing sign `sgn det(d_i, d_j)` of an actual crossing is constant along a continuous
generic family (the determinant is continuous and nonzero, `crossing_edgeParameter_det_ne_zero`). -/
theorem generic_family_crossingSign_constant (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) (i j : ZMod n) (hij : IsCrossing (F s).val {i, j}) :
    crossingSign (F s).val i j = crossingSign (F t).val i j := by
  sorry

theorem generic_family_crossingParameterOrderAgrees (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) : CrossingParameterOrderAgrees (F s).val (F t).val := by
  sorry

omit [NeZero n] in
theorem generic_family_turn_constant {F : α → GenericTuple n} (hF : Continuous F) (s t : α)
    (i : ZMod n) : turn (F s).val i = turn (F t).val i :=
  generic_family_chi_constant hF s t _ _ _

variable (hn : 3 ≤ n) {P Q : GenericTuple n} (γ : Path P Q)
include hn γ

omit [NeZero n] in
theorem path_crossing_iff (s t : unitInterval) (c : Finset (ZMod n)) :
    IsCrossing (γ s).val c ↔ IsCrossing (γ t).val c :=
  generic_family_crossing_constant hn γ.continuous s t c

/-- The mark transport along a path, from time `s` to time `t`. -/
noncomputable def pathTransport (s t : unitInterval) : MarkTransport hn (γ s).2 (γ t).2 where
  vert := Equiv.refl _
  cross := crossingTransport (path_crossing_iff hn γ s t)
  visit := visitTransport (path_crossing_iff hn γ s t)
  visit_fst := fun _ => rfl
  twin_eq := visitTransport_twin _
  markList_rotated := by
    rw [markList_transport hn (γ s).2 (γ t).2 (path_crossing_iff hn γ s t)
      (generic_family_crossingParameterOrderAgrees hn γ.continuous s t)]
    exact List.IsRotated.refl _
  interlaces_iff := fun x y =>
    ((geometric_interlaces_transport (generic_crossingGeometry hn (γ s).2)
      (generic_crossingGeometry hn (γ t).2) (path_crossing_iff hn γ s t)
      (generic_family_crossingParameterOrderAgrees hn γ.continuous s t) x y)).symm
  turn_eq := fun i => generic_family_turn_constant γ.continuous t s i
  sign_eq := fun v => by
    sorry

theorem pathTransport_toMark_self (s : unitInterval) (m : Mark (γ s).val) :
    (pathTransport hn γ s s).toMark m = m := by
  sorry

theorem pathTransport_markList_eq (s t : unitInterval) :
    markList hn (γ t).2 = (markList hn (γ s).2).map (pathTransport hn γ s t).toMark :=
  markList_transport hn (γ s).2 (γ t).2 (path_crossing_iff hn γ s t)
    (generic_family_crossingParameterOrderAgrees hn γ.continuous s t)

/-! ### 2a. The corner polygons form a continuous family of regular tuples -/

/-- The crossing point of a persisting crossing moves continuously (Cramer: `edgeParameter` is
continuous, `generic_family_edgeParameter_continuous`). -/
theorem continuous_path_crossingPoint (c : Crossing (γ 0).val) :
    Continuous fun t : unitInterval => crossingPoint (crossingTransport (path_crossing_iff hn γ 0 t) c) := by
  sorry

theorem continuous_transportedCornerPolygon (S : Finset (Crossing (γ 0).val))
    (q : Component hn (γ 0).2 S) (j : ZMod (ccpCornerCount hn (γ 0).2 S q)) :
    Continuous fun t : unitInterval => (pathTransport hn γ 0 t).transportedCornerPolygon S q j := by
  sorry

theorem transportedCornerPolygon_zero (S : Finset (Crossing (γ 0).val))
    (q : Component hn (γ 0).2 S) :
    (pathTransport hn γ 0 0).transportedCornerPolygon S q = ccpCornerPolygon hn (γ 0).2 S q := by
  sorry

theorem ccpCornerPolygon_pathTransport (t : unitInterval) (S : Finset (Crossing (γ 0).val))
    (q : Component hn (γ 0).2 S) :
    ccpCornerPolygon hn (γ t).2 ((pathTransport hn γ 0 t).support S)
        ((pathTransport hn γ 0 t).component S q) =
      recastTuple ((pathTransport hn γ 0 t).ccpCornerCount_transport S q)
        ((pathTransport hn γ 0 t).transportedCornerPolygon S q) :=
  (pathTransport hn γ 0 t).ccpCornerPolygon_transport_of_markList_eq
    (pathTransport_markList_eq hn γ 0 t) S q

theorem regular_transportedCornerPolygon {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval) :
    Regular ((pathTransport hn γ 0 t).transportedCornerPolygon S q) := by
  sorry

/-- lem:rot (ii) along the path: the rotation of the carrier is constant. -/
theorem carrierRotation_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    carrierRotation hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q) = carrierRotation hn (γ 0).2 S q := by
  sorry

/-! ### 2b. The positive lifts are related by a generic deformation -/

/-- The carrier shadow at time `t` is the carrier shadow at time `0` re-vertexed with the
transported corner polygon (from `ccpCornerPolygon_pathTransport` and `polyComp_recastTuple`). -/
theorem carrierShadow_pathTransport (t : unitInterval) {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    carrierShadow hn (γ t).2 ((pathTransport hn γ 0 t).support S)
        ((pathTransport hn γ 0 t).component S q)
        (((pathTransport hn γ 0 t).isDecomposition_transport S).mpr hS) =
      (carrierShadow hn (γ 0).2 S q hS).withVertices
        (fun _ => (pathTransport hn γ 0 t).transportedCornerPolygon S q) := by
  sorry

theorem deform_positiveLift_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    Deform (positiveLift hn (γ 0).2 S q hS)
      (positiveLift hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q)
        (((pathTransport hn γ 0 1).isDecomposition_transport S).mpr hS)) := by
  sorry

theorem homfly_positiveLift_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    homfly (positiveLift hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q)
        (((pathTransport hn γ 0 1).isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn (γ 0).2 S q hS) :=
  (homfly_planar (PlanarIsotopic.of_deform (deform_positiveLift_path hn γ hS q))).symm

theorem cornerCoefficient_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) :
    cornerCoefficient hn (γ 1).2 ((pathTransport hn γ 0 1).support S)
        ((pathTransport hn γ 0 1).component S q)
        (((pathTransport hn γ 0 1).isDecomposition_transport S).mpr hS) =
      cornerCoefficient hn (γ 0).2 S q hS :=
  (pathTransport hn γ 0 1).cornerCoefficient_transport hS q (carrierRotation_path hn γ hS q)
    (homfly_positiveLift_path hn γ hS q)

/-- Constancy of `C` along a labelled path. -/
theorem cornerStateSum_path_constant : cornerStateSum hn P.2 = cornerStateSum hn Q.2 := by
  have h01 : cornerStateSum hn (γ 1).2 = cornerStateSum hn (γ 0).2 :=
    (pathTransport hn γ 0 1).cornerStateSum_transport fun S hS q => cornerCoefficient_path hn γ hS q
  have h0 : cornerStateSum hn (γ 0).2 = cornerStateSum hn P.2 :=
    congrArg (fun R : GenericTuple n => cornerStateSum hn R.2) γ.source
  have h1 : cornerStateSum hn (γ 1).2 = cornerStateSum hn Q.2 :=
    congrArg (fun R : GenericTuple n => cornerStateSum hn R.2) γ.target
  rw [← h0, ← h1, h01]

end PathTransport

/-! ## 2c. Link-layer lemmas used by the deformation -/

namespace Link

/-- Along a continuous family of vertex tuples through generic shadows, each pair of strands is a
crossing at every time or at no time (the set of times is clopen in the connected interval: closed
by compactness of the parameter square, open by persistence of transverse interior meetings). -/
theorem Shadow.isCrossing_constant_of_generic_family (Γ : Shadow)
    {V : unitInterval → Γ.Vertices}
    (hV : ∀ (i : Fin Γ.c) (j : ZMod (Γ.comp i).k), Continuous fun t => V t i j)
    (hgen : ∀ t, (Γ.withVertices (V t)).Generic) (x : Finset Γ.Strand) (s t : unitInterval) :
    (Γ.withVertices (V s)).IsCrossing x ↔ (Γ.withVertices (V t)).IsCrossing x := by
  sorry

/-- A generic deformation from a family on the unit interval. -/
theorem Deform.of_family (D : Diagram) {V : unitInterval → D.Γ.Vertices}
    (hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun t => V t i j)
    (hgen : ∀ t, (D.Γ.withVertices (V t)).Generic)
    (hcross : ∀ t (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x)
    (h0 : V 0 = D.Γ.vertices) :
    Deform D (D.deform (V 1) (hgen 1) (hcross 1)) := by
  sorry

/-- Positivity of every crossing persists along a generic deformation: the determinant of the
over and under directions is continuous and nonzero at every time. -/
theorem Diagram.isPositive_deform_of_family (D : Diagram) {V : unitInterval → D.Γ.Vertices}
    (hV : ∀ (i : Fin D.Γ.c) (j : ZMod (D.Γ.comp i).k), Continuous fun t => V t i j)
    (hgen : ∀ t, (D.Γ.withVertices (V t)).Generic)
    (hcross : ∀ t (x : Finset D.Γ.Strand),
      (D.Γ.withVertices (V t)).IsCrossing x ↔ D.Γ.IsCrossing x)
    (h0 : V 0 = D.Γ.vertices) (hpos : ∀ x, D.IsPositive x)
    (x : (D.deform (V 1) (hgen 1) (hcross 1)).Γ.Crossing) :
    (D.deform (V 1) (hgen 1) (hcross 1)).IsPositive x := by
  sorry

/-- A recast of the polygon does not change the positive diagram of a one-component shadow. -/
theorem positiveDiagram_single_recast {k k' : ℕ} (hk : k' = k) (h : 3 ≤ k) (h' : 3 ≤ k')
    (X : LabelledTuple k) (hΓ : (Shadow.single ⟨k', h', recastTuple hk X⟩).Generic)
    (hΓ' : (Shadow.single ⟨k, h, X⟩).Generic) :
    (Shadow.single ⟨k', h', recastTuple hk X⟩).positiveDiagram hΓ =
      (Shadow.single ⟨k, h, X⟩).positiveDiagram hΓ' := by
  sorry

/-- A cyclic shift of the labels of a one-component positive diagram is a reparametrization
(`φ = traversalShift r`, `traversalBetween_shift`, `traversalEvaluation_shift`; the over strand is
the positive one on both sides since `edge_shift` preserves the determinants). -/
theorem reparam_positiveDiagram_single_shift (C : PolyComp) (r : ZMod C.k)
    (hΓ : (Shadow.single C).Generic) (hΓ' : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Generic) :
    Reparam ((Shadow.single C).positiveDiagram hΓ)
      ((Shadow.single ⟨C.k, C.hk, shift r C.P⟩).positiveDiagram hΓ') := by
  sorry

end Link

/-! ## 3. Transport along a cyclic relabelling -/

section ShiftTransport

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (a : ZMod n)

theorem visitShift_twin (v : Visit P) :
    visitShiftEquiv a P (visitTwin v) = visitTwin (visitShiftEquiv a P v) := by
  sorry

/-- The sorted mark list of the relabelled polygon is a rotation of the relabelled sorted mark
list (`sorted_map_cut_rotation`, as for `gaussList_shift_rotation`). -/
theorem markList_shift_rotated :
    (markList hn ((generic_shift a P).mpr hP)).IsRotated
      ((markList hn hP).map (Sum.map (Equiv.addRight (-a)) (visitShiftEquiv a P))) := by
  sorry

/-- The mark transport of the cyclic relabelling `shift a P`. -/
noncomputable def shiftTransport : MarkTransport hn hP ((generic_shift a P).mpr hP) where
  vert := Equiv.addRight (-a)
  cross := crossingShiftEquiv a P
  visit := visitShiftEquiv a P
  visit_fst := fun _ => rfl
  twin_eq := visitShift_twin a
  markList_rotated := markList_shift_rotated hn hP a
  interlaces_iff := interlaces_shift hn hP a
  turn_eq := fun i => by
    sorry
  sign_eq := fun v => by
    sorry

/-- Relabelling does not move points: the transported corner polygon is the corner polygon. -/
theorem transportedCornerPolygon_shift (S : Finset (Crossing P)) (q : Component hn hP S) :
    (shiftTransport hn hP a).transportedCornerPolygon S q = ccpCornerPolygon hn hP S q := by
  sorry

theorem carrierRotation_shift (S : Finset (Crossing P)) (q : Component hn hP S) :
    carrierRotation hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q) = carrierRotation hn hP S q := by
  sorry

theorem reparam_positiveLift_shift {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    Reparam (positiveLift hn hP S q hS)
      (positiveLift hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q)
        (((shiftTransport hn hP a).isDecomposition_transport S).mpr hS)) := by
  sorry

theorem homfly_positiveLift_shift {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    homfly (positiveLift hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q)
        (((shiftTransport hn hP a).isDecomposition_transport S).mpr hS)) =
      homfly (positiveLift hn hP S q hS) :=
  (homfly_planar (PlanarIsotopic.of_reparam (reparam_positiveLift_shift hn hP a hS q))).symm

theorem cornerCoefficient_shift {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S) :
    cornerCoefficient hn ((generic_shift a P).mpr hP) ((shiftTransport hn hP a).support S)
        ((shiftTransport hn hP a).component S q)
        (((shiftTransport hn hP a).isDecomposition_transport S).mpr hS) =
      cornerCoefficient hn hP S q hS :=
  (shiftTransport hn hP a).cornerCoefficient_transport hS q (carrierRotation_shift hn hP a S q)
    (homfly_positiveLift_shift hn hP a hS q)

/-- "Cyclically shifting the vertex labels preserves `C`." -/
theorem cornerStateSum_shift :
    cornerStateSum hn ((generic_shift a P).mpr hP) = cornerStateSum hn hP :=
  (shiftTransport hn hP a).cornerStateSum_transport fun _ hS q => cornerCoefficient_shift hn hP a hS q

end ShiftTransport

end Carrier

/-! ## 4. Descent to the cyclic quotient and the theorem -/

variable {n : ℕ} [NeZero n]

theorem cornerStateSum_genericShift (hn : 3 ≤ n) (a : ZMod n) (P : GenericTuple n) :
    cornerStateSum hn (genericShift a P).2 = cornerStateSum hn P.2 :=
  Carrier.cornerStateSum_shift hn P.2 a

theorem cornerStateSum_eq_of_mem_labelledChamber (hn : 3 ≤ n) {P Q : GenericTuple n}
    (hQ : Q ∈ labelledChamber P) : cornerStateSum hn P.2 = cornerStateSum hn Q.2 := by
  obtain ⟨γ⟩ := ((labelledChambers_open_pathConnected hn P).2.joinedIn P mem_connectedComponent
    Q hQ).joined
  exact Carrier.cornerStateSum_path_constant hn γ

/-- prop:C-chamber as printed: "The state sum `C` of Definition def:C is constant on every chamber." -/
structure CChamberData : Prop where
  constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    polygonProjection Q ∈ chamber (polygonProjection P) →
    cornerStateSum hn P.2 = cornerStateSum hn Q.2

theorem C_chamber : CChamberData where
  constant := by
    intro n _ hn P Q hQ
    rw [← projection_labelledChamber_eq_chamber hn P] at hQ
    obtain ⟨Q', hQ', hproj⟩ := hQ
    obtain ⟨a, rfl⟩ := (projection_eq_iff Q' Q).mp hproj
    rw [cornerStateSum_genericShift hn a Q']
    exact cornerStateSum_eq_of_mem_labelledChamber hn hQ'

end SM
