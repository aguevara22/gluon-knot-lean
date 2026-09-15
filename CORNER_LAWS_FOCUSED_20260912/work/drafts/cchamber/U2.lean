import SM.CornerStateSum
import SM.Chambers
import SM.ChamberPaths
import SM.CyclicChambers
import SM.CrossingTransport
import SM.GeometricInterlacement
import SM.GeometricCrossingStability
import SM.RotationContinuity
import SM.LinkMoves
import SM.VisitRelabel
import SM.InterlaceRelabel
import Mathlib.Topology.LocallyConstant.Basic

/-! # Skeleton FINAL for prop:C-chamber (chamber constancy of the corner state sum)

Plan: work/drafts/cchamber/PLAN_FINAL.md (route B with three grafts from route A).

Route.  A *mark transport* `Carrier.MarkTransport hn hP hQ` between two generic polygons (bijections
of vertex labels, crossings and visits over their crossings, carrying the sorted mark list of `P` to a
rotation of the sorted mark list of `Q`, preserving interlacement and the vertex turn signs) transports
the whole Carrier lane: the smoothing successor, the carriers (`Component`), their crossings and
`m_Q`, decompositions, true corners, the corner list up to rotation, and the index set
`uniformDecompositions` — the last *given* that uniformity is preserved, which is read on the
*transported corner polygon* `Φ = transportedCornerPolygon` (the corners of the old carrier evaluated
in the new polygon).  The corner state sum is carried once, per carrier, (i) uniformity of `Φ`
matches, (ii) `carrierRotation` agrees and (iii) `homfly` of the positive lifts agrees
(`cornerStateSum_transport`).

Two instances.  (i) `pathTransport γ 0 t` along `γ : Path P Q` in `GenericTuple n` (accepted
`SM.chambers`: constant chirotope, crossing set and same-edge parameter orders; the mark list is
carried *literally*, so the corner polygon of the transported carrier is a recast of `Φ t`); `Φ t` is
continuous in `t` and regular, so its rotation is constant (`rotationNumber_family_constant`) and its
turn signs are constant (continuous nonzero determinants); its crossing pairs are constant (accepted
`crossing_support_persists_of_geometry` + connectedness of `unitInterval`) and positivity persists, so
the positive lifts at `0` and `1` are related by a `Deform` (`Deform.of_family`) and `homfly` agrees
(`homfly_planar`).  (ii) `shiftTransport a` for the cyclic relabelling `shift a P`: `Φ` is literally
`ccpCornerPolygon`, so uniformity is trivial, the rotation agrees by `rotationNumber_shift`, and the
positive lifts differ by a cyclic re-indexing of the one component, a `Reparam`
(`reparam_positiveDiagram_single_shift`).

Descent (already closed, no sorry): `chamber (polygonProjection P) = polygonProjection '' labelledChamber P`
(accepted `projection_labelledChamber_eq_chamber`), `projection_eq_iff`, and labelled chambers are path
connected (`labelledChambers_open_pathConnected`).

Every lemma of the chain is stated; `sorry` marks the obligations of the six prover units of
PLAN_FINAL.md.  `SM.C_chamber` is proved from the chain. -/

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

/-! ## 0. Re-indexing a labelled tuple along an equality of sizes (unit U1b) -/

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

theorem forall_turn_recastTuple {k k' : ℕ} (hk : k' = k) (f : LabelledTuple k) (σ : SignType) :
    (∀ j, turn (recastTuple hk f) j = σ) ↔ ∀ j, turn f j = σ := by
  sorry

/-- The one-component shadow data is unchanged by a recast. -/
theorem polyComp_recastTuple {k k' : ℕ} (hk : k' = k) (h : 3 ≤ k) (h' : 3 ≤ k')
    (f : LabelledTuple k) : (PolyComp.mk k' h' (recastTuple hk f)) = PolyComp.mk k h f := by
  sorry

namespace Carrier

variable {n : ℕ} [NeZero n]

/-! ## 1. Mark transports: the combinatorial equivalence of two generic marked traversals -/

/-- A *mark transport* from the generic polygon `P` to the generic polygon `Q`: compatible bijections
of vertex labels, crossings and visits (visits over their crossings), carrying the sorted mark list of
`P` to a rotation of the sorted mark list of `Q` (hence commuting with `markSuccessor`), preserving
interlacement and the vertex turn signs.  (The visit twin is carried automatically, `twin_eq`.) -/
structure MarkTransport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : Generic P) (hQ : Generic Q) where
  /-- vertex relabelling -/
  vert : ZMod n ≃ ZMod n
  /-- crossing bijection -/
  cross : Crossing P ≃ Crossing Q
  /-- visit bijection -/
  visit : Visit P ≃ Visit Q
  /-- visits are carried over their crossings -/
  visit_fst : ∀ v, (visit v).1 = cross v.1
  /-- the sorted mark list of `Q` is a rotation of the transported sorted mark list of `P` -/
  markList_rotated :
    (markList hn hQ).IsRotated ((markList hn hP).map (Sum.map vert visit))
  /-- interlacement is preserved -/
  interlaces_iff : ∀ x y, Interlaces hn hQ (cross x) (cross y) ↔ Interlaces hn hP x y
  /-- vertex turn signs are preserved -/
  turn_eq : ∀ i, turn Q (vert i) = turn P i

namespace MarkTransport

variable {hn : 3 ≤ n} {P Q : LabelledTuple n} {hP : Generic P} {hQ : Generic Q}
  (τ : MarkTransport hn hP hQ)

/-- The induced bijection of marks. -/
def toMark : Mark P ≃ Mark Q := Equiv.sumCongr τ.vert τ.visit

theorem toMark_apply (m : Mark P) : τ.toMark m = Sum.map τ.vert τ.visit m := rfl

theorem toMark_inl (i : ZMod n) : τ.toMark (Sum.inl i) = Sum.inl (τ.vert i) := rfl

theorem toMark_inr (v : Visit P) : τ.toMark (Sum.inr v) = Sum.inr (τ.visit v) := rfl

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

/-! ### 1a. The twin, the successor and the smoothing successor (unit U1a) -/

/-- The visit twin is carried to the visit twin (`visitTwin_unique`: same crossing by `visit_fst`,
distinct by injectivity). -/
theorem twin_eq (v : Visit P) : τ.visit (visitTwin v) = visitTwin (τ.visit v) := by
  sorry

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

/-! ### 1b. Carriers, their crossings, decompositions, true corners (unit U1a) -/

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

/-! ### 1c. The corner list and the corner polygon (unit U1b) -/

/-- The mark list of the transported carrier is a rotation of the transported mark list
(`List.IsRotated.filter`, `List.filter_map`). -/
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

/-! ### 1d. Uniformity read on the transported corner polygon, the index set, the prefactor
(unit U2) -/

/-- Uniformity of the transported carrier is uniformity of the transported corner polygon
(`exists_ccpCornerPolygon_transport`, `forall_turn_recastTuple`, `turn_shift`, reindexing by
`Equiv.addRight r`). -/
theorem carrierUniform_iff_transported (S : Finset (Crossing P)) (q : Component hn hP S) :
    CarrierUniform hn hQ (τ.support S) (τ.component S q) ↔
      ∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ := by
  obtain ⟨r, hr⟩ := τ.exists_ccpCornerPolygon_transport S q
  unfold CarrierUniform
  rw [hr]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  rw [forall_turn_recastTuple]
  simp only [turn_shift]
  constructor
  · intro h j
    have := h (j - r)
    rwa [sub_add_cancel] at this
  · intro h j
    exact h _

theorem uniformDecomposition_transport {S : Finset (Crossing P)}
    (huni : ∀ q : Component hn hP S,
      (∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ) ↔
        CarrierUniform hn hP S q) :
    UniformDecomposition hn hQ (τ.support S) ↔ UniformDecomposition hn hP S := by
  unfold UniformDecomposition
  rw [(τ.component S).surjective.forall]
  exact forall_congr' fun q => (τ.carrierUniform_iff_transported S q).trans (huni q)

theorem mem_uniformDecompositions_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      (∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ) ↔
        CarrierUniform hn hP S q)
    (S : Finset (Crossing P)) :
    τ.support S ∈ uniformDecompositions hn hQ ↔ S ∈ uniformDecompositions hn hP := by
  rw [mem_uniformDecompositions, mem_uniformDecompositions]
  have hd : τ.support S ∈ independentSupports hn hQ ↔ S ∈ independentSupports hn hP :=
    τ.isDecomposition_transport S
  by_cases hS : IsDecomposition hn hP S
  · exact and_congr hd (τ.uniformDecomposition_transport (huni S hS))
  · constructor
    · rintro ⟨h, _⟩
      exact absurd (hd.mp h) hS
    · rintro ⟨h, _⟩
      exact absurd h hS

theorem leftTurns_transport : leftTurns Q = leftTurns P := by
  sorry
/- U2 NOTE (2026-09-13): `leftTurns_transport` is FALSE AS STATED and cannot be proved. Its
statement does not mention `τ`, so under Lean 4's variable-inclusion rule the section variable
`τ : MarkTransport hn hP hQ` (and `hn hP hQ`) is NOT a parameter of the theorem: its type is
`∀ {n} [NeZero n] {P Q : LabelledTuple n}, leftTurns Q = leftTurns P`
(check: `#check @SM.Carrier.MarkTransport.leftTurns_transport`; inside `by` the identifier `τ` is
unknown, and `τ.leftTurns_transport` is rejected — "no usable parameter of type `MarkTransport`").
Counterexample (n = 3): `P i = (i, i²)` (a convex arc, left turn at `1`, so `leftTurns P ≠ 0`)
against the constant tuple `Q` (all edges zero, every turn `0`, `leftTurns Q = 0`); machine-checked
as `leftTurns_transport_false_as_stated` below.  Intended fix (a one-token statement change, NOT made
here): prefix the theorem with `include τ in`.  The intended content is proved as
`leftTurns_eq_of_transport` (next), which the assembly `cornerStateSum_transport` uses. -/

/-- `leftTurns_transport` as stated is the universally quantified claim over `P Q`, and it is
false: the parabola `i ↦ (i, i²)` on `ZMod 3` has a left turn at `1`, the constant tuple has none. -/
theorem leftTurns_transport_false_as_stated :
    ¬ ∀ (P Q : LabelledTuple 3), leftTurns Q = leftTurns P := by
  intro h
  let P : LabelledTuple 3 := fun i => ((i.val : ℝ), ((i.val : ℝ)) ^ 2)
  let Q : LabelledTuple 3 := fun _ => (0, 0)
  have hQ : leftTurns Q = 0 := by
    unfold leftTurns
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    rw [turn_left]
    simp [Q, edge, det]
  have hP : leftTurns P ≠ 0 := by
    unfold leftTurns
    rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
    refine ⟨1, ?_⟩
    rw [Finset.mem_filter, turn_left]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h0 : ((1 : ZMod 3) - 1).val = 0 := by decide
    have h1 : (1 : ZMod 3).val = 1 := by decide
    have h2 : ((1 : ZMod 3) + 1).val = 2 := by decide
    have h3 : ((1 : ZMod 3) - 1 + 1).val = 1 := by decide
    simp only [P, edge, det, h0, h1, h2, h3]
    norm_num
  exact hP ((h P Q).symm.trans hQ)

include τ in
/-- The intended `leftTurns_transport`: the prefactor `ℓ` is carried by a mark transport
(`Finset.card_equiv τ.vert`, `turn_eq`). -/
theorem leftTurns_eq_of_transport : leftTurns Q = leftTurns P := by
  unfold leftTurns
  symm
  apply Finset.card_equiv τ.vert
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, τ.turn_eq]

/-! ### 1e. The state sum under a transport with equal corner coefficients (unit U2) -/

theorem cornerSlot_transport {S : Finset (Crossing P)} (q : Component hn hP S)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q) :
    cornerSlot hn hQ (τ.support S) (τ.component S q) = cornerSlot hn hP S q := by
  unfold cornerSlot carrierRotationInt
  rw [τ.carrierCrossingCount_transport S q, hrot]

theorem cornerCoefficient_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (q : Component hn hP S)
    (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) = carrierRotation hn hP S q)
    (hH : homfly (positiveLift hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS)) = homfly (positiveLift hn hP S q hS)) :
    cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt]
  unfold cornerHomfly
  rw [τ.cornerSlot_transport q hrot, hH]

theorem cornerProduct_transport {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S)
    (hcoef : ∀ q : Component hn hP S,
      cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerProduct hn hQ (τ.support S) ((τ.isDecomposition_transport S).mpr hS) =
      cornerProduct hn hP S hS := by
  unfold cornerProduct
  exact (Fintype.prod_equiv (τ.component S) _ _ fun q => (hcoef q).symm).symm

/-- **Assembly.** The corner state sum is carried by a mark transport under which uniformity
(read on the transported corner polygons) and the corner coefficients agree. -/
theorem cornerStateSum_transport
    (huni : ∀ (S : Finset (Crossing P)), IsDecomposition hn hP S → ∀ q : Component hn hP S,
      (∃ σ : SignType, σ ≠ 0 ∧ ∀ j, turn (τ.transportedCornerPolygon S q) j = σ) ↔
        CarrierUniform hn hP S q)
    (hcoef : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
      cornerCoefficient hn hQ (τ.support S) (τ.component S q)
        ((τ.isDecomposition_transport S).mpr hS) = cornerCoefficient hn hP S q hS) :
    cornerStateSum hn hQ = cornerStateSum hn hP := by
  unfold cornerStateSum
  rw [τ.leftTurns_eq_of_transport]
  congr 1
  -- the dependent summands as total functions of the underlying set (device of
  -- `cornerStateSum_eq_sum_independentSupports`)
  set g : Finset (Crossing P) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions hn hP then
      (-1) ^ S.card * cornerProduct hn hP S (isDecomposition_of_mem_uniformDecompositions hn hP h)
    else 0 with hg
  set g' : Finset (Crossing Q) → ℤ := fun S =>
    if h : S ∈ uniformDecompositions hn hQ then
      (-1) ^ S.card * cornerProduct hn hQ S (isDecomposition_of_mem_uniformDecompositions hn hQ h)
    else 0 with hg'
  have h1 : (∑ S ∈ (uniformDecompositions hn hQ).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hQ S.1 (isDecomposition_of_mem_uniformDecompositions hn hQ S.2)) =
      ∑ S ∈ (uniformDecompositions hn hQ).attach, g' S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg']
    rw [dite_eq_left S.2]
  have h2 : (∑ S ∈ (uniformDecompositions hn hP).attach,
      (-1) ^ S.1.card *
        cornerProduct hn hP S.1 (isDecomposition_of_mem_uniformDecompositions hn hP S.2)) =
      ∑ S ∈ (uniformDecompositions hn hP).attach, g S.1 := by
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hg]
    rw [dite_eq_left S.2]
  rw [h1, h2, Finset.sum_attach, Finset.sum_attach]
  symm
  -- reindex the index set along `τ.support`, a bijection `uD(P) → uD(Q)`
  refine Finset.sum_nbij τ.support ?_ ?_ ?_ ?_
  · intro S hS
    exact (τ.mem_uniformDecompositions_transport huni S).mpr hS
  · intro S _ T _ h
    exact Finset.map_injective τ.cross.toEmbedding h
  · intro S' hS'
    obtain ⟨S, rfl⟩ := τ.support_surjective S'
    exact ⟨S, (τ.mem_uniformDecompositions_transport huni S).mp hS', rfl⟩
  · intro S hS
    have hS' : IsDecomposition hn hP S := isDecomposition_of_mem_uniformDecompositions hn hP hS
    have hSQ : τ.support S ∈ uniformDecompositions hn hQ :=
      (τ.mem_uniformDecompositions_transport huni S).mpr hS
    simp only [hg, hg']
    rw [dite_eq_left hS, dite_eq_left hSQ, τ.support_card]
    congr 1
    exact (τ.cornerProduct_transport hS' (hcoef S hS')).symm

end MarkTransport

end Carrier

/-! ## 2c. Link-layer lemmas (units U4 and U5) -/

namespace Link

/-- Proof-irrelevant congruence of positive diagrams along an equality of shadows. -/
theorem positiveDiagram_congr {Γ Γ' : Shadow} (h : Γ = Γ') (hΓ : Γ.Generic) (hΓ' : Γ'.Generic) :
    Γ.positiveDiagram hΓ = Γ'.positiveDiagram hΓ' := by
  subst h
  rfl

/-- Crossing pairs of one-component shadows on two polygons with the same crossing supports. -/
theorem single_isCrossing_iff_of_forall {k : ℕ} (hk : 3 ≤ k) {X Y : LabelledTuple k}
    (h : ∀ s, IsCrossing X s ↔ IsCrossing Y s) (x : Finset (Shadow.single ⟨k, hk, X⟩).Strand) :
    (Shadow.single ⟨k, hk, X⟩).IsCrossing x ↔ (Shadow.single ⟨k, hk, Y⟩).IsCrossing x := by
  rw [Shadow.single_isCrossing_iff, Shadow.single_isCrossing_iff]
  exact h _

/-- (Graft from route A.)  A polygon whose one-component shadow is generic lies on the geometric
record domain: nonzero edges (`regular`), meetings of remote edges interior and transverse
(`tail_off`, `transverse`), no triple point (`no_triple`). -/
theorem crossingGeometry_of_single_generic {k : ℕ} (hk : 3 ≤ k) {T : LabelledTuple k}
    (h : (Shadow.single ⟨k, hk, T⟩).Generic) : CrossingGeometry T := by
  sorry

/-- A generic deformation from a family on the unit interval (`DeformData` with
`γ t := V (Set.projIcc 0 1 zero_le_one t)`). -/
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
(`StrandMap` `⟨i, a⟩ ↦ ⟨i, a + r⟩` with `f = id`, `sgn = 1`; the pullback of the positive diagram is
positive, hence the positive diagram of the shifted shadow; `ReparamData` with
`φ = traversalShiftEquiv r`, `traversalBetween_shift`, `traversalEvaluation_shift`; over occurrences
by `toFun_pullback_overStrand` and uniqueness of the crossing parameter on a nonzero edge). -/
theorem reparam_positiveDiagram_single_shift (C : PolyComp) (r : ZMod C.k)
    (hΓ : (Shadow.single C).Generic) (hΓ' : (Shadow.single ⟨C.k, C.hk, shift r C.P⟩).Generic) :
    Reparam ((Shadow.single C).positiveDiagram hΓ)
      ((Shadow.single ⟨C.k, C.hk, shift r C.P⟩).positiveDiagram hΓ') := by
  sorry

end Link

namespace Carrier

variable {n : ℕ} [NeZero n]

/-! ## 2. Transport along a path of generic polygons (unit U3) -/

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

variable {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]

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
  markList_rotated := by
    rw [markList_transport hn (γ s).2 (γ t).2 (path_crossing_iff hn γ s t)
      (generic_family_crossingParameterOrderAgrees hn γ.continuous s t)]
    exact List.IsRotated.refl _
  interlaces_iff := fun x y =>
    ((geometric_interlaces_transport (generic_crossingGeometry hn (γ s).2)
      (generic_crossingGeometry hn (γ t).2) (path_crossing_iff hn γ s t)
      (generic_family_crossingParameterOrderAgrees hn γ.continuous s t) x y)).symm
  turn_eq := fun i => generic_family_turn_constant γ.continuous t s i

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

/-- (Graft from route A.)  Turn signs of the transported corner polygon are constant along the
path: `turn = sign ∘ det` of consecutive edges, continuous in `t` and nonzero at every `t`
(`ccpCornerPolygon_turn_ne_zero` through `ccpCornerPolygon_pathTransport` and `turn_recastTuple`),
hence constant on the connected `unitInterval`. -/
theorem turn_transportedCornerPolygon_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval)
    (j : ZMod (ccpCornerCount hn (γ 0).2 S q)) :
    turn ((pathTransport hn γ 0 t).transportedCornerPolygon S q) j =
      turn (ccpCornerPolygon hn (γ 0).2 S q) j := by
  sorry

theorem uniform_transportedCornerPolygon_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval) :
    (∃ σ : SignType, σ ≠ 0 ∧
        ∀ j, turn ((pathTransport hn γ 0 t).transportedCornerPolygon S q) j = σ) ↔
      CarrierUniform hn (γ 0).2 S q := by
  simp only [turn_transportedCornerPolygon_path hn γ hS q t]
  rfl

/-- (Graft from route A.)  The crossing pairs of the transported corner polygon are constant along
the path: locally constant by the accepted `crossing_support_persists_of_geometry` at every
`t` (the corner polygon is on the geometric record domain, `crossingGeometry_of_single_generic`),
pulled back along the continuous family; constant on the connected `unitInterval`. -/
theorem isCrossing_transportedCornerPolygon_path {S : Finset (Crossing (γ 0).val)}
    (hS : IsDecomposition hn (γ 0).2 S) (q : Component hn (γ 0).2 S) (t : unitInterval)
    (s : Finset (ZMod (ccpCornerCount hn (γ 0).2 S q))) :
    IsCrossing ((pathTransport hn γ 0 t).transportedCornerPolygon S q) s ↔
      IsCrossing ((pathTransport hn γ 0 0).transportedCornerPolygon S q) s := by
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
    (pathTransport hn γ 0 1).cornerStateSum_transport
      (fun S hS q => uniform_transportedCornerPolygon_path hn γ hS q 1)
      (fun S hS q => cornerCoefficient_path hn γ hS q)
  have h0 : cornerStateSum hn (γ 0).2 = cornerStateSum hn P.2 :=
    congrArg (fun R : GenericTuple n => cornerStateSum hn R.2) γ.source
  have h1 : cornerStateSum hn (γ 1).2 = cornerStateSum hn Q.2 :=
    congrArg (fun R : GenericTuple n => cornerStateSum hn R.2) γ.target
  rw [← h0, ← h1, h01]

end PathTransport

/-! ## 3. Transport along a cyclic relabelling (unit U5) -/

section ShiftTransport

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (a : ZMod n)

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
  markList_rotated := markList_shift_rotated hn hP a
  interlaces_iff := interlaces_shift hn hP a
  turn_eq := fun i => by
    show turn (shift a P) (i + -a) = turn P i
    rw [turn_shift, neg_add_cancel_right]

/-- Relabelling does not move points: the transported corner polygon is the corner polygon. -/
theorem transportedCornerPolygon_shift (S : Finset (Crossing P)) (q : Component hn hP S) :
    (shiftTransport hn hP a).transportedCornerPolygon S q = ccpCornerPolygon hn hP S q := by
  sorry

theorem uniform_transportedCornerPolygon_shift (S : Finset (Crossing P)) (q : Component hn hP S) :
    (∃ σ : SignType, σ ≠ 0 ∧
        ∀ j, turn ((shiftTransport hn hP a).transportedCornerPolygon S q) j = σ) ↔
      CarrierUniform hn hP S q := by
  rw [transportedCornerPolygon_shift]
  rfl

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
  (shiftTransport hn hP a).cornerStateSum_transport
    (fun S _ q => uniform_transportedCornerPolygon_shift hn hP a S q)
    (fun _ hS q => cornerCoefficient_shift hn hP a hS q)

end ShiftTransport

end Carrier

/-! ## 4. Descent to the cyclic quotient and the theorem (closed) -/

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
