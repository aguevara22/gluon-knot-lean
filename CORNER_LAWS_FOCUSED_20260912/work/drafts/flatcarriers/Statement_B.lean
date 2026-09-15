import SM.FlatSides
import SM.CarriersLemma
import SM.UniformDefinition
import SM.SmoothingDefinition

/-! Source def:flat-carriers (reference/SM/sm-3-statesum.tex:788-803, frame SM15) and
cor:flat-carriers (sm-3-statesum.tex:805-835, proof 838-913). STATEMENT DRAFT, tag B.
Main declarations: `SM.flat_carriers_definition` (def row) and `SM.flat_carriers` (cor row).

Design (tag B, "the same words define them, no genericity being assumed"). The accepted carrier
machinery (`SM.Carrier.markPosition`, `markSuccessor`, `smoothingSuccessor`, `Component`, `owner`,
`componentMarkList`, `componentPlaneCycle`, `ccpCornerPolygon`, ...) is parametrized by
`hP : Generic P`, and it uses genericity only for (a) the strict interiority of every crossing
parameter and (b) the injectivity of the visit positions; both are available on the accepted
geometric record domain `CrossingGeometry P` (`crossingParameter_interior_of_geometry`,
`geometricVisitPosition_injective`), which holds at the nongeneric flat centre
(`flat_crossingGeometry`). So this file restates the marked traversal circle, the successor, the
reconnection and the carriers directly on `CrossingGeometry P` (namespace `SM.GeoCarrier`,
prefix `geo`), word for word as the accepted `Generic` versions:
`geoMarkPosition` (vertex `i ↦ (i, 0)`, visit `v ↦ geometricVisitPosition hP v`),
`geoMarkList` (all marks sorted by traversal coordinate), `geoMarkSuccessor = ρ`,
`geoSmoothingSuccessor hP S = ρ_S = ρ ∘ selectedMarkPerm S` (the reconnection of def:smoothing /
conv:selected-visits, the SAME `selectedMarkPerm` as the accepted library),
`GeoComponent hP S` = cycles of `ρ_S` = the carriers, `geoOwner`, `geoComponentMarkList` (the
marks of a carrier in inherited order), `geoComponentPlaneCycle` (the traced closed polygonal
cycle), `geoSmoothingSegment` (the inherited straight subsegment from a mark to its `ρ_S`-successor),
`geoComponentCornerList` / `geoCornerCount` / `geoCornerPolygon` (the carrier at its corners:
original vertices and selected visits, in inherited order), `geoCornerTurn` (the turn of a carrier
at one of its corner marks), `geoCarrierCrossings` (the retained crossings of a carrier),
`carrierSelector` (cor (iii)). The four flat configurations are instances of ONE definition:
centre `g.center` with `flat_crossingGeometry`, deletion `deleteVertex g.center j` with
`generic_crossingGeometry ∘ generic_deleteVertex`, sides `(g.sideTuple b t).val` with
`generic_crossingGeometry`. On a generic `P` the geo machinery coincides with the accepted one
(`geoMarkPosition_eq_generic`; the successor/list/component agreement is stated in the def row,
field `sides_are_smoothing_carriers`).

The visit identifications are the accepted transports: sides ↔ centre through
`visitTransport hs` / `crossingTransport hs` where `hs : ∀ s, IsCrossing g.center s ↔ IsCrossing
(side) s` (the identification of `GeometricRecordsAgree`, lem:flat-sides (ii)), extended to marks by
`markTransport hs` (vertices fixed); deletion ↔ centre through `fusionVisitEquiv` /
`fusionCrossingEquiv` (lem:flat-sides (iii)), extended to marks by `fusionMark : Mark D → Mark C`
(vertex `i ↦ deletionIndex j i`, visit `w ↦ fusionVisitEquiv⁻¹ w`) and its left inverse `delMark`.
"Corresponding carriers" are the carriers of corresponding marks. Right side = the side `b` with
`turn (side b t) j = -1` (sm-1-polygons.tex:743-744), left side `= +1`; `FlatSidesData` fixes no
side as right, only that the two signs are opposite, so both sides are quantified by `b : Bool`. -/

namespace SM

open Carrier

namespace GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 1. The marked traversal circle on the geometric record domain -/

/-- "mark the traversal circle at every original vertex and every crossing visit": the position
of a mark, an original vertex at `(i, 0)`, a crossing visit at its actual crossing parameter on the
visited edge. Word for word `Carrier.markPosition`, with `CrossingGeometry` in place of `G1`. -/
def geoMarkPosition (hP : CrossingGeometry P) : Mark P → TraversalPoint n
  | Sum.inl i => (i, ⟨0, by norm_num⟩)
  | Sum.inr v => geometricVisitPosition hP v

omit [NeZero n] in
theorem geoMarkPosition_vertex (hP : CrossingGeometry P) (i : ZMod n) :
    geoMarkPosition hP (Sum.inl i) = (i, ⟨0, by norm_num⟩) := rfl

omit [NeZero n] in
theorem geoMarkPosition_visit (hP : CrossingGeometry P) (v : Visit P) :
    geoMarkPosition hP (Sum.inr v) = geometricVisitPosition hP v := rfl

omit [NeZero n] in
theorem geoMarkPosition_evaluation_vertex (hP : CrossingGeometry P) (i : ZMod n) :
    traversalEvaluation P (geoMarkPosition hP (Sum.inl i)) = P i := by
  simp [geoMarkPosition, traversalEvaluation, edgePoint]

omit [NeZero n] in
theorem geoMarkPosition_evaluation_visit (hP : CrossingGeometry P) (v : Visit P) :
    traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) = crossingPoint v.1 :=
  geometricVisitPosition_evaluation hP v

omit [NeZero n] in
/-- On a generic polygon the geometric mark position is the accepted one. -/
theorem geoMarkPosition_eq_generic (hn : 3 ≤ n) (hP : Generic P) (a : Mark P) :
    geoMarkPosition (generic_crossingGeometry hn hP) a = markPosition hn hP.1 a := by
  cases a <;> rfl

omit [NeZero n] in
/-- Marks have distinct positions: a visit parameter is strictly interior, and visit positions are
injective on the geometric record domain (no genericity). -/
theorem geoMarkPosition_injective (hP : CrossingGeometry P) :
    Function.Injective (geoMarkPosition hP) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (congrArg Prod.fst hab)
    | inr v =>
      have he : (0 : ℝ) = visitParameter v := congrArg (fun x => x.2.val) hab
      exact ((ne_of_gt (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1)
        he.symm).elim
  | inr v =>
    cases b with
    | inl i =>
      have he : visitParameter v = (0 : ℝ) := congrArg (fun x => x.2.val) hab
      exact ((ne_of_gt (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1)
        he).elim
    | inr w => exact congrArg Sum.inr (geometricVisitPosition_injective hP hab)

def geoMarkKey (hP : CrossingGeometry P) (a : Mark P) : ℝ := traversalKey (geoMarkPosition hP a)

theorem geoMarkKey_injective (hP : CrossingGeometry P) : Function.Injective (geoMarkKey hP) :=
  traversalKey_injective.comp (geoMarkPosition_injective hP)

@[instance_reducible]
def geoMarkLinearOrder (hP : CrossingGeometry P) : LinearOrder (Mark P) :=
  LinearOrder.lift' (geoMarkKey hP) (geoMarkKey_injective hP)

/-- All marks sorted by traversal coordinate: a linear representative of the marked traversal
circle, cut at the vertex `0`. -/
def geoMarkList (hP : CrossingGeometry P) : List (Mark P) := by
  classical
  letI := geoMarkLinearOrder hP
  exact Finset.univ.sort

theorem geoMarkList_nodup (hP : CrossingGeometry P) : (geoMarkList hP).Nodup := by
  classical
  let _ := geoMarkLinearOrder hP
  exact Finset.sort_nodup _ _

theorem mem_geoMarkList (hP : CrossingGeometry P) (a : Mark P) : a ∈ geoMarkList hP := by
  classical
  let _ := geoMarkLinearOrder hP
  exact (Finset.mem_sort _).mpr (Finset.mem_univ a)

theorem geoMarkList_sorted (hP : CrossingGeometry P) :
    (geoMarkList hP).Pairwise (fun a b => geoMarkKey hP a ≤ geoMarkKey hP b) := by
  classical
  let _ := geoMarkLinearOrder hP
  exact Finset.pairwise_sort _ _

/-- The marked traversal circle itself: the rotation class of the sorted list. -/
def geoMarkCycle (hP : CrossingGeometry P) : Cycle (Mark P) := (geoMarkList hP : Cycle (Mark P))

theorem geoMarkCycle_nodup (hP : CrossingGeometry P) : (geoMarkCycle hP).Nodup :=
  geoMarkList_nodup hP

theorem mem_geoMarkCycle (hP : CrossingGeometry P) (a : Mark P) : a ∈ geoMarkCycle hP :=
  mem_geoMarkList hP a

def geoNextMark (hP : CrossingGeometry P) (a : Mark P) : Mark P :=
  (geoMarkCycle hP).next (geoMarkCycle_nodup hP) a (mem_geoMarkCycle hP a)

def geoPrevMark (hP : CrossingGeometry P) (a : Mark P) : Mark P :=
  (geoMarkCycle hP).prev (geoMarkCycle_nodup hP) a (mem_geoMarkCycle hP a)

theorem geoNextMark_eq_list_next (hP : CrossingGeometry P) (a : Mark P) :
    geoNextMark hP a = (geoMarkList hP).next a (mem_geoMarkList hP a) := rfl

theorem geoPrevMark_geoNextMark (hP : CrossingGeometry P) (a : Mark P) :
    geoPrevMark hP (geoNextMark hP a) = a :=
  Cycle.prev_next (geoMarkCycle hP) (geoMarkCycle_nodup hP) a (mem_geoMarkCycle hP a)

theorem geoNextMark_geoPrevMark (hP : CrossingGeometry P) (a : Mark P) :
    geoNextMark hP (geoPrevMark hP a) = a :=
  Cycle.next_prev (geoMarkCycle hP) (geoMarkCycle_nodup hP) a (mem_geoMarkCycle hP a)

/-- `ρ`, the successor permutation of the marked traversal circle (the "outgoing successor" of
every mark). -/
def geoMarkSuccessor (hP : CrossingGeometry P) : Equiv.Perm (Mark P) where
  toFun := geoNextMark hP
  invFun := geoPrevMark hP
  left_inv := geoPrevMark_geoNextMark hP
  right_inv := geoNextMark_geoPrevMark hP

@[simp]
theorem geoMarkSuccessor_apply (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkSuccessor hP a = geoNextMark hP a := rfl

theorem geoMarkSuccessor_getElem (hP : CrossingGeometry P) (i : ℕ)
    (hi : i < (geoMarkList hP).length) :
    geoMarkSuccessor hP ((geoMarkList hP)[i]'hi) =
      (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  change (geoMarkList hP).next ((geoMarkList hP)[i]'hi)
    (mem_geoMarkList hP ((geoMarkList hP)[i]'hi)) = _
  exact List.next_getElem (geoMarkList hP) (geoMarkList_nodup hP) i hi

theorem geoMarkSuccessor_sameCycle_getElem (hP : CrossingGeometry P) (i : ℕ)
    (hi : i < (geoMarkList hP).length) :
    (geoMarkSuccessor hP).SameCycle
      ((geoMarkList hP)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le i) hi)) ((geoMarkList hP)[i]'hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      exact Equiv.Perm.SameCycle.refl _ _
  | succ i ih =>
      intro hi
      have hi' : i < (geoMarkList hP).length := (Nat.lt_succ_self i).trans hi
      have hc := (ih hi').apply_right
      rw [geoMarkSuccessor_getElem hP i hi'] at hc
      simpa only [Nat.mod_eq_of_lt hi] using hc

/-- Before any reconnection the marked circle is one cycle of `ρ`. -/
theorem geoMarkSuccessor_sameCycle (hP : CrossingGeometry P) (a b : Mark P) :
    (geoMarkSuccessor hP).SameCycle a b := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP a)
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP b)
  exact (geoMarkSuccessor_sameCycle_getElem hP i hi).symm.trans
    (geoMarkSuccessor_sameCycle_getElem hP k hk)

/-! ## 2. The reconnection and the carriers -/

/-- `ρ_S = ρ ∘ selectedMarkPerm S`: "exchange the two outgoing successors at the two visits of
every selected crossing" (def:smoothing with conv:selected-visits). The SAME `selectedMarkPerm`
as the accepted library; only `ρ` is read on the geometric record domain. -/
def geoSmoothingSuccessor (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    Equiv.Perm (Mark P) :=
  (selectedMarkPerm S).trans (geoMarkSuccessor hP)

theorem geoSmoothingSuccessor_apply (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (a : Mark P) : geoSmoothingSuccessor hP S a = geoMarkSuccessor hP (selectedMarkPerm S a) := rfl

theorem geoSmoothingSuccessor_vertex (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (i : ZMod n) : geoSmoothingSuccessor hP S (Sum.inl i) = geoMarkSuccessor hP (Sum.inl i) := rfl

theorem geoSmoothingSuccessor_visit_of_mem (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (v : Visit P) (hv : v.1 ∈ S) :
    geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr (visitTwin v)) := by
  change geoMarkSuccessor hP (Sum.inr (selectedVisitTwin S v)) = _
  rw [selectedVisitTwin_of_mem S v hv]

theorem geoSmoothingSuccessor_visit_of_not_mem (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr v) := by
  change geoMarkSuccessor hP (Sum.inr (selectedVisitTwin S v)) = _
  rw [selectedVisitTwin_of_not_mem S v hv]

/-- The carriers of `S`: the cycles of `ρ_S` ("trace the resulting oriented closed cycles"). -/
def GeoComponent (hP : CrossingGeometry P) (S : Finset (Crossing P)) :=
  Quotient (Equiv.Perm.SameCycle.setoid (geoSmoothingSuccessor hP S))

/-- The carrier through a mark (incoming-visit convention: a mark keeps its own cycle). -/
def geoOwner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    GeoComponent hP S :=
  Quotient.mk _ a

theorem geoOwner_eq_iff (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a b : Mark P) :
    geoOwner hP S a = geoOwner hP S b ↔ (geoSmoothingSuccessor hP S).SameCycle a b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem geoOwner_successor (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    geoOwner hP S (geoSmoothingSuccessor hP S a) = geoOwner hP S a :=
  (geoOwner_eq_iff hP S _ _).mpr (Equiv.Perm.SameCycle.refl _ a).apply_left

theorem geoOwner_predecessor (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    geoOwner hP S ((geoSmoothingSuccessor hP S).symm a) = geoOwner hP S a :=
  (geoOwner_eq_iff hP S _ _).mpr (Equiv.Perm.SameCycle.refl _ a).symm_apply_left

theorem geoOwner_surjective (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    Function.Surjective (geoOwner hP S) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact ⟨a, rfl⟩

instance geoComponentFintype (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    Fintype (GeoComponent hP S) :=
  Quotient.fintype _

/-- The marks of a carrier in the cyclic order inherited from the marked traversal circle
(the accepted `componentMarkList`, word for word). -/
def geoComponentMarkList (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : List (Mark P) :=
  (geoMarkList hP).filter (fun m => decide (geoOwner hP S m = q))

theorem mem_geoComponentMarkList (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (m : Mark P) :
    m ∈ geoComponentMarkList hP S q ↔ geoOwner hP S m = q := by
  simp only [geoComponentMarkList, List.mem_filter, mem_geoMarkList, true_and, decide_eq_true_eq]

theorem geoComponentMarkList_nodup (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : (geoComponentMarkList hP S q).Nodup :=
  (geoMarkList_nodup hP).filter _

theorem geoComponentMarkList_length_pos (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : 0 < (geoComponentMarkList hP S q).length := by
  obtain ⟨a, ha⟩ := geoOwner_surjective hP S q
  exact List.length_pos_of_mem ((mem_geoComponentMarkList hP S q a).mpr ha)

/-- The oriented closed polygonal cycle traced by a carrier: the plane points of its marks in
inherited cyclic order (the accepted `componentPlaneCycle`, word for word). -/
def geoComponentPlaneCycle (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : Cycle Plane :=
  ((geoComponentMarkList hP S q).map (fun m => traversalEvaluation P (geoMarkPosition hP m)) :
    Cycle Plane)

/-- The inherited straight subsegment from a mark to its `ρ_S`-successor (the accepted
`smoothingSegment`, word for word). -/
def geoSmoothingSegment (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P)
    (u : ℝ) : Plane :=
  traversalEvaluation P (geoMarkPosition hP a) +
    u • (traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) -
      traversalEvaluation P (geoMarkPosition hP a))

/-! ## 3. Corners, the corner polygon, turns, retained crossings, selector -/

/-- The owner block of a carrier is invariant under `ρ_S` (in both directions). -/
theorem geoSmoothingSuccessor_bijOn_owner (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) :
    Set.BijOn (geoSmoothingSuccessor hP S) {m | geoOwner hP S m = q} {m | geoOwner hP S m = q} := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    change geoOwner hP S (geoSmoothingSuccessor hP S a) = q
    rw [geoOwner_successor]
    exact ha
  · intro a _ b _ hab
    exact (geoSmoothingSuccessor hP S).injective hab
  · intro a ha
    refine ⟨(geoSmoothingSuccessor hP S).symm a, ?_, Equiv.apply_symm_apply _ a⟩
    change geoOwner hP S ((geoSmoothingSuccessor hP S).symm a) = q
    rw [geoOwner_predecessor]
    exact ha

/-- Every carrier has a corner (an original vertex or a selected visit): a carrier without one
would be a cycle of `ρ`, which has a single cycle through the vertex `0`. -/
theorem geoComponent_has_trueCorner (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : ∃ a : Mark P, geoOwner hP S a = q ∧ IsTrueCorner S a := by
  by_contra hnoc
  have hnone : ∀ a : Mark P, geoOwner hP S a = q → ¬ IsTrueCorner S a := by
    intro a ha hc
    exact hnoc ⟨a, ha, hc⟩
  obtain ⟨m, hm⟩ := geoOwner_surjective hP S q
  have he : Set.EqOn (geoSmoothingSuccessor hP S) (geoMarkSuccessor hP)
      {a | geoOwner hP S a = q} := by
    intro a ha
    cases a with
    | inl i => exact False.elim (hnone (Sum.inl i) ha (isTrueCorner_vertex S i))
    | inr v => exact geoSmoothingSuccessor_visit_of_not_mem hP S v (hnone (Sum.inr v) ha)
  have hc : (geoSmoothingSuccessor hP S).SameCycle m (Sum.inl (0 : ZMod n)) :=
    (sameCycle_congr_of_eqOn_bijOn (geoSmoothingSuccessor hP S) (geoMarkSuccessor hP)
      {a | geoOwner hP S a = q} (geoSmoothingSuccessor_bijOn_owner hP S q) he
      m hm (Sum.inl (0 : ZMod n))).mp (geoMarkSuccessor_sameCycle hP m (Sum.inl 0))
  have hv : geoOwner hP S (Sum.inl (0 : ZMod n)) = q :=
    ((geoOwner_eq_iff hP S m (Sum.inl 0)).mpr hc).symm.trans hm
  exact hnone (Sum.inl (0 : ZMod n)) hv (isTrueCorner_vertex S 0)

/-- The corners of a carrier in inherited cyclic order: its marks that are original vertices or
selected visits (`IsTrueCorner`, the accepted `ccpCornerList`, word for word). -/
def geoComponentCornerList (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : List (Mark P) :=
  (geoComponentMarkList hP S q).filter (fun a => decide (IsTrueCorner S a))

theorem mem_geoComponentCornerList (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (a : Mark P) :
    a ∈ geoComponentCornerList hP S q ↔ geoOwner hP S a = q ∧ IsTrueCorner S a := by
  simp only [geoComponentCornerList, List.mem_filter, mem_geoComponentMarkList,
    decide_eq_true_eq]

theorem geoComponentCornerList_nodup (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : (geoComponentCornerList hP S q).Nodup :=
  (geoComponentMarkList_nodup hP S q).filter _

theorem geoComponentCornerList_length_pos (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : 0 < (geoComponentCornerList hP S q).length := by
  obtain ⟨a, ha, hac⟩ := geoComponent_has_trueCorner hP S q
  exact List.length_pos_of_mem ((mem_geoComponentCornerList hP S q a).mpr ⟨ha, hac⟩)

/-- `c`, the number of corners (= turns) of a carrier. -/
def geoCornerCount (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    ℕ :=
  (geoComponentCornerList hP S q).length

instance geoCornerCount_neZero (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : NeZero (geoCornerCount hP S q) :=
  ⟨(geoComponentCornerList_length_pos hP S q).ne'⟩

/-- The `k`-th corner mark of a carrier, in inherited cyclic order. -/
def geoCornerMark (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) : Mark P :=
  (geoComponentCornerList hP S q)[k.val]'(ZMod.val_lt k)

/-- The carrier read as a closed polygon at its corners (the accepted `ccpCornerPolygon`, word for
word): its turns, rotation number and selector are those of this labelled tuple. -/
def geoCornerPolygon (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    LabelledTuple (geoCornerCount hP S q) :=
  fun k => traversalEvaluation P (geoMarkPosition hP (geoCornerMark hP S q k))

/-- The index of a mark among the corners of its own carrier (junk if the mark is not a corner). -/
def geoCornerIndex (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) :
    ZMod (geoCornerCount hP S (geoOwner hP S a)) :=
  ((geoComponentCornerList hP S (geoOwner hP S a)).idxOf a : ZMod _)

/-- The turn of a carrier at one of its corner marks `a` (`τ ∈ {-1, 0, 1}`, `+1` = left turn). -/
def geoCornerTurn (hP : CrossingGeometry P) (S : Finset (Crossing P)) (a : Mark P) : SignType :=
  turn (geoCornerPolygon hP S (geoOwner hP S a)) (geoCornerIndex hP S a)

/-- The retained (self-)crossings of a carrier: the unselected crossings both of whose visits it
owns (def:smoothing, the accepted `carrierCrossings`, word for word). -/
def geoCarrierCrossings (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : Finset (Crossing P) :=
  Finset.univ.filter fun x : Crossing P =>
    x ∉ S ∧ ∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q

/-- `S` is independent in the interlacement graph read on the geometric record domain. -/
def GeoIndependent (hP : CrossingGeometry P) (S : Finset (Crossing P)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ GeometricInterlaces hP x y

end
end GeoCarrier

/-- cor:flat-carriers (iii): "a carrier's selector [is] `1` if all its turns are right, `(-1)^c` if
all its `c` turns are left, and `0` if its turns are mixed" (right turn `= -1`, left turn `= +1`,
`c` = the number of corners of the closed polygon). -/
noncomputable def carrierSelector {k : ℕ} [NeZero k] (Q : LabelledTuple k) : ℤ :=
  open scoped Classical in
  if ∀ i, turn Q i = -1 then 1 else if ∀ i, turn Q i = 1 then (-1) ^ k else 0


/-! ## 4. The four flat configurations and their identifications -/

section FlatConfigurations

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The centre `P(0)` on the geometric record domain (lem:flat-sides (ii): the central crossing
data are read from the segments of `P(0)` exactly as for a generic polygon). -/
theorem flatCentreCG (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : CrossingGeometry g.center :=
  flat_crossingGeometry (by omega) hz hb hc

/-- The deletion `Q = P(0) ∖ j` (generic, lem:flat-sides (iii)) on the geometric record domain. -/
theorem flatDeletionCG (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : CrossingGeometry (deleteVertex g.center j) :=
  generic_crossingGeometry hn (generic_deleteVertex hn hz hb hc)

omit [NeZero n] in
/-- A side `P(t)`, `t ≠ 0` (generic), on the geometric record domain; `b = true` is `t > 0`. -/
theorem flatSideCG (hn : 3 ≤ n) (g : WallGerm (n + 1)) (b : Bool) (t : g.SideParameter) :
    CrossingGeometry (g.sideTuple b t).val :=
  generic_crossingGeometry (by omega) (g.sideTuple b t).property

/-- The *right side* is the side with `τ_j = -1`, the *left side* the one with `τ_j = +1`
(def:walls (F), sm-1-polygons.tex:743-744). -/
def IsRightSide (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool) (t : g.SideParameter) :
    Prop :=
  turn (g.sideTuple b t).val j = -1

def IsLeftSide (g : WallGerm (n + 1)) (j : ZMod (n + 1)) (b : Bool) (t : g.SideParameter) :
    Prop :=
  turn (g.sideTuple b t).val j = 1

/-- The identification of the marks of two polygons with the same crossing supports: vertices
fixed, visits through the accepted `visitTransport` (the identification "through the common
cyclic Gauss word" of lem:flat-sides (ii), `GeometricRecordsAgree`). -/
def markTransport {m : ℕ} {P Q : LabelledTuple m} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    Mark P ≃ Mark Q :=
  Equiv.sumCongr (Equiv.refl (ZMod m)) (visitTransport hs)

/-- The support `S` read on a polygon with the same crossing supports. -/
def transportSupport {m : ℕ} {P Q : LabelledTuple m} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) : Finset (Crossing Q) :=
  S.map (crossingTransport hs).toEmbedding

/-- The support `S` read on the deletion through the fused-edge bijection of lem:flat-sides
(iii). -/
def deletionSupport (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) :
    Finset (Crossing (deleteVertex g.center j)) :=
  S.map (fusionCrossingEquiv hn hz hb hc).toEmbedding

/-- A mark of the deletion read at the centre: the vertex `i` of `Q` is the vertex
`deletionIndex j i` of `P(0)`, a visit of `Q` is the centre visit fused to it. Injective; its
range is every centre mark except the deleted vertex `μ_j`. -/
def fusionMark (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : Mark (deleteVertex g.center j) → Mark g.center
  | Sum.inl i => Sum.inl (deletionIndex j i)
  | Sum.inr w => Sum.inr ((fusionVisitEquiv hn hz hb hc).symm w)

/-- A centre mark read on the deletion (the left inverse of `fusionMark`; junk at `μ_j`). -/
def delMark (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : Mark g.center → Mark (deleteVertex g.center j)
  | Sum.inl k => Sum.inl (fusionIndex j k)
  | Sum.inr v => Sum.inr (fusionVisitEquiv hn hz hb hc v)

theorem delMark_fusionMark (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (b : Mark (deleteVertex g.center j)) :
    delMark hn g j hz hb hc (fusionMark hn g j hz hb hc b) = b := by
  cases b with
  | inl i => exact congrArg Sum.inl (fusionIndex_deletionIndex j i)
  | inr w => exact congrArg Sum.inr (Equiv.apply_symm_apply _ w)

theorem fusionMark_delMark (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (a : Mark g.center) (ha : a ≠ Sum.inl j) :
    fusionMark hn g j hz hb hc (delMark hn g j hz hb hc a) = a := by
  cases a with
  | inl k =>
    have hk : k ≠ j := fun he => ha (congrArg Sum.inl he)
    obtain ⟨i, rfl⟩ := deletionIndex_exhaust j hk
    exact congrArg Sum.inl (congrArg (deletionIndex j) (fusionIndex_deletionIndex j i))
  | inr v => exact congrArg Sum.inr (Equiv.symm_apply_apply _ v)

theorem fusionMark_ne_deleted (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (b : Mark (deleteVertex g.center j)) :
    fusionMark hn g j hz hb hc b ≠ Sum.inl j := by
  cases b with
  | inl i => exact fun he => deletionIndex_ne_deleted j i (Sum.inl.inj he)
  | inr w => exact Sum.inr_ne_inl

/-- The central carrier through `μ_j` (the carrier of the mark `μ_j`). -/
def centralCarrierThroughJ (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) :
    GeoComponent (flatCentreCG hn g j hz hb hc) S :=
  geoOwner (flatCentreCG hn g j hz hb hc) S (Sum.inl j)

/-- Its deletion copy: the deletion carrier of the mark following `μ_j` on the central carrier
(that mark is not `μ_j`, so it is read on the deletion by `delMark`). -/
def deletionCopyThroughJ (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) :
    GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) :=
  geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
    (delMark hn g j hz hb hc
      (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))

end
end FlatConfigurations

/-! ## 4b. On a generic polygon the geometric machinery is the accepted one -/

section GenericAgreement

open GeoCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

omit [NeZero n] in
theorem geoMarkKey_eq_generic (hn : 3 ≤ n) (hP : Generic P) (a : Mark P) :
    geoMarkKey (generic_crossingGeometry hn hP) a = markKey hn hP.1 a := by
  unfold geoMarkKey markKey
  rw [geoMarkPosition_eq_generic hn hP]

/-- The sorted marked circle of a generic polygon is the accepted one. -/
theorem geoMarkList_eq_generic (hn : 3 ≤ n) (hP : Generic P) :
    geoMarkList (generic_crossingGeometry hn hP) = markList hn hP := by
  apply List.Perm.eq_of_pairwise (le := fun a b => markKey hn hP.1 a ≤ markKey hn hP.1 b)
  · intro a b _ _ hab hba
    exact markKey_injective hn hP (le_antisymm hab hba)
  · have h := geoMarkList_sorted (generic_crossingGeometry hn hP)
    simpa only [geoMarkKey_eq_generic hn hP] using h
  · exact markList_sorted hn hP
  · apply (List.perm_ext_iff_of_nodup (geoMarkList_nodup _) (markList_nodup hn hP)).mpr
    intro a
    exact ⟨fun _ => mem_markList hn hP a, fun _ => mem_geoMarkList _ a⟩

theorem list_next_congr {α : Type*} [DecidableEq α] {L L' : List α} (h : L = L') (a : α)
    (ha : a ∈ L) (ha' : a ∈ L') : L.next a ha = L'.next a ha' := by
  subst h
  rfl

/-- The successor `ρ` of a generic polygon is the accepted one. -/
theorem geoMarkSuccessor_eq_generic (hn : 3 ≤ n) (hP : Generic P) :
    geoMarkSuccessor (generic_crossingGeometry hn hP) = markSuccessor hn hP := by
  ext a
  rw [geoMarkSuccessor_apply, markSuccessor_apply, geoNextMark_eq_list_next, nextMark_eq_list_next]
  exact list_next_congr (geoMarkList_eq_generic hn hP) a _ _

/-- The reconnected successor `ρ_S` of a generic polygon is the accepted one: the carriers of
def:flat-carriers on a generic side are literally the cycles of def:smoothing's `ρ_S`. -/
theorem geoSmoothingSuccessor_eq_generic (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P)) :
    geoSmoothingSuccessor (generic_crossingGeometry hn hP) S = smoothingSuccessor hn hP S := by
  unfold geoSmoothingSuccessor smoothingSuccessor
  rw [geoMarkSuccessor_eq_generic hn hP]

/-- The carriers of a generic polygon are the accepted `Component`s (same marks, same cycles). -/
def geoComponentEquivGeneric (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P)) :
    GeoComponent (generic_crossingGeometry hn hP) S ≃ Component hn hP S :=
  Quotient.congrRight (fun a b => by
    change (geoSmoothingSuccessor (generic_crossingGeometry hn hP) S).SameCycle a b ↔
      (smoothingSuccessor hn hP S).SameCycle a b
    rw [geoSmoothingSuccessor_eq_generic hn hP S])

theorem geoComponentEquivGeneric_owner (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
    (a : Mark P) :
    geoComponentEquivGeneric hn hP S (geoOwner (generic_crossingGeometry hn hP) S a) =
      owner hn hP S a := rfl

theorem geoComponentMarkList_eq_generic (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoComponentMarkList (generic_crossingGeometry hn hP) S q =
      componentMarkList hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoComponentMarkList componentMarkList
  rw [geoMarkList_eq_generic hn hP]
  apply List.filter_congr
  intro a _
  apply decide_eq_decide.mpr
  rw [← geoComponentEquivGeneric_owner hn hP S a]
  exact (geoComponentEquivGeneric hn hP S).injective.eq_iff.symm

theorem geoComponentPlaneCycle_eq_generic (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoComponentPlaneCycle (generic_crossingGeometry hn hP) S q =
      componentPlaneCycle hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoComponentPlaneCycle componentPlaneCycle
  rw [geoComponentMarkList_eq_generic hn hP S q]
  have hf : (fun m : Mark P =>
      traversalEvaluation P (geoMarkPosition (generic_crossingGeometry hn hP) m)) =
      (fun m : Mark P => traversalEvaluation P (markPosition hn hP.1 m)) := by
    funext m
    rw [geoMarkPosition_eq_generic hn hP]
  rw [hf]

theorem geoComponentCornerList_eq_generic (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
    (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoComponentCornerList (generic_crossingGeometry hn hP) S q =
      ccpCornerList hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoComponentCornerList ccpCornerList
  rw [geoComponentMarkList_eq_generic hn hP S q]

end
end GenericAgreement

/-! ## 5. def:flat-carriers -/

section Definition

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- The words of def:flat-carriers / def:smoothing / conv:selected-visits read in ONE configuration
`P` on the geometric record domain (no genericity): the marked traversal circle, the exchange of
the two outgoing successors at the two visits of every selected crossing, the resulting cycles,
and their tracing by the inherited straight subsegments. -/
structure GeoCarrierSpec {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    Prop where
  /-- "mark the traversal circle at every original vertex": the vertex `i` is the mark `(i, 0)` -/
  mark_vertex : ∀ i : ZMod n,
    traversalEvaluation P (geoMarkPosition hP (Sum.inl i)) = P i ∧
    (geoMarkPosition hP (Sum.inl i)).1 = i ∧ (geoMarkPosition hP (Sum.inl i)).2.val = 0
  /-- "... and every crossing visit": the visit `v` of the crossing `v.1` on the edge `v.2` is the
  mark at its actual (strictly interior) crossing parameter, whose point is the crossing point -/
  mark_visit : ∀ v : Visit P,
    traversalEvaluation P (geoMarkPosition hP (Sum.inr v)) = crossingPoint v.1 ∧
    (geoMarkPosition hP (Sum.inr v)).1 = v.2.val ∧
    (geoMarkPosition hP (Sum.inr v)).2.val = visitParameter v ∧
    0 < visitParameter v ∧ visitParameter v < 1
  /-- distinct marks have distinct positions on the circle -/
  marks_injective : Function.Injective (geoMarkPosition hP)
  /-- `ρ` is the traversal successor: no mark lies strictly between a mark and its successor -/
  successor_gap : ∀ a u : Mark P, ¬ traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP u)
    (geoMarkPosition hP (geoMarkSuccessor hP a))
  /-- "exchange the two outgoing successors at the two visits of every selected crossing":
  `ρ_S = ρ ∘ selectedMarkPerm S` -/
  reconnection : ∀ a : Mark P,
    geoSmoothingSuccessor hP S a = geoMarkSuccessor hP (selectedMarkPerm S a)
  /-- at the visits `a = v`, `b = visitTwin v` of a selected crossing: `ρ_S a = ρ b`, `ρ_S b = ρ a`
  (conv:selected-visits) -/
  reconnect_selected : ∀ v : Visit P, v.1 ∈ S →
    geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr (visitTwin v)) ∧
    geoSmoothingSuccessor hP S (Sum.inr (visitTwin v)) = geoMarkSuccessor hP (Sum.inr v)
  /-- unselected visits and original vertices keep their outgoing successor -/
  keep_unselected : ∀ v : Visit P, v.1 ∉ S →
    geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr v)
  keep_vertex : ∀ i : ZMod n, geoSmoothingSuccessor hP S (Sum.inl i) = geoMarkSuccessor hP (Sum.inl i)
  /-- "the resulting oriented closed cycles": the carriers are the cycles of `ρ_S`; a mark belongs
  to its own cycle (incoming-visit convention) -/
  carriers : ∀ a b : Mark P,
    geoOwner hP S a = geoOwner hP S b ↔ (geoSmoothingSuccessor hP S).SameCycle a b
  /-- "trace ... by the inherited straight subsegments": the traced oriented closed polygonal
  cycle of a carrier is the cycle of the plane points of its marks in inherited order -/
  traced_curve : ∀ q : GeoComponent hP S,
    geoComponentPlaneCycle hP S q =
      ((geoComponentMarkList hP S q).map
        (fun m => traversalEvaluation P (geoMarkPosition hP m)) : Cycle Plane)
  /-- the marks of a carrier: a nonempty duplicate-free list of exactly the marks it owns, in
  inherited order, consecutive entries being `ρ_S`-successors (cyclically) -/
  traced_marks : ∀ q : GeoComponent hP S,
    (geoComponentMarkList hP S q).Nodup ∧ 0 < (geoComponentMarkList hP S q).length ∧
    ∀ m : Mark P, m ∈ geoComponentMarkList hP S q ↔ geoOwner hP S m = q
  traced_successor : ∀ (q : GeoComponent hP S) (i : Fin (geoComponentMarkList hP S q).length),
    geoSmoothingSuccessor hP S ((geoComponentMarkList hP S q)[i.val]'i.isLt) =
      (geoComponentMarkList hP S q)[(i.val + 1) % (geoComponentMarkList hP S q).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt))
  /-- the straight subsegment from a mark to its `ρ_S`-successor, inherited from the original edge
  of the outgoing slot (the mark itself, or its twin at a selected visit) -/
  straight_pieces : ∀ (a : Mark P) (u : ℝ),
    geoSmoothingSegment hP S a u =
      traversalEvaluation P (geoMarkPosition hP a) +
        u • (traversalEvaluation P (geoMarkPosition hP (geoSmoothingSuccessor hP S a)) -
          traversalEvaluation P (geoMarkPosition hP a))
  inherited_pieces : ∀ (a : Mark P) (u : ℝ), 0 ≤ u → u ≤ 1 →
    geoSmoothingSegment hP S a u ∈ edgeSegment P (geoMarkPosition hP (selectedMarkPerm S a)).1
  /-- the corners of a carrier are its original vertices and its selected visits, in inherited
  order; an unselected visit is passed straight through -/
  corners : ∀ q : GeoComponent hP S,
    geoComponentCornerList hP S q =
      (geoComponentMarkList hP S q).filter (fun a => decide (IsTrueCorner S a))
  corner_vertex : ∀ i : ZMod n, IsTrueCorner S (Sum.inl i)
  corner_visit : ∀ v : Visit P, IsTrueCorner S (Sum.inr v) ↔ v.1 ∈ S

/-- def:flat-carriers, one field per printed sentence (sentences 1 and 2 are compound and split
along their clauses), at one radius `δ` ("after shrinking the interval" of lem:flat-sides). -/
structure FlatCarriersDefinitionData (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) (δ : ℝ) : Prop where
  radius_pos : 0 < δ
  radius_le : δ ≤ g.radius
  /-- Sentence 1a: "identify the crossing visits of the two sides, of the centre `P(0)` ... through
  the common cyclic Gauss word of that lemma's clauses (ii)": on both sides the accepted geometric
  records agree with the centre's, the identification being `visitTransport hs` -/
  identify_sides : ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
    GeometricRecordsAgree (flatCentreCG hn g j hz hb hc) (flatSideCG hn g b t)
  /-- ... and the identification extends to the marked circles (vertices fixed): the side's
  marked circle is the centre's, mark by mark in order -/
  identify_sides_marks : ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
    ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
    (geoMarkList (flatCentreCG hn g j hz hb hc)).map (markTransport hs) =
      geoMarkList (flatSideCG hn g b t)
  /-- Sentence 1b: "... and of the deletion `P(0) ∖ j` through ... clause (iii)": the fused-edge
  bijection (accepted `FlatFusionData`: cyclic visit order, pairing, signs, over/under bits) -/
  identify_deletion : FlatFusionData hn hz hb hc
  /-- ... and on marks: the deletion's marked circle is the centre's with the mark `μ_j` removed -/
  identify_deletion_marks :
    ((((geoMarkList (flatCentreCG hn g j hz hb hc)).erase (Sum.inl j)).map
      (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
        Cycle (Mark (deleteVertex g.center j))) =
      (geoMarkList (flatDeletionCG hn g j hz hb hc) : Cycle (Mark (deleteVertex g.center j)))
  /-- Sentence 1c: "fix an independent set `S` in their common interlacement graph": independence
  at the centre is independence (a decomposition, def:decomposition) on each side and on the
  deletion under the identifications -/
  common_independence :
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      (GeoIndependent (flatCentreCG hn g j hz hb hc) S ↔
        IsDecomposition (by omega) (g.sideTuple b t).property (transportSupport hs S))) ∧
    (GeoIndependent (flatCentreCG hn g j hz hb hc) S ↔
      IsDecomposition hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S))
  /-- Sentence 2 ("In each of these four configurations mark ..., exchange ..., and trace ...")
  at the centre -/
  centre_carriers : GeoIndependent (flatCentreCG hn g j hz hb hc) S →
    GeoCarrierSpec (flatCentreCG hn g j hz hb hc) S
  /-- Sentence 2 on the deletion -/
  deletion_carriers : GeoIndependent (flatCentreCG hn g j hz hb hc) S →
    GeoCarrierSpec (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
  /-- Sentence 2 on the two sides -/
  side_carriers : ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
    ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
    GeoIndependent (flatCentreCG hn g j hz hb hc) S →
    GeoCarrierSpec (flatSideCG hn g b t) (transportSupport hs S)
  /-- Sentence 3: "These oriented closed polygonal cycles are the carriers of `S` in that
  configuration": every carrier is the cycle of one of its marks, traced as above (centre and
  deletion; the sides are covered by sentence 4) -/
  carriers_are_cycles :
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      ∃ a : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a = q ∧
        (∀ m, geoOwner (flatCentreCG hn g j hz hb hc) S m = q ↔
          (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).SameCycle a m) ∧
        geoComponentPlaneCycle (flatCentreCG hn g j hz hb hc) S q =
          ((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S q).map
            (fun m => traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) m)) :
              Cycle Plane)) ∧
    (∀ q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S),
      ∃ b : Mark (deleteVertex g.center j),
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b = q ∧
        (∀ m, geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) m = q ↔
          (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc)
            (deletionSupport hn g j hz hb hc S)).SameCycle b m) ∧
        geoComponentPlaneCycle (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q =
          ((geoComponentMarkList (flatDeletionCG hn g j hz hb hc)
            (deletionSupport hn g j hz hb hc S) q).map
            (fun m => traversalEvaluation (deleteVertex g.center j)
              (geoMarkPosition (flatDeletionCG hn g j hz hb hc) m)) : Cycle Plane))
  /-- Sentence 4: "On the two generic sides they are the carriers of Definition def:smoothing": the
  geometric marks, marked circle and reconnected successor are the accepted ones, so the carriers
  (cycles), owners, mark lists and traced cycles are those of def:smoothing, and def:smoothing's
  description (`SmoothingData`) holds -/
  sides_are_smoothing_carriers : ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
    ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
    (∀ a : Mark (g.sideTuple b t).val,
      geoMarkPosition (flatSideCG hn g b t) a = markPosition (by omega) (g.sideTuple b t).property.1 a) ∧
    geoMarkList (flatSideCG hn g b t) = markList (by omega) (g.sideTuple b t).property ∧
    geoMarkSuccessor (flatSideCG hn g b t) = markSuccessor (by omega) (g.sideTuple b t).property ∧
    geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport hs S) =
      smoothingSuccessor (by omega) (g.sideTuple b t).property (transportSupport hs S) ∧
    (∀ a : Mark (g.sideTuple b t).val,
      geoComponentEquivGeneric (by omega) (g.sideTuple b t).property (transportSupport hs S)
        (geoOwner (flatSideCG hn g b t) (transportSupport hs S) a) =
      owner (by omega) (g.sideTuple b t).property (transportSupport hs S) a) ∧
    (∀ q : GeoComponent (flatSideCG hn g b t) (transportSupport hs S),
      geoComponentMarkList (flatSideCG hn g b t) (transportSupport hs S) q =
        componentMarkList (by omega) (g.sideTuple b t).property (transportSupport hs S)
          (geoComponentEquivGeneric (by omega) (g.sideTuple b t).property (transportSupport hs S) q) ∧
      geoComponentPlaneCycle (flatSideCG hn g b t) (transportSupport hs S) q =
        componentPlaneCycle (by omega) (g.sideTuple b t).property (transportSupport hs S)
          (geoComponentEquivGeneric (by omega) (g.sideTuple b t).property (transportSupport hs S) q) ∧
      geoComponentCornerList (flatSideCG hn g b t) (transportSupport hs S) q =
        ccpCornerList (by omega) (g.sideTuple b t).property (transportSupport hs S)
          (geoComponentEquivGeneric (by omega) (g.sideTuple b t).property (transportSupport hs S) q)) ∧
    (GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      SmoothingData (by omega) (g.sideTuple b t).property (transportSupport hs S))
  /-- Sentence 5: "at the centre and on the deletion the same words define them, no genericity being
  assumed": the centre is not generic, yet its carriers are the cycles of the same reconnected
  successor `ρ_S = ρ ∘ selectedMarkPerm S` of its own marked circle; on the (generic) deletion the
  same words give the carriers of def:smoothing -/
  centre_deletion_same_words :
    ¬ Generic g.center ∧
    (∀ a : Mark g.center, geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a =
      geoMarkSuccessor (flatCentreCG hn g j hz hb hc) (selectedMarkPerm S a)) ∧
    (∀ a b : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a =
      geoOwner (flatCentreCG hn g j hz hb hc) S b ↔
      (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).SameCycle a b) ∧
    geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) =
      smoothingSuccessor hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) ∧
    geoMarkList (flatDeletionCG hn g j hz hb hc) = markList hn (generic_deleteVertex hn hz hb hc) ∧
    (∀ b : Mark (deleteVertex g.center j),
      geoComponentEquivGeneric hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      owner hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S) b) ∧
    (GeoIndependent (flatCentreCG hn g j hz hb hc) S →
      SmoothingData hn (generic_deleteVertex hn hz hb hc) (deletionSupport hn g j hz hb hc S))

/-- def:flat-carriers for every flat wall germ (the hypotheses of lem:flat-sides) and every
independent `S` at the centre. -/
theorem flat_carriers_definition (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)
    (hsc : g.SignChanges (fun P => (turn P j : ℝ)))
    (S : Finset (Crossing g.center)) (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    ∃ δ : ℝ, FlatCarriersDefinitionData hn g j hz hb hc S δ := by
  sorry

end Definition


/-! ## 6. cor:flat-carriers -/

section Corollary

open GeoCarrier

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-- cor:flat-carriers, one field per printed clause (each clause split along its sentences), at
one radius `δ`. Notation in the docstrings: `C = P(0)` (centre), `D = P(0) ∖ j` (deletion),
`T = P(t)` (a side `b` at `t`, `0 < t < δ`); `S_T = transportSupport hs S`, `S_D = deletionSupport S`;
`ρ_S` the reconnected successor of a configuration; carriers correspond through the marks:
the side copy of the centre carrier of the mark `a` is the side carrier of `markTransport hs a`,
the centre copy of the deletion carrier of the mark `b` is the centre carrier of `fusionMark b`. -/
structure FlatCarriersData (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (S : Finset (Crossing g.center)) (δ : ℝ) : Prop where
  radius_pos : 0 < δ
  radius_le : δ ≤ g.radius
  /-- the identification of the sides with the centre exists on the whole radius (lem:flat-sides
  (ii)); every `∀ hs` below is therefore about the (unique) identification -/
  side_records : ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
    GeometricRecordsAgree (flatCentreCG hn g j hz hb hc) (flatSideCG hn g b t)
  /-- (i) "The carriers correspond under their named traversal arcs" — sides: the identification of
  marks conjugates the reconnected successors (arc by arc), so it induces a bijection of carriers:
  two centre marks lie on one carrier iff their side images do -/
  correspond_sides : ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
    ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
    (∀ a : Mark g.center,
      geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ∧
    (∀ a a' : Mark g.center,
      geoOwner (flatCentreCG hn g j hz hb hc) S a = geoOwner (flatCentreCG hn g j hz hb hc) S a' ↔
        geoOwner (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs a) =
          geoOwner (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs a'))
  /-- (i) correspondence with the deletion: the deletion's arc from a mark is the centre's arc from
  the same mark, skipping the mark `μ_j` when the centre arc leads to it; two deletion marks lie on
  one carrier iff their centre images do -/
  correspond_deletion :
    (∀ b : Mark (deleteVertex g.center j),
      geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        delMark hn g j hz hb hc
          (if geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
              Sum.inl j
            then geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)
            else geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S
              (fusionMark hn g j hz hb hc b))) ∧
    (∀ b b' : Mark (deleteVertex g.center j),
      geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b =
        geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b' ↔
      geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) =
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b'))
  /-- (i) "Exactly one contains `μ_j`": at the centre the carrier of the mark `μ_j` is the only one
  passing through the point `μ_j`; likewise on each side through `μ_j(t)` (and that side carrier is
  the side copy of the central one, the mark `μ_j` being fixed by the identification) -/
  unique_through_mu_j :
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      (∃ a : Mark g.center, geoOwner (flatCentreCG hn g j hz hb hc) S a = q ∧
        traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a) =
          g.center j) ↔
      q = centralCarrierThroughJ hn g j hz hb hc S) ∧
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      ∀ q : GeoComponent (flatSideCG hn g b t) (transportSupport hs S),
      (∃ a : Mark (g.sideTuple b t).val,
        geoOwner (flatSideCG hn g b t) (transportSupport hs S) a = q ∧
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a) =
          (g.sideTuple b t).val j) ↔
      q = geoOwner (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs (Sum.inl j)))
  /-- (i) "The central copy of that carrier differs from its deletion copy only by the positive-flat
  subdivision at `μ_j`": its marks are the deletion copy's marks with `μ_j` inserted (as cycles,
  through the identification), and `μ_j` lies strictly between its two carrier neighbours, the
  incoming and outgoing directions at `μ_j` being positive multiples of the fused direction
  `w = μ_{j+1} - μ_{j-1}` (eq. flatpr:fusion) -/
  central_vs_deletion_through_mu_j :
    ((((geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (centralCarrierThroughJ hn g j hz hb hc S)).erase (Sum.inl j)).map
          (delMark hn g j hz hb hc) : List (Mark (deleteVertex g.center j))) :
            Cycle (Mark (deleteVertex g.center j))) =
      (geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S) : Cycle (Mark (deleteVertex g.center j))) ∧
    StrictBetween
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))))
      (g.center j)
      (traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j)))) ∧
    (∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      g.center j - traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        ((geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S).symm (Sum.inl j))) =
        r • edge (deleteVertex g.center j) (-1) ∧
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S (Sum.inl j))) - g.center j =
        s • edge (deleteVertex g.center j) (-1))
  /-- (i) "every other central carrier is unchanged by deletion": its marks are the marks of its
  deletion copy (through the identification, as cycles) and its traced polygonal cycle is the
  same cycle of points of the plane -/
  others_unchanged : ∀ b : Mark (deleteVertex g.center j),
    geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b) ≠
      centralCarrierThroughJ hn g j hz hb hc S →
    (((geoComponentMarkList (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)).map
          (fusionMark hn g j hz hb hc) : List (Mark g.center)) : Cycle (Mark g.center)) =
      (geoComponentMarkList (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) :
          Cycle (Mark g.center)) ∧
    geoComponentPlaneCycle (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b) =
      geoComponentPlaneCycle (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))
  /-- (i) "Every carrier has nonzero segments": every inherited subsegment (mark to `ρ_S`-successor)
  and every edge of every corner polygon is nonzero, in all four configurations -/
  nonzero_segments :
    (∀ a : Mark g.center,
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatCentreCG hn g j hz hb hc) S a)) ≠
      traversalEvaluation g.center (geoMarkPosition (flatCentreCG hn g j hz hb hc) a)) ∧
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      edge (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k ≠ 0) ∧
    (∀ b : Mark (deleteVertex g.center j),
      traversalEvaluation (deleteVertex g.center j) (geoMarkPosition (flatDeletionCG hn g j hz hb hc)
        (geoSmoothingSuccessor (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) ≠
      traversalEvaluation (deleteVertex g.center j) (geoMarkPosition (flatDeletionCG hn g j hz hb hc) b)) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      edge (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
        ≠ 0) ∧
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      (∀ a : Mark (g.sideTuple b t).val,
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t)
          (geoSmoothingSuccessor (flatSideCG hn g b t) (transportSupport hs S) a)) ≠
        traversalEvaluation (g.sideTuple b t).val (geoMarkPosition (flatSideCG hn g b t) a)) ∧
      ∀ (q : GeoComponent (flatSideCG hn g b t) (transportSupport hs S)) (k : ZMod (geoCornerCount _ _ q)),
        edge (geoCornerPolygon (flatSideCG hn g b t) (transportSupport hs S) q) k ≠ 0)
  /-- (i) "... and no antiparallel corner": every corner polygon is regular (nonzero edges, no
  antiparallel consecutive directions), in all four configurations -/
  no_antiparallel :
    (∀ q : GeoComponent (flatCentreCG hn g j hz hb hc) S,
      Regular (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q)) ∧
    (∀ q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S),
      Regular (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q)) ∧
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      ∀ q : GeoComponent (flatSideCG hn g b t) (transportSupport hs S),
        Regular (geoCornerPolygon (flatSideCG hn g b t) (transportSupport hs S) q))
  /-- (i) "except for that one central zero turn, all corner turns are nonzero": at the centre a
  corner turn vanishes exactly at the corner `μ_j`; on the deletion and on both sides every corner
  turn is nonzero -/
  turns_nonzero :
    (∀ (q : GeoComponent (flatCentreCG hn g j hz hb hc) S) (k : ZMod (geoCornerCount _ S q)),
      turn (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S q) k = 0 ↔
        geoCornerMark (flatCentreCG hn g j hz hb hc) S q k = Sum.inl j) ∧
    (∀ (q : GeoComponent (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S))
      (k : ZMod (geoCornerCount _ _ q)),
      turn (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) q) k
        ≠ 0) ∧
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      ∀ (q : GeoComponent (flatSideCG hn g b t) (transportSupport hs S)) (k : ZMod (geoCornerCount _ _ q)),
        turn (geoCornerPolygon (flatSideCG hn g b t) (transportSupport hs S) q) k ≠ 0)
  /-- (ii) "Corresponding carriers have the same retained self-crossing visits": the retained
  crossings of a centre carrier are, through the identifications, those of its side copies and of
  its deletion copy (visit by visit, since the identifications act on visits) -/
  same_retained_crossings :
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      ∀ (a : Mark g.center) (x : Crossing g.center),
        x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S a) ↔
        crossingTransport hs x ∈ geoCarrierCrossings (flatSideCG hn g b t) (transportSupport hs S)
          (geoOwner (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs a))) ∧
    (∀ (b : Mark (deleteVertex g.center j)) (x : Crossing g.center),
      x ∈ geoCarrierCrossings (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)) ↔
      fusionCrossingEquiv hn hz hb hc x ∈
        geoCarrierCrossings (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))
  /-- (ii) "... pairing": the identifications commute with the pairing of the two visits of a
  crossing -/
  same_pairing :
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      ∀ v : Visit g.center, visitTransport hs (visitTwin v) = visitTwin (visitTransport hs v)) ∧
    (∀ v : Visit g.center,
      fusionVisitEquiv hn hz hb hc (visitTwin v) = visitTwin (fusionVisitEquiv hn hz hb hc v))
  /-- (ii) "... signs and positive over/under bits": at every crossing visit the crossing sign read
  from the visited edge, and the positive over/under bit (`E_e` over `E_f` iff `det(d_e, d_f) > 0`),
  are the same in the centre, on both sides and on the deletion -/
  same_signs :
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ v : Visit g.center,
        crossingSign (g.sideTuple b t).val v.2.val (visitTwin v).2.val =
          crossingSign g.center v.2.val (visitTwin v).2.val ∧
        (0 < det (edge g.center v.2.val) (edge g.center (visitTwin v).2.val) ↔
          0 < det (edge (g.sideTuple b t).val v.2.val) (edge (g.sideTuple b t).val (visitTwin v).2.val))) ∧
    (∀ v : Visit g.center,
      crossingSign (deleteVertex g.center j) (fusionVisitEquiv hn hz hb hc v).2.val
          (visitTwin (fusionVisitEquiv hn hz hb hc v)).2.val =
        crossingSign g.center v.2.val (visitTwin v).2.val ∧
      (0 < det (edge g.center v.2.val) (edge g.center (visitTwin v).2.val) ↔
        0 < det (edge (deleteVertex g.center j) (fusionVisitEquiv hn hz hb hc v).2.val)
          (edge (deleteVertex g.center j) (visitTwin (fusionVisitEquiv hn hz hb hc v)).2.val)))
  /-- (ii) "They have the same signed rotation and hence the same absolute rotation" (the centre
  copy included, round 4): the rotation numbers of corresponding corner polygons agree -/
  same_rotation :
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      ∀ a : Mark g.center,
        rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport hs S)
          (geoOwner (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs a))) =
        rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S a)) ∧
        |rotationNumber (geoCornerPolygon (flatSideCG hn g b t) (transportSupport hs S)
          (geoOwner (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs a)))| =
        |rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
          (geoOwner (flatCentreCG hn g j hz hb hc) S a))|) ∧
    (∀ b : Mark (deleteVertex g.center j),
      rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b)) =
      rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b))) ∧
      |rotationNumber (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b))| =
      |rotationNumber (geoCornerPolygon (flatCentreCG hn g j hz hb hc) S
        (geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b)))|)
  /-- (ii) "Every corresponding corner away from `μ_j` has the same turn sign on both sides and in
  the deletion" (and at the centre, where these turns are nonzero by (i)): for every corner mark
  `a ≠ μ_j` of the centre, the turn of its carrier at `a` equals the turn of the side copy at
  `markTransport hs a` and the turn of the deletion copy at `delMark a` -/
  same_turn_signs_away :
    ∀ a : Mark g.center, a ≠ Sum.inl j → IsTrueCorner S a →
    (∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport hs S) (markTransport hs a) =
        geoCornerTurn (flatCentreCG hn g j hz hb hc) S a) ∧
    geoCornerTurn (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (delMark hn g j hz hb hc a) =
      geoCornerTurn (flatCentreCG hn g j hz hb hc) S a
  /-- (ii) "The extra corner at `μ_j` is right on the right side and left on the left side": the turn
  of the side carrier at its corner `μ_j` is the side's own turn `τ_j(t)`, `-1` on the right side
  (`τ_j = -1`) and `+1` on the left side (`τ_j = +1`) -/
  extra_corner :
    ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      geoCornerTurn (flatSideCG hn g b t) (transportSupport hs S) (Sum.inl j) =
        turn (g.sideTuple b t).val j ∧
      (IsRightSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport hs S) (Sum.inl j) = -1) ∧
      (IsLeftSide g j b t →
        geoCornerTurn (flatSideCG hn g b t) (transportSupport hs S) (Sum.inl j) = 1)
  /-- (iii) eq. flatpr:selector-identity: `W_right - W_left = W_del` for the carrier through `μ_j`
  (`W` = `carrierSelector` of its corner polygon on the right side, on the left side, and of its
  deletion copy) -/
  selector_identity :
    ∀ (t : g.SideParameter), t.val < δ → ∀ (bR bL : Bool),
      IsRightSide g j bR t → IsLeftSide g j bL t →
      ∀ (hsR : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple bR t).val s)
        (hsL : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple bL t).val s),
      carrierSelector (geoCornerPolygon (flatSideCG hn g bR t) (transportSupport hsR S)
          (geoOwner (flatSideCG hn g bR t) (transportSupport hsR S) (markTransport hsR (Sum.inl j)))) -
        carrierSelector (geoCornerPolygon (flatSideCG hn g bL t) (transportSupport hsL S)
          (geoOwner (flatSideCG hn g bL t) (transportSupport hsL S) (markTransport hsL (Sum.inl j)))) =
      carrierSelector (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
        (deletionCopyThroughJ hn g j hz hb hc S))
  /-- (iii) "All other corresponding carrier selectors agree": for every carrier not through `μ_j`,
  the selector of each side copy equals the selector of the deletion copy (hence the two sides
  agree) -/
  other_selectors_agree :
    ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ hs : ∀ s, IsCrossing g.center s ↔ IsCrossing (g.sideTuple b t).val s,
      ∀ b' : Mark (deleteVertex g.center j),
        geoOwner (flatCentreCG hn g j hz hb hc) S (fusionMark hn g j hz hb hc b') ≠
          centralCarrierThroughJ hn g j hz hb hc S →
        carrierSelector (geoCornerPolygon (flatSideCG hn g b t) (transportSupport hs S)
          (geoOwner (flatSideCG hn g b t) (transportSupport hs S)
            (markTransport hs (fusionMark hn g j hz hb hc b')))) =
        carrierSelector (geoCornerPolygon (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S)
          (geoOwner (flatDeletionCG hn g j hz hb hc) (deletionSupport hn g j hz hb hc S) b'))

/-- cor:flat-carriers for every flat wall germ (the hypotheses of lem:flat-sides) and every
independent `S` at the centre. The closing sentences ("These assertions concern geometric and
combinatorial carrier data. They make no assignment of a state-sum value at the flat centre.") are
non-definitional and have no field. -/
theorem flat_carriers (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)
    (hsc : g.SignChanges (fun P => (turn P j : ℝ)))
    (S : Finset (Crossing g.center)) (hS : GeoIndependent (flatCentreCG hn g j hz hb hc) S) :
    ∃ δ : ℝ, FlatCarriersData hn g j hz hb hc S δ := by
  sorry

end Corollary

end SM
