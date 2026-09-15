import SM.FlatCarriers

/-! Ported 2026-09-14 from work/drafts/cvdom/U1a/GeoCarrierCount.lean (CV-DOM unit U1a, decision work/drafts/cvdom/DECISION_FINAL.md: tier-0 port of the Carrier lane's combinatorial core onto the accepted geo definitions; REPORT.md in the same directory). Library module, no row. Only this header added. -/

/-! # SM/GeoCarrierCount.lean — the carrier count on the geometric carrier layer (CV-DOM unit U1a)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3 rulings R1–R3/R5, §5 unit U1a). Draft home
work/drafts/cvdom/U1a/; intended home work/lean/SM/GeoCarrierCount.lean. Tier 0 throughout: every
statement is on the accepted geometric record domain `hP : CrossingGeometry P`
(SM/CrossingGeometry.lean:11), on the ACCEPTED geometric carrier definitions of
SM/FlatCarriersDefs.lean (`geoMarkPosition`, `geoMarkList`, `geoMarkSuccessor`,
`geoSmoothingSuccessor`, `GeoComponent`, `geoOwner`, `GeoIndependent`, …; def:flat-carriers). No
accepted declaration is redefined or shadowed; everything here is additive (namespace
`SM.GeoCarrier`, prefix `geo`).

Content: the mechanical port (work/drafts/cvdom/port_lane.py, extended DEFMAP) of the combinatorial
core of the Carrier lane — SM/CarrierMarks, CarrierSuccessor, CarrierSmoothing (residue not in
FlatCarriersDefs), CarrierSingleSwitch, CarrierOrbitRefinement, CarrierFilteredCycles,
CarrierCycleList, CarrierSingleSupport, CarrierInheritedOrder, CarrierCurrentCycle,
CarrierUnchangedComponent, CarrierInsertOrbits, CarrierInheritedInsert, CarrierComponentFibers,
CarrierSameArc, CarrierMarkedArcLists, CarrierPendingPairs, CarrierIndependentOrder,
CarrierComponentCount, CarrierTrueCorners — from `hn : 3 ≤ n, hP : Generic P` to
`hP : CrossingGeometry P`. The lane used `Generic` only as Prop plumbing (`markPosition hn hP.1`,
`visitPosition hn hP.1`, `Interlaces hn hP`), replaced by `geoMarkPosition hP`,
`geometricVisitPosition hP`, `GeometricInterlaces hP`; `S ∈ independentSupports hn hP` becomes the
accepted `GeoIndependent hP S` (definitionally the same `∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ …` clause).
Hypothesis-free lemmas of the lane (`selectedMarkPerm_*`, `splitList_*`, `sameCycle_*`,
`filter_splitList_*`, `IsTrueCorner`, …) are NOT re-declared: they are shared with the accepted lane
through `open Carrier`. Declarations whose `geo*` counterpart already exists in
SM/FlatCarriersDefs.lean / SM/FlatCarriers.lean are not re-declared either (marked `-- [port]`).

Targets (DECISION_FINAL §5, U1a): `geoComponent_card` (lem:carriers (i): `|carriers| = |S| + 1`),
`geo_selected_visits_separated` (the two visits of a selected crossing lie on different carriers),
`geoOwner_refines` (lem:carrierword clause 3: for independent `S ⊆ S'` every carrier of `S'` lies in
one carrier of `S`). Also `GeoInheritsMarkOrder` / `geoInheritsMarkOrder_of_independent` (the
inherited-order invariant the count induction carries; nominally U1b's, needed here).

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U1a/GeoCarrierCount.lean`. -/

namespace SM.GeoCarrier

open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n]

/-! ### Port of SM/CarrierMarks.lean -/

-- [port] `Mark` -> accepted `Carrier.Mark` (hypothesis-free, shared); not re-declared

-- [port] `markPosition` -> accepted `geoMarkPosition` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markPosition_vertex` -> accepted `geoMarkPosition_vertex` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markPosition_visit` -> accepted `geoMarkPosition_visit` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markPosition_evaluation_vertex` -> accepted `geoMarkPosition_evaluation_vertex` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markPosition_evaluation_visit` -> accepted `geoMarkPosition_evaluation_visit` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markPosition_injective` -> accepted `geoMarkPosition_injective` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markKey` -> accepted `geoMarkKey` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markKey_vertex` -> accepted `geoMarkKey_vertex` (SM/FlatCarriers*.lean); not re-declared

omit [NeZero n] in
theorem geoMarkKey_visit {P : LabelledTuple n} (hP : CrossingGeometry P)
    (v : Visit P) : geoMarkKey hP (Sum.inr v) = geometricVisitKey hP v := rfl

-- [port] `markKey_injective` -> accepted `geoMarkKey_injective` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markLinearOrder` -> accepted `geoMarkLinearOrder` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markList` -> accepted `geoMarkList` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markList_nodup` -> accepted `geoMarkList_nodup` (SM/FlatCarriers*.lean); not re-declared

-- [port] `mem_markList` -> accepted `mem_geoMarkList` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markList_sorted` -> accepted `geoMarkList_sorted` (SM/FlatCarriers*.lean); not re-declared

theorem geoMarkList_length {P : LabelledTuple n} (hP : CrossingGeometry P) :
    (geoMarkList hP).length = n + 2 * (crossingSet P).card := by
  classical
  let _ := geoMarkLinearOrder hP
  change (Finset.univ.sort (α := Mark P)).length = _
  rw [Finset.length_sort, Finset.card_univ, Fintype.card_sum, ZMod.card, card_visit]

/-- Ordinary vertices ensure a nonempty marked circle, even with no visits. -/
theorem geoMarkList_nonempty {P : LabelledTuple n} (hP : CrossingGeometry P) :
    (∃ a : Mark P, a ∈ geoMarkList hP) :=
  ⟨Sum.inl (0 : ZMod n), mem_geoMarkList hP _⟩


/-! ### Port of SM/CarrierSuccessor.lean -/

-- [port] `markCycle` -> accepted `geoMarkCycle` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markCycle_nodup` -> accepted `geoMarkCycle_nodup` (SM/FlatCarriers*.lean); not re-declared

-- [port] `mem_markCycle` -> accepted `mem_geoMarkCycle` (SM/FlatCarriers*.lean); not re-declared

/-- Changing the chosen first entry by rotation does not change the marked circle. -/
theorem geoMarkCycle_rotation {P : LabelledTuple n} (hP : CrossingGeometry P) (k : ℕ) :
    ((geoMarkList hP).rotate k : Cycle (Mark P)) = geoMarkCycle hP :=
  Cycle.coe_eq_coe.mpr (List.IsRotated.forall _ _)

-- [port] `nextMark` -> accepted `geoNextMark` (SM/FlatCarriers*.lean); not re-declared

-- [port] `prevMark` -> accepted `geoPrevMark` (SM/FlatCarriers*.lean); not re-declared

-- [port] `nextMark_eq_list_next` -> accepted `geoNextMark_eq_list_next` (SM/FlatCarriers*.lean); not re-declared

@[simp]
theorem geoPrevMark_eq_list_prev {P : LabelledTuple n} (hP : CrossingGeometry P)
    (a : Mark P) : geoPrevMark hP a = (geoMarkList hP).prev a (mem_geoMarkList hP a) := rfl

-- [port] `prevMark_nextMark` -> accepted `geoPrevMark_geoNextMark` (SM/FlatCarriers*.lean); not re-declared

-- [port] `nextMark_prevMark` -> accepted `geoNextMark_geoPrevMark` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markSuccessor` -> accepted `geoMarkSuccessor` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markSuccessor_apply` -> accepted `geoMarkSuccessor_apply` (SM/FlatCarriers*.lean); not re-declared

@[simp]
theorem geoMarkSuccessor_symm_apply {P : LabelledTuple n} (hP : CrossingGeometry P)
    (a : Mark P) : (geoMarkSuccessor hP).symm a = geoPrevMark hP a := rfl

-- [port] `markSuccessor_getElem` -> accepted `geoMarkSuccessor_getElem` (SM/FlatCarriers*.lean); not re-declared

/-- The inverse formula retreats modulo the same complete mark count, including
its first/last transition. No crossing-nonempty assumption is needed. -/
theorem geoMarkSuccessor_symm_getElem {P : LabelledTuple n} (hP : CrossingGeometry P)
    (i : ℕ) (hi : i < (geoMarkList hP).length) :
    (geoMarkSuccessor hP).symm ((geoMarkList hP)[i]'hi) =
      (geoMarkList hP)[(i + ((geoMarkList hP).length - 1)) % (geoMarkList hP).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  change (geoMarkList hP).prev ((geoMarkList hP)[i]'hi) _ = _
  exact List.prev_getElem (geoMarkList hP) (geoMarkList_nodup hP) i hi

-- [port] `nextMark_no_mark_between` -> accepted `geoNextMark_no_mark_between` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markSuccessor_no_mark_between` -> accepted `geoMarkSuccessor_no_mark_between` (SM/FlatCarriers*.lean); not re-declared

/-- Backward traversal uses the preceding oriented gap, from the predecessor to
the current mark, and that gap also contains no actual mark. -/
theorem geoMarkSuccessor_prev_no_mark_between {P : LabelledTuple n} (hP : CrossingGeometry P)
    (a u : Mark P) :
    ¬ traversalBetween (geoMarkPosition hP ((geoMarkSuccessor hP).symm a))
      (geoMarkPosition hP u) (geoMarkPosition hP a) :=
  geoNextMark_no_mark_between hP (geoNextMark_geoPrevMark hP a) u

-- [port] `markSuccessor_sameCycle_getElem` -> accepted `geoMarkSuccessor_sameCycle_getElem` (SM/FlatCarriers*.lean); not re-declared

-- [port] `markSuccessor_sameCycle` -> accepted `geoMarkSuccessor_sameCycle` (SM/FlatCarriers*.lean); not re-declared


/-! ### Port of SM/CarrierSmoothing.lean -/

-- [port] `selectedMarkPerm` -> accepted `Carrier.selectedMarkPerm` (hypothesis-free, shared); not re-declared

-- [port] `selectedMarkPerm_vertex` -> accepted `Carrier.selectedMarkPerm_vertex` (hypothesis-free, shared); not re-declared

-- [port] `selectedMarkPerm_visit` -> accepted `Carrier.selectedMarkPerm_visit` (hypothesis-free, shared); not re-declared

-- [port] `selectedMarkPerm_involutive` -> accepted `Carrier.selectedMarkPerm_involutive` (hypothesis-free, shared); not re-declared

-- [port] `selectedMarkPerm_evaluation` -> accepted `geoSelectedMarkPerm_evaluation` (SM/FlatCarriers*.lean); not re-declared

-- [port] `selectedMarkPerm_commute` -> accepted `Carrier.selectedMarkPerm_commute` (hypothesis-free, shared); not re-declared

-- [port] `selectedMarkPerm_union_of_disjoint` -> accepted `Carrier.selectedMarkPerm_union_of_disjoint` (hypothesis-free, shared); not re-declared

-- [port] `smoothingSuccessor` -> accepted `geoSmoothingSuccessor` (SM/FlatCarriers*.lean); not re-declared

-- [port] `smoothingSuccessor_vertex` -> accepted `geoSmoothingSuccessor_vertex` (SM/FlatCarriers*.lean); not re-declared

-- [port] `smoothingSuccessor_visit_of_mem` -> accepted `geoSmoothingSuccessor_visit_of_mem` (SM/FlatCarriers*.lean); not re-declared

-- [port] `smoothingSuccessor_visit_of_not_mem` -> accepted `geoSmoothingSuccessor_visit_of_not_mem` (SM/FlatCarriers*.lean); not re-declared

theorem geoSmoothingSuccessor_empty {P : LabelledTuple n} (hP : CrossingGeometry P) :
    geoSmoothingSuccessor hP ∅ = geoMarkSuccessor hP := by
  ext a
  cases a with
  | inl i => rfl
  | inr v =>
    change geoMarkSuccessor hP (Sum.inr (selectedVisitTwin ∅ v)) = _
    rw [selectedVisitTwin_empty]
    rfl

/-- Adding disjoint switches acts on outgoing slots of the already reconnected
successor. This is an equality of the constructed permutations. -/
theorem geoSmoothingSuccessor_union_of_disjoint {P : LabelledTuple n} (hP : CrossingGeometry P) (S T : Finset (Crossing P)) (hST : Disjoint S T) :
    geoSmoothingSuccessor hP (S ∪ T) =
      (selectedMarkPerm T).trans (geoSmoothingSuccessor hP S) := by
  rw [geoSmoothingSuccessor, selectedMarkPerm_union_of_disjoint S T hST]
  rfl

-- [port] `Component` -> accepted `GeoComponent` (SM/FlatCarriers*.lean); not re-declared

-- [port] `owner` -> accepted `geoOwner` (SM/FlatCarriers*.lean); not re-declared

-- [port] `owner_eq_iff` -> accepted `geoOwner_eq_iff` (SM/FlatCarriers*.lean); not re-declared

-- [port] `owner_successor` -> accepted `geoOwner_successor` (SM/FlatCarriers*.lean); not re-declared

-- [port] `owner_predecessor` -> accepted `geoOwner_predecessor` (SM/FlatCarriers*.lean); not re-declared

-- [port] `owner_surjective` -> accepted `geoOwner_surjective` (SM/FlatCarriers*.lean); not re-declared

-- [port] `componentFintype` -> accepted `geoComponentFintype` (SM/FlatCarriers*.lean); not re-declared

theorem geoComponent_card_pos {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) : 0 < Fintype.card (GeoComponent hP S) :=
  Fintype.card_pos_iff.mpr ⟨geoOwner hP S (Sum.inl (0 : ZMod n))⟩

/-- The empty support has a single actual component, since the unmodified
successor traverses every mark. -/
theorem geoComponent_empty_subsingleton {P : LabelledTuple n} (hP : CrossingGeometry P) : Subsingleton (GeoComponent hP ∅) := by
  constructor
  intro q r
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP ∅ q
  obtain ⟨b, rfl⟩ := geoOwner_surjective hP ∅ r
  apply (geoOwner_eq_iff hP ∅ a b).mpr
  rw [geoSmoothingSuccessor_empty]
  exact geoMarkSuccessor_sameCycle hP a b

theorem geoComponent_card_empty {P : LabelledTuple n} (hP : CrossingGeometry P) :
    Fintype.card (GeoComponent hP ∅) = 1 := by
  let _ := geoComponent_empty_subsingleton hP
  let _ : Unique (GeoComponent hP ∅) :=
    uniqueOfSubsingleton (geoOwner hP ∅ (Sum.inl (0 : ZMod n)))
  exact Fintype.card_unique


/-! ### Port of SM/CarrierSingleSwitch.lean -/

-- [port] `selectedVisitTwin_singleton` -> accepted `Carrier.selectedVisitTwin_singleton` (hypothesis-free, shared); not re-declared

-- [port] `selectedVisitTwinPerm_singleton` -> accepted `Carrier.selectedVisitTwinPerm_singleton` (hypothesis-free, shared); not re-declared

-- [port] `selectedMarkPerm_singleton` -> accepted `Carrier.selectedMarkPerm_singleton` (hypothesis-free, shared); not re-declared

/-- Adding an unselected actual crossing swaps its two outgoing slots in the
current successor. Right multiplication applies that transposition first. -/
theorem geoSmoothingSuccessor_insert {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    geoSmoothingSuccessor hP (insert v.1 S) =
      geoSmoothingSuccessor hP S *
        Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  have hS : insert v.1 S = S ∪ {v.1} := by
    ext c
    simp
  rw [hS, geoSmoothingSuccessor_union_of_disjoint hP S {v.1}
    (Finset.disjoint_singleton_right.mpr hv), selectedMarkPerm_singleton]
  rfl

theorem geoSmoothingSuccessor_insert_visit {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    geoSmoothingSuccessor hP (insert v.1 S) (Sum.inr v) =
      geoSmoothingSuccessor hP S (Sum.inr (visitTwin v)) := by
  rw [geoSmoothingSuccessor_insert hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left]

theorem geoSmoothingSuccessor_insert_twin {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    geoSmoothingSuccessor hP (insert v.1 S) (Sum.inr (visitTwin v)) =
      geoSmoothingSuccessor hP S (Sum.inr v) := by
  rw [geoSmoothingSuccessor_insert hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_right]

/-- Every other marked outgoing slot is unchanged by this one reconnection. -/
theorem geoSmoothingSuccessor_insert_other {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (a : Mark P) (hav : a ≠ Sum.inr v) (hat : a ≠ Sum.inr (visitTwin v)) :
    geoSmoothingSuccessor hP (insert v.1 S) a = geoSmoothingSuccessor hP S a := by
  rw [geoSmoothingSuccessor_insert hP S v hv, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hav hat]


/-! ### Port of SM/CarrierOrbitRefinement.lean -/

-- [port] `sameCycle_refines_of_step` -> accepted `Carrier.sameCycle_refines_of_step` (hypothesis-free, shared); not re-declared

-- [port] `mul_swap_sameCycle_step` -> accepted `Carrier.mul_swap_sameCycle_step` (hypothesis-free, shared); not re-declared

-- [port] `sameCycle_mul_swap_refines` -> accepted `Carrier.sameCycle_mul_swap_refines` (hypothesis-free, shared); not re-declared

/-- Actual reconnection refines old carrier orbits when its two actual visits
are currently together. Independence must later establish this premise. -/
theorem geoSmoothingSuccessor_insert_sameCycle_refines {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (v : Visit P) (hv : v.1 ∉ S)
    (hc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    {a b : Mark P} (hab : (geoSmoothingSuccessor hP (insert v.1 S)).SameCycle a b) :
    (geoSmoothingSuccessor hP S).SameCycle a b := by
  rw [geoSmoothingSuccessor_insert hP S v hv] at hab
  exact sameCycle_mul_swap_refines _ _ _ hc hab

theorem geoOwner_insert_eq_imp {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    {a b : Mark P} (hab : geoOwner hP (insert v.1 S) a = geoOwner hP (insert v.1 S) b) :
    geoOwner hP S a = geoOwner hP S b :=
  (geoOwner_eq_iff hP S a b).mpr
    (geoSmoothingSuccessor_insert_sameCycle_refines hP S v hv hc
      ((geoOwner_eq_iff hP (insert v.1 S) a b).mp hab))

/-- Previously separated marked owners remain separated under a split step. -/
theorem geoOwner_insert_ne_of_ne {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    {a b : Mark P} (hab : geoOwner hP S a ≠ geoOwner hP S b) :
    geoOwner hP (insert v.1 S) a ≠ geoOwner hP (insert v.1 S) b :=
  fun h => hab (geoOwner_insert_eq_imp hP S v hv hc h)

/-- The actual quotient map sends a new component to its unique old component.
Its well-definedness is the proved refinement, not a supplied correspondence. -/
def geoComponentForgetSwitch {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v))) :
    GeoComponent hP (insert v.1 S) → GeoComponent hP S :=
  Quotient.map id (fun _ _ hab =>
    geoSmoothingSuccessor_insert_sameCycle_refines hP S v hv hc hab)

theorem geoComponentForgetSwitch_owner {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    (a : Mark P) :
    geoComponentForgetSwitch hP S v hv hc (geoOwner hP (insert v.1 S) a) =
      geoOwner hP S a := rfl

theorem geoComponentForgetSwitch_surjective {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v))) :
    Function.Surjective (geoComponentForgetSwitch hP S v hv hc) := by
  intro q
  obtain ⟨a, rfl⟩ := geoOwner_surjective hP S q
  exact ⟨geoOwner hP (insert v.1 S) a, rfl⟩

/-- The proved quotient map gives a weak count inequality. Strict increase by
one still requires the exact two-child split theorem and independence induction. -/
theorem geoComponent_card_le_insert {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v))) :
    Fintype.card (GeoComponent hP S) ≤ Fintype.card (GeoComponent hP (insert v.1 S)) :=
  Fintype.card_le_of_surjective _ (geoComponentForgetSwitch_surjective hP S v hv hc)


/-! ### Port of SM/CarrierFilteredCycles.lean -/

/-- The original traversal's cyclic order restricted to one actual successor
orbit. Compatibility with the reconnected successor is a separate invariant. -/
def geoComponentCycle {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (q : GeoComponent hP T) : Cycle (Mark P) :=
  (geoMarkCycle hP).filter (fun m => decide (geoOwner hP T m = q))

/-- Filtering the complete sorted representative represents the inherited
component cycle. The definition is independent of the chosen first mark. -/
theorem geoComponentCycle_eq_filtered_markList {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T) :
    geoComponentCycle hP T q =
      ((geoMarkList hP).filter (fun m => decide (geoOwner hP T m = q)) : Cycle (Mark P)) := rfl

/-- Every actual mark occurs in the original circle, so the sole membership
condition in its inherited component cycle is its actual incoming geoOwner. -/
@[simp]
theorem mem_geoComponentCycle {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (q : GeoComponent hP T) (m : Mark P) :
    m ∈ geoComponentCycle hP T q ↔ geoOwner hP T m = q := by
  simp [geoComponentCycle, Cycle.mem_filter, mem_geoMarkCycle]

/-- Restriction retains the original marked circle's absence of repetitions. -/
theorem geoComponentCycle_nodup {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (q : GeoComponent hP T) :
    (geoComponentCycle hP T q).Nodup :=
  (geoMarkCycle_nodup hP).filter (fun m => decide (geoOwner hP T m = q))

/-- Every mark belongs to the inherited cycle of its constructed geoOwner. -/
theorem mem_geoComponentCycle_owner {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (m : Mark P) :
    m ∈ geoComponentCycle hP T (geoOwner hP T m) :=
  (mem_geoComponentCycle hP T _ m).mpr rfl

/-- Each actual quotient component has a mark representative; filtering cannot
make its inherited component cycle empty. No crossing-nonempty premise enters. -/
theorem geoComponentCycle_nonempty {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (q : GeoComponent hP T) :
    ∃ m : Mark P, m ∈ geoComponentCycle hP T q := by
  obtain ⟨m, hm⟩ := geoOwner_surjective hP T q
  exact ⟨m, (mem_geoComponentCycle hP T q m).mpr hm⟩

/-- Distinct actual components have disjoint mark membership in their inherited
cycles, since every incoming mark has one quotient geoOwner. -/
theorem geoComponentCycle_members_disjoint {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q r : GeoComponent hP T)
    (hqr : q ≠ r) (m : Mark P) :
    m ∈ geoComponentCycle hP T q → m ∉ geoComponentCycle hP T r := by
  intro hq hr
  exact hqr (((mem_geoComponentCycle hP T q m).mp hq).symm.trans
    ((mem_geoComponentCycle hP T r m).mp hr))

/-- Distinct quotient components yield distinct inherited cycles. The proof
uses an actual representative of the nonempty component, not a cycle count. -/
theorem geoComponentCycle_injective {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) :
    Function.Injective (geoComponentCycle hP T) := by
  intro q r he
  obtain ⟨m, hm⟩ := geoComponentCycle_nonempty hP T q
  have hr : m ∈ geoComponentCycle hP T r := he ▸ hm
  exact ((mem_geoComponentCycle hP T q m).mp hm).symm.trans
    ((mem_geoComponentCycle hP T r m).mp hr)

/-- At empty support every actual mark has the unique original component geoOwner,
so filtering retains the complete original marked circle. -/
theorem geoComponentCycle_empty {P : LabelledTuple n} (hP : CrossingGeometry P)
    (q : GeoComponent hP ∅) : geoComponentCycle hP ∅ q = geoMarkCycle hP := by
  unfold geoComponentCycle
  apply Cycle.filter_eq_self
  intro m _
  have hm : geoOwner hP ∅ m = q := (geoComponent_empty_subsingleton hP).elim _ _
  simp only [hm, decide_true]

/-- A rotation giving the original split-list presentation filters literally
between its two retained endpoints. Both filtered intervening lists may be empty;
this identity makes no claim about the current successor on the filtered cycle. -/
theorem geoComponentCycle_eq_filtered_splitList {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B))
    (ha : geoOwner hP T a = q) (hb : geoOwner hP T b = q) :
    geoComponentCycle hP T q =
      (a :: (A.filter (fun m => decide (geoOwner hP T m = q)) ++
        b :: B.filter (fun m => decide (geoOwner hP T m = q))) : Cycle (Mark P)) := by
  have hc : geoMarkCycle hP = (a :: (A ++ b :: B) : Cycle (Mark P)) := by
    rw [← hrot]
    exact (geoMarkCycle_rotation hP k).symm
  rw [geoComponentCycle, hc, Cycle.filter_coe]
  simp [List.filter_append, ha, hb]


/-! ### Port of SM/CarrierCycleList.lean -/

/-- The constructed actual cyclic successor is exactly the permutation formed
from the complete sorted mark list, on every actual mark. -/
theorem geoMarkSuccessor_eq_formPerm {P : LabelledTuple n} (hP : CrossingGeometry P) : geoMarkSuccessor hP = (geoMarkList hP).formPerm := by
  classical
  ext a
  change (geoMarkList hP).next a (mem_geoMarkList hP a) = _
  exact (List.formPerm_apply_mem_eq_next (geoMarkList_nodup hP) a
    (mem_geoMarkList hP a)).symm

/-- An actual mark can be made the first entry by rotating the complete list.
The rotation is constructed by splitting at its actual occurrence. -/
theorem geoMarkList_rotate_start {P : LabelledTuple n} (hP : CrossingGeometry P) (a : Mark P) :
    ∃ k : ℕ, ∃ T : List (Mark P), (geoMarkList hP).rotate k = a :: T := by
  obtain ⟨L, R, he⟩ := List.mem_iff_append.mp (mem_geoMarkList hP a)
  refine ⟨L.length, R ++ L, ?_⟩
  rw [he, List.rotate_append_length_eq, List.cons_append]

/-- For any distinct actual marks, the complete marked circle has the literal
split-list presentation used by the source. Either intervening list may be empty. -/
theorem geoMarkList_rotate_split {P : LabelledTuple n} (hP : CrossingGeometry P) (a b : Mark P) (hab : a ≠ b) :
    ∃ k : ℕ, ∃ A B : List (Mark P),
      (geoMarkList hP).rotate k = a :: (A ++ b :: B) := by
  obtain ⟨k, T, hrot⟩ := geoMarkList_rotate_start hP a
  have hb : b ∈ a :: T := hrot ▸ (List.mem_rotate.mpr (mem_geoMarkList hP b))
  have hbT : b ∈ T := (List.mem_cons.mp hb).resolve_left hab.symm
  obtain ⟨A, B, hT⟩ := List.mem_iff_append.mp hbT
  exact ⟨k, A, B, hT ▸ hrot⟩

/-- The actual original successor admits the source's duplicate-free split-list
presentation for arbitrary distinct actual marks. Rotation retains every vertex
and crossing visit, so no supplied representation or current-carrier premise enters. -/
theorem geoMarkSuccessor_splitList {P : LabelledTuple n} (hP : CrossingGeometry P) (a b : Mark P) (hab : a ≠ b) :
    ∃ A B : List (Mark P),
      (a :: (A ++ b :: B)).Nodup ∧
      (a :: (A ++ b :: B)).formPerm = geoMarkSuccessor hP ∧
      ∀ m : Mark P, m ∈ a :: (A ++ b :: B) := by
  classical
  obtain ⟨k, A, B, hrot⟩ := geoMarkList_rotate_split hP a b hab
  refine ⟨A, B, ?_, ?_, ?_⟩
  · rw [← hrot]
    exact List.nodup_rotate.mpr (geoMarkList_nodup hP)
  · rw [← hrot, List.formPerm_rotate _ (geoMarkList_nodup hP) k]
    exact (geoMarkSuccessor_eq_formPerm hP).symm
  · intro m
    rw [← hrot]
    exact List.mem_rotate.mpr (mem_geoMarkList hP m)


/-! ### Port of SM/CarrierSingleSupport.lean -/

/-- The actual full marked traversal, cut at a crossing's actual two visits,
supplies the source split list. Its completeness is proved from the traversal. -/
theorem geoSmoothingSuccessor_singleton_splitList {P : LabelledTuple n} (hP : CrossingGeometry P) (v : Visit P) :
    ∃ A B : List (Mark P),
      (Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)).Nodup ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) ∧
      geoSmoothingSuccessor hP {v.1} =
        (Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)).formPerm *
          Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  have hv : (Sum.inr v : Mark P) ≠ Sum.inr (visitTwin v) := by
    intro h
    exact (visitTwin_ne v).symm (Sum.inr.inj h)
  obtain ⟨A, B, hN, hperm, hfull⟩ :=
    geoMarkSuccessor_splitList hP (Sum.inr v) (Sum.inr (visitTwin v)) hv
  refine ⟨A, B, hN, hfull, ?_⟩
  have he := geoSmoothingSuccessor_insert hP (∅ : Finset (Crossing P)) v
    (Finset.notMem_empty v.1)
  simpa only [Finset.insert_empty, geoSmoothingSuccessor_empty, hperm] using he

/-- The two incoming owners at one actual selected crossing are distinct. -/
theorem geoOwner_singleton_ne {P : LabelledTuple n} (hP : CrossingGeometry P)
    (v : Visit P) :
    geoOwner hP {v.1} (Sum.inr v) ≠ geoOwner hP {v.1} (Sum.inr (visitTwin v)) := by
  obtain ⟨A, B, hN, _, he⟩ := geoSmoothingSuccessor_singleton_splitList hP v
  intro h
  have hc := (geoOwner_eq_iff hP {v.1} _ _).mp h
  rw [he] at hc
  exact splitList_not_sameCycle (Sum.inr v) (Sum.inr (visitTwin v)) A B hN hc

/-- Every actual component of one selected crossing is one of the two endpoint
components. This uses completeness of the actual list, including all vertices. -/
theorem geoOwner_singleton_exhaust {P : LabelledTuple n} (hP : CrossingGeometry P)
    (v : Visit P) (q : GeoComponent hP {v.1}) :
    q = geoOwner hP {v.1} (Sum.inr v) ∨
      q = geoOwner hP {v.1} (Sum.inr (visitTwin v)) := by
  obtain ⟨A, B, hN, hfull, he⟩ := geoSmoothingSuccessor_singleton_splitList hP v
  obtain ⟨x, rfl⟩ := geoOwner_surjective hP {v.1} q
  have hcL (hx : x ∈ Sum.inr v :: B) :
      geoOwner hP {v.1} x = geoOwner hP {v.1} (Sum.inr v) := by
    apply (geoOwner_eq_iff hP {v.1} _ _).mpr
    rw [he]
    exact ((splitList_left_sameCycle_iff (Sum.inr v) (Sum.inr (visitTwin v)) A B hN x).mpr hx).symm
  have hcR (hx : x ∈ Sum.inr (visitTwin v) :: A) :
      geoOwner hP {v.1} x = geoOwner hP {v.1} (Sum.inr (visitTwin v)) := by
    apply (geoOwner_eq_iff hP {v.1} _ _).mpr
    rw [he]
    exact ((splitList_right_sameCycle_iff (Sum.inr v) (Sum.inr (visitTwin v)) A B hN x).mpr hx).symm
  rcases List.mem_cons.mp (hfull x) with hx | hx
  · exact Or.inl (hcL (List.mem_cons.mpr (Or.inl hx)))
  · rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (hcR (List.mem_cons_of_mem _ hx))
    · rcases List.mem_cons.mp hx with hx | hx
      · exact Or.inr (hcR (List.mem_cons.mpr (Or.inl hx)))
      · exact Or.inl (hcL (List.mem_cons_of_mem _ hx))

/-- Exactly two actual successor-orbit components arise from one selected
crossing. No arbitrary cycle representation or component correspondence is assumed. -/
theorem geoComponent_card_singleton {P : LabelledTuple n} (hP : CrossingGeometry P)
    (v : Visit P) : Fintype.card (GeoComponent hP {v.1}) = 2 := by
  have hu : (Finset.univ : Finset (GeoComponent hP {v.1})) =
      {geoOwner hP {v.1} (Sum.inr v), geoOwner hP {v.1} (Sum.inr (visitTwin v))} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact geoOwner_singleton_exhaust hP v q
  have hc : (Finset.univ : Finset (GeoComponent hP {v.1})).card = 2 :=
    Finset.card_eq_two.mpr ⟨_, _, geoOwner_singleton_ne hP v, hu⟩
  simpa only [Finset.card_univ] using hc


/-! ### Port of SM/CarrierInheritedOrder.lean -/

/-- The current actual successor follows each component's inherited original
cyclic order. This is an explicit invariant, not part of geoComponentCycle's definition. -/
def GeoInheritsMarkOrder {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) : Prop :=
  ∀ (q : GeoComponent hP T) (a : Mark P) (ha : a ∈ geoComponentCycle hP T q),
    (geoComponentCycle hP T q).next (geoComponentCycle_nodup hP T q) a ha =
      geoSmoothingSuccessor hP T a

/-- The next-point invariant is equivalently the actual filtered cycle's
formPerm action on its members. No assertion is made about nonmembers. -/
theorem geoInheritsMarkOrder_iff_formPerm {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) :
    GeoInheritsMarkOrder hP T ↔
      ∀ (q : GeoComponent hP T) (a : Mark P) (_ha : a ∈ geoComponentCycle hP T q),
        (geoComponentCycle hP T q).formPerm (geoComponentCycle_nodup hP T q) a =
          geoSmoothingSuccessor hP T a := by
  constructor
  · intro h q a ha
    rw [Cycle.formPerm_apply_mem_eq_next _ _ a ha]
    exact h q a ha
  · intro h q a ha
    rw [← Cycle.formPerm_apply_mem_eq_next _ _ a ha]
    exact h q a ha

/-- Before any selected reconnection the inherited component cycle is the
original circle, whose next point is the constructed actual successor. -/
theorem geoInheritsMarkOrder_empty {P : LabelledTuple n} (hP : CrossingGeometry P) : GeoInheritsMarkOrder hP ∅ := by
  rw [geoInheritsMarkOrder_iff_formPerm]
  intro q a ha
  have he : (⟨geoComponentCycle hP ∅ q, geoComponentCycle_nodup hP ∅ q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨geoMarkCycle hP, geoMarkCycle_nodup hP⟩ :=
    Subtype.ext (geoComponentCycle_empty hP q)
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  rw [hp, geoSmoothingSuccessor_empty]
  exact Cycle.formPerm_apply_mem_eq_next (geoMarkCycle hP) (geoMarkCycle_nodup hP)
    a (mem_geoMarkCycle hP a)

-- [port] `filter_splitList_left` -> accepted `Carrier.filter_splitList_left` (hypothesis-free, shared); not re-declared

-- [port] `filter_splitList_right` -> accepted `Carrier.filter_splitList_right` (hypothesis-free, shared); not re-declared

/-- One actual selected crossing has the two literal inherited child cycles.
Their representations, membership filters and permutation product are derived
from a rotation of the complete original marked circle. -/
theorem geoComponentCycle_singleton_splitList {P : LabelledTuple n} (hP : CrossingGeometry P) (v : Visit P) :
    ∃ A B : List (Mark P),
      (Sum.inr v :: B).Nodup ∧ (Sum.inr (visitTwin v) :: A).Nodup ∧
      (Sum.inr v :: B).Disjoint (Sum.inr (visitTwin v) :: A) ∧
      geoComponentCycle hP {v.1} (geoOwner hP {v.1} (Sum.inr v)) =
        (Sum.inr v :: B : Cycle (Mark P)) ∧
      geoComponentCycle hP {v.1} (geoOwner hP {v.1} (Sum.inr (visitTwin v))) =
        (Sum.inr (visitTwin v) :: A : Cycle (Mark P)) ∧
      geoSmoothingSuccessor hP {v.1} =
        (Sum.inr v :: B).formPerm * (Sum.inr (visitTwin v) :: A).formPerm := by
  classical
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  have hab : a ≠ b := fun he => (visitTwin_ne v).symm (Sum.inr.inj he)
  obtain ⟨k, A, B, hrot⟩ := geoMarkList_rotate_split hP a b hab
  have hN : (a :: (A ++ b :: B)).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr (geoMarkList_nodup hP)
  obtain ⟨hL, hR, hd⟩ := splitList_child_data a b A B hN
  have hc : geoMarkCycle hP = (a :: (A ++ b :: B) : Cycle (Mark P)) := by
    rw [← hrot]
    exact (geoMarkCycle_rotation hP k).symm
  have hp : (a :: (A ++ b :: B)).formPerm = geoMarkSuccessor hP := by
    rw [← hrot, List.formPerm_rotate _ (geoMarkList_nodup hP) k]
    exact (geoMarkSuccessor_eq_formPerm hP).symm
  have hs : geoSmoothingSuccessor hP {v.1} =
      (a :: (A ++ b :: B)).formPerm * Equiv.swap a b := by
    simpa only [Finset.insert_empty, geoSmoothingSuccessor_empty, hp] using
      geoSmoothingSuccessor_insert hP (∅ : Finset (Crossing P)) v
        (Finset.notMem_empty v.1)
  have hownerL (m : Mark P) : geoOwner hP {v.1} m = geoOwner hP {v.1} a ↔
      m ∈ a :: B := by
    rw [geoOwner_eq_iff, hs, Equiv.Perm.sameCycle_comm]
    exact splitList_left_sameCycle_iff a b A B hN m
  have hownerR (m : Mark P) : geoOwner hP {v.1} m = geoOwner hP {v.1} b ↔
      m ∈ b :: A := by
    rw [geoOwner_eq_iff, hs, Equiv.Perm.sameCycle_comm]
    exact splitList_right_sameCycle_iff a b A B hN m
  have hpL : (fun m => decide (geoOwner hP {v.1} m = geoOwner hP {v.1} a)) =
      (fun m => decide (m ∈ a :: B)) := by
    funext m
    simp only [hownerL m]
  have hpR : (fun m => decide (geoOwner hP {v.1} m = geoOwner hP {v.1} b)) =
      (fun m => decide (m ∈ b :: A)) := by
    funext m
    simp only [hownerR m]
  have hcL : geoComponentCycle hP {v.1} (geoOwner hP {v.1} a) =
      (a :: B : Cycle (Mark P)) := by
    rw [geoComponentCycle, hc, Cycle.filter_coe, hpL]
    refine congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_left a b A B hN))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  have hcR : geoComponentCycle hP {v.1} (geoOwner hP {v.1} b) =
      (b :: A : Cycle (Mark P)) := by
    rw [geoComponentCycle, hc, Cycle.filter_coe, hpR]
    refine (congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_right a b A B hN))).trans
      (Cycle.coe_eq_coe.mpr (List.isRotated_concat b A))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  exact ⟨A, B, hL, hR, hd, hcL, hcR, hs.trans (splitList_identity a b A B hN)⟩

/-- The inherited-order invariant holds for one actual selected crossing.
Actual geoOwner exhaustion reduces to the two child cycles, and disjointness
makes the full successor product restrict to each child's own formPerm. -/
theorem geoInheritsMarkOrder_singleton {P : LabelledTuple n} (hP : CrossingGeometry P) (v : Visit P) : GeoInheritsMarkOrder hP {v.1} := by
  rw [geoInheritsMarkOrder_iff_formPerm]
  intro q m hm
  obtain ⟨A, B, hL, hR, hd, hcL, hcR, hs⟩ := geoComponentCycle_singleton_splitList hP v
  rcases geoOwner_singleton_exhaust hP v q with hq | hq
  · subst q
    have hmL : m ∈ Sum.inr v :: B := by
      rw [hcL] at hm
      exact hm
    have he : (⟨geoComponentCycle hP {v.1} (geoOwner hP {v.1} (Sum.inr v)),
        geoComponentCycle_nodup hP {v.1} (geoOwner hP {v.1} (Sum.inr v))⟩ :
        {s : Cycle (Mark P) // s.Nodup}) = ⟨(Sum.inr v :: B : Cycle (Mark P)), hL⟩ :=
      Subtype.ext hcL
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    rw [hp]
    change (Sum.inr v :: B).formPerm m = geoSmoothingSuccessor hP {v.1} m
    rw [hs, Equiv.Perm.mul_apply,
      List.formPerm_apply_of_notMem (fun hr => hd hmL hr)]
  · subst q
    have hmR : m ∈ Sum.inr (visitTwin v) :: A := by
      rw [hcR] at hm
      exact hm
    have he : (⟨geoComponentCycle hP {v.1} (geoOwner hP {v.1} (Sum.inr (visitTwin v))),
        geoComponentCycle_nodup hP {v.1} (geoOwner hP {v.1} (Sum.inr (visitTwin v)))⟩ :
        {s : Cycle (Mark P) // s.Nodup}) =
        ⟨(Sum.inr (visitTwin v) :: A : Cycle (Mark P)), hR⟩ := Subtype.ext hcR
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    rw [hp]
    change (Sum.inr (visitTwin v) :: A).formPerm m = geoSmoothingSuccessor hP {v.1} m
    rw [hs,
      (formPerm_disjoint_of_disjoint (Sum.inr v :: B) (Sum.inr (visitTwin v) :: A) hd).commute.eq,
      Equiv.Perm.mul_apply, List.formPerm_apply_of_notMem (fun hl => hd hl hmR)]


/-! ### Port of SM/CarrierCurrentCycle.lean -/

/-- Any literal representative of an actual inherited component has no repeated marks. -/
theorem geoComponentCycle_list_nodup {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T)
    (L : List (Mark P)) (hL : geoComponentCycle hP T q = (L : Cycle (Mark P))) :
    L.Nodup := by
  have hN := geoComponentCycle_nodup hP T q
  rw [hL] at hN
  exact hN

/-- The representative's membership is exactly its constructed incoming geoOwner. -/
theorem geoComponentCycle_list_mem_iff {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T)
    (L : List (Mark P)) (hL : geoComponentCycle hP T q = (L : Cycle (Mark P)))
    (m : Mark P) : m ∈ L ↔ geoOwner hP T m = q := by
  change m ∈ (L : Cycle (Mark P)) ↔ _
  rw [← hL]
  exact mem_geoComponentCycle hP T q m

/-- An explicit inherited-order hypothesis gives equality of the representative's
permutation with the current successor on its own marks, not on the whole ambient type. -/
theorem geoComponentCycle_list_eqOn {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (q : GeoComponent hP T) (L : List (Mark P))
    (hL : geoComponentCycle hP T q = (L : Cycle (Mark P))) :
    Set.EqOn L.formPerm (geoSmoothingSuccessor hP T) {m | m ∈ L} := by
  have hN := geoComponentCycle_list_nodup hP T q L hL
  have he : (⟨geoComponentCycle hP T q, geoComponentCycle_nodup hP T q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨(L : Cycle (Mark P)), hN⟩ :=
    Subtype.ext hL
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  change (geoComponentCycle hP T q).formPerm (geoComponentCycle_nodup hP T q) =
    (L : Cycle (Mark P)).formPerm hN at hp
  have hp' : (geoComponentCycle hP T q).formPerm
      (geoComponentCycle_nodup hP T q) = L.formPerm :=
    hp.trans (Cycle.formPerm_coe L hN)
  intro m hm
  have hmc : m ∈ geoComponentCycle hP T q := by
    rw [hL]
    exact hm
  rw [← hp']
  exact (geoInheritsMarkOrder_iff_formPerm hP T).mp hI q m hmc

/-- Distinct marks in one actual component supply the original rotation and
the geoOwner-filtered literal current split list. Its action equality is derived
from the explicit induction invariant. No representation is supplied as input. -/
theorem geoComponentCycle_current_split_data {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (q : GeoComponent hP T) (a b : Mark P) (hab : a ≠ b)
    (ha : geoOwner hP T a = q) (hb : geoOwner hP T b = q) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (geoMarkList hP).rotate k = a :: (A ++ b :: B) ∧
      let L := a :: (A.filter (fun m => decide (geoOwner hP T m = q)) ++
        b :: B.filter (fun m => decide (geoOwner hP T m = q)))
      geoComponentCycle hP T q = (L : Cycle (Mark P)) ∧ L.Nodup ∧
        (∀ m : Mark P, m ∈ L ↔ geoOwner hP T m = q) ∧
        Set.EqOn L.formPerm (geoSmoothingSuccessor hP T) {m | m ∈ L} := by
  obtain ⟨k, A, B, hrot⟩ := geoMarkList_rotate_split hP a b hab
  let L := a :: (A.filter (fun m => decide (geoOwner hP T m = q)) ++
    b :: B.filter (fun m => decide (geoOwner hP T m = q)))
  have hL : geoComponentCycle hP T q = (L : Cycle (Mark P)) :=
    geoComponentCycle_eq_filtered_splitList hP T q k a b A B hrot ha hb
  exact ⟨k, A, B, hrot, hL, geoComponentCycle_list_nodup hP T q L hL,
    geoComponentCycle_list_mem_iff hP T q L hL,
    geoComponentCycle_list_eqOn hP T hI q L hL⟩


/-! ### Port of SM/CarrierUnchangedComponent.lean -/

/-- The actual forward successor stays in its incoming geoOwner block for every
support, without independence or inherited-order assumptions. -/
theorem geoSmoothingSuccessor_mapsTo_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T) :
    Set.MapsTo (geoSmoothingSuccessor hP T)
      {m | geoOwner hP T m = q} {m | geoOwner hP T m = q} := by
  intro m hm
  exact (geoOwner_successor hP T m).trans hm

/-- The inverse actual successor also stays in the same geoOwner block. -/
theorem geoSmoothingSuccessor_symm_mapsTo_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T) :
    Set.MapsTo (geoSmoothingSuccessor hP T).symm
      {m | geoOwner hP T m = q} {m | geoOwner hP T m = q} := by
  intro m hm
  exact (geoOwner_predecessor hP T m).trans hm

-- [port] `smoothingSuccessor_bijOn_owner` -> accepted `geoSmoothingSuccessor_bijOn_owner` (SM/FlatCarriers*.lean); not re-declared

/-- If a fresh actual crossing's two incoming marks share an old geoOwner, its
insertion changes no outgoing slot in any other actual old geoOwner block. -/
theorem geoSmoothingSuccessor_insert_eqOn_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (q : GeoComponent hP T) (hq : q ≠ geoOwner hP T (Sum.inr v)) :
    Set.EqOn (geoSmoothingSuccessor hP (insert v.1 T)) (geoSmoothingSuccessor hP T)
      {m | geoOwner hP T m = q} := by
  intro m hm
  apply geoSmoothingSuccessor_insert_other hP T v hv m
  · intro he
    subst m
    exact hq hm.symm
  · intro he
    subst m
    exact hq (hm.symm.trans hc.symm)

/-- The new actual successor is bijective on every unaffected old geoOwner block,
since its action there agrees with the proved old block bijection. -/
theorem geoSmoothingSuccessor_insert_bijOn_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (q : GeoComponent hP T) (hq : q ≠ geoOwner hP T (Sum.inr v)) :
    Set.BijOn (geoSmoothingSuccessor hP (insert v.1 T))
      {m | geoOwner hP T m = q} {m | geoOwner hP T m = q} :=
  (geoSmoothingSuccessor_insert_eqOn_owner hP T v hv hc q hq).bijOn_iff.mpr
    (geoSmoothingSuccessor_bijOn_owner hP T q)

/-- Backward traversal on an unaffected old geoOwner block is unchanged as well.
The old inverse remains in that block, where the two forward actions agree. -/
theorem geoSmoothingSuccessor_insert_symm_eqOn_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (q : GeoComponent hP T) (hq : q ≠ geoOwner hP T (Sum.inr v)) :
    Set.EqOn (geoSmoothingSuccessor hP (insert v.1 T)).symm (geoSmoothingSuccessor hP T).symm
      {m | geoOwner hP T m = q} := by
  intro m hm
  have hx : geoOwner hP T ((geoSmoothingSuccessor hP T).symm m) = q :=
    (geoOwner_predecessor hP T m).trans hm
  have he := geoSmoothingSuccessor_insert_eqOn_owner hP T v hv hc q hq hx
  apply (geoSmoothingSuccessor hP (insert v.1 T)).injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]


/-! ### Port of SM/CarrierInsertOrbits.lean -/

/-- For a fresh actual selected crossing, an explicit inherited-order invariant
and same-current-component premise give the two exact ambient child orbits and
their successor actions. The original rotation and filtered child lists are constructed. -/
theorem geoSmoothingSuccessor_insert_child_data {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (geoMarkList hP).rotate k = Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B) ∧
      let q := geoOwner hP T (Sum.inr v)
      let AL := A.filter (fun m => decide (geoOwner hP T m = q))
      let BL := B.filter (fun m => decide (geoOwner hP T m = q))
      (Sum.inr v :: BL).Nodup ∧ (Sum.inr (visitTwin v) :: AL).Nodup ∧
      (Sum.inr v :: BL).Disjoint (Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, geoOwner hP (insert v.1 T) m =
          geoOwner hP (insert v.1 T) (Sum.inr v) ↔ m ∈ Sum.inr v :: BL) ∧
      (∀ m : Mark P, geoOwner hP (insert v.1 T) m =
          geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) ↔
          m ∈ Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: BL →
        geoSmoothingSuccessor hP (insert v.1 T) m = (Sum.inr v :: BL).formPerm m) ∧
      (∀ m : Mark P, m ∈ Sum.inr (visitTwin v) :: AL →
        geoSmoothingSuccessor hP (insert v.1 T) m =
          (Sum.inr (visitTwin v) :: AL).formPerm m) := by
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  let q := geoOwner hP T a
  have hab : a ≠ b := fun he => (visitTwin_ne v).symm (Sum.inr.inj he)
  obtain ⟨k, A, B, hrot, hL, hN, hmem, he⟩ :=
    geoComponentCycle_current_split_data hP T hI q a b hab rfl hc.symm
  let AL := A.filter (fun m => decide (geoOwner hP T m = q))
  let BL := B.filter (fun m => decide (geoOwner hP T m = q))
  have hdata := splitList_child_data a b AL BL hN
  refine ⟨k, A, B, hrot, hdata.1, hdata.2.1, hdata.2.2, ?_, ?_, ?_, ?_⟩
  · intro m
    rw [geoOwner_eq_iff, Equiv.Perm.sameCycle_comm, geoSmoothingSuccessor_insert hP T v hv]
    exact splitList_ambient_left_sameCycle_iff (geoSmoothingSuccessor hP T)
      a b AL BL hN he m
  · intro m
    rw [geoOwner_eq_iff, Equiv.Perm.sameCycle_comm, geoSmoothingSuccessor_insert hP T v hv]
    exact splitList_ambient_right_sameCycle_iff (geoSmoothingSuccessor hP T)
      a b AL BL hN he m
  · intro m hm
    rw [geoSmoothingSuccessor_insert hP T v hv]
    exact splitList_ambient_left_apply (geoSmoothingSuccessor hP T)
      a b AL BL hN he m hm
  · intro m hm
    rw [geoSmoothingSuccessor_insert hP T v hv]
    exact splitList_ambient_right_apply (geoSmoothingSuccessor hP T)
      a b AL BL hN he m hm

/-- An unaffected old geoOwner block remains exactly one new orbit, with no new
outside marks. Both directions use proved invariant-set orbit transport. -/
theorem geoOwner_insert_iff_of_unaffected {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (q : GeoComponent hP T) (hq : q ≠ geoOwner hP T (Sum.inr v))
    (m : Mark P) (hm : geoOwner hP T m = q) (z : Mark P) :
    geoOwner hP (insert v.1 T) z = geoOwner hP (insert v.1 T) m ↔
      geoOwner hP T z = q := by
  have ht := sameCycle_congr_of_eqOn_bijOn
    (geoSmoothingSuccessor hP T) (geoSmoothingSuccessor hP (insert v.1 T))
    {x | geoOwner hP T x = q} (geoSmoothingSuccessor_bijOn_owner hP T q)
    (geoSmoothingSuccessor_insert_eqOn_owner hP T v hv hc q hq).symm m hm z
  constructor
  · intro hz
    have hi := (geoOwner_eq_iff hP (insert v.1 T) m z).mp hz.symm
    have ho := (geoOwner_eq_iff hP T m z).mpr (ht.mp hi)
    exact ho.symm.trans hm
  · intro hz
    have ho := (geoOwner_eq_iff hP T m z).mp (hm.trans hz.symm)
    exact ((geoOwner_eq_iff hP (insert v.1 T) m z).mpr (ht.mpr ho)).symm

/-- The actual inherited cycle of an unaffected component is unchanged, since
its new geoOwner filter is pointwise the same original-circle predicate. -/
theorem geoComponentCycle_insert_unaffected {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (q : GeoComponent hP T) (hq : q ≠ geoOwner hP T (Sum.inr v))
    (m : Mark P) (hm : geoOwner hP T m = q) :
    geoComponentCycle hP (insert v.1 T) (geoOwner hP (insert v.1 T) m) =
      geoComponentCycle hP T q := by
  unfold geoComponentCycle
  apply congrArg (fun p : Mark P → Bool => (geoMarkCycle hP).filter p)
  funext z
  exact decide_eq_decide.mpr (geoOwner_insert_iff_of_unaffected hP T v hv hc q hq m hm z)


/-! ### Port of SM/CarrierInheritedInsert.lean -/

/-- If an actual new-geoOwner block lies in one old-geoOwner block, its inherited
cycle is obtained by filtering that old inherited cycle. The absorption is
proved on the full original marked circle before restricting to the old block. -/
theorem geoComponentCycle_filter_of_owner_imp {P : LabelledTuple n} (hP : CrossingGeometry P) (T U : Finset (Crossing P))
    (q : GeoComponent hP T) (r : GeoComponent hP U)
    (hsub : ∀ m : Mark P, geoOwner hP U m = r → geoOwner hP T m = q) :
    geoComponentCycle hP U r =
      (geoComponentCycle hP T q).filter (fun m => decide (geoOwner hP U m = r)) := by
  unfold geoComponentCycle
  rw [Cycle.filter_filter]
  apply congrArg (fun p : Mark P → Bool => (geoMarkCycle hP).filter p)
  funext m
  by_cases hm : geoOwner hP U m = r
  · simp only [hm, hsub m hm, decide_true, Bool.and_self]
  · simp only [hm, decide_false, Bool.false_and]

/-- The affected new inherited cycles are the literal two geoOwner-filtered child
lists, using the same actual original rotation as the insertion orbit data.
Full-circle filter absorption justifies the restriction to the old component. -/
theorem geoComponentCycle_insert_child_cycles {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (geoMarkList hP).rotate k = Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B) ∧
      let q := geoOwner hP T (Sum.inr v)
      let AL := A.filter (fun m => decide (geoOwner hP T m = q))
      let BL := B.filter (fun m => decide (geoOwner hP T m = q))
      geoComponentCycle hP T q =
        (Sum.inr v :: (AL ++ Sum.inr (visitTwin v) :: BL) : Cycle (Mark P)) ∧
      geoComponentCycle hP (insert v.1 T)
          (geoOwner hP (insert v.1 T) (Sum.inr v)) =
        (Sum.inr v :: BL : Cycle (Mark P)) ∧
      geoComponentCycle hP (insert v.1 T)
          (geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v))) =
        (Sum.inr (visitTwin v) :: AL : Cycle (Mark P)) ∧
      (∀ m : Mark P, geoOwner hP (insert v.1 T) m =
          geoOwner hP (insert v.1 T) (Sum.inr v) ↔ m ∈ Sum.inr v :: BL) ∧
      (∀ m : Mark P, geoOwner hP (insert v.1 T) m =
          geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) ↔
          m ∈ Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: BL →
        geoSmoothingSuccessor hP (insert v.1 T) m = (Sum.inr v :: BL).formPerm m) ∧
      (∀ m : Mark P, m ∈ Sum.inr (visitTwin v) :: AL →
        geoSmoothingSuccessor hP (insert v.1 T) m =
          (Sum.inr (visitTwin v) :: AL).formPerm m) := by
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  let q := geoOwner hP T a
  obtain ⟨k, A, B, hrot, hL, hR, hd, hownerL, hownerR, hstepL, hstepR⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI v hv hc
  let AL := A.filter (fun m => decide (geoOwner hP T m = q))
  let BL := B.filter (fun m => decide (geoOwner hP T m = q))
  have hparent : geoComponentCycle hP T q = (a :: (AL ++ b :: BL) : Cycle (Mark P)) :=
    geoComponentCycle_eq_filtered_splitList hP T q k a b A B hrot rfl hc.symm
  have hN := geoComponentCycle_list_nodup hP T q (a :: (AL ++ b :: BL)) hparent
  have hsubL (m : Mark P)
      (hm : geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) a) :
      geoOwner hP T m = q := by
    rcases List.mem_cons.mp ((hownerL m).mp hm) with hm | hm
    · subst m
      rfl
    · exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hsubR (m : Mark P)
      (hm : geoOwner hP (insert v.1 T) m = geoOwner hP (insert v.1 T) b) :
      geoOwner hP T m = q := by
    rcases List.mem_cons.mp ((hownerR m).mp hm) with hm | hm
    · subst m
      exact hc.symm
    · exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hpL : (fun m => decide (geoOwner hP (insert v.1 T) m =
      geoOwner hP (insert v.1 T) a)) = (fun m => decide (m ∈ a :: BL)) := by
    funext m
    exact decide_eq_decide.mpr (hownerL m)
  have hpR : (fun m => decide (geoOwner hP (insert v.1 T) m =
      geoOwner hP (insert v.1 T) b)) = (fun m => decide (m ∈ b :: AL)) := by
    funext m
    exact decide_eq_decide.mpr (hownerR m)
  have hcL : geoComponentCycle hP (insert v.1 T) (geoOwner hP (insert v.1 T) a) =
      (a :: BL : Cycle (Mark P)) := by
    rw [geoComponentCycle_filter_of_owner_imp hP T (insert v.1 T) q
      (geoOwner hP (insert v.1 T) a) hsubL, hparent, Cycle.filter_coe, hpL]
    refine congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_left a b AL BL hN))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  have hcR : geoComponentCycle hP (insert v.1 T) (geoOwner hP (insert v.1 T) b) =
      (b :: AL : Cycle (Mark P)) := by
    rw [geoComponentCycle_filter_of_owner_imp hP T (insert v.1 T) q
      (geoOwner hP (insert v.1 T) b) hsubR, hparent, Cycle.filter_coe, hpR]
    refine (congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_right a b AL BL hN))).trans
      (Cycle.coe_eq_coe.mpr (List.isRotated_concat b AL))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  exact ⟨k, A, B, hrot, hparent, hcL, hcR, hownerL, hownerR, hstepL, hstepR⟩

/-- A proved inherited-cycle representative transports the complete formPerm
through its Nodup subtype, without a dependent rewrite or an order assumption. -/
theorem geoComponentCycle_formPerm_eq_of_list {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T)
    (L : List (Mark P)) (hL : geoComponentCycle hP T q = (L : Cycle (Mark P))) :
    (geoComponentCycle hP T q).formPerm (geoComponentCycle_nodup hP T q) = L.formPerm := by
  have hN := geoComponentCycle_list_nodup hP T q L hL
  have he : (⟨geoComponentCycle hP T q, geoComponentCycle_nodup hP T q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨(L : Cycle (Mark P)), hN⟩ := Subtype.ext hL
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  change (geoComponentCycle hP T q).formPerm (geoComponentCycle_nodup hP T q) =
    (L : Cycle (Mark P)).formPerm hN at hp
  exact hp.trans (Cycle.formPerm_coe L hN)

/-- Inserting a fresh actual crossing whose incoming marks currently share an
geoOwner preserves the inherited-order invariant. The affected cycles are derived
by full-circle filtering, and every other old geoOwner's cycle and action agree.
No independence premise or supplied component correspondence is used. -/
theorem geoInheritsMarkOrder_insert {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) :
    GeoInheritsMarkOrder hP (insert v.1 T) := by
  rw [geoInheritsMarkOrder_iff_formPerm]
  intro r z hz
  have hr := (mem_geoComponentCycle hP (insert v.1 T) r z).mp hz
  subst r
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  let q := geoOwner hP T a
  by_cases hqz : geoOwner hP T z = q
  · obtain ⟨k, A, B, hrot, hparent, hcL, hcR, hownerL, hownerR, hstepL, hstepR⟩ :=
      geoComponentCycle_insert_child_cycles hP T hI v hv hc
    let AL := A.filter (fun m => decide (geoOwner hP T m = q))
    let BL := B.filter (fun m => decide (geoOwner hP T m = q))
    have hzP : z ∈ a :: (AL ++ b :: BL) :=
      (geoComponentCycle_list_mem_iff hP T q (a :: (AL ++ b :: BL)) hparent z).mpr hqz
    have hzchild : z ∈ a :: BL ∨ z ∈ b :: AL := by
      rcases List.mem_cons.mp hzP with he | hzP
      · exact Or.inl (List.mem_cons.mpr (Or.inl he))
      · rcases List.mem_append.mp hzP with hzA | hzB
        · exact Or.inr (List.mem_cons_of_mem b hzA)
        · rcases List.mem_cons.mp hzB with he | hzB
          · exact Or.inr (List.mem_cons.mpr (Or.inl he))
          · exact Or.inl (List.mem_cons_of_mem a hzB)
    rcases hzchild with hzL | hzR
    · have hcz : geoComponentCycle hP (insert v.1 T) (geoOwner hP (insert v.1 T) z) =
          (a :: BL : Cycle (Mark P)) := by
        rw [(hownerL z).mpr hzL]
        exact hcL
      rw [geoComponentCycle_formPerm_eq_of_list hP (insert v.1 T)
        (geoOwner hP (insert v.1 T) z) (a :: BL) hcz]
      exact (hstepL z hzL).symm
    · have hcz : geoComponentCycle hP (insert v.1 T) (geoOwner hP (insert v.1 T) z) =
          (b :: AL : Cycle (Mark P)) := by
        rw [(hownerR z).mpr hzR]
        exact hcR
      rw [geoComponentCycle_formPerm_eq_of_list hP (insert v.1 T)
        (geoOwner hP (insert v.1 T) z) (b :: AL) hcz]
      exact (hstepR z hzR).symm
  · have hcz := geoComponentCycle_insert_unaffected hP T v hv hc
      (geoOwner hP T z) hqz z rfl
    have he : (⟨geoComponentCycle hP (insert v.1 T) (geoOwner hP (insert v.1 T) z),
        geoComponentCycle_nodup hP (insert v.1 T) (geoOwner hP (insert v.1 T) z)⟩ :
        {s : Cycle (Mark P) // s.Nodup}) =
        ⟨geoComponentCycle hP T (geoOwner hP T z),
          geoComponentCycle_nodup hP T (geoOwner hP T z)⟩ := Subtype.ext hcz
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    change (geoComponentCycle hP (insert v.1 T) (geoOwner hP (insert v.1 T) z)).formPerm
        (geoComponentCycle_nodup hP (insert v.1 T) (geoOwner hP (insert v.1 T) z)) =
      (geoComponentCycle hP T (geoOwner hP T z)).formPerm
        (geoComponentCycle_nodup hP T (geoOwner hP T z)) at hp
    rw [hp]
    have ho := (geoInheritsMarkOrder_iff_formPerm hP T).mp hI (geoOwner hP T z) z
      (mem_geoComponentCycle_owner hP T z)
    exact ho.trans ((geoSmoothingSuccessor_insert_eqOn_owner hP T v hv hc
      (geoOwner hP T z) hqz) rfl).symm


/-! ### Port of SM/CarrierComponentFibers.lean -/

/-- The actual quotient forget map has exactly two elements over the affected
old geoOwner: the distinct new incoming owners of the inserted crossing's visits.
Completeness uses the same original split rotation as the checked child data. -/
theorem geoComponentForgetSwitch_fiber_affected {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) :
    geoOwner hP (insert v.1 T) (Sum.inr v) ≠
        geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) ∧
      (Finset.univ.filter (fun r =>
        geoComponentForgetSwitch hP T v hv
          ((geoOwner_eq_iff hP T (Sum.inr v) (Sum.inr (visitTwin v))).mp hc) r =
            geoOwner hP T (Sum.inr v))) =
        {geoOwner hP (insert v.1 T) (Sum.inr v),
          geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v))} := by
  obtain ⟨k, A, B, hrot, hNLeft, hNRight, hdisjoint,
      hleft, hright, hactLeft, hactRight⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI v hv hc
  have hcOrbit := (geoOwner_eq_iff hP T (Sum.inr v) (Sum.inr (visitTwin v))).mp hc
  refine ⟨?_, ?_⟩
  · intro he
    have hbLeft := (hleft (Sum.inr (visitTwin v))).mp he.symm
    exact hdisjoint hbLeft List.mem_cons_self
  · ext r
    obtain ⟨m, rfl⟩ := geoOwner_surjective hP (insert v.1 T) r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      geoComponentForgetSwitch_owner, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hm
      have hfull : m ∈ Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B) := by
        rw [← hrot]
        exact List.mem_rotate.mpr (mem_geoMarkList hP m)
      rcases List.mem_cons.mp hfull with he | hfull
      · subst m
        exact Or.inl rfl
      · rcases List.mem_append.mp hfull with hmA | hmB
        · have hmAL : m ∈ A.filter
              (fun x => decide (geoOwner hP T x = geoOwner hP T (Sum.inr v))) :=
            List.mem_filter.mpr ⟨hmA, by simpa only [decide_eq_true_eq] using hm⟩
          exact Or.inr ((hright m).mpr (List.mem_cons_of_mem _ hmAL))
        · rcases List.mem_cons.mp hmB with he | hmB
          · subst m
            exact Or.inr rfl
          · have hmBL : m ∈ B.filter
                (fun x => decide (geoOwner hP T x = geoOwner hP T (Sum.inr v))) :=
              List.mem_filter.mpr ⟨hmB, by simpa only [decide_eq_true_eq] using hm⟩
            exact Or.inl ((hleft m).mpr (List.mem_cons_of_mem _ hmBL))
    · rintro (he | he)
      · exact geoOwner_insert_eq_imp hP T v hv hcOrbit he
      · exact (geoOwner_insert_eq_imp hP T v hv hcOrbit he).trans hc.symm

/-- Every unaffected old component has one element in the actual forget-map
fiber, namely the new geoOwner of any of its actual marks. Its representative is
supplied as a mark with its old-geoOwner equality, not as a component correspondence. -/
theorem geoComponentForgetSwitch_fiber_unaffected {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (q : GeoComponent hP T) (hq : q ≠ geoOwner hP T (Sum.inr v))
    (m : Mark P) (hm : geoOwner hP T m = q) :
    (Finset.univ.filter (fun r =>
      geoComponentForgetSwitch hP T v hv
        ((geoOwner_eq_iff hP T (Sum.inr v) (Sum.inr (visitTwin v))).mp hc) r = q)) =
      {geoOwner hP (insert v.1 T) m} := by
  ext r
  obtain ⟨z, rfl⟩ := geoOwner_surjective hP (insert v.1 T) r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    geoComponentForgetSwitch_owner, Finset.mem_singleton]
  exact (geoOwner_insert_iff_of_unaffected hP T v hv hc q hq m hm z).symm


/-! ### Geometric interlacement: the complement law and the printed "exactly one visit between" clause
(CV-free copies of CV/Events.lean `geometricCrossingVisitBetween_complement`,
`geometric_alternating_visits_iff_unique`, `geometric_unique_between_swap`,
`geometricInterlaces_iff_unique`; the tier-0 replacements of `crossingVisitBetween_complement`
(SM/Interlacement.lean:35) and `interlaces_iff_unique` (SM/InterlaceCount.lean:20) consumed by
SM/CarrierSameArc.lean) -/

omit [NeZero n] in
theorem geo_visitPosition_ne_of_ne {P : LabelledTuple n} (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (i : {k // k ∈ x.val}) (j : {k // k ∈ y.val}) :
    geometricVisitPosition hP ⟨x, i⟩ ≠ geometricVisitPosition hP ⟨y, j⟩ := by
  intro he
  exact hxy (congrArg Sigma.fst (geometricVisitPosition_injective hP he))

omit [NeZero n] in
theorem geo_visitPosition_ne_of_visit_ne {P : LabelledTuple n} (hP : CrossingGeometry P)
    (x : Crossing P) {i j : {k // k ∈ x.val}} (hij : i ≠ j) :
    geometricVisitPosition hP ⟨x, i⟩ ≠ geometricVisitPosition hP ⟨x, j⟩ := by
  intro he
  have h := geometricVisitPosition_injective hP he
  exact hij (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- On the geometric record domain the two open arcs cut by the two visits of `x` are
complementary for the visits of another crossing `y`. -/
theorem geo_crossingVisitBetween_complement {P : LabelledTuple n} (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j : {i // i ∈ y.val}) :
    geometricCrossingVisitBetween hP x x₀ x₁ y j ↔
      ¬ geometricCrossingVisitBetween hP x x₁ x₀ y j := by
  apply traversalBetween_complement
  · exact geo_visitPosition_ne_of_ne hP hxy x₀ j
  · exact geo_visitPosition_ne_of_ne hP hxy.symm j x₁
  · exact geo_visitPosition_ne_of_visit_ne hP x hx.symm

theorem geo_alternating_visits_iff_unique {P : LabelledTuple n} (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    (∃ y₀ y₁ : {i // i ∈ y.val}, y₀ ≠ y₁ ∧
      geometricCrossingVisitBetween hP x x₀ x₁ y y₀ ∧
      geometricCrossingVisitBetween hP x x₁ x₀ y y₁) ↔
      ∃! j, geometricCrossingVisitBetween hP x x₀ x₁ y j := by
  rw [crossing_unique_visit_iff]
  constructor
  · rintro ⟨y₀, y₁, hy, h₀, h₁⟩
    exact ⟨y₀, y₁, hy, h₀,
      (geo_crossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₁).mp h₁⟩
  · rintro ⟨y₀, y₁, hy, h₀, h₁⟩
    exact ⟨y₀, y₁, hy, h₀,
      (geo_crossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₁).mpr h₁⟩

theorem geo_unique_between_swap {P : LabelledTuple n} (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    (∃! j, geometricCrossingVisitBetween hP x x₀ x₁ y j) ↔
      ∃! j, geometricCrossingVisitBetween hP x x₁ x₀ y j := by
  rw [← geo_alternating_visits_iff_unique hP hxy x₀ x₁ hx,
    ← geo_alternating_visits_iff_unique hP hxy x₁ x₀ hx.symm]
  constructor <;> rintro ⟨a, b, hab, ha, hb⟩
  · exact ⟨b, a, hab.symm, hb, ha⟩
  · exact ⟨b, a, hab.symm, hb, ha⟩

/-- The printed clause of def:interlace on the geometric record domain: `x ∼ y` iff exactly one of
the two visits of `y` lies between the two visits of `x`, for either order of the visits of `x`. -/
theorem geo_interlaces_iff_unique {P : LabelledTuple n} (hP : CrossingGeometry P)
    (x y : Crossing P) (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁) :
    GeometricInterlaces hP x y ↔ x ≠ y ∧
      ∃! j, geometricCrossingVisitBetween hP x x₀ x₁ y j := by
  constructor
  · rintro ⟨hxy, a, b, c, d, hab, hcd, h₀, h₁⟩
    refine ⟨hxy, ?_⟩
    have hu := (geo_alternating_visits_iff_unique hP hxy a b hab).mp ⟨c, d, hcd, h₀, h₁⟩
    rcases crossing_visits_exhaust x x₀ x₁ hx a with he | he
    · subst a
      have hb : b = x₁ := by
        rcases crossing_visits_exhaust x x₀ x₁ hx b with hb | hb
        · exact (hab hb.symm).elim
        · exact hb
      simpa only [hb] using hu
    · subst a
      have hb : b = x₀ := by
        rcases crossing_visits_exhaust x x₀ x₁ hx b with hb | hb
        · exact hb
        · exact (hab hb.symm).elim
      rw [hb] at hu
      exact (geo_unique_between_swap hP hxy x₀ x₁ hx).mpr hu
  · rintro ⟨hxy, hu⟩
    obtain ⟨a, b, hab, ha, hb⟩ :=
      (geo_alternating_visits_iff_unique hP hxy x₀ x₁ hx).mpr hu
    exact ⟨hxy, x₀, x₁, a, b, hx, hab, ha, hb⟩


/-! ### Port of SM/CarrierSameArc.lean -/

section SameArc

variable {P : LabelledTuple n}

/-- For distinct actual crossings and either ordering of each actual visit pair,
noninterlacement is exactly equality of the two open-arc membership statuses. -/
theorem geo_not_interlaces_iff_same_arc_status (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ GeometricInterlaces hP x y ↔
      (geometricCrossingVisitBetween hP x x₀ x₁ y y₀ ↔
        geometricCrossingVisitBetween hP x x₀ x₁ y y₁) := by
  constructor
  · intro hNI
    constructor
    · intro h₀
      by_contra h₁
      exact hNI ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀,
        (geo_crossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₁).mpr h₁⟩
    · intro h₁
      by_contra h₀
      exact hNI ⟨hxy, x₀, x₁, y₁, y₀, hx, hy.symm, h₁,
        (geo_crossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₀).mpr h₀⟩
  · intro hsame hI
    obtain ⟨j, hj, hu⟩ := (geo_interlaces_iff_unique hP x y x₀ x₁ hx).mp hI |>.2
    have h₀ : geometricCrossingVisitBetween hP x x₀ x₁ y y₀ := by
      rcases crossing_visits_exhaust y y₀ y₁ hy j with he | he
      · exact he ▸ hj
      · exact hsame.mpr (he ▸ hj)
    exact hy ((hu y₀ h₀).trans (hu y₁ (hsame.mp h₀)).symm)

/-- The equivalent statuses put both actual visits in one of the two oriented
open arcs. The complement law uses distinct crossing positions, so no endpoint
case is silently discarded. -/
theorem geo_not_interlaces_iff_one_open_arc (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ GeometricInterlaces hP x y ↔
      (geometricCrossingVisitBetween hP x x₀ x₁ y y₀ ∧
        geometricCrossingVisitBetween hP x x₀ x₁ y y₁) ∨
      (geometricCrossingVisitBetween hP x x₁ x₀ y y₀ ∧
        geometricCrossingVisitBetween hP x x₁ x₀ y y₁) := by
  rw [geo_not_interlaces_iff_same_arc_status hP hxy x₀ x₁ hx y₀ y₁ hy,
    geo_crossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₀,
    geo_crossingVisitBetween_complement hP hxy x₁ x₀ hx.symm y₁]
  by_cases h₀ : geometricCrossingVisitBetween hP x x₀ x₁ y y₀ <;>
    by_cases h₁ : geometricCrossingVisitBetween hP x x₀ x₁ y y₁ <;> simp [h₀, h₁]

/-- No choice of first visit of the second crossing affects its arc membership
when the actual crossings do not interlace. The two input visits may coincide. -/
theorem geo_not_interlaces_all_visits_same_arc (hP : CrossingGeometry P)
    {x y : Crossing P} (hxy : x ≠ y) (hNI : ¬ GeometricInterlaces hP x y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    geometricCrossingVisitBetween hP x x₀ x₁ y j ↔
      geometricCrossingVisitBetween hP x x₀ x₁ y k := by
  by_cases hjk : j = k
  · subst k
    exact Iff.rfl
  · exact (geo_not_interlaces_iff_same_arc_status hP hxy x₀ x₁ hx j k hjk).mp hNI

/-- Actual independent support supplies noninterlacement for any two distinct
selected crossings; no hypothesis about current carrier ownership is used. -/
theorem geoIndependent_crossing_visits_same_arc (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    geometricCrossingVisitBetween hP x x₀ x₁ y j ↔
      geometricCrossingVisitBetween hP x x₀ x₁ y k :=
  geo_not_interlaces_all_visits_same_arc hP hxy
    (hS x hxS y hyS hxy) x₀ x₁ hx j k

/-- The other selected pair is wholly in one original open arc of the selected
pair, the noninterlacement input needed for the source's splitting induction. -/
theorem geoIndependent_crossing_visits_one_open_arc (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    (geometricCrossingVisitBetween hP x x₀ x₁ y y₀ ∧
      geometricCrossingVisitBetween hP x x₀ x₁ y y₁) ∨
    (geometricCrossingVisitBetween hP x x₁ x₀ y y₀ ∧
      geometricCrossingVisitBetween hP x x₁ x₀ y y₁) :=
  (geo_not_interlaces_iff_one_open_arc hP hxy x₀ x₁ hx y₀ y₁ hy).mp
    (hS x hxS y hyS hxy)

/-- The status equivalence for the constructed actual twin pairing, written
literally in physical traversal positions. The pair inequalities are derived
from the checked construction rather than supplied as extra premises. -/
theorem geo_not_interlaces_iff_twin_same_arc (hP : CrossingGeometry P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ GeometricInterlaces hP v.1 w.1 ↔
      (traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP w)
          (geometricVisitPosition hP (visitTwin v)) ↔
        traversalBetween (geometricVisitPosition hP v)
          (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP (visitTwin v))) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact geo_not_interlaces_iff_same_arc_status hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- Noninterlacement places the actual twin pair together on either the forward
or backward open arc of the other actual twin pair, including wraparound. -/
theorem geo_not_interlaces_iff_twin_one_open_arc (hP : CrossingGeometry P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ GeometricInterlaces hP v.1 w.1 ↔
      (traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP w)
          (geometricVisitPosition hP (visitTwin v)) ∧
        traversalBetween (geometricVisitPosition hP v)
          (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP (visitTwin v))) ∨
      (traversalBetween (geometricVisitPosition hP (visitTwin v)) (geometricVisitPosition hP w)
          (geometricVisitPosition hP v) ∧
        traversalBetween (geometricVisitPosition hP (visitTwin v))
          (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP v)) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact geo_not_interlaces_iff_one_open_arc hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- In an actual independent support, every other selected twin pair lies in
one original oriented open arc of the selected pair. This is a statement about
actual traversal positions, not a supplied current-cycle correspondence. -/
theorem geoIndependent_twin_one_open_arc (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1) :
    (traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP w)
        (geometricVisitPosition hP (visitTwin v)) ∧
      traversalBetween (geometricVisitPosition hP v)
        (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP (visitTwin v))) ∨
    (traversalBetween (geometricVisitPosition hP (visitTwin v)) (geometricVisitPosition hP w)
        (geometricVisitPosition hP v) ∧
      traversalBetween (geometricVisitPosition hP (visitTwin v))
        (geometricVisitPosition hP (visitTwin w)) (geometricVisitPosition hP v)) :=
  (geo_not_interlaces_iff_twin_one_open_arc hP v w hvw).mp
    (hS v.1 hvS w.1 hwS hvw)

end SameArc


/-! ### Port of SM/CarrierMarkedArcLists.lean -/

/-- In any actual rotated complete marked list, the open list from a to b
is exactly the strict physical traversal arc, including wraparound. -/
theorem geoMarkList_rotate_left_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ A ↔ traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP m)
      (geoMarkPosition hP b) := by
  let _ := geoMarkLinearOrder hP
  have hr : (Finset.univ : Finset (Mark P)).sort.rotate k = a :: (A ++ b :: B) := hrot
  exact sorted_rotate_split_mem_iff Finset.univ k a b A B m hr (Finset.mem_univ m)

/-- The other open list is the reverse oriented physical arc, with both
endpoint marks excluded rather than assigned by a non-strict inequality. -/
theorem geoMarkList_rotate_right_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ B ↔ traversalBetween (geoMarkPosition hP b) (geoMarkPosition hP m)
      (geoMarkPosition hP a) := by
  let _ := geoMarkLinearOrder hP
  have hr : (Finset.univ : Finset (Mark P)).sort.rotate k = a :: (A ++ b :: B) := hrot
  exact sorted_rotate_split_reverse_mem_iff Finset.univ k a b A B m hr (Finset.mem_univ m)

/-- Filtering the physical forward arc to one actual component adds precisely
its geoOwner equality. No compatibility with the current successor is assumed. -/
theorem geoMarkList_filter_left_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (q : GeoComponent hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ A.filter (fun x => decide (geoOwner hP T x = q)) ↔
      traversalBetween (geoMarkPosition hP a) (geoMarkPosition hP m)
        (geoMarkPosition hP b) ∧ geoOwner hP T m = q := by
  simp only [List.mem_filter, decide_eq_true_eq,
    geoMarkList_rotate_left_iff hP k a b A B hrot m]

theorem geoMarkList_filter_right_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (T : Finset (Crossing P)) (q : GeoComponent hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k = a :: (A ++ b :: B)) (m : Mark P) :
    m ∈ B.filter (fun x => decide (geoOwner hP T x = q)) ↔
      traversalBetween (geoMarkPosition hP b) (geoMarkPosition hP m)
        (geoMarkPosition hP a) ∧ geoOwner hP T m = q := by
  simp only [List.mem_filter, decide_eq_true_eq,
    geoMarkList_rotate_right_iff hP k a b A B hrot m]

/-- Actual independence puts another selected twin pair wholly into one
literal original split-list arc. This connects physical noninterlacement to
list membership, without replacing original arcs by current components. -/
theorem geoIndependent_twin_same_slice {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k =
      Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A ∧ Sum.inr (visitTwin w) ∈ A) ∨
      (Sum.inr w ∈ B ∧ Sum.inr (visitTwin w) ∈ B) := by
  rcases geoIndependent_twin_one_open_arc hP hS v w hvS hwS hvw with ha | hb
  · exact Or.inl
      ⟨(geoMarkList_rotate_left_iff hP k _ _ A B hrot _).mpr ha.1,
        (geoMarkList_rotate_left_iff hP k _ _ A B hrot _).mpr ha.2⟩
  · exact Or.inr
      ⟨(geoMarkList_rotate_right_iff hP k _ _ A B hrot _).mpr hb.1,
        (geoMarkList_rotate_right_iff hP k _ _ A B hrot _).mpr hb.2⟩

/-- When the other selected pair currently has geoOwner q, the proved original
same-arc property puts both visits in one geoOwner-filtered arc. The current-geoOwner
equalities remain explicit inputs for the later simultaneous induction. -/
theorem geoIndependent_twin_same_filtered_slice {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1)
    (T : Finset (Crossing P)) (q : GeoComponent hP T)
    (hqw : geoOwner hP T (Sum.inr w) = q)
    (hqt : geoOwner hP T (Sum.inr (visitTwin w)) = q)
    (k : ℕ) (A B : List (Mark P))
    (hrot : (geoMarkList hP).rotate k =
      Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) :
    (Sum.inr w ∈ A.filter (fun x => decide (geoOwner hP T x = q)) ∧
      Sum.inr (visitTwin w) ∈ A.filter (fun x => decide (geoOwner hP T x = q))) ∨
    (Sum.inr w ∈ B.filter (fun x => decide (geoOwner hP T x = q)) ∧
      Sum.inr (visitTwin w) ∈ B.filter (fun x => decide (geoOwner hP T x = q))) := by
  simpa only [List.mem_filter, hqw, hqt, decide_true, and_true] using
    geoIndependent_twin_same_slice hP hS v w hvS hwS hvw k A B hrot


/-! ### Port of SM/CarrierPendingPairs.lean -/

/-- Every selected crossing still awaiting processing has both actual visits
in one current successor component. This invariant refers to current owners. -/
def GeoPendingPairsTogether {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S T : Finset (Crossing P)) : Prop :=
  ∀ w : Visit P, w.1 ∈ S → w.1 ∉ T →
    geoOwner hP T (Sum.inr w) = geoOwner hP T (Sum.inr (visitTwin w))

/-- Before any reconnection all marks lie in the single original component,
so every pending pair lies together, without an independence assumption. -/
theorem geoPendingPairsTogether_empty {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    GeoPendingPairsTogether hP S ∅ := by
  intro w _ _
  exact (geoComponent_empty_subsingleton hP).elim _ _

/-- Inserting a fresh selected crossing preserves current-geoOwner equality for
every other pending selected pair. An unaffected geoOwner block is unchanged.
Inside the affected block, independence puts the pair in one actual physical
arc, and the checked filtered child classification gives one new geoOwner. -/
theorem geoPendingPairsTogether_insert {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (hPending : GeoPendingPairsTogether hP S T)
    (v : Visit P) (hvS : v.1 ∈ S) (hv : v.1 ∉ T) :
    GeoPendingPairsTogether hP S (insert v.1 T) := by
  intro w hwS hw
  have hwT : w.1 ∉ T := fun hwT => hw (Finset.mem_insert_of_mem hwT)
  have hvw : v.1 ≠ w.1 := by
    intro he
    apply hw
    rw [← he]
    exact Finset.mem_insert_self _ _
  have hc := hPending v hvS hv
  have hwt := hPending w hwS hwT
  by_cases hq : geoOwner hP T (Sum.inr w) = geoOwner hP T (Sum.inr v)
  · obtain ⟨k, A, B, hrot, hNLeft, hNRight, hdisjoint,
      hleft, hright, hactLeft, hactRight⟩ :=
      geoSmoothingSuccessor_insert_child_data hP T hI v hv hc
    have hqt : geoOwner hP T (Sum.inr (visitTwin w)) =
        geoOwner hP T (Sum.inr v) := hwt.symm.trans hq
    rcases geoIndependent_twin_same_filtered_slice hP hS v w hvS hwS hvw
      T (geoOwner hP T (Sum.inr v)) hq hqt k A B hrot with ha | hb
    · exact ((hright (Sum.inr w)).mpr
        (List.mem_cons_of_mem _ ha.1)).trans
        ((hright (Sum.inr (visitTwin w))).mpr
          (List.mem_cons_of_mem _ ha.2)).symm
    · exact ((hleft (Sum.inr w)).mpr
        (List.mem_cons_of_mem _ hb.1)).trans
        ((hleft (Sum.inr (visitTwin w))).mpr
          (List.mem_cons_of_mem _ hb.2)).symm
  · exact ((geoOwner_insert_iff_of_unaffected hP T v hv hc
      (geoOwner hP T (Sum.inr w)) hq (Sum.inr w) rfl
      (Sum.inr (visitTwin w))).mpr hwt.symm).symm


/-! ### Port of SM/CarrierIndependentOrder.lean -/

/-- Process any subset of an actual independent support. The induction maintains
both inherited cyclic order and co-location of every unprocessed actual twin pair. -/
theorem geoIndependent_partial_invariants {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) :
    GeoInheritsMarkOrder hP T ∧ GeoPendingPairsTogether hP S T := by
  revert hTS
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨geoInheritsMarkOrder_empty hP, geoPendingPairsTogether_empty hP S⟩
  | @insert c T hc ih =>
    intro hTS
    have hcS : c ∈ S := hTS (Finset.mem_insert_self c T)
    have hTS' : T ⊆ S := fun z hz => hTS (Finset.mem_insert_of_mem hz)
    obtain ⟨hI, hPending⟩ := ih hTS'
    obtain ⟨i, j, hij⟩ := crossing_visits_exist c
    let v : Visit P := ⟨c, i⟩
    have hvS : v.1 ∈ S := hcS
    have hv : v.1 ∉ T := hc
    have hsame := hPending v hvS hv
    exact ⟨geoInheritsMarkOrder_insert hP T hI v hv hsame,
      geoPendingPairsTogether_insert hP hS T hI hPending v hvS hv⟩

/-- Every actual independent support inherits the original marked cyclic order.
All current-order and same-component induction premises have been discharged. -/
theorem geoIndependent_inheritsMarkOrder {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    GeoInheritsMarkOrder hP S :=
  (geoIndependent_partial_invariants hP hS S (Finset.Subset.refl S)).1

/-- For any partially processed independent support, every remaining actual
crossing still has both visits on a single actual current component. -/
theorem geoIndependent_remaining_pair_owners {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) (v : Visit P)
    (hvS : v.1 ∈ S) (hv : v.1 ∉ T) :
    geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)) :=
  (geoIndependent_partial_invariants hP hS T hTS).2 v hvS hv

/-- The two incoming visits of every selected actual crossing have distinct
final owners. Process all other selected crossings first, then use the exact
actual final split; the support permutation is already independent of order. -/
theorem geoIndependent_selected_pair_owners_ne {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (v : Visit P) (hvS : v.1 ∈ S) :
    geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) := by
  let T := S.erase v.1
  have hTS : T ⊆ S := Finset.erase_subset _ _
  have hv : v.1 ∉ T := by simp [T]
  obtain ⟨hI, hPending⟩ := geoIndependent_partial_invariants hP hS T hTS
  have hc := hPending v hvS hv
  obtain ⟨k, A, B, hrot, hNL, hNR, hd, hleft, hright, hactL, hactR⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI v hv hc
  have hne : geoOwner hP (insert v.1 T) (Sum.inr v) ≠
      geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
    intro he
    have hbL := (hleft (Sum.inr (visitTwin v))).mp he.symm
    exact hd hbL List.mem_cons_self
  have hins : insert v.1 T = S := Finset.insert_erase hvS
  exact Eq.mp (congrArg (fun U : Finset (Crossing P) =>
    geoOwner hP U (Sum.inr v) ≠ geoOwner hP U (Sum.inr (visitTwin v))) hins) hne


/-! ### Port of SM/CarrierComponentCount.lean -/

/-- A fresh reconnection whose actual incoming marks share one current component
increases the actual successor-orbit quotient count by exactly one. The count
comes from the proved literal fibers of the constructed quotient forget map. -/
theorem geoComponent_card_insert {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) :
    Fintype.card (GeoComponent hP (insert v.1 T)) =
      Fintype.card (GeoComponent hP T) + 1 := by
  refine fintype_card_eq_add_one_of_fiber_cards
    (geoComponentForgetSwitch hP T v hv ((geoOwner_eq_iff hP T _ _).mp hc))
    (geoOwner hP T (Sum.inr v)) ?_ ?_
  · obtain ⟨hne, hfiber⟩ := geoComponentForgetSwitch_fiber_affected hP T hI v hv hc
    exact (congrArg Finset.card hfiber).trans (Finset.card_pair hne)
  · intro q hq
    obtain ⟨m, hm⟩ := geoOwner_surjective hP T q
    exact (congrArg Finset.card
      (geoComponentForgetSwitch_fiber_unaffected hP T v hv hc q hq m hm)).trans
        (Finset.card_singleton _)

/-- Every processed subset of an actual independent support has one more
successor-orbit component than processed crossings. Current-order and geoOwner
premises for the count step are supplied by the checked simultaneous induction. -/
theorem geoComponent_card_independent_partial {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) :
    Fintype.card (GeoComponent hP T) = T.card + 1 := by
  revert hTS
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.card_empty, Nat.zero_add] using geoComponent_card_empty hP
  | @insert c T hc ih =>
    intro hTS
    have hcS : c ∈ S := hTS (Finset.mem_insert_self c T)
    have hTS' : T ⊆ S := fun z hz => hTS (Finset.mem_insert_of_mem hz)
    obtain ⟨hI, hPending⟩ := geoIndependent_partial_invariants hP hS T hTS'
    obtain ⟨i, j, hij⟩ := crossing_visits_exist c
    let v : Visit P := ⟨c, i⟩
    have hvS : v.1 ∈ S := hcS
    have hv : v.1 ∉ T := hc
    have hsame := hPending v hvS hv
    have hstep := geoComponent_card_insert hP T hI v hv hsame
    change Fintype.card (GeoComponent hP (insert c T)) =
      Fintype.card (GeoComponent hP T) + 1 at hstep
    rw [hstep, ih hTS', Finset.card_insert_of_notMem hc]

/-- An actual independent support has exactly its cardinality plus one actual
successor-orbit components. Empty support and singleton components are included. -/
theorem geoComponent_card_independent {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    Fintype.card (GeoComponent hP S) = S.card + 1 :=
  geoComponent_card_independent_partial hP hS S (Finset.Subset.refl S)

/-- The finite successor model satisfies all three combinatorial conclusions:
exact count, inherited marked order and separation of every selected twin pair.
Geometric realization of these orbit components remains a separate obligation. -/
theorem geoIndependent_successor_components {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    Fintype.card (GeoComponent hP S) = S.card + 1 ∧
      GeoInheritsMarkOrder hP S ∧
      ∀ v : Visit P, v.1 ∈ S →
        geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) :=
  ⟨geoComponent_card_independent hP hS, geoIndependent_inheritsMarkOrder hP hS,
    fun v hv => geoIndependent_selected_pair_owners_ne hP hS v hv⟩


/-! ### Port of SM/CarrierTrueCorners.lean -/

-- [port] `IsTrueCorner` -> accepted `Carrier.IsTrueCorner` (hypothesis-free, shared); not re-declared

-- [port] `isTrueCorner_vertex` -> accepted `Carrier.isTrueCorner_vertex` (hypothesis-free, shared); not re-declared

-- [port] `isTrueCorner_visit` -> accepted `Carrier.isTrueCorner_visit` (hypothesis-free, shared); not re-declared

-- [port] `component_has_trueCorner` -> accepted `geoComponent_has_trueCorner` (SM/FlatCarriers*.lean); not re-declared

/-- The actual inherited component cycle restricted to precisely its true
corners. Geometric compression and source regularity are separate theorems. -/
def geoComponentCornerCycle {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) : Cycle (Mark P) :=
  (geoComponentCycle hP S q).filter (fun a => decide (IsTrueCorner S a))

/-- A literal representative retains exact geoOwner and true-corner membership
in their inherited original cyclic order. -/
theorem geoComponentCornerCycle_eq_filtered_markList {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    geoComponentCornerCycle hP S q =
      (((geoMarkList hP).filter (fun a => decide (geoOwner hP S a = q))).filter
        (fun a => decide (IsTrueCorner S a)) : Cycle (Mark P)) := rfl

@[simp]
theorem mem_geoComponentCornerCycle {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (a : Mark P) : a ∈ geoComponentCornerCycle hP S q ↔
      geoOwner hP S a = q ∧ IsTrueCorner S a := by
  simp only [geoComponentCornerCycle, Cycle.mem_filter, mem_geoComponentCycle, decide_eq_true_eq]

theorem geoComponentCornerCycle_nodup {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    (geoComponentCornerCycle hP S q).Nodup :=
  (geoComponentCycle_nodup hP S q).filter (fun a => decide (IsTrueCorner S a))

/-- The corner filter is nonempty for every actual component and every
support; corner existence is derived above rather than supplied. -/
theorem geoComponentCornerCycle_nonempty {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    ∃ a : Mark P, a ∈ geoComponentCornerCycle hP S q := by
  obtain ⟨a, ha, hc⟩ := geoComponent_has_trueCorner hP S q
  exact ⟨a, (mem_geoComponentCornerCycle hP S q a).mpr ⟨ha, hc⟩⟩


/-! ## Targets (DECISION_FINAL §5, unit U1a) -/

set_option linter.unusedVariables false in
/-- lem:carriers (i) on the geometric carrier layer: an independent set `S` of crossings has exactly
`|S| + 1` carriers (the cycles of `geoSmoothingSuccessor hP S`). `hn` is not used by the proof
(the geometric carrier definitions do not take it); it is kept in the binder list §5 prescribes. -/
theorem geoComponent_card (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) :
    Fintype.card (GeoComponent hP S) = S.card + 1 :=
  geoComponent_card_independent hP hS

/-- The two visits of a selected crossing of an independent set lie on different carriers
(conv:selected-visits: the reconnection separates them). -/
theorem geo_selected_visits_separated {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) (v : Visit P) (hv : v.1 ∈ S) :
    geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) :=
  geoIndependent_selected_pair_owners_ne hP hS v hv

/-- Every independent set inherits the cyclic order of the marked traversal circle on each carrier
(U1b's spec name for `geoIndependent_inheritsMarkOrder`). -/
theorem geoInheritsMarkOrder_of_independent {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : GeoIndependent hP S) : GeoInheritsMarkOrder hP S :=
  geoIndependent_inheritsMarkOrder hP hS

/-- Refinement of ownership: for independent `S ⊆ S'`, two marks on one carrier of `S'` lie on one
carrier of `S`. Induction on `S' \ S`: each inserted crossing has its two visits on one current
carrier (`geoIndependent_remaining_pair_owners`), so the insertion refines the carriers
(`geoOwner_insert_eq_imp`). -/
theorem geoOwner_eq_of_subset {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S S' : Finset (Crossing P)} (hS' : GeoIndependent hP S') (hSS' : S ⊆ S') (a b : Mark P)
    (hab : geoOwner hP S' a = geoOwner hP S' b) : geoOwner hP S a = geoOwner hP S b := by
  suffices key : ∀ D : Finset (Crossing P), D ⊆ S' \ S → ∀ T : Finset (Crossing P), T = S ∪ D →
      ∀ a b : Mark P, geoOwner hP T a = geoOwner hP T b → geoOwner hP S a = geoOwner hP S b from
    key (S' \ S) (Finset.Subset.refl _) S' (Finset.union_sdiff_of_subset hSS').symm a b hab
  intro D
  induction D using Finset.induction_on with
  | empty =>
    rintro _ T hT a b h
    rw [Finset.union_empty] at hT
    subst hT
    exact h
  | @insert c D hcD ih =>
    rintro hD T rfl a b h
    have hc : c ∈ S' \ S := hD (Finset.mem_insert_self c D)
    have hDsub : D ⊆ S' \ S := fun z hz => hD (Finset.mem_insert_of_mem hz)
    have hcS' : c ∈ S' := (Finset.mem_sdiff.mp hc).1
    have hcS : c ∉ S := (Finset.mem_sdiff.mp hc).2
    have hcT : c ∉ S ∪ D := by
      intro h'
      rcases Finset.mem_union.mp h' with h' | h'
      · exact hcS h'
      · exact hcD h'
    have hTS' : S ∪ D ⊆ S' := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact hSS' hz
      · exact (Finset.mem_sdiff.mp (hDsub hz)).1
    obtain ⟨i, j, hij⟩ := crossing_visits_exist c
    let v : Visit P := ⟨c, i⟩
    have hsame := geoIndependent_remaining_pair_owners hP hS' (S ∪ D) hTS' v hcS' hcT
    have hcyc := (geoOwner_eq_iff hP (S ∪ D) _ _).mp hsame
    have hT : S ∪ insert c D = insert v.1 (S ∪ D) := Finset.union_insert c S D
    have hgen : ∀ T : Finset (Crossing P), T = insert v.1 (S ∪ D) →
        geoOwner hP T a = geoOwner hP T b →
        geoOwner hP (insert v.1 (S ∪ D)) a = geoOwner hP (insert v.1 (S ∪ D)) b := by
      rintro T rfl h
      exact h
    exact ih hDsub (S ∪ D) rfl a b (geoOwner_insert_eq_imp hP (S ∪ D) v hcT hcyc (hgen _ hT h))

/-- lem:carrierword clause 3 on the geometric carrier layer: for independent `S ⊆ S'`, every carrier
of `S'` lies inside one carrier of `S` (with the induced order, `geoInheritsMarkOrder_of_independent`). -/
theorem geoOwner_refines {P : LabelledTuple n} (hP : CrossingGeometry P)
    {S S' : Finset (Crossing P)} (hS' : GeoIndependent hP S') (hSS' : S ⊆ S')
    (q' : GeoComponent hP S') :
    ∃ q : GeoComponent hP S, ∀ m, geoOwner hP S' m = q' → geoOwner hP S m = q := by
  obtain ⟨m₀, hm₀⟩ := geoOwner_surjective hP S' q'
  exact ⟨geoOwner hP S m₀, fun m hm =>
    geoOwner_eq_of_subset hP hS' hSS' m m₀ (hm.trans hm₀.symm)⟩

end
end SM.GeoCarrier
