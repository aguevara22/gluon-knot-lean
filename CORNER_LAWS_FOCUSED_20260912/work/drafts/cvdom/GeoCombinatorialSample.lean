import SM.FlatCarriers

/-! CV-DOM prototype (analyst A, 2026-09-14): MECHANICAL port of two combinatorial lane modules
(SM/CarrierSingleSwitch.lean, SM/CarrierUnchangedComponent.lean) to the accepted geometric layer by
`port_lane.py` (pure renaming: `hn hP` -> `hP : CrossingGeometry P`, lane names -> `geo*`). The only
hand-written addition is the port of `smoothingSuccessor_union_of_disjoint` (CarrierSmoothing.lean),
which the geo layer did not have. Checked with `cd work/lean && lake env lean ../drafts/cvdom/GeoCombinatorialSample.lean`. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace SM.GeoCarrier
open Carrier
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Port of `smoothingSuccessor_union_of_disjoint` (SM/CarrierSmoothing.lean). -/
theorem geoSmoothingSuccessor_union_of_disjoint {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S T : Finset (Crossing P)) (hST : Disjoint S T) :
    geoSmoothingSuccessor hP (S ∪ T) =
      (selectedMarkPerm T).trans (geoSmoothingSuccessor hP S) := by
  rw [geoSmoothingSuccessor, selectedMarkPerm_union_of_disjoint S T hST]
  rfl

end
end SM.GeoCarrier

namespace SM.GeoCarrier
open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- On the actual two-visit fiber, selecting this crossing is exactly the
transposition of its constructed pair; all other crossing fibers are fixed. -/
theorem geo_selectedVisitTwin_singleton {P : LabelledTuple n} (v w : Visit P) :
    selectedVisitTwin {v.1} w = Equiv.swap v (visitTwin v) w := by
  by_cases hc : w.1 = v.1
  · rcases visit_eq_or_twin v w hc with hw | hw
    · subst w
      simp [selectedVisitTwin]
    · subst w
      simp [selectedVisitTwin]
  · have hwv : w ≠ v := fun h => hc (congrArg (fun x : Visit P => x.1) h)
    have hwt : w ≠ visitTwin v := by
      intro h
      apply hc
      rw [h, visitTwin_crossing]
    rw [Equiv.swap_apply_of_ne_of_ne hwv hwt]
    simp [selectedVisitTwin, hc]

theorem geo_selectedVisitTwinPerm_singleton {P : LabelledTuple n} (v : Visit P) :
    selectedVisitTwinPerm {v.1} = Equiv.swap v (visitTwin v) := by
  apply Equiv.ext
  intro w
  exact geo_selectedVisitTwin_singleton v w

/-- The full marked permutation fixes original vertices and exchanges exactly
the two distinct actual marks of this crossing. -/
theorem geo_selectedMarkPerm_singleton {P : LabelledTuple n} (v : Visit P) :
    selectedMarkPerm {v.1} =
      Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  rw [selectedMarkPerm, geo_selectedVisitTwinPerm_singleton]
  exact Equiv.Perm.sumCongr_refl_swap v (visitTwin v)

/-- Adding an unselected actual crossing swaps its two outgoing slots in the
current successor. Right multiplication applies that transposition first. -/
theorem geoSmoothingSuccessor_insert {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    geoSmoothingSuccessor hP (insert v.1 S) =
      geoSmoothingSuccessor hP S *
        Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  have hS : insert v.1 S = S ∪ {v.1} := by
    ext c
    simp [or_comm]
  rw [hS, geoSmoothingSuccessor_union_of_disjoint hP S {v.1}
    (Finset.disjoint_singleton_right.mpr hv), geo_selectedMarkPerm_singleton]
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

end
end SM.GeoCarrier

namespace SM.GeoCarrier
open Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual forward successor stays in its incoming owner block for every
support, without independence or inherited-order assumptions. -/
theorem geoSmoothingSuccessor_mapsTo_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T) :
    Set.MapsTo (geoSmoothingSuccessor hP T)
      {m | geoOwner hP T m = q} {m | geoOwner hP T m = q} := by
  intro m hm
  exact (geoOwner_successor hP T m).trans hm

/-- The inverse actual successor also stays in the same owner block. -/
theorem geoSmoothingSuccessor_symm_mapsTo_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (q : GeoComponent hP T) :
    Set.MapsTo (geoSmoothingSuccessor hP T).symm
      {m | geoOwner hP T m = q} {m | geoOwner hP T m = q} := by
  intro m hm
  exact (geoOwner_predecessor hP T m).trans hm

-- [port] `geoSmoothingSuccessor_bijOn_owner` -> accepted `geoSmoothingSuccessor_bijOn_owner` (SM/FlatCarriers*.lean); not re-declared

/-- If a fresh actual crossing's two incoming marks share an old owner, its
insertion changes no outgoing slot in any other actual old owner block. -/
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

/-- The new actual successor is bijective on every unaffected old owner block,
since its action there agrees with the proved old block bijection. -/
theorem geoSmoothingSuccessor_insert_bijOn_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v)))
    (q : GeoComponent hP T) (hq : q ≠ geoOwner hP T (Sum.inr v)) :
    Set.BijOn (geoSmoothingSuccessor hP (insert v.1 T))
      {m | geoOwner hP T m = q} {m | geoOwner hP T m = q} :=
  (geoSmoothingSuccessor_insert_eqOn_owner hP T v hv hc q hq).bijOn_iff.mpr
    (geoSmoothingSuccessor_bijOn_owner hP T q)

/-- Backward traversal on an unaffected old owner block is unchanged as well.
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

end
end SM.GeoCarrier
