import SM.CurveCubeSubdivision
import SM.WaypointOpenDomain
import SM.OrderedCoordinateLegs

/-! Actual adjacent-cube overlaps supply the open domains for the independent
internal waypoints. The ordered central legs are indexed by actual cells and
scalar coordinates, and one joint assignment satisfies every required condition. -/

namespace SM.CurveCubeSubdivision

open Set

noncomputable section

variable {n : ℕ} {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  (d : CurveCubeSubdivision γ δ)

abbrev InternalWaypoint := Fin (d.count - 1)

def overlapLeft (k : d.InternalWaypoint) : Fin d.count :=
  ⟨k.val, by have := k.isLt; omega⟩

def overlapRight (k : d.InternalWaypoint) : Fin d.count :=
  ⟨k.val + 1, by have := k.isLt; omega⟩

def overlapTime (k : d.InternalWaypoint) : unitInterval := d.time (d.overlapLeft k).succ

def overlap (k : d.InternalWaypoint) : Set (LabelledTuple n) :=
  d.cube (d.overlapLeft k) ∩ d.cube (d.overlapRight k)

theorem overlapTime_eq_right (k : d.InternalWaypoint) :
    d.overlapTime k = d.time (d.overlapRight k).castSucc := by
  have he : (d.overlapLeft k).succ = (d.overlapRight k).castSucc := Fin.ext rfl
  exact congrArg d.time he

theorem curve_mem_overlap (k : d.InternalWaypoint) : γ (d.overlapTime k) ∈ d.overlap k := by
  constructor
  · exact d.curve_mem_cube (d.overlapLeft k) _
      (uniformMeshCell_right_mem d.count d.count_pos (d.overlapLeft k))
  · rw [d.overlapTime_eq_right k]
    exact d.curve_mem_cube (d.overlapRight k) _
      (uniformMeshCell_left_mem d.count d.count_pos (d.overlapRight k))

theorem isOpen_overlap [NeZero n] (k : d.InternalWaypoint) : IsOpen (d.overlap k) :=
  (d.isOpen_cube (d.overlapLeft k)).inter (d.isOpen_cube (d.overlapRight k))

theorem overlap_nonempty (k : d.InternalWaypoint) : (d.overlap k).Nonempty :=
  ⟨γ (d.overlapTime k), d.curve_mem_overlap k⟩

def scalarOverlap (k : d.InternalWaypoint) : Set (ScalarCoordinate n → ℝ) :=
  tupleOfScalarCoordinates ⁻¹' d.overlap k

theorem isOpen_scalarOverlap [NeZero n] (k : d.InternalWaypoint) : IsOpen (d.scalarOverlap k) :=
  (d.isOpen_overlap k).preimage continuous_tupleOfScalarCoordinates

theorem scalarOverlap_nonempty (k : d.InternalWaypoint) : (d.scalarOverlap k).Nonempty := by
  refine ⟨scalarCoordinates (γ (d.overlapTime k)), ?_⟩
  change tupleOfScalarCoordinates (scalarCoordinates (γ (d.overlapTime k))) ∈ d.overlap k
  rw [tupleOf_scalarCoordinates]
  exact d.curve_mem_overlap k

theorem exists_joint_in_overlaps (hn : 3 ≤ n) {ι : Type*} [Finite ι]
    (legs : ι → CoordinateWaypointLeg d.InternalWaypoint (ScalarCoordinate n)) :
    ∃ W : d.InternalWaypoint × ScalarCoordinate n → ℝ,
      (∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k) ∧
      ∀ i, JointLegConditions (legs i) W := by
  haveI : NeZero n := ⟨by omega⟩
  exact exists_joint_waypoint_conditions_in_domains hn legs d.scalarOverlap
    d.isOpen_scalarOverlap d.scalarOverlap_nonempty

abbrev CentralCell := {i : Fin d.count // 0 < i.val ∧ i.val + 1 < d.count}

abbrev CentralLegIndex := d.CentralCell × Fin (2 * n)

def centralLeftTag (i : d.CentralCell) : d.InternalWaypoint :=
  ⟨i.val.val - 1, by have := i.property.1; have := i.property.2; omega⟩

def centralRightTag (i : d.CentralCell) : d.InternalWaypoint :=
  ⟨i.val.val, by have := i.property.2; omega⟩

theorem central_tags_ne (i : d.CentralCell) : d.centralLeftTag i ≠ d.centralRightTag i := by
  intro he
  have hv := congrArg Fin.val he
  change i.val.val - 1 = i.val.val at hv
  have := i.property.1
  omega

def centralLeg (hn : 3 ≤ n) (j : d.CentralLegIndex) :
    CoordinateWaypointLeg d.InternalWaypoint (ScalarCoordinate n) := by
  haveI : NeZero n := ⟨by omega⟩
  exact orderedWaypointLeg (scalarCoordinateOrder n)
    (d.centralLeftTag j.1) (d.centralRightTag j.1) (d.central_tags_ne j.1) j.2

theorem exists_joint_central_waypoints (hn : 3 ≤ n) :
    ∃ W : d.InternalWaypoint × ScalarCoordinate n → ℝ,
      (∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k) ∧
      ∀ j : d.CentralLegIndex, JointLegConditions (d.centralLeg hn j) W :=
  d.exists_joint_in_overlaps hn (d.centralLeg hn)

end

end SM.CurveCubeSubdivision
