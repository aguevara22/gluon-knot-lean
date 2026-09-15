import SM.CubeWaypointDomains

/-! Fixed original labelled endpoints and the chosen independent internal
waypoints form one actual sequence. Every pair of successive endpoints lies
in its assigned cube, so all ordered coordinate legs lie there as well. -/

namespace SM.CurveCubeSubdivision

open Set

noncomputable section

variable {n : ℕ} {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  (d : CurveCubeSubdivision γ δ)

def waypoint (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (j : Fin (d.count + 1)) : LabelledTuple n := by
  classical
  exact if hzero : j.val = 0 then γ 0 else
    if hend : j.val = d.count then γ 1 else
      tupleOfScalarCoordinates (waypointProjection
        (⟨j.val - 1, by have := j.isLt; omega⟩ : d.InternalWaypoint) W)

theorem waypoint_first (W : d.InternalWaypoint × ScalarCoordinate n → ℝ) :
    d.waypoint W ⟨0, by omega⟩ = γ 0 := by
  simp [waypoint]

theorem waypoint_last (W : d.InternalWaypoint × ScalarCoordinate n → ℝ) :
    d.waypoint W ⟨d.count, by omega⟩ = γ 1 := by
  simp [waypoint, ne_of_gt d.count_pos]

theorem waypoint_of_internal (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (j : Fin (d.count + 1)) (hzero : 0 < j.val) (hend : j.val < d.count) :
    d.waypoint W j = tupleOfScalarCoordinates (waypointProjection
      (⟨j.val - 1, by omega⟩ : d.InternalWaypoint) W) := by
  simp [waypoint, ne_of_gt hzero, ne_of_lt hend]

theorem waypoint_left_mem_cube (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (hW : ∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k)
    (i : Fin d.count) : d.waypoint W i.castSucc ∈ d.cube i := by
  by_cases hi : i.val = 0
  · have he : i.castSucc = (⟨0, by omega⟩ : Fin (d.count + 1)) := Fin.ext hi
    rw [he, d.waypoint_first]
    have htime : d.time i.castSucc = 0 := by
      rw [he]
      exact uniformMeshPoint_first d.count d.count_pos
    have hg := d.curve_mem_cube i (d.time i.castSucc)
      (uniformMeshCell_left_mem d.count d.count_pos i)
    rwa [htime] at hg
  · have hpos : 0 < i.val := by omega
    rw [d.waypoint_of_internal W i.castSucc hpos i.isLt]
    let k : d.InternalWaypoint := ⟨i.val - 1, by have := i.isLt; omega⟩
    have he : d.overlapRight k = i := Fin.ext (by dsimp [overlapRight, k]; omega)
    have hh := (hW k).2
    rw [he] at hh
    exact hh

theorem waypoint_right_mem_cube (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (hW : ∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k)
    (i : Fin d.count) : d.waypoint W i.succ ∈ d.cube i := by
  by_cases hi : i.val + 1 = d.count
  · have he : i.succ = (⟨d.count, by omega⟩ : Fin (d.count + 1)) := Fin.ext hi
    rw [he, d.waypoint_last]
    have htime : d.time i.succ = 1 := by
      rw [he]
      exact uniformMeshPoint_last d.count d.count_pos
    have hg := d.curve_mem_cube i (d.time i.succ)
      (uniformMeshCell_right_mem d.count d.count_pos i)
    rwa [htime] at hg
  · have hlt : i.val + 1 < d.count := by have := i.isLt; omega
    rw [d.waypoint_of_internal W i.succ (by change 0 < i.val + 1; omega) hlt]
    let k : d.InternalWaypoint := ⟨i.val, by omega⟩
    have he : d.overlapLeft k = i := Fin.ext rfl
    have hh := (hW k).1
    rw [he] at hh
    simpa only [Fin.val_succ, Nat.add_sub_cancel] using hh

theorem waypoint_central_left (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (i : d.CentralCell) : d.waypoint W i.val.castSucc =
      tupleOfScalarCoordinates (waypointProjection (d.centralLeftTag i) W) :=
  d.waypoint_of_internal W i.val.castSucc i.property.1 i.val.isLt

theorem waypoint_central_right (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (i : d.CentralCell) : d.waypoint W i.val.succ =
      tupleOfScalarCoordinates (waypointProjection (d.centralRightTag i) W) := by
  have he := d.waypoint_of_internal W i.val.succ
    (by change 0 < i.val.val + 1; omega) i.property.2
  simpa only [centralRightTag, Fin.val_succ, Nat.add_sub_cancel] using he

theorem central_orderedLeg_eq_assignment [NeZero n] (hn : 3 ≤ n)
    (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (i : d.CentralCell) (j : Fin (2 * n)) (t : ℝ) :
    orderedScalarLeg (scalarCoordinateOrder n)
      (scalarCoordinates (d.waypoint W i.val.castSucc))
      (scalarCoordinates (d.waypoint W i.val.succ)) j t =
        (d.centralLeg hn (i, j)).assignment W t := by
  rw [d.waypoint_central_left, d.waypoint_central_right]
  simp only [scalarCoordinates_tupleOf]
  exact (orderedWaypointLeg_assignment (scalarCoordinateOrder n)
    (d.centralLeftTag i) (d.centralRightTag i) (d.central_tags_ne i) j W t).symm

theorem ordered_tuple_leg_mem_cube [NeZero n]
    (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (hW : ∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k)
    (i : Fin d.count) (j : Fin (2 * n)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    tupleOfScalarCoordinates (orderedScalarLeg (scalarCoordinateOrder n)
      (scalarCoordinates (d.waypoint W i.castSucc))
      (scalarCoordinates (d.waypoint W i.succ)) j t) ∈ d.cube i := by
  change scalarCoordinates (tupleOfScalarCoordinates _) ∈
    scalarOpenBox (scalarCoordinates (d.center i)) (d.radius i)
  rw [scalarCoordinates_tupleOf]
  exact orderedScalarLeg_mem_box (scalarCoordinateOrder n) _ _ _ _
    (d.waypoint_left_mem_cube W hW i) (d.waypoint_right_mem_cube W hW i) j t ht

theorem ordered_tuple_leg_regular [NeZero n]
    (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (hW : ∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k)
    (i : Fin d.count) (j : Fin (2 * n)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Regular (tupleOfScalarCoordinates (orderedScalarLeg (scalarCoordinateOrder n)
      (scalarCoordinates (d.waypoint W i.castSucc))
      (scalarCoordinates (d.waypoint W i.succ)) j t)) :=
  d.closure_regular i (subset_closure (d.ordered_tuple_leg_mem_cube W hW i j t ht))

theorem ordered_tuple_leg_generic_collar [NeZero n]
    (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (hW : ∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k)
    (i : Fin d.count) (hi : i.val = 0 ∨ i.val + 1 = d.count)
    (j : Fin (2 * n)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Generic (tupleOfScalarCoordinates (orderedScalarLeg (scalarCoordinateOrder n)
      (scalarCoordinates (d.waypoint W i.castSucc))
      (scalarCoordinates (d.waypoint W i.succ)) j t)) :=
  d.endpoint_generic i hi (subset_closure (d.ordered_tuple_leg_mem_cube W hW i j t ht))

end

end SM.CurveCubeSubdivision
