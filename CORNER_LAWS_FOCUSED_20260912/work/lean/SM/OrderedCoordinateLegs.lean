import SM.ScalarBoxes
import SM.CentralLegCollision
import Mathlib.Data.Fintype.EquivFin

/-! A fixed finite order of actual scalar coordinates and the corresponding
coordinate legs. Endpoint collars use arbitrary fixed endpoint vectors. For
central legs the same construction equals the proved joint-waypoint assignment. -/

namespace SM

open Set

noncomputable section

variable {κ σ : Type*} {m n : ℕ}

def scalarCoordinateOrder (n : ℕ) [NeZero n] : ScalarCoordinate n ≃ Fin (2 * n) :=
  Fintype.equivFinOfCardEq (by simp [ScalarCoordinate, Fintype.card_prod, ZMod.card,
    Nat.mul_comm])

def orderedHybrid (order : σ ≃ Fin m) (x y : σ → ℝ) (k : ℕ) : σ → ℝ :=
  fun z => if (order z).val < k then y z else x z

theorem orderedHybrid_zero (order : σ ≃ Fin m) (x y : σ → ℝ) :
    orderedHybrid order x y 0 = x := by
  funext z
  simp [orderedHybrid]

theorem orderedHybrid_last (order : σ ≃ Fin m) (x y : σ → ℝ) :
    orderedHybrid order x y m = y := by
  funext z
  simp [orderedHybrid, (order z).isLt]

theorem orderedHybrid_mem_box (order : σ ≃ Fin m) (center x y : σ → ℝ)
    (radius : ℝ) (hx : x ∈ scalarOpenBox center radius)
    (hy : y ∈ scalarOpenBox center radius) (k : ℕ) :
    orderedHybrid order x y k ∈ scalarOpenBox center radius := by
  apply scalarOpenBox_mem_of_coordinates center x y _ radius hx hy
  intro z
  by_cases hz : (order z).val < k
  · exact Or.inr (if_pos hz)
  · exact Or.inl (if_neg hz)

def orderedScalarLeg (order : σ ≃ Fin m) (x y : σ → ℝ) (j : Fin m) (t : ℝ) : σ → ℝ :=
  scalarAssignmentLine (orderedHybrid order x y j.val)
    (orderedHybrid order x y (j.val + 1)) t

theorem orderedScalarLeg_zero (order : σ ≃ Fin m) (x y : σ → ℝ) (j : Fin m) :
    orderedScalarLeg order x y j 0 = orderedHybrid order x y j.val := by
  funext z
  simp [orderedScalarLeg, scalarAssignmentLine]

theorem orderedScalarLeg_one (order : σ ≃ Fin m) (x y : σ → ℝ) (j : Fin m) :
    orderedScalarLeg order x y j 1 = orderedHybrid order x y (j.val + 1) := by
  funext z
  simp [orderedScalarLeg, scalarAssignmentLine]

theorem orderedScalarLeg_join (order : σ ≃ Fin m) (x y : σ → ℝ)
    (j : Fin m) (hj : j.val + 1 < m) :
    orderedScalarLeg order x y j 1 =
      orderedScalarLeg order x y ⟨j.val + 1, hj⟩ 0 := by
  rw [orderedScalarLeg_one, orderedScalarLeg_zero]

theorem orderedScalarLeg_start (order : σ ≃ Fin m) (x y : σ → ℝ) (hm : 0 < m) :
    orderedScalarLeg order x y ⟨0, hm⟩ 0 = x := by
  rw [orderedScalarLeg_zero]
  exact orderedHybrid_zero order x y

theorem orderedScalarLeg_finish (order : σ ≃ Fin m) (x y : σ → ℝ)
    (j : Fin m) (hj : j.val + 1 = m) : orderedScalarLeg order x y j 1 = y := by
  rw [orderedScalarLeg_one, hj, orderedHybrid_last]

theorem continuous_orderedScalarLeg (order : σ ≃ Fin m) (x y : σ → ℝ) (j : Fin m) :
    Continuous (orderedScalarLeg order x y j) := continuous_scalarAssignmentLine _ _

theorem orderedScalarLeg_mem_box (order : σ ≃ Fin m) (center x y : σ → ℝ)
    (radius : ℝ) (hx : x ∈ scalarOpenBox center radius)
    (hy : y ∈ scalarOpenBox center radius) (j : Fin m) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : orderedScalarLeg order x y j t ∈ scalarOpenBox center radius :=
  scalarAssignmentLine_mem_box center _ _ radius t
    (orderedHybrid_mem_box order center x y radius hx hy j.val)
    (orderedHybrid_mem_box order center x y radius hx hy (j.val + 1)) ht

def orderedWaypointLeg (order : σ ≃ Fin m) (left right : κ) (hne : left ≠ right)
    (j : Fin m) : CoordinateWaypointLeg κ σ where
  left := left
  right := right
  left_ne_right := hne
  moving := order.symm j
  switched := {z | (order z).val < j.val}
  moving_not_switched := by simp

theorem orderedWaypointLeg_endpoint_false (order : σ ≃ Fin m)
    (left right : κ) (hne : left ≠ right) (j : Fin m) (W : κ × σ → ℝ) :
    (orderedWaypointLeg order left right hne j).endpoint false W =
      orderedHybrid order (fun z => W (left, z)) (fun z => W (right, z)) j.val := by
  classical
  funext z
  by_cases hz : order z < j <;>
    simp [CoordinateWaypointLeg.endpoint, waypointHybrid, waypointSelection,
      CoordinateWaypointLeg.beforeTag, orderedWaypointLeg, orderedHybrid, hz]

theorem orderedWaypointLeg_endpoint_true (order : σ ≃ Fin m)
    (left right : κ) (hne : left ≠ right) (j : Fin m) (W : κ × σ → ℝ) :
    (orderedWaypointLeg order left right hne j).endpoint true W =
      orderedHybrid order (fun z => W (left, z)) (fun z => W (right, z)) (j.val + 1) := by
  classical
  funext z
  by_cases hmove : z = order.symm j
  · subst z
    simp [CoordinateWaypointLeg.endpoint, waypointHybrid, waypointSelection,
      CoordinateWaypointLeg.afterTag, orderedWaypointLeg, orderedHybrid]
  · have hindex : (order z).val ≠ j.val := by
      intro he
      apply hmove
      apply order.injective
      exact (Fin.ext he).trans (order.apply_symm_apply j).symm
    by_cases hbefore : (order z).val < j.val
    · have hafter : (order z).val < j.val + 1 := by omega
      have hbefore' : order z < j := hbefore
      simp [CoordinateWaypointLeg.endpoint, waypointHybrid, waypointSelection,
        CoordinateWaypointLeg.afterTag, CoordinateWaypointLeg.beforeTag,
        orderedWaypointLeg, orderedHybrid, hmove, hbefore, hbefore', hafter]
    · have hafter : ¬ (order z).val < j.val + 1 := by omega
      have hbefore' : ¬ order z < j := hbefore
      simp [CoordinateWaypointLeg.endpoint, waypointHybrid, waypointSelection,
        CoordinateWaypointLeg.afterTag, CoordinateWaypointLeg.beforeTag,
        orderedWaypointLeg, orderedHybrid, hmove, hbefore, hbefore', hafter]

theorem orderedWaypointLeg_assignment (order : σ ≃ Fin m)
    (left right : κ) (hne : left ≠ right) (j : Fin m) (W : κ × σ → ℝ) (t : ℝ) :
    (orderedWaypointLeg order left right hne j).assignment W t =
      orderedScalarLeg order (fun z => W (left, z)) (fun z => W (right, z)) j t := by
  rw [CoordinateWaypointLeg.assignment_eq_line, orderedWaypointLeg_endpoint_false,
    orderedWaypointLeg_endpoint_true]
  rfl

end

end SM
