import SM.UniformMeshCells
import SM.OrderedCoordinateLegs
import Mathlib.Topology.LocallyFinite

/-! Development prototype: genuine continuous coordinate polylines on a fixed
uniform time mesh. Outside the theorem library pending independent review. -/

namespace SM

open Set

noncomputable section

theorem exists_finite_closed_gluing {ι X Y : Type*} [Finite ι]
    [TopologicalSpace X] [TopologicalSpace Y]
    (C : ι → Set X) (hcover : ⋃ i, C i = univ) (hclosed : ∀ i, IsClosed (C i))
    (F : ι → X → Y) (hcontinuous : ∀ i, Continuous (F i))
    (hagrees : ∀ i j, ∀ x ∈ C i, x ∈ C j → F i x = F j x) :
    ∃ g : X → Y, Continuous g ∧ ∀ i, ∀ x ∈ C i, g x = F i x := by
  classical
  have hsome : ∀ x : X, ∃ i, x ∈ C i := by
    intro x
    apply mem_iUnion.mp
    rw [hcover]
    trivial
  choose index hindex using hsome
  let g : X → Y := fun x => F (index x) x
  have he : ∀ i, ∀ x ∈ C i, g x = F i x :=
    fun i x hx => hagrees (index x) i x (hindex x) hx
  refine ⟨g, ?_, he⟩
  exact (locallyFinite_of_finite C).continuous hcover hclosed
    (fun i => (hcontinuous i).continuousOn.congr (he i))

def uniformMeshLocalTime (N : ℕ) (j : Fin N) (t : unitInterval) : ℝ :=
  (N : ℝ) * (t : ℝ) - (j.val : ℝ)

theorem continuous_uniformMeshLocalTime (N : ℕ) (j : Fin N) :
    Continuous (uniformMeshLocalTime N j) :=
  (continuous_const.mul continuous_subtype_val).sub continuous_const

theorem uniformMeshLocalTime_mem_unit (N : ℕ) (hN : 0 < N)
    (j : Fin N) (t : unitInterval) (ht : t ∈ uniformMeshCell N hN j) :
    uniformMeshLocalTime N j t ∈ Icc (0 : ℝ) 1 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlo : (j.val : ℝ) / (N : ℝ) ≤ (t : ℝ) := ht.1
  have hup : (t : ℝ) ≤ ((j.val : ℝ) + 1) / (N : ℝ) := by
    have hu : (t : ℝ) ≤ (uniformMeshPoint N hN j.succ : ℝ) := ht.2
    simpa only [uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hu
  have hmullo := (div_le_iff₀ hNR).mp hlo
  have hmulhi := (le_div_iff₀ hNR).mp hup
  constructor <;> dsimp [uniformMeshLocalTime] <;> nlinarith

theorem uniformMeshLocalTime_left (N : ℕ) (hN : 0 < N) (j : Fin N) :
    uniformMeshLocalTime N j (uniformMeshPoint N hN j.castSucc) = 0 := by
  have hNR : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  simp only [uniformMeshLocalTime, uniformMeshPoint, Fin.val_castSucc]
  field_simp [hNR] <;> ring

theorem uniformMeshLocalTime_right (N : ℕ) (hN : 0 < N) (j : Fin N) :
    uniformMeshLocalTime N j (uniformMeshPoint N hN j.succ) = 1 := by
  have hNR : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  simp only [uniformMeshLocalTime, uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  field_simp [hNR] <;> ring

variable {σ : Type*} {m : ℕ}

def timedScalarBranch (order : σ ≃ Fin m) (x y : σ → ℝ) (j : Fin m)
    (t : unitInterval) : σ → ℝ :=
  orderedScalarLeg order x y j (uniformMeshLocalTime m j t)

theorem continuous_timedScalarBranch (order : σ ≃ Fin m) (x y : σ → ℝ) (j : Fin m) :
    Continuous (timedScalarBranch order x y j) :=
  (continuous_orderedScalarLeg order x y j).comp (continuous_uniformMeshLocalTime m j)

theorem timedScalarBranch_left (order : σ ≃ Fin m) (hm : 0 < m)
    (x y : σ → ℝ) (j : Fin m) :
    timedScalarBranch order x y j (uniformMeshPoint m hm j.castSucc) =
      orderedHybrid order x y j.val := by
  rw [timedScalarBranch, uniformMeshLocalTime_left, orderedScalarLeg_zero]

theorem timedScalarBranch_right (order : σ ≃ Fin m) (hm : 0 < m)
    (x y : σ → ℝ) (j : Fin m) :
    timedScalarBranch order x y j (uniformMeshPoint m hm j.succ) =
      orderedHybrid order x y (j.val + 1) := by
  rw [timedScalarBranch, uniformMeshLocalTime_right, orderedScalarLeg_one]

theorem timedScalarBranches_agree_of_lt (order : σ ≃ Fin m) (hm : 0 < m)
    (x y : σ → ℝ) (i j : Fin m) (hij : i < j) (t : unitInterval)
    (hi : t ∈ uniformMeshCell m hm i) (hj : t ∈ uniformMeshCell m hm j) :
    timedScalarBranch order x y i t = timedScalarBranch order x y j t := by
  obtain ⟨hindex, hit, hjt⟩ := uniformMeshCell_ordered_intersection m hm i j hij t hi hj
  calc
    timedScalarBranch order x y i t = orderedHybrid order x y (i.val + 1) := by
      rw [hit, timedScalarBranch_right]
    _ = orderedHybrid order x y j.val := by rw [hindex]
    _ = timedScalarBranch order x y j t := by rw [hjt, timedScalarBranch_left]

theorem exists_timedCoordinatePolyline (order : σ ≃ Fin m) (hm : 0 < m)
    (x y : σ → ℝ) :
    ∃ g : unitInterval → (σ → ℝ), Continuous g ∧
      (∀ j : Fin m, ∀ t ∈ uniformMeshCell m hm j,
        g t = timedScalarBranch order x y j t) ∧ g 0 = x ∧ g 1 = y ∧
      (∀ center : σ → ℝ, ∀ radius : ℝ, x ∈ scalarOpenBox center radius →
        y ∈ scalarOpenBox center radius → ∀ t, g t ∈ scalarOpenBox center radius) := by
  have hagree : ∀ i j : Fin m, ∀ t ∈ uniformMeshCell m hm i,
      t ∈ uniformMeshCell m hm j →
        timedScalarBranch order x y i t = timedScalarBranch order x y j t := by
    intro i j t hi hj
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact timedScalarBranches_agree_of_lt order hm x y i j hij t hi hj
    · rfl
    · exact (timedScalarBranches_agree_of_lt order hm x y j i hji t hj hi).symm
  obtain ⟨g, hg, he⟩ := exists_finite_closed_gluing (uniformMeshCell m hm)
    (iUnion_uniformMeshCell m hm) (isClosed_uniformMeshCell m hm)
    (timedScalarBranch order x y) (continuous_timedScalarBranch order x y) hagree
  refine ⟨g, hg, he, ?_, ?_, ?_⟩
  · let j : Fin m := ⟨0, hm⟩
    have hj : uniformMeshPoint m hm j.castSucc = 0 := uniformMeshPoint_first m hm
    rw [← hj, he j _ (uniformMeshCell_left_mem m hm j), timedScalarBranch_left]
    exact orderedHybrid_zero order x y
  · let j : Fin m := ⟨m - 1, by omega⟩
    have hi : j.val + 1 = m := by dsimp [j]; omega
    have hj : uniformMeshPoint m hm j.succ = 1 := by
      have hidx : j.succ = (⟨m, by omega⟩ : Fin (m + 1)) := Fin.ext hi
      rw [hidx, uniformMeshPoint_last]
    rw [← hj, he j _ (uniformMeshCell_right_mem m hm j), timedScalarBranch_right, hi]
    exact orderedHybrid_last order x y
  · intro center radius hx hy t
    obtain ⟨j, hj⟩ := exists_uniformMeshCell m hm t
    rw [he j t hj]
    exact orderedScalarLeg_mem_box order center x y radius hx hy j
      (uniformMeshLocalTime m j t) (uniformMeshLocalTime_mem_unit m hm j t hj)

end

end SM

#print axioms SM.exists_finite_closed_gluing
#print axioms SM.uniformMeshLocalTime_mem_unit
#print axioms SM.timedScalarBranches_agree_of_lt
#print axioms SM.exists_timedCoordinatePolyline
