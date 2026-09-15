import SM.CentralRootGerms
import SM.CubeWaypoints
import SM.CentralLegFiniteRoots
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


namespace SM

open Set

noncomputable section

variable {σ : Type*} {N m : ℕ}

/- The fine mesh has exactly m coordinate legs per coarse cell. Division and
remainder retain the actual coarse-cell and moving-coordinate labels. -/
def multiScalarBranch (order : σ ≃ Fin m) (v : Fin (N + 1) → σ → ℝ)
    (k : Fin (N * m)) (t : unitInterval) : σ → ℝ :=
  orderedScalarLeg order (v k.divNat.castSucc) (v k.divNat.succ) k.modNat
    (uniformMeshLocalTime (N * m) k t)

theorem continuous_multiScalarBranch (order : σ ≃ Fin m)
    (v : Fin (N + 1) → σ → ℝ) (k : Fin (N * m)) :
    Continuous (multiScalarBranch order v k) :=
  (continuous_orderedScalarLeg order _ _ _).comp
    (continuous_uniformMeshLocalTime (N * m) k)

theorem multiScalarBranch_left (order : σ ≃ Fin m) (hN : 0 < N) (hm : 0 < m)
    (v : Fin (N + 1) → σ → ℝ) (k : Fin (N * m)) :
    multiScalarBranch order v k (uniformMeshPoint (N * m) (Nat.mul_pos hN hm) k.castSucc) =
      orderedHybrid order (v k.divNat.castSucc) (v k.divNat.succ) k.modNat.val := by
  rw [multiScalarBranch, uniformMeshLocalTime_left, orderedScalarLeg_zero]

theorem multiScalarBranch_right (order : σ ≃ Fin m) (hN : 0 < N) (hm : 0 < m)
    (v : Fin (N + 1) → σ → ℝ) (k : Fin (N * m)) :
    multiScalarBranch order v k (uniformMeshPoint (N * m) (Nat.mul_pos hN hm) k.succ) =
      orderedHybrid order (v k.divNat.castSucc) (v k.divNat.succ) (k.modNat.val + 1) := by
  rw [multiScalarBranch, uniformMeshLocalTime_right, orderedScalarLeg_one]

theorem quotient_remainder_successor (a m : ℕ) (hm : 0 < m) :
    (a % m + 1 < m ∧ (a + 1) / m = a / m ∧ (a + 1) % m = a % m + 1) ∨
    (a % m + 1 = m ∧ (a + 1) / m = a / m + 1 ∧ (a + 1) % m = 0) := by
  have hd := Nat.div_add_mod a m
  have hd' := Nat.div_add_mod (a + 1) m
  have hr := Nat.mod_lt a hm
  by_cases hnext : a % m + 1 < m
  · have hq : (a + 1) / m = a / m :=
      Nat.div_eq_of_lt_le (by
        calc
          a / m * m = m * (a / m) := Nat.mul_comm _ _
          _ ≤ m * (a / m) + a % m := Nat.le_add_right _ _
          _ = a := hd
          _ ≤ a + 1 := Nat.le_succ a) (by
        calc
          a + 1 = m * (a / m) + (a % m + 1) := by omega
          _ < m * (a / m) + m := Nat.add_lt_add_left hnext _
          _ = (a / m + 1) * m := by ring)
    rw [hq] at hd'
    exact Or.inl ⟨hnext, hq, by omega⟩
  · have hc : a % m + 1 = m := by omega
    have hq : (a + 1) / m = a / m + 1 :=
      Nat.div_eq_of_eq_mul_right hm (by nlinarith)
    rw [hq] at hd'
    exact Or.inr ⟨hc, hq, by nlinarith⟩

theorem multiScalarBranch_join (order : σ ≃ Fin m) (hm : 0 < m)
    (v : Fin (N + 1) → σ → ℝ) (k l : Fin (N * m)) (hkl : l.val = k.val + 1) :
    orderedHybrid order (v k.divNat.castSucc) (v k.divNat.succ) (k.modNat.val + 1) =
      orderedHybrid order (v l.divNat.castSucc) (v l.divNat.succ) l.modNat.val := by
  rcases quotient_remainder_successor k.val m hm with ⟨_, hq, hr⟩ | ⟨hc, hq, hr⟩
  · have hdiv : l.divNat = k.divNat := Fin.ext (by change l.val / m = k.val / m; simpa only [hkl] using hq)
    have hmod : l.modNat.val = k.modNat.val + 1 := by
      change l.val % m = k.val % m + 1
      simpa only [hkl] using hr
    rw [hdiv, hmod]
  · have hlast : k.modNat.val + 1 = m := hc
    have hfirst : l.modNat.val = 0 := by
      change l.val % m = 0
      simpa only [hkl] using hr
    have hjoin : l.divNat.castSucc = k.divNat.succ :=
      Fin.ext (by change l.val / m = k.val / m + 1; simpa only [hkl] using hq)
    rw [hlast, hfirst, orderedHybrid_last, orderedHybrid_zero, hjoin]

theorem fine_uniformMeshCell_subset_coarse (hN : 0 < N) (hm : 0 < m)
    (k : Fin (N * m)) :
    uniformMeshCell (N * m) (Nat.mul_pos hN hm) k ⊆
      uniformMeshCell N hN k.divNat := by
  intro t ht
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hNM : (0 : ℝ) < (N * m : ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hN hm)
  have hlo : (k.val : ℝ) / (N * m : ℕ) ≤ (t : ℝ) := ht.1
  have hup : (t : ℝ) ≤ ((k.val : ℝ) + 1) / (N * m : ℕ) := by
    have hu : (t : ℝ) ≤ (uniformMeshPoint (N * m) (Nat.mul_pos hN hm) k.succ : ℝ) := ht.2
    simpa only [uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hu
  have hmullo := (div_le_iff₀ hNM).mp hlo
  have hmulhi := (le_div_iff₀ hNM).mp hup
  rw [Nat.cast_mul] at hmullo hmulhi
  have hd : (m : ℝ) * (k.divNat.val : ℝ) + (k.modNat.val : ℝ) = (k.val : ℝ) := by
    exact_mod_cast Nat.div_add_mod k.val m
  have hr : (k.modNat.val : ℝ) + 1 ≤ (m : ℝ) := by
    exact_mod_cast k.modNat.isLt
  have hr0 : (0 : ℝ) ≤ (k.modNat.val : ℝ) := Nat.cast_nonneg _
  have hlow : (k.divNat.val : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
    apply (mul_le_mul_iff_right₀ hmR).mp
    nlinarith
  have hhigh : (N : ℝ) * (t : ℝ) ≤ (k.divNat.val : ℝ) + 1 := by
    apply (mul_le_mul_iff_right₀ hmR).mp
    nlinarith
  constructor
  · change (k.divNat.val : ℝ) / (N : ℝ) ≤ (t : ℝ)
    exact (div_le_iff₀ hNR).mpr (by nlinarith)
  · change (t : ℝ) ≤ (uniformMeshPoint N hN k.divNat.succ : ℝ)
    simp only [uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    exact (le_div_iff₀ hNR).mpr (by nlinarith)

theorem exists_multiCellCoordinatePolyline (order : σ ≃ Fin m)
    (hN : 0 < N) (hm : 0 < m) (v : Fin (N + 1) → σ → ℝ) :
    ∃ g : unitInterval → (σ → ℝ), Continuous g ∧
      (∀ k : Fin (N * m), ∀ t ∈ uniformMeshCell (N * m) (Nat.mul_pos hN hm) k,
        g t = multiScalarBranch order v k t) ∧
      g 0 = v ⟨0, by omega⟩ ∧ g 1 = v ⟨N, by omega⟩ := by
  let hNM := Nat.mul_pos hN hm
  have hagree_lt : ∀ k l : Fin (N * m), k < l →
      ∀ t ∈ uniformMeshCell (N * m) hNM k,
      t ∈ uniformMeshCell (N * m) hNM l →
        multiScalarBranch order v k t = multiScalarBranch order v l t := by
    intro k l hkl t hk hl
    obtain ⟨hindex, hkt, hlt⟩ := uniformMeshCell_ordered_intersection _ hNM k l hkl t hk hl
    calc
      multiScalarBranch order v k t =
          orderedHybrid order (v k.divNat.castSucc) (v k.divNat.succ) (k.modNat.val + 1) := by
        rw [hkt, multiScalarBranch_right order hN hm]
      _ = orderedHybrid order (v l.divNat.castSucc) (v l.divNat.succ) l.modNat.val :=
        multiScalarBranch_join order hm v k l hindex
      _ = multiScalarBranch order v l t := by rw [hlt, multiScalarBranch_left order hN hm]
  have hagree : ∀ k l : Fin (N * m), ∀ t ∈ uniformMeshCell (N * m) hNM k,
      t ∈ uniformMeshCell (N * m) hNM l →
        multiScalarBranch order v k t = multiScalarBranch order v l t := by
    intro k l t hk hl
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact hagree_lt k l hkl t hk hl
    · rfl
    · exact (hagree_lt l k hlk t hl hk).symm
  obtain ⟨g, hg, he⟩ := exists_finite_closed_gluing (uniformMeshCell (N * m) hNM)
    (iUnion_uniformMeshCell _ hNM) (isClosed_uniformMeshCell _ hNM)
    (multiScalarBranch order v) (continuous_multiScalarBranch order v) hagree
  refine ⟨g, hg, he, ?_, ?_⟩
  · let k : Fin (N * m) := ⟨0, hNM⟩
    have hk : uniformMeshPoint _ hNM k.castSucc = 0 := uniformMeshPoint_first _ hNM
    rw [← hk, he k _ (uniformMeshCell_left_mem _ hNM k), multiScalarBranch_left order hN hm]
    have hr : k.modNat.val = 0 := by simp [k, Fin.modNat]
    have hq : k.divNat.castSucc = (⟨0, by omega⟩ : Fin (N + 1)) :=
      Fin.ext (by simp [k, Fin.divNat])
    rw [hr, orderedHybrid_zero, hq]
  · let k : Fin (N * m) := ⟨N * m - 1, by omega⟩
    have hlast : k.val + 1 = N * m := by dsimp [k]; omega
    have hk : uniformMeshPoint _ hNM k.succ = 1 := by
      rw [show k.succ = (⟨N * m, by omega⟩ : Fin (N * m + 1)) from Fin.ext hlast]
      exact uniformMeshPoint_last _ hNM
    have hd := Nat.div_add_mod k.val m
    have hq : k.divNat.val + 1 = N := by
      have hqbound := k.divNat.isLt
      have hrbound := k.modNat.isLt
      change k.val / m < N at hqbound
      change k.val % m < m at hrbound
      change k.val / m + 1 = N
      nlinarith
    have hr : k.modNat.val + 1 = m := by
      change k.val / m + 1 = N at hq
      change k.val % m + 1 = m
      nlinarith
    have hqi : k.divNat.succ = (⟨N, by omega⟩ : Fin (N + 1)) := Fin.ext hq
    rw [← hk, he k _ (uniformMeshCell_right_mem _ hNM k), multiScalarBranch_right order hN hm,
      hr, orderedHybrid_last, hqi]

theorem multiScalarBranch_affine (order : σ ≃ Fin m)
    (v : Fin (N + 1) → σ → ℝ) (k : Fin (N * m)) :
    ∃ a b : σ → ℝ, ∀ t : unitInterval,
      multiScalarBranch order v k t = fun z => a z + (t : ℝ) * b z := by
  let x := orderedHybrid order (v k.divNat.castSucc) (v k.divNat.succ) k.modNat.val
  let y := orderedHybrid order (v k.divNat.castSucc) (v k.divNat.succ) (k.modNat.val + 1)
  refine ⟨(fun z => x z - (k.val : ℝ) * (y z - x z)),
    (fun z => (N * m : ℕ) * (y z - x z)), ?_⟩
  intro t
  funext z
  dsimp [multiScalarBranch, orderedScalarLeg, scalarAssignmentLine, uniformMeshLocalTime, x, y]
  ring

namespace CurveCubeSubdivision

variable {n : ℕ} {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  (d : CurveCubeSubdivision γ δ)

/- This structure records only the constructed approximation. The finite-root,
wall-type and ambient-smoothness conclusions of thm:relgp still need proofs. -/
structure CubeCoordinateApproximation [NeZero n]
    (W : d.InternalWaypoint × ScalarCoordinate n → ℝ) where
  path : unitInterval → LabelledTuple n
  continuous : Continuous path
  first : path 0 = γ 0
  last : path 1 = γ 1
  branch : ∀ k : Fin (d.count * (2 * n)),
    ∀ t ∈ uniformMeshCell (d.count * (2 * n))
        (Nat.mul_pos d.count_pos (by have := NeZero.pos n; omega)) k,
      scalarCoordinates (path t) = multiScalarBranch (scalarCoordinateOrder n)
        (fun j => scalarCoordinates (d.waypoint W j)) k t
  regular : ∀ t, Regular (path t)
  close : ∀ t, dist (tupleCoordinates (path t)) (tupleCoordinates (γ t)) < δ
  affine_on_cells : ∀ k : Fin (d.count * (2 * n)),
    ∃ a b : ScalarCoordinate n → ℝ,
      ∀ t ∈ uniformMeshCell (d.count * (2 * n))
          (Nat.mul_pos d.count_pos (by have := NeZero.pos n; omega)) k,
        scalarCoordinates (path t) = fun z => a z + (t : ℝ) * b z
  generic_collar_cells : ∀ k : Fin (d.count * (2 * n)),
    (k.divNat.val = 0 ∨ k.divNat.val + 1 = d.count) →
      ∀ t ∈ uniformMeshCell (d.count * (2 * n))
          (Nat.mul_pos d.count_pos (by have := NeZero.pos n; omega)) k,
        Generic (path t)

theorem nonempty_cubeCoordinateApproximation [NeZero n]
    (W : d.InternalWaypoint × ScalarCoordinate n → ℝ)
    (hW : ∀ k, tupleOfScalarCoordinates (waypointProjection k W) ∈ d.overlap k) :
    Nonempty (d.CubeCoordinateApproximation W) := by
  have hm : 0 < 2 * n := by have := NeZero.pos n; omega
  let hNM := Nat.mul_pos d.count_pos hm
  let v := fun j => scalarCoordinates (d.waypoint W j)
  obtain ⟨g, hg, he, hfirst, hlast⟩ := exists_multiCellCoordinatePolyline
    (scalarCoordinateOrder n) d.count_pos hm v
  let p := fun t => tupleOfScalarCoordinates (g t)
  have hscalar : ∀ t, scalarCoordinates (p t) = g t := fun t => scalarCoordinates_tupleOf _
  have hbranch : ∀ k : Fin (d.count * (2 * n)),
      ∀ t ∈ uniformMeshCell _ hNM k,
        p t = tupleOfScalarCoordinates (orderedScalarLeg (scalarCoordinateOrder n)
          (v k.divNat.castSucc) (v k.divNat.succ) k.modNat
          (uniformMeshLocalTime _ k t)) := by
    intro k t ht
    dsimp [p]
    rw [he k t ht]
    rfl
  have hcube : ∀ k : Fin (d.count * (2 * n)),
      ∀ t ∈ uniformMeshCell _ hNM k, p t ∈ d.cube k.divNat := by
    intro k t ht
    rw [hbranch k t ht]
    exact d.ordered_tuple_leg_mem_cube W hW k.divNat k.modNat _
      (uniformMeshLocalTime_mem_unit _ hNM k t ht)
  refine ⟨{
    path := p
    continuous := continuous_tupleOfScalarCoordinates.comp hg
    first := ?_
    last := ?_
    branch := ?_
    regular := ?_
    close := ?_
    affine_on_cells := ?_
    generic_collar_cells := ?_ }⟩
  · dsimp [p]
    rw [hfirst]
    dsimp [v]
    rw [tupleOf_scalarCoordinates]
    exact d.waypoint_first W
  · dsimp [p]
    rw [hlast]
    dsimp [v]
    rw [tupleOf_scalarCoordinates, d.waypoint_last]
  · intro k t ht
    rw [hscalar t]
    exact he k t ht
  · intro t
    obtain ⟨k, hk⟩ := exists_uniformMeshCell _ hNM t
    exact d.closure_regular k.divNat (subset_closure (hcube k t hk))
  · intro t
    obtain ⟨k, hk⟩ := exists_uniformMeshCell _ hNM t
    have hcoarse := fine_uniformMeshCell_subset_coarse d.count_pos hm k hk
    exact d.pairwise_dist_lt k.divNat (p t) (hcube k t hk) (γ t)
      (d.curve_mem_cube k.divNat t hcoarse)
  · intro k
    obtain ⟨a, b, hab⟩ := multiScalarBranch_affine (scalarCoordinateOrder n) v k
    refine ⟨a, b, ?_⟩
    intro t ht
    rw [hscalar t, he k t ht, hab t]
  · intro k hk t ht
    exact d.endpoint_generic k.divNat hk (subset_closure (hcube k t ht))

namespace CubeCoordinateApproximation

variable [NeZero n] {d} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
  (A : d.CubeCoordinateApproximation W)

theorem central_branch (hn : 3 ≤ n) (k : Fin (d.count * (2 * n)))
    (hk : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count)
    (t : unitInterval) (ht : t ∈ uniformMeshCell (d.count * (2 * n))
      (Nat.mul_pos d.count_pos (by omega)) k) :
    A.path t = tupleOfScalarCoordinates
      ((d.centralLeg hn (⟨k.divNat, hk⟩, k.modNat)).assignment W
        (uniformMeshLocalTime _ k t)) := by
  calc
    A.path t = tupleOfScalarCoordinates (scalarCoordinates (A.path t)) :=
      (tupleOf_scalarCoordinates _).symm
    _ = tupleOfScalarCoordinates (multiScalarBranch (scalarCoordinateOrder n)
        (fun j => scalarCoordinates (d.waypoint W j)) k t) :=
      congrArg tupleOfScalarCoordinates (A.branch k t ht)
    _ = _ := congrArg tupleOfScalarCoordinates
      (d.central_orderedLeg_eq_assignment hn W ⟨k.divNat, hk⟩ k.modNat _)

theorem collision_free (hn : 3 ≤ n)
    (hJ : ∀ j, JointLegConditions (d.centralLeg hn j) W) (t : unitInterval) :
    Function.Injective (A.path t) := by
  have hm : 0 < 2 * n := by omega
  obtain ⟨k, hk⟩ := exists_uniformMeshCell _ (Nat.mul_pos d.count_pos hm) t
  by_cases hend : k.divNat.val = 0 ∨ k.divNat.val + 1 = d.count
  · exact g1_vertices_injective hn (A.generic_collar_cells k hend t hk).1
  · have hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count := by
      have := k.divNat.isLt
      omega
    rw [A.central_branch hn k hc t hk]
    exact central_leg_collision_free _ W (hJ (⟨k.divNat, hc⟩, k.modNat)) _

theorem finite_nongeneric (hn : 3 ≤ n)
    (hJ : ∀ j, JointLegConditions (d.centralLeg hn j) W) :
    {t : unitInterval | ¬ Generic (A.path t)}.Finite := by
  have hm : 0 < 2 * n := by omega
  let hNM := Nat.mul_pos d.count_pos hm
  let S := fun k : Fin (d.count * (2 * n)) =>
    {t : unitInterval | t ∈ uniformMeshCell _ hNM k ∧ ¬ Generic (A.path t)}
  have hS : ∀ k, (S k).Finite := by
    intro k
    by_cases hend : k.divNat.val = 0 ∨ k.divNat.val + 1 = d.count
    · have he : S k = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact ht.2 (A.generic_collar_cells k hend t ht.1)
      rw [he]
      exact finite_empty
    · have hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count := by
        have := k.divNat.isLt
        omega
      let leg := d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)
      have hlocal := finite_central_nongeneric hn leg W (hJ (⟨k.divNat, hc⟩, k.modNat))
      have hinj : Function.Injective (uniformMeshLocalTime (d.count * (2 * n)) k) := by
        intro s t h
        apply Subtype.ext
        have hpos : (0 : ℝ) < (d.count * (2 * n) : ℕ) := Nat.cast_pos.mpr hNM
        dsimp [uniformMeshLocalTime] at h
        nlinarith
      apply (hlocal.preimage hinj.injOn).subset
      intro t ht
      change ¬ Generic (tupleOfScalarCoordinates (leg.assignment W
        (uniformMeshLocalTime _ k t)))
      rw [← A.central_branch hn k hc t ht.1]
      exact ht.2
  apply (Set.finite_iUnion hS).subset
  intro t ht
  obtain ⟨k, hk⟩ := exists_uniformMeshCell _ hNM t
  exact mem_iUnion.mpr ⟨k, hk, ht⟩

end CubeCoordinateApproximation

theorem exists_joint_cubeCoordinateApproximation [NeZero n] (hn : 3 ≤ n) :
    ∃ W : d.InternalWaypoint × ScalarCoordinate n → ℝ,
      ∃ A : d.CubeCoordinateApproximation W,
        (∀ j, JointLegConditions (d.centralLeg hn j) W) ∧
        (∀ t, Function.Injective (A.path t)) ∧
        {t : unitInterval | ¬ Generic (A.path t)}.Finite := by
  obtain ⟨W, hW, hJ⟩ := d.exists_joint_central_waypoints hn
  obtain ⟨A⟩ := d.nonempty_cubeCoordinateApproximation W hW
  exact ⟨W, A, hJ, A.collision_free hn hJ, A.finite_nongeneric hn hJ⟩

end CurveCubeSubdivision

end

end SM


namespace SM

open Set

noncomputable section

theorem uniformMeshLocalTime_mem_unit_iff (N : ℕ) (hN : 0 < N)
    (k : Fin N) (t : unitInterval) :
    uniformMeshLocalTime N k t ∈ Icc (0 : ℝ) 1 ↔ t ∈ uniformMeshCell N hN k := by
  constructor
  · intro ht
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    dsimp [uniformMeshLocalTime] at ht
    constructor
    · change (k.val : ℝ) / (N : ℝ) ≤ (t : ℝ)
      exact (div_le_iff₀ hNR).mpr (by nlinarith [ht.1])
    · change (t : ℝ) ≤ (uniformMeshPoint N hN k.succ : ℝ)
      simp only [uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      exact (le_div_iff₀ hNR).mpr (by nlinarith [ht.2])
  · exact uniformMeshLocalTime_mem_unit N hN k t

namespace CurveCubeSubdivision.CubeCoordinateApproximation

variable {n : ℕ} [NeZero n] {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
  (A : d.CubeCoordinateApproximation W)

theorem generic_endpoint_collar :
    ∃ ε > 0, ∀ t : unitInterval,
      ((t : ℝ) < ε ∨ 1 - ε < (t : ℝ)) → Generic (A.path t) := by
  have hm : 0 < 2 * n := by have := NeZero.pos n; omega
  have hNR : (0 : ℝ) < d.count := Nat.cast_pos.mpr d.count_pos
  refine ⟨1 / (d.count : ℝ), one_div_pos.mpr hNR, ?_⟩
  intro t ht
  obtain ⟨k, hk⟩ := exists_uniformMeshCell _ (Nat.mul_pos d.count_pos hm) t
  have hc := fine_uniformMeshCell_subset_coarse d.count_pos hm k hk
  have hlo : (k.divNat.val : ℝ) / (d.count : ℝ) ≤ (t : ℝ) := hc.1
  have hup : (t : ℝ) ≤ ((k.divNat.val : ℝ) + 1) / (d.count : ℝ) := by
    have hu : (t : ℝ) ≤ (uniformMeshPoint d.count d.count_pos k.divNat.succ : ℝ) := hc.2
    simpa only [uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hu
  apply A.generic_collar_cells k _ t hk
  rcases ht with hfirst | hlast
  · have hqR : (k.divNat.val : ℝ) < 1 :=
      (div_lt_div_iff_of_pos_right hNR).mp (hlo.trans_lt hfirst)
    have hqN : k.divNat.val < 1 := by exact_mod_cast hqR
    exact Or.inl (by omega)
  · have hmul := mul_lt_mul_of_pos_left hlast hNR
    have hupper := (le_div_iff₀ hNR).mp hup
    have hcancel : (d.count : ℝ) * (1 / (d.count : ℝ)) = 1 :=
      mul_one_div_cancel (ne_of_gt hNR)
    have hqR : (d.count : ℝ) < (k.divNat.val : ℝ) + 2 := by nlinarith
    have hqN : d.count < k.divNat.val + 2 := by exact_mod_cast hqR
    have := k.divNat.isLt
    exact Or.inr (by omega)

theorem nongeneric_central_time (hn : 3 ≤ n)
    (hJ : ∀ j, JointLegConditions (d.centralLeg hn j) W)
    (k : Fin (d.count * (2 * n))) (t : unitInterval)
    (ht : t ∈ uniformMeshCell _ (Nat.mul_pos d.count_pos (by omega)) k)
    (hng : ¬ Generic (A.path t)) :
    ∃ hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count,
      uniformMeshLocalTime _ k t ∈ Ioo (0 : ℝ) 1 ∧
      uniformMeshLocalTime _ k t ∈
        centralControlRootSet (d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)) W := by
  have hnotend : ¬ (k.divNat.val = 0 ∨ k.divNat.val + 1 = d.count) :=
    fun he => hng (A.generic_collar_cells k he t ht)
  have hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count := by
    have := k.divNat.isLt
    omega
  let leg := d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)
  have hng' : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W
      (uniformMeshLocalTime _ k t))) := by
    rw [← A.central_branch hn k hc t ht]
    exact hng
  have hr := central_nongeneric_subset_roots hn leg W hng'
  have hzero : uniformMeshLocalTime _ k t ≠ 0 := by
    intro hz
    rw [hz] at hr
    exact central_root_zero_excluded leg W (hJ _) hr
  have hone : uniformMeshLocalTime _ k t ≠ 1 := by
    intro ho
    rw [ho] at hr
    exact central_root_one_excluded leg W (hJ _) hr
  have hclosed := uniformMeshLocalTime_mem_unit _ (Nat.mul_pos d.count_pos (by omega)) k t ht
  exact ⟨hc, ⟨lt_of_le_of_ne hclosed.1 hzero.symm, lt_of_le_of_ne hclosed.2 hone⟩, hr⟩

end CurveCubeSubdivision.CubeCoordinateApproximation

end

end SM

namespace SM

open Set MvPolynomial

noncomputable section

namespace CentralRootPatch

variable {κ : Type*} {n : ℕ}
  {leg : CoordinateWaypointLeg κ (ScalarCoordinate n)}
  {W : κ × ScalarCoordinate n → ℝ} {name : PolynomialControlName n} {r : ℝ}
  (patch : CentralRootPatch leg W name r) (a : ℝ) (ha : 0 < a)

include ha in
theorem scaled_parameter_mem (s : Ioo (-(patch.radius / a)) (patch.radius / a)) :
    a * s.val ∈ Ioo (-patch.radius) patch.radius := by
  have hupper := (lt_div_iff₀ ha).mp s.property.2
  have hlower : -s.val < patch.radius / a := by linarith [s.property.1]
  have hneg := (lt_div_iff₀ ha).mp hlower
  constructor <;> nlinarith

def scaledToWallGerm
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) : WallGerm n where
  radius := patch.radius / a
  radius_pos := div_pos patch.radius_pos ha
  curve := fun s => tupleOfScalarCoordinates (leg.assignment W (r + a * s.val))
  continuous_curve := (continuous_central_tuple_leg leg W).comp
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
  generic_punctured := by
    intro s hs
    apply patch.generic_punctured (r + a * s.val)
    · simpa only [add_sub_cancel_left] using abs_lt.mpr (patch.scaled_parameter_mem a ha s)
    · intro he
      apply mul_ne_zero (ne_of_gt ha) hs
      linarith
  nongeneric_center := by simpa only [mul_zero, add_zero] using hng

@[simp] theorem scaledToWallGerm_center
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    (patch.scaledToWallGerm a ha hng).center = tupleOfScalarCoordinates (leg.assignment W r) := by
  simp only [WallGerm.center, WallGerm.zeroParameter, scaledToWallGerm, mul_zero, add_zero]

theorem scaled_time_mem_leg
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)))
    (s : (patch.scaledToWallGerm a ha hng).Parameter) :
    r + a * s.val ∈ Ioo (0 : ℝ) 1 :=
  patch.time_mem_leg _ (patch.scaled_parameter_mem a ha s)

theorem scaledToWallGerm_signChanges (h : JointLegConditions leg W)
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r))) :
    (patch.scaledToWallGerm a ha hng).SignChanges
      (fun P => eval (scalarCoordinates P) (namedControlPolynomial name)) := by
  refine ⟨patch.radius / a, div_pos patch.radius_pos ha, le_rfl, ?_⟩
  intro s _
  have hs : 0 < a * s.val := mul_pos ha s.property.1
  have hp := central_control_crossing_product leg W h name r (r - a * s.val) (r + a * s.val)
    patch.parameter_isRoot (by linarith) (by linarith)
  change eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + a * s.val))))
      (namedControlPolynomial name) *
    eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + a * -s.val))))
      (namedControlPolynomial name) < 0
  simpa only [scalarCoordinates_tupleOf, mul_neg, sub_eq_add_neg, mul_comm] using hp

theorem scaledToWallGerm_other_products
    (hng : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)))
    (s : (patch.scaledToWallGerm a ha hng).Parameter)
    (other : PolynomialControlName n) (hne : other ≠ name) :
    0 < eval (scalarCoordinates ((patch.scaledToWallGerm a ha hng).curve s))
        (namedControlPolynomial other) *
      eval (scalarCoordinates (patch.scaledToWallGerm a ha hng).center)
        (namedControlPolynomial other) := by
  rw [patch.scaledToWallGerm_center a ha hng]
  change 0 < eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W (r + a * s.val))))
      (namedControlPolynomial other) *
    eval (scalarCoordinates (tupleOfScalarCoordinates (leg.assignment W r)))
      (namedControlPolynomial other)
  simp only [scalarCoordinates_tupleOf]
  apply patch.other_products _ _ other hne
  simpa only [add_sub_cancel_left] using abs_lt.mpr (patch.scaled_parameter_mem a ha s)

theorem scaled_control_hasDerivAt :
    HasDerivAt (fun s : ℝ => eval (leg.assignment W (r + a * s)) (namedControlPolynomial name))
      (leg.parameterSlope W (namedControlPolynomial name) * a) 0 := by
  have ht : HasDerivAt (fun s : ℝ => r + a * s) a 0 := by
    simpa only [mul_one] using ((hasDerivAt_id' (0 : ℝ)).const_mul a).const_add r
  have hc := (central_control_hasDerivAt leg W name (r + a * 0)).comp 0 ht
  simpa only [Function.comp_def] using hc

end CentralRootPatch

theorem uniformMesh_shift_mem_unit (N : ℕ) (hN : 0 < N) (k : Fin N)
    (t : unitInterval) (s : ℝ)
    (hloc : uniformMeshLocalTime N k t + (N : ℝ) * s ∈ Ioo (0 : ℝ) 1) :
    (t : ℝ) + s ∈ Icc (0 : ℝ) 1 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk0 : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hk1 : (k.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast k.isLt
  dsimp [uniformMeshLocalTime] at hloc
  have hlo : (0 : ℝ) * (N : ℝ) < ((t : ℝ) + s) * (N : ℝ) := by nlinarith [hloc.1]
  have hhi : ((t : ℝ) + s) * (N : ℝ) < 1 * (N : ℝ) := by nlinarith [hloc.2]
  have hleft : (0 : ℝ) < (t : ℝ) + s :=
    (mul_lt_mul_iff_right₀ hNR).mp (by nlinarith [hlo])
  have hright : (t : ℝ) + s < 1 :=
    (mul_lt_mul_iff_right₀ hNR).mp (by nlinarith [hhi])
  exact ⟨hleft.le, hright.le⟩

namespace CurveCubeSubdivision.CubeCoordinateApproximation

variable {n : ℕ} [NeZero n] {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
  (A : d.CubeCoordinateApproximation W)

theorem nongeneric_has_timed_wallGerm (hn : 3 ≤ n)
    (hJ : ∀ j, JointLegConditions (d.centralLeg hn j) W)
    (t : unitInterval) (hng : ¬ Generic (A.path t)) :
    ∃ k : Fin (d.count * (2 * n)),
      ∃ hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count,
        ∃ name : PolynomialControlName n, ∃ g : WallGerm n,
          g.center = A.path t ∧
          (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
            g.curve s = A.path ⟨(t : ℝ) + s.val, hs⟩) ∧
          (∀ s : g.Parameter, Regular (g.curve s) ∧ Function.Injective (g.curve s)) ∧
          g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial name)) ∧
          (∀ s : g.Parameter, ∀ other : PolynomialControlName n, other ≠ name →
            0 < eval (scalarCoordinates (g.curve s)) (namedControlPolynomial other) *
              eval (scalarCoordinates g.center) (namedControlPolynomial other)) ∧
          (∃ slope : ℝ, slope ≠ 0 ∧ HasDerivAt
            (fun s : ℝ => eval
              ((d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)).assignment W
                (uniformMeshLocalTime _ k t + (d.count * (2 * n) : ℕ) * s))
              (namedControlPolynomial name)) slope 0) := by
  have hm : 0 < 2 * n := by omega
  let hNM := Nat.mul_pos d.count_pos hm
  let a : ℝ := (d.count * (2 * n) : ℕ)
  have ha : 0 < a := Nat.cast_pos.mpr hNM
  obtain ⟨k, ht⟩ := exists_uniformMeshCell _ hNM t
  obtain ⟨hc, hrange, hr⟩ := A.nongeneric_central_time hn hJ k t ht hng
  let leg := d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)
  let r := uniformMeshLocalTime _ k t
  obtain ⟨name, hroot⟩ := hr
  let patch := chooseCentralRootPatch hn leg W (hJ _) name r hrange hroot
  have hng' : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W r)) := by
    rw [← A.central_branch hn k hc t ht]
    exact hng
  let g := patch.scaledToWallGerm a ha hng'
  have hcurve : ∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      g.curve s = A.path ⟨(t : ℝ) + s.val, hs⟩ := by
    intro s
    have hloc := patch.scaled_time_mem_leg a ha hng' s
    have hs := uniformMesh_shift_mem_unit _ hNM k t s.val hloc
    let u : unitInterval := ⟨(t : ℝ) + s.val, hs⟩
    have he : uniformMeshLocalTime _ k u = r + a * s.val := by
      dsimp [uniformMeshLocalTime, u, r, a]
      ring
    have hu : u ∈ uniformMeshCell _ hNM k := by
      apply (uniformMeshLocalTime_mem_unit_iff _ hNM k u).mp
      rw [he]
      exact ⟨hloc.1.le, hloc.2.le⟩
    refine ⟨hs, ?_⟩
    change tupleOfScalarCoordinates (leg.assignment W (r + a * s.val)) = A.path u
    rw [A.central_branch hn k hc u hu, he]
  refine ⟨k, hc, name, g, ?_, hcurve, ?_, patch.scaledToWallGerm_signChanges a ha (hJ _) hng',
    patch.scaledToWallGerm_other_products a ha hng', ?_⟩
  · rw [patch.scaledToWallGerm_center a ha hng']
    exact (A.central_branch hn k hc t ht).symm
  · intro s
    obtain ⟨hs, he⟩ := hcurve s
    rw [he]
    exact ⟨A.regular _, A.collision_free hn hJ _⟩
  · refine ⟨leg.parameterSlope W (namedControlPolynomial name) * a,
      mul_ne_zero (patch.parameterSlope_ne_zero (hJ _)) (ne_of_gt ha), ?_⟩
    exact CentralRootPatch.scaled_control_hasDerivAt a

end CurveCubeSubdivision.CubeCoordinateApproximation

end

end SM

#print axioms SM.uniformMeshLocalTime_mem_unit_iff
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.generic_endpoint_collar
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.nongeneric_central_time
#print axioms SM.CentralRootPatch.scaledToWallGerm_signChanges
#print axioms SM.CentralRootPatch.scaledToWallGerm_other_products
#print axioms SM.CentralRootPatch.scaled_control_hasDerivAt
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.nongeneric_has_timed_wallGerm
