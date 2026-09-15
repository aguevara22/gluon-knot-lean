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


set_option pp.universes false
#check SM.exists_finite_closed_gluing
#print axioms SM.exists_finite_closed_gluing
#check SM.uniformMeshLocalTime
#print axioms SM.uniformMeshLocalTime
#check SM.continuous_uniformMeshLocalTime
#print axioms SM.continuous_uniformMeshLocalTime
#check SM.uniformMeshLocalTime_mem_unit
#print axioms SM.uniformMeshLocalTime_mem_unit
#check SM.uniformMeshLocalTime_left
#print axioms SM.uniformMeshLocalTime_left
#check SM.uniformMeshLocalTime_right
#print axioms SM.uniformMeshLocalTime_right
#check SM.timedScalarBranch
#print axioms SM.timedScalarBranch
#check SM.continuous_timedScalarBranch
#print axioms SM.continuous_timedScalarBranch
#check SM.timedScalarBranch_left
#print axioms SM.timedScalarBranch_left
#check SM.timedScalarBranch_right
#print axioms SM.timedScalarBranch_right
#check SM.timedScalarBranches_agree_of_lt
#print axioms SM.timedScalarBranches_agree_of_lt
#check SM.exists_timedCoordinatePolyline
#print axioms SM.exists_timedCoordinatePolyline
#check SM.multiScalarBranch
#print axioms SM.multiScalarBranch
#check SM.continuous_multiScalarBranch
#print axioms SM.continuous_multiScalarBranch
#check SM.multiScalarBranch_left
#print axioms SM.multiScalarBranch_left
#check SM.multiScalarBranch_right
#print axioms SM.multiScalarBranch_right
#check SM.quotient_remainder_successor
#print axioms SM.quotient_remainder_successor
#check SM.multiScalarBranch_join
#print axioms SM.multiScalarBranch_join
#check SM.fine_uniformMeshCell_subset_coarse
#print axioms SM.fine_uniformMeshCell_subset_coarse
#check SM.exists_multiCellCoordinatePolyline
#print axioms SM.exists_multiCellCoordinatePolyline
#check SM.multiScalarBranch_affine
#print axioms SM.multiScalarBranch_affine
#print SM.CurveCubeSubdivision.CubeCoordinateApproximation
#check SM.CurveCubeSubdivision.nonempty_cubeCoordinateApproximation
#print axioms SM.CurveCubeSubdivision.nonempty_cubeCoordinateApproximation
#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.central_branch
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.central_branch
#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.collision_free
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.collision_free
#check SM.CurveCubeSubdivision.CubeCoordinateApproximation.finite_nongeneric
#print axioms SM.CurveCubeSubdivision.CubeCoordinateApproximation.finite_nongeneric
#check SM.CurveCubeSubdivision.exists_joint_cubeCoordinateApproximation
#print axioms SM.CurveCubeSubdivision.exists_joint_cubeCoordinateApproximation
#print SM.multiScalarBranch

open Set

-- Raw original curve hypotheses construct d, one W and the actual A.
-- NeZero is derived here, not imposed as an extra source premise.
example {n : ℕ} (hn : 3 ≤ n)
    (gamma : unitInterval → SM.LabelledTuple n) (hgamma : Continuous gamma)
    (hregular : ∀ t, SM.Regular (gamma t))
    (hfirst : SM.Generic (gamma 0)) (hlast : SM.Generic (gamma 1))
    (delta : ℝ) (hdelta : 0 < delta) :
    letI : NeZero n := ⟨by omega⟩
    ∃ d : SM.CurveCubeSubdivision gamma delta,
      ∃ W : d.InternalWaypoint × SM.ScalarCoordinate n → ℝ,
      ∃ A : d.CubeCoordinateApproximation W,
        (∀ j, SM.JointLegConditions (d.centralLeg hn j) W) ∧
        Continuous A.path ∧ A.path 0 = gamma 0 ∧ A.path 1 = gamma 1 ∧
        (∀ t, SM.Regular (A.path t)) ∧
        (∀ t, dist (SM.tupleCoordinates (A.path t)) (SM.tupleCoordinates (gamma t)) < delta) ∧
        (∀ t, Function.Injective (A.path t)) ∧
        {t : unitInterval | ¬ SM.Generic (A.path t)}.Finite ∧
        (∀ k : Fin (d.count * (2*n)), ∃ a b : SM.ScalarCoordinate n → ℝ,
          ∀ t ∈ SM.uniformMeshCell (d.count * (2*n)) (Nat.mul_pos d.count_pos (by omega)) k,
            SM.scalarCoordinates (A.path t) = fun z => a z + (t : ℝ) * b z) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨d⟩ := SM.nonempty_curveCubeSubdivision hn gamma hgamma hregular hfirst hlast delta hdelta
  obtain ⟨W, A, hJ, hc, hf⟩ := d.exists_joint_cubeCoordinateApproximation hn
  exact ⟨d, W, A, hJ, A.continuous, A.first, A.last, A.regular, A.close, hc, hf,
    A.affine_on_cells⟩

-- The carry at a coarse-cell boundary advances exactly one waypoint and
-- resets the moving-coordinate index, including the source n=3 case m=6.
example : (5 : ℕ) % 6 + 1 = 6 ∧ (5 + 1) / 6 = 5 / 6 + 1 ∧ (5 + 1) % 6 = 0 := by
  decide
