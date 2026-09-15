import SM.TimedCoordinatePolyline
import SM.CubeWaypoints
import SM.CentralLegFiniteRoots

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
