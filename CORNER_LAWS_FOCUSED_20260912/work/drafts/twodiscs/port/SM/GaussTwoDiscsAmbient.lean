-- Ported <HH:MM>Z 2026-09-19 from work/drafts/twodiscs/W2_Assembled.lean by the pod executor (files prepared by the U12 assembler)
import SM.GaussTwoDiscsEars

/-! # Row 57 lem:gauss-two-discs — units U5-U9 (the sequential chain)

U5 the ear-cut ambient homeomorphism, U6 the ambient parametrisation `AmbientParam` and 57a/57e (the two
regions), U7 57b for the interior region, U8 57b for the exterior region (cap chart, exterior fan), U9
orientation bookkeeping (`InteriorOnLeft`, `CyclicPos`, `traversalPositiveFor`).  Every leaf is proved.
Provenance: `SM.GaussTwoDiscsDefs`. -/

namespace SM

open Set OnePoint

variable {n : ℕ}

/-! ### U5 (sequential) — the ear-cut ambient homeomorphism -/

/-! ### U5 helpers (`u5h_`), 2026-09-19: the ear-cut ambient homeomorphism.  Placed here,
immediately before the U5 leaf `U5_exists_ear_homeo` that uses them.  See W2_U5_REPORT.md. -/

section U5_block
open Filter

-- ---- piece A ----
/-- barycentric form of the triangle hull relative to the vertex `a` -/
theorem u5h_mem_hull3 (a b c x : Plane) :
    x ∈ convexHull ℝ {a, b, c} ↔
      ∃ μ ν : ℝ, 0 ≤ μ ∧ 0 ≤ ν ∧ μ + ν ≤ 1 ∧ x = a + μ • (b - a) + ν • (c - a) := by
  rw [u4h_mem_hull3_iff]
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hs, rfl⟩
    refine ⟨β, γ, hβ, hγ, by linarith, ?_⟩
    have : α = 1 - β - γ := by linarith
    subst this
    ext <;> simp <;> ring
  · rintro ⟨μ, ν, hμ, hν, hs, rfl⟩
    refine ⟨1 - μ - ν, μ, ν, by linarith, hμ, hν, by ring, ?_⟩
    ext <;> simp <;> ring

theorem u5h_mem_hull3_of (a b c : Plane) {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hs : μ + ν ≤ 1) :
    a + μ • (b - a) + ν • (c - a) ∈ convexHull ℝ {a, b, c} :=
  (u5h_mem_hull3 a b c _).mpr ⟨μ, ν, hμ, hν, hs, rfl⟩

/-- `det e (· - v)` along a barycentric combination -/
theorem u5h_det_bary (e v p q r : Plane) (α β : ℝ) :
    det e (p + α • (q - p) + β • (r - p) - v) =
      (1 - α - β) * det e (p - v) + α * det e (q - v) + β * det e (r - v) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

theorem u5h_hull3_perm_231 (a b c : Plane) : convexHull ℝ {a, b, c} = convexHull ℝ {b, c, a} :=
  u4h_hull3_rot a b c

theorem u5h_hull3_perm_213 (a b c : Plane) : convexHull ℝ {a, b, c} = convexHull ℝ {b, a, c} := by
  rw [Set.insert_comm]

theorem u5h_hull3_perm_132 (a b c : Plane) : convexHull ℝ {a, b, c} = convexHull ℝ {a, c, b} := by
  rw [Set.pair_comm]

theorem u5h_hull3_perm_321 (a b c : Plane) : convexHull ℝ {a, b, c} = convexHull ℝ {c, b, a} := by
  rw [u5h_hull3_perm_231, u5h_hull3_perm_213]

/-- barycentric form relative to the third vertex -/
theorem u5h_mem_hull3_third (a b c x : Plane) :
    x ∈ convexHull ℝ {a, b, c} ↔
      ∃ μ ν : ℝ, 0 ≤ μ ∧ 0 ≤ ν ∧ μ + ν ≤ 1 ∧ x = c + μ • (a - c) + ν • (b - c) := by
  rw [u4h_hull3_rot, u4h_hull3_rot, u5h_mem_hull3]

/-- splitting a triangle along a cevian to an open-edge point -/
theorem u5h_hull_split {x y z q : Plane} (hq : q ∈ openSegment ℝ x y) :
    convexHull ℝ {x, y, z} = convexHull ℝ {x, q, z} ∪ convexHull ℝ {q, y, z} := by
  rw [openSegment_eq_image'] at hq
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hq
  apply Subset.antisymm
  · intro p hp
    rw [u5h_mem_hull3_third] at hp
    obtain ⟨μ, ν, hμ, hν, hs, rfl⟩ := hp
    -- weights: μ on x, ν on y, relative to z
    by_cases hcase : ν ≤ θ * (μ + ν)
    · left
      rw [u5h_mem_hull3_third]
      refine ⟨μ - ν * (1 - θ) / θ, ν / θ, ?_, by positivity, ?_, ?_⟩
      · rw [sub_nonneg, div_le_iff₀ hθ0]; nlinarith
      · have : μ - ν * (1 - θ) / θ + ν / θ = μ + ν := by field_simp; ring
        linarith
      · ext <;> simp <;> field_simp <;> ring
    · right
      rw [u5h_mem_hull3_third]
      have h1θ : 0 < 1 - θ := by linarith
      refine ⟨μ / (1 - θ), ν - μ * θ / (1 - θ), by positivity, ?_, ?_, ?_⟩
      · rw [sub_nonneg, div_le_iff₀ h1θ]; nlinarith
      · have : μ / (1 - θ) + (ν - μ * θ / (1 - θ)) = μ + ν := by field_simp; ring
        linarith
      · ext <;> simp <;> field_simp <;> ring
  · apply union_subset
    · apply convexHull_min _ (convex_convexHull ℝ _)
      intro w hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact subset_convexHull ℝ _ (by simp)
      · exact u4h_segment_subset_hull3 x y z ⟨1 - θ, θ, by linarith, hθ0.le, by ring, by
          ext <;> simp <;> ring⟩
      · exact subset_convexHull ℝ _ (by simp)
    · apply convexHull_min _ (convex_convexHull ℝ _)
      intro w hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact u4h_segment_subset_hull3 x y z ⟨1 - θ, θ, by linarith, hθ0.le, by ring, by
          ext <;> simp <;> ring⟩
      · exact subset_convexHull ℝ _ (by simp)
      · exact subset_convexHull ℝ _ (by simp)

-- ---- piece B ----
/-- the midpoint of the diagonal `[a, c]` -/
noncomputable def u5h_mid (a c : Plane) : Plane := (1 / 2 : ℝ) • (a + c)

/-- the apex moved along the ray from the midpoint through `b`: `m + τ • (b - m)` -/
noncomputable def u5h_apex (a b c : Plane) (τ : ℝ) : Plane := u5h_mid a c + τ • (b - u5h_mid a c)

theorem u5h_mid_comm (a c : Plane) : u5h_mid c a = u5h_mid a c := by
  simp only [u5h_mid, add_comm]

theorem u5h_apex_comm (a b c : Plane) (τ : ℝ) : u5h_apex c b a τ = u5h_apex a b c τ := by
  simp only [u5h_apex, u5h_mid_comm]

theorem u5h_apex_one (a b c : Plane) : u5h_apex a b c 1 = b := by
  simp [u5h_apex]

theorem u5h_apex_sub (a b c : Plane) (τ : ℝ) :
    u5h_apex a b c τ - a = τ • (b - a) + ((1 - τ) / 2) • (c - a) := by
  simp only [u5h_apex, u5h_mid]; ext <;> simp <;> ring

theorem u5h_apex_sub_b (a b c : Plane) (τ : ℝ) :
    u5h_apex a b c τ - b = (τ - 1) • (b - u5h_mid a c) := by
  simp only [u5h_apex, u5h_mid]; ext <;> simp <;> ring

theorem u5h_continuous_apex (a b c : Plane) : Continuous (u5h_apex a b c) := by
  unfold u5h_apex; fun_prop

/-- Cramer: the coordinates of `v` in the basis `b - a, c - a` -/
theorem u5h_basis {a b c : Plane} (hD : det (b - a) (c - a) ≠ 0) (v : Plane) :
    v = (det v (c - a) / det (b - a) (c - a)) • (b - a) +
      (det (b - a) v / det (b - a) (c - a)) • (c - a) := by
  have key : det (b - a) (c - a) • v = det v (c - a) • (b - a) + det (b - a) v • (c - a) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul, det] <;> ring
  rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← key, smul_smul,
    inv_mul_cancel₀ hD, one_smul]

theorem u5h_coords_unique {a b c : Plane} (hD : det (b - a) (c - a) ≠ 0) {A B A' B' : ℝ}
    (h : A • (b - a) + B • (c - a) = A' • (b - a) + B' • (c - a)) : A = A' ∧ B = B' := by
  have h1 : A * det (b - a) (c - a) = A' * det (b - a) (c - a) := by
    have := congrArg (fun v => det v (c - a)) h
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at this ⊢
    linear_combination this
  have h2 : B * det (b - a) (c - a) = B' * det (b - a) (c - a) := by
    have := congrArg (fun v => det (b - a) v) h
    simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at this ⊢
    linear_combination this
  exact ⟨mul_right_cancel₀ hD h1, mul_right_cancel₀ hD h2⟩

/-- W1: a compact set disjoint from the ear stays disjoint from the slightly enlarged ear -/
theorem u5h_wedge_far {a b c : Plane} {e : Set Plane} (he : IsCompact e)
    (h : Disjoint e (convexHull ℝ {a, b, c})) :
    ∀ᶠ τ in nhds (1 : ℝ), Disjoint e (convexHull ℝ {a, u5h_apex a b c τ, c}) := by
  obtain ⟨δ, hδ, hdisj⟩ := h.exists_cthickenings he
    ((Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)).isClosed
  have ht : Tendsto (fun τ : ℝ => |τ - 1| * ‖b - u5h_mid a c‖) (nhds 1) (nhds 0) := by
    have : Continuous (fun τ : ℝ => |τ - 1| * ‖b - u5h_mid a c‖) := by fun_prop
    simpa using this.tendsto 1
  filter_upwards [ht.eventually_lt_const hδ] with τ hτ
  rw [Set.disjoint_left]
  intro x hxe hxT
  rw [u5h_mem_hull3] at hxT
  obtain ⟨μ, ν, hμ, hν, hs, rfl⟩ := hxT
  have hx' : a + μ • (b - a) + ν • (c - a) ∈ convexHull ℝ {a, b, c} :=
    u5h_mem_hull3_of a b c hμ hν hs
  have hdist : dist (a + μ • (u5h_apex a b c τ - a) + ν • (c - a)) (a + μ • (b - a) + ν • (c - a))
      ≤ δ := by
    rw [dist_eq_norm]
    have : a + μ • (u5h_apex a b c τ - a) + ν • (c - a) - (a + μ • (b - a) + ν • (c - a)) =
        μ • ((τ - 1) • (b - u5h_mid a c)) := by
      rw [← u5h_apex_sub_b]; ext <;> simp <;> ring
    rw [this, norm_smul, norm_smul, Real.norm_of_nonneg hμ, Real.norm_eq_abs]
    calc μ * (|τ - 1| * ‖b - u5h_mid a c‖) ≤ 1 * (|τ - 1| * ‖b - u5h_mid a c‖) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ δ := by rw [one_mul]; exact hτ.le
  have h1 : a + μ • (u5h_apex a b c τ - a) + ν • (c - a) ∈
      Metric.cthickening δ (convexHull ℝ {a, b, c}) :=
    Metric.mem_cthickening_of_dist_le _ _ δ _ hx' hdist
  have h2 : a + μ • (u5h_apex a b c τ - a) + ν • (c - a) ∈ Metric.cthickening δ e :=
    Metric.self_subset_cthickening _ hxe
  exact Set.disjoint_left.mp hdisj h2 h1

/-- W2: an edge `[d, a]` meeting the ear only at `a` meets the slightly enlarged ear only at `a` -/
theorem u5h_wedge_adj {a b c d : Plane} (hD : det (b - a) (c - a) ≠ 0) (hd : d ≠ a)
    (h : segment ℝ d a ∩ convexHull ℝ {a, b, c} ⊆ {a}) :
    ∀ᶠ τ in nhds (1 : ℝ), segment ℝ d a ∩ convexHull ℝ {a, u5h_apex a b c τ, c} ⊆ {a} := by
  set D := det (b - a) (c - a) with hDdef
  set α := det (d - a) (c - a) / D with hα
  set β := det (b - a) (d - a) / D with hβ
  have hbasis : d - a = α • (b - a) + β • (c - a) := u5h_basis hD (d - a)
  -- step 1: the direction of the edge is not in the closed cone of the ear at `a`
  have hnot : ¬ (0 ≤ α ∧ 0 ≤ β) := by
    rintro ⟨hα0, hβ0⟩
    set ε := 1 / (1 + α + β) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; linarith
    have hx1 : a + ε • (d - a) ∈ segment ℝ d a := by
      rw [segment_symm, segment_eq_image']; exact ⟨ε, ⟨hε0.le, hε1⟩, rfl⟩
    have hx2 : a + ε • (d - a) ∈ convexHull ℝ {a, b, c} := by
      rw [hbasis, smul_add, smul_smul, smul_smul, ← add_assoc]
      apply u5h_mem_hull3_of _ _ _ (by positivity) (by positivity)
      have : ε * α + ε * β = (α + β) / (1 + α + β) := by rw [hε]; field_simp
      rw [this, div_le_one (by positivity)]; linarith
    have := h ⟨hx1, hx2⟩
    rw [mem_singleton_iff, add_eq_left, smul_eq_zero, sub_eq_zero] at this
    rcases this with h0 | h0
    · exact hε0.ne' h0
    · exact hd h0
  -- step 2
  have hev : ∀ᶠ τ in nhds (1 : ℝ), 1 / 2 < τ ∧ (β < 0 → α * (τ - 1) < -β) := by
    refine (eventually_gt_nhds (by norm_num)).and ?_
    by_cases hβ0 : β < 0
    · have ht : Tendsto (fun τ : ℝ => α * (τ - 1)) (nhds 1) (nhds 0) := by
        have : Continuous (fun τ : ℝ => α * (τ - 1)) := by fun_prop
        simpa using this.tendsto 1
      filter_upwards [ht.eventually_lt_const (by linarith : (0:ℝ) < -β)] with τ hτ using fun _ => hτ
    · exact Eventually.of_forall fun τ h' => (hβ0 h').elim
  filter_upwards [hev] with τ ⟨hτ, hτ'⟩
  rintro x ⟨hx1, hx2⟩
  rw [segment_symm, segment_eq_image'] at hx1
  obtain ⟨σ, ⟨hσ0, hσ1⟩, rfl⟩ := hx1
  rw [u5h_mem_hull3] at hx2
  obtain ⟨μ, ν, hμ, hν, hs, hx⟩ := hx2
  have hv : σ • (d - a) = μ • (u5h_apex a b c τ - a) + ν • (c - a) := by
    rw [add_assoc] at hx; exact add_left_cancel hx
  rw [u5h_apex_sub, hbasis] at hv
  have hv' : (σ * α) • (b - a) + (σ * β) • (c - a) =
      (μ * τ) • (b - a) + (μ * ((1 - τ) / 2) + ν) • (c - a) := by
    rw [← smul_smul, ← smul_smul, ← smul_add, hv]
    simp only [smul_add, smul_smul, add_smul]; abel
  obtain ⟨e1, e2⟩ := u5h_coords_unique hD hv'
  rw [mem_singleton_iff]
  suffices hσ : σ = 0 by subst hσ; simp
  by_contra hσ
  have hσp : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσ)
  have hτ0 : (0:ℝ) ≤ τ := by linarith
  have hα0 : 0 ≤ α := by
    by_contra hneg
    have h1 := mul_neg_of_pos_of_neg hσp (not_le.mp hneg)
    have h2 : 0 ≤ μ * τ := mul_nonneg hμ hτ0
    linarith
  have hβ0 : β < 0 := by
    by_contra hβ0; exact hnot ⟨hα0, not_lt.mp hβ0⟩
  have hkey := hτ' hβ0
  have h3 : σ * (2 * τ * β + α * (τ - 1)) = 2 * τ * ν := by
    linear_combination (2 * τ) * e2 + (τ - 1) * e1
  have h4 : 0 ≤ 2 * τ * β + α * (τ - 1) := by
    by_contra hc
    have := mul_neg_of_pos_of_neg hσp (not_le.mp hc)
    have : 0 ≤ 2 * τ * ν := by positivity
    linarith
  nlinarith [mul_neg_of_neg_of_pos hβ0 (by linarith : (0:ℝ) < 2 * τ - 1), h4, hkey]

/-- W2 at the other endpoint `c` -/
theorem u5h_wedge_adj' {a b c d : Plane} (hD : det (b - a) (c - a) ≠ 0) (hd : d ≠ c)
    (h : segment ℝ d c ∩ convexHull ℝ {a, b, c} ⊆ {c}) :
    ∀ᶠ τ in nhds (1 : ℝ), segment ℝ d c ∩ convexHull ℝ {a, u5h_apex a b c τ, c} ⊆ {c} := by
  have hD' : det (b - c) (a - c) ≠ 0 := by
    intro h0; apply hD; simp only [det, Prod.fst_sub, Prod.snd_sub] at h0 ⊢; linear_combination -h0
  have := u5h_wedge_adj hD' hd (by rwa [u5h_hull3_perm_321])
  simpa only [u5h_apex_comm, u5h_hull3_perm_321 c] using this

-- ---- piece C ----
/-- a segment from a point outside a closed set to a point inside meets its frontier -/
theorem u5h_segment_meets_frontier {U : Set Plane} (hU : IsClosed U) {b x : Plane} (hb : b ∉ U)
    (hx : x ∈ U) : ∃ y ∈ segment ℝ b x, y ∈ frontier U := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hpre : IsPreconnected (segment ℝ b x) := (convex_segment b x).isPreconnected
  have hsub := hpre.subset_of_closure_inter_subset hU.isOpen_compl
    ⟨b, left_mem_segment ℝ b x, hb⟩ ?_
  · exact hsub (right_mem_segment ℝ b x) hx
  · rintro y ⟨hy1, hy2⟩ hyU
    apply hcon y hy2
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hyU, hy1⟩

/-- the open half-plane `{y | det u (y - q) * D < 0}` is convex -/
theorem u5h_convex_side (u q : Plane) (D : ℝ) : Convex ℝ {y : Plane | det u (y - q) * D < 0} := by
  intro x hx y hy θ₁ θ₂ h1 h2 h12
  simp only [mem_ofPred_eq] at hx hy ⊢
  obtain rfl : θ₂ = 1 - θ₁ := by linarith
  have hlin : det u (θ₁ • x + (1 - θ₁) • y - q) * D =
      θ₁ * (det u (x - q) * D) + (1 - θ₁) * (det u (y - q) * D) := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  rw [hlin]
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · have := mul_neg_of_pos_of_neg h1' hx
    have := mul_nonpos_of_nonneg_of_nonpos h2 hy.le
    linarith
  · rw [← h1']; simp only [zero_mul, zero_add, sub_zero, one_mul]; exact hy

/-- per edge of the cut polygon: eventually the enlarged ear meets it only inside the diagonal -/
theorem u5h_edge_wedge [NeZero n] (P' : LabelledTuple n) (hP' : Embedded P') (b : Plane)
    (hD : det (b - P' (-1)) (P' 0 - P' (-1)) ≠ 0)
    (hear : convexHull ℝ {P' (-1), b, P' 0} ∩ embeddedPolygonImage P' =
      segment ℝ (P' (-1)) (P' 0)) (i : ZMod n) :
    ∀ᶠ τ in nhds (1 : ℝ), edgeSegment P' i ∩
      convexHull ℝ {P' (-1), u5h_apex (P' (-1)) b (P' 0) τ, P' 0} ⊆ segment ℝ (P' (-1)) (P' 0) := by
  set a := P' (-1) with ha
  set c := P' 0 with hc
  have hdiag : edgeSegment P' (-1) = segment ℝ a c := by
    rw [u4h_edgeSegment_eq_segment, neg_add_cancel]
  have hsub : ∀ k, edgeSegment P' k ∩ convexHull ℝ {a, b, c} ⊆ edgeSegment P' k ∩ segment ℝ a c := by
    rintro k x ⟨hx1, hx2⟩
    exact ⟨hx1, hear ▸ ⟨hx2, u4h_edgeSegment_subset_polygonImage P' k hx1⟩⟩
  have hcomp : ∀ k, IsCompact (edgeSegment P' k) := by
    intro k; rw [u4h_edgeSegment_eq_segment]; exact u4h_isCompact_segment _ _
  by_cases h1 : i = -1
  · subst h1; rw [hdiag]; exact Eventually.of_forall fun τ => inter_subset_left
  by_cases h2 : i = -2
  · subst h2
    have e21 : (-2 : ZMod n) + 1 = -1 := by ring
    have hcons := hP'.consecutive (-2)
    rw [e21, hdiag] at hcons
    have hseg : edgeSegment P' (-2) = segment ℝ (P' (-2)) a := by
      rw [u4h_edgeSegment_eq_segment, e21]
    have hd : P' (-2) ≠ a := by
      intro h; apply hP'.edge_ne_zero (-2); simp only [edge, e21]; rw [← ha, h, sub_self]
    have hint : segment ℝ (P' (-2)) a ∩ convexHull ℝ {a, b, c} ⊆ {a} := by
      intro x hx
      have := hsub (-2) (by rwa [hseg])
      rw [hcons] at this; exact this
    filter_upwards [u5h_wedge_adj hD hd hint] with τ hτ
    rw [hseg]
    exact hτ.trans (singleton_subset_iff.mpr (left_mem_segment ℝ a c))
  by_cases h3 : i = 0
  · subst h3
    have hcons := hP'.consecutive (-1)
    rw [neg_add_cancel, hdiag] at hcons
    have hseg : edgeSegment P' 0 = segment ℝ (P' 1) c := by
      rw [u4h_edgeSegment_eq_segment, zero_add, segment_symm]
    have hd : P' 1 ≠ c := by
      intro h; apply hP'.edge_ne_zero 0; simp only [edge, zero_add]; rw [← hc, h, sub_self]
    have hint : segment ℝ (P' 1) c ∩ convexHull ℝ {a, b, c} ⊆ {c} := by
      intro x hx
      have := hsub 0 (by rwa [hseg])
      rw [inter_comm, hcons] at this; exact this
    filter_upwards [u5h_wedge_adj' hD hd hint] with τ hτ
    rw [hseg]
    exact hτ.trans (singleton_subset_iff.mpr (right_mem_segment ℝ a c))
  · have hrem : remote i (-1) := by
      intro hadj
      unfold adjacent at hadj
      rcases hadj with h | h | h
      · exact h3 (by linear_combination -h)
      · exact h1 (by linear_combination -h)
      · exact h2 (by linear_combination -h)
    have hdisj := hP'.remote_disjoint i (-1) hrem
    rw [hdiag] at hdisj
    have hdisjT : Disjoint (edgeSegment P' i) (convexHull ℝ {a, b, c}) := by
      rw [Set.disjoint_left]
      intro x hx hxT
      exact Set.disjoint_left.mp hdisj hx (hsub i ⟨hx, hxT⟩).2
    filter_upwards [u5h_wedge_far (hcomp i) hdisjT] with τ hτ
    intro x hx
    exact (Set.disjoint_left.mp hτ hx.1 hx.2).elim

-- ---- piece D ----
/-- `b` lies in the enlarged ear for `τ ≥ 1` -/
theorem u5h_b_mem_enlarged (a b c : Plane) {τ : ℝ} (hτ : 1 ≤ τ) :
    b ∈ convexHull ℝ {a, u5h_apex a b c τ, c} := by
  have hτ0 : 0 < τ := by linarith
  have h3 : 1 / τ + (τ - 1) / (2 * τ) ≤ 1 := by
    rw [div_add_div _ _ hτ0.ne' (by positivity), div_le_one (by positivity)]; nlinarith
  convert u5h_mem_hull3_of a (u5h_apex a b c τ) c (by positivity : (0:ℝ) ≤ 1 / τ)
    (div_nonneg (by linarith) (by positivity) : (0:ℝ) ≤ (τ - 1) / (2 * τ)) h3 using 1
  rw [u5h_apex_sub]; ext <;> simp <;> field_simp <;> ring

/-- the diagonal lies in the (enlarged) ear -/
theorem u5h_diag_subset_hull3 (a b c : Plane) : segment ℝ a c ⊆ convexHull ℝ {a, b, c} := by
  rw [u5h_hull3_perm_132]; exact u4h_segment_subset_hull3 a c b

/-- a point of the ear off the diagonal is strictly on the side of `b` -/
theorem u5h_det_side_of_mem {a b c x : Plane} (hD : det (b - a) (c - a) ≠ 0) {τ : ℝ} (hτ : 0 < τ)
    (hx : x ∈ convexHull ℝ {a, u5h_apex a b c τ, c}) (hxs : x ∉ segment ℝ a c) :
    det (c - a) (x - a) * det (b - a) (c - a) < 0 := by
  rw [u5h_mem_hull3] at hx
  obtain ⟨μ, ν, hμ, hν, hs, rfl⟩ := hx
  have hμ' : 0 < μ := by
    rcases lt_or_eq_of_le hμ with h | h
    · exact h
    · exfalso; apply hxs
      rw [← h, zero_smul, add_zero, segment_eq_image']
      exact ⟨ν, ⟨hν, by linarith⟩, rfl⟩
  have hdet : det (c - a) (a + μ • (u5h_apex a b c τ - a) + ν • (c - a) - a) =
      -(μ * τ) * det (b - a) (c - a) := by
    rw [u5h_apex_sub]
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  rw [hdet]
  have : 0 < det (b - a) (c - a) * det (b - a) (c - a) := mul_self_pos.mpr hD
  nlinarith [mul_pos hμ' hτ]

/-- Part W: for `τ > 1` close to `1`, the enlarged ear meets the region exactly in the diagonal -/
theorem u5h_wedge_main [NeZero n] (P' : LabelledTuple n) (hP' : Embedded P') (b : Plane)
    (hD : det (b - P' (-1)) (P' 0 - P' (-1)) ≠ 0)
    (hear : convexHull ℝ {P' (-1), b, P' 0} ∩ embeddedPolygonImage P' =
      segment ℝ (P' (-1)) (P' 0))
    (U' : Set Plane) (hUc : IsClosed U') (hU' : frontier U' = embeddedPolygonImage P')
    (hcut : convexHull ℝ {P' (-1), b, P' 0} ∩ U' = segment ℝ (P' (-1)) (P' 0)) :
    ∀ᶠ τ in nhdsWithin (1 : ℝ) (Ioi 1),
      convexHull ℝ {P' (-1), u5h_apex (P' (-1)) b (P' 0) τ, P' 0} ∩ U' =
        segment ℝ (P' (-1)) (P' 0) := by
  set a := P' (-1) with ha
  set c := P' 0 with hc
  have hall : ∀ᶠ τ in nhds (1 : ℝ), ∀ i, edgeSegment P' i ∩
      convexHull ℝ {a, u5h_apex a b c τ, c} ⊆ segment ℝ a c :=
    eventually_all.mpr fun i => u5h_edge_wedge P' hP' b hD hear i
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with τ hτ hτ1
  have hτ1' : (1 : ℝ) < τ := hτ1
  have hsegU : segment ℝ a c ⊆ U' := by
    intro x hx; rw [← hcut] at hx; exact hx.2
  have hbU : b ∉ U' := by
    intro hbU
    have hb : b ∈ segment ℝ a c := hcut ▸ ⟨subset_convexHull ℝ _ (by simp), hbU⟩
    have h0 := u4h_det_segment_zero hb
    apply hD; rw [u4h_det_swap']; rw [h0]; ring
  have hbT : b ∈ convexHull ℝ {a, u5h_apex a b c τ, c} := u5h_b_mem_enlarged a b c hτ1'.le
  apply Subset.antisymm
  · rintro x ⟨hxT, hxU⟩
    by_contra hxs
    have hH : ∀ y ∈ segment ℝ b x, det (c - a) (y - a) * det (b - a) (c - a) < 0 := by
      apply (u5h_convex_side (c - a) a (det (b - a) (c - a))).segment_subset
      · show det (c - a) (b - a) * det (b - a) (c - a) < 0
        rw [u4h_det_swap' (c - a)]
        have := mul_self_pos.mpr hD
        nlinarith
      · exact u5h_det_side_of_mem hD (by linarith) hxT hxs
    obtain ⟨y, hy, hyF⟩ := u5h_segment_meets_frontier hUc hbU hxU
    rw [hU'] at hyF
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyF
    have hyT : y ∈ convexHull ℝ {a, u5h_apex a b c τ, c} :=
      (convex_convexHull ℝ _).segment_subset hbT hxT hy
    have hys : y ∈ segment ℝ a c := hτ i ⟨hi, hyT⟩
    have h0 := u4h_det_segment_zero hys
    have := hH y hy
    rw [h0, zero_mul] at this
    exact lt_irrefl _ this
  · intro x hx
    exact ⟨u5h_diag_subset_hull3 a _ c hx, hsegU hx⟩

-- ---- piece E1 ----
/-! ### The hat-function homeomorphism of a convex quadrilateral (generic part)

`v : Fin 4 → Plane` are the vertices of a convex quadrilateral in counterclockwise order; a
*hub* `p` is a point strictly inside every edge half-plane.  `u5h_ell v p i x` is the affine
functional of edge `i` normalised to be `1` at the hub, `u5h_phi v p` its hat function
(`max 0 (min_i ℓ_i)`), and `u5h_hmap v p q x = x + φ_p x • (q - p)` moves the hub `p` to `q`,
affinely on each fan triangle `conv {p, v i, v (i+1)}` and identically outside the quadrilateral. -/

/-- minimum of four reals -/
def u5h_min4 (f : Fin 4 → ℝ) : ℝ := min (min (f 0) (f 1)) (min (f 2) (f 3))

theorem u5h_min4_le (f : Fin 4 → ℝ) (i : Fin 4) : u5h_min4 f ≤ f i := by
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem u5h_le_min4 {f : Fin 4 → ℝ} {t : ℝ} (h : ∀ i, t ≤ f i) : t ≤ u5h_min4 f :=
  le_min (le_min (h 0) (h 1)) (le_min (h 2) (h 3))

theorem u5h_min4_eq {f : Fin 4 → ℝ} {j : Fin 4} (h : ∀ i, f j ≤ f i) : u5h_min4 f = f j :=
  le_antisymm (u5h_min4_le f j) (u5h_le_min4 h)

theorem u5h_continuous_min4 {f : Fin 4 → Plane → ℝ} (hf : ∀ i, Continuous (f i)) :
    Continuous fun x => u5h_min4 fun i => f i x :=
  ((hf 0).min (hf 1)).min ((hf 2).min (hf 3))

/-- the normalised edge functional of edge `i` (from `v i` to `v (i+1)`) with hub `p` -/
noncomputable def u5h_ell (v : Fin 4 → Plane) (p : Plane) (i : Fin 4) (x : Plane) : ℝ :=
  det (v (i + 1) - v i) (x - v i) / det (v (i + 1) - v i) (p - v i)

/-- the hat function of the hub -/
noncomputable def u5h_phi (v : Fin 4 → Plane) (p : Plane) (x : Plane) : ℝ :=
  max 0 (u5h_min4 fun i => u5h_ell v p i x)

/-- the PL map moving the hub `p` to `q` -/
noncomputable def u5h_hmap (v : Fin 4 → Plane) (p q : Plane) (x : Plane) : Plane :=
  x + u5h_phi v p x • (q - p)

/-- convex position: every vertex is on the left of every edge -/
def u5h_IsConvexQuad (v : Fin 4 → Plane) : Prop :=
  ∀ i j, 0 ≤ det (v (i + 1) - v i) (v j - v i)

/-- a hub: strictly on the left of every edge -/
def u5h_IsHub (v : Fin 4 → Plane) (p : Plane) : Prop :=
  ∀ i, 0 < det (v (i + 1) - v i) (p - v i)

/-- the hub lies on one of the two diagonals -/
def u5h_OnDiag (v : Fin 4 → Plane) (p : Plane) : Prop :=
  (∃ κ : ℝ, 0 ≤ κ ∧ v 2 - p = -(κ • (v 0 - p))) ∨ (∃ κ : ℝ, 0 ≤ κ ∧ v 3 - p = -(κ • (v 1 - p)))

section generic
variable {v : Fin 4 → Plane} {p : Plane}

theorem u5h_continuous_ell (v : Fin 4 → Plane) (p : Plane) (i : Fin 4) :
    Continuous (u5h_ell v p i) := by
  unfold u5h_ell det; fun_prop

theorem u5h_continuous_phi (v : Fin 4 → Plane) (p : Plane) : Continuous (u5h_phi v p) :=
  continuous_const.max (u5h_continuous_min4 (u5h_continuous_ell v p))

theorem u5h_continuous_hmap (v : Fin 4 → Plane) (p q : Plane) : Continuous (u5h_hmap v p q) :=
  continuous_id.add ((u5h_continuous_phi v p).smul continuous_const)

theorem u5h_ell_hub (hp : u5h_IsHub v p) (i : Fin 4) : u5h_ell v p i p = 1 :=
  div_self (hp i).ne'

theorem u5h_ell_vertex_self (v : Fin 4 → Plane) (p : Plane) (i : Fin 4) :
    u5h_ell v p i (v i) = 0 := by
  simp [u5h_ell]

theorem u5h_ell_vertex_next (v : Fin 4 → Plane) (p : Plane) (i : Fin 4) :
    u5h_ell v p i (v (i + 1)) = 0 := by
  simp [u5h_ell]

theorem u5h_ell_vertex_nonneg (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p) (i j : Fin 4) :
    0 ≤ u5h_ell v p i (v j) :=
  div_nonneg (hconv i j) (hp i).le

/-- affinity of the edge functional along a barycentric combination based at the hub -/
theorem u5h_ell_bary (hp : u5h_IsHub v p) (i : Fin 4) (u u' : Plane) (α β : ℝ) :
    u5h_ell v p i (p + α • (u - p) + β • (u' - p)) =
      (1 - α - β) + α * u5h_ell v p i u + β * u5h_ell v p i u' := by
  unfold u5h_ell
  rw [u5h_det_bary, add_div, add_div, mul_div_assoc, mul_div_assoc, mul_div_assoc,
    div_self (hp i).ne', mul_one]

theorem u5h_ell_nonpos_iff (hp : u5h_IsHub v p) (i : Fin 4) (x : Plane) :
    u5h_ell v p i x ≤ 0 ↔ det (v (i + 1) - v i) (x - v i) ≤ 0 := by
  unfold u5h_ell; rw [div_le_iff₀ (hp i), zero_mul]

theorem u5h_ell_nonneg_iff (hp : u5h_IsHub v p) (i : Fin 4) (x : Plane) :
    0 ≤ u5h_ell v p i x ↔ 0 ≤ det (v (i + 1) - v i) (x - v i) := by
  unfold u5h_ell; rw [le_div_iff₀ (hp i), zero_mul]

theorem u5h_phi_eq_zero (_hp : u5h_IsHub v p) {x : Plane} {i : Fin 4} (h : u5h_ell v p i x ≤ 0) :
    u5h_phi v p x = 0 := by
  unfold u5h_phi
  exact max_eq_left ((u5h_min4_le _ i).trans h)

theorem u5h_hmap_id (hp : u5h_IsHub v p) (q : Plane) {x : Plane} {i : Fin 4}
    (h : u5h_ell v p i x ≤ 0) : u5h_hmap v p q x = x := by
  unfold u5h_hmap; rw [u5h_phi_eq_zero hp h, zero_smul, add_zero]

theorem u5h_phi_pos_iff (v : Fin 4 → Plane) (p x : Plane) :
    0 < u5h_phi v p x ↔ ∀ i, 0 < u5h_ell v p i x := by
  unfold u5h_phi
  constructor
  · intro h i
    rcases lt_or_ge 0 (u5h_min4 fun i => u5h_ell v p i x) with h' | h'
    · exact lt_of_lt_of_le h' (u5h_min4_le _ i)
    · rw [max_eq_left h'] at h; exact (lt_irrefl _ h).elim
  · intro h
    have : 0 < u5h_min4 fun i => u5h_ell v p i x := by
      unfold u5h_min4; exact lt_min (lt_min (h 0) (h 1)) (lt_min (h 2) (h 3))
    exact lt_max_of_lt_right this

/-- on the fan triangle `conv {p, v i, v (i+1)}` the hat function is the hub weight -/
theorem u5h_phi_fan (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p) (i : Fin 4) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ 1) :
    u5h_phi v p (p + α • (v i - p) + β • (v (i + 1) - p)) = 1 - α - β := by
  unfold u5h_phi
  have hmin : u5h_min4 (fun j => u5h_ell v p j (p + α • (v i - p) + β • (v (i + 1) - p))) =
      1 - α - β := by
    have hi : u5h_ell v p i (p + α • (v i - p) + β • (v (i + 1) - p)) = 1 - α - β := by
      rw [u5h_ell_bary hp, u5h_ell_vertex_self, u5h_ell_vertex_next]; ring
    rw [← hi]
    apply u5h_min4_eq
    intro j
    rw [hi, u5h_ell_bary hp]
    have h1 := u5h_ell_vertex_nonneg hconv hp j i
    have h2 := u5h_ell_vertex_nonneg hconv hp j (i + 1)
    nlinarith [mul_nonneg hα h1, mul_nonneg hβ h2]
  rw [hmin, max_eq_right (by linarith)]

theorem u5h_hmap_fan (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p) (q : Plane) (i : Fin 4)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β ≤ 1) :
    u5h_hmap v p q (p + α • (v i - p) + β • (v (i + 1) - p)) =
      q + α • (v i - q) + β • (v (i + 1) - q) := by
  unfold u5h_hmap
  rw [u5h_phi_fan hconv hp i hα hβ hs]
  ext <;> simp <;> ring

end generic

-- ---- piece E2 ----
section generic
variable {v : Fin 4 → Plane} {p q : Plane}

/-- membership in a fan triangle by three determinant signs -/
theorem u5h_mem_fan_iff (hp : u5h_IsHub v p) (i : Fin 4) (x : Plane) :
    x ∈ convexHull ℝ {p, v i, v (i + 1)} ↔
      0 ≤ det (v i - p) (x - p) ∧ 0 ≤ det (v (i + 1) - v i) (x - v i) ∧
        det (v (i + 1) - p) (x - p) ≤ 0 := by
  have hpos : 0 < det (v i - p) (v (i + 1) - p) := by
    rw [u4h_det_rot2]; exact hp i
  rw [u4h_mem_hull3_iff_det hpos]
  have : det (p - v (i + 1)) (x - v (i + 1)) = -det (v (i + 1) - p) (x - p) := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  rw [this, neg_nonneg]

theorem u5h_fan_pos (hp : u5h_IsHub v p) (i : Fin 4) : 0 < det (v i - p) (v (i + 1) - p) := by
  rw [u4h_det_rot2]; exact hp i

/-- the four fan triangles of a hub on a diagonal cover the quadrilateral -/
theorem u5h_cover (hp : u5h_IsHub v p) (hd : u5h_OnDiag v p) {x : Plane}
    (hx : ∀ i, 0 ≤ u5h_ell v p i x) : ∃ i, x ∈ convexHull ℝ {p, v i, v (i + 1)} := by
  have hnum : ∀ i, 0 ≤ det (v (i + 1) - v i) (x - v i) :=
    fun i => (u5h_ell_nonneg_iff hp i x).mp (hx i)
  by_contra hcon
  simp only [not_exists] at hcon
  have key : ∀ i, 0 ≤ det (v i - p) (x - p) → 0 < det (v (i + 1) - p) (x - p) := by
    intro i h
    by_contra h'
    exact hcon i ((u5h_mem_fan_iff hp i x).mpr ⟨h, hnum i, not_lt.mp h'⟩)
  have k0 : 0 ≤ det (v 0 - p) (x - p) → 0 < det (v 1 - p) (x - p) := key 0
  have k1 : 0 ≤ det (v 1 - p) (x - p) → 0 < det (v 2 - p) (x - p) := key 1
  have k2 : 0 ≤ det (v 2 - p) (x - p) → 0 < det (v 3 - p) (x - p) := key 2
  have k3 : 0 ≤ det (v 3 - p) (x - p) → 0 < det (v 0 - p) (x - p) := key 3
  rcases hd with ⟨κ, hκ, h2⟩ | ⟨κ, hκ, h3⟩
  · have hd2 : det (v 2 - p) (x - p) = -(κ * det (v 0 - p) (x - p)) := by
      rw [h2]; simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rcases le_or_gt 0 (det (v 0 - p) (x - p)) with h0 | h0
    · have h1 := k0 h0
      have h2' := k1 h1.le
      nlinarith [mul_nonneg hκ h0]
    · have h2' : 0 ≤ det (v 2 - p) (x - p) := by rw [hd2]; nlinarith [mul_nonneg hκ (le_of_lt (neg_pos.mpr h0))]
      have h3' := k2 h2'
      have h0' := k3 h3'.le
      linarith
  · have hd3 : det (v 3 - p) (x - p) = -(κ * det (v 1 - p) (x - p)) := by
      rw [h3]; simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rcases le_or_gt 0 (det (v 1 - p) (x - p)) with h1 | h1
    · have h2' := k1 h1
      have h3' := k2 h2'.le
      nlinarith [mul_nonneg hκ h1]
    · have h3' : 0 ≤ det (v 3 - p) (x - p) := by rw [hd3]; nlinarith [mul_nonneg hκ (le_of_lt (neg_pos.mpr h1))]
      have h0' := k3 h3'
      have h1' := k0 h0'.le
      linarith

/-- outside the quadrilateral some edge functional is negative -/
theorem u5h_ell_neg_of_not_mem (hp : u5h_IsHub v p) (hd : u5h_OnDiag v p) {x : Plane}
    (hx : x ∉ ⋃ i, convexHull ℝ {p, v i, v (i + 1)}) : ∃ i, u5h_ell v p i x < 0 := by
  by_contra h
  simp only [not_exists, not_lt] at h
  obtain ⟨i, hi⟩ := u5h_cover hp hd h
  exact hx (mem_iUnion.mpr ⟨i, hi⟩)

theorem u5h_hmap_id_of_not_mem (hp : u5h_IsHub v p) (hd : u5h_OnDiag v p) (q : Plane) {x : Plane}
    (hx : x ∉ ⋃ i, convexHull ℝ {p, v i, v (i + 1)}) : u5h_hmap v p q x = x := by
  obtain ⟨i, hi⟩ := u5h_ell_neg_of_not_mem hp hd hx
  exact u5h_hmap_id hp q hi.le

/-- the two hub maps are inverse to each other -/
theorem u5h_hmap_inv (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p) (hpd : u5h_OnDiag v p)
    (hq : u5h_IsHub v q) (x : Plane) : u5h_hmap v q p (u5h_hmap v p q x) = x := by
  by_cases h : ∃ i, u5h_ell v p i x ≤ 0
  · obtain ⟨i, hi⟩ := h
    rw [u5h_hmap_id hp q hi]
    exact u5h_hmap_id hq p ((u5h_ell_nonpos_iff hq i x).mpr ((u5h_ell_nonpos_iff hp i x).mp hi))
  · simp only [not_exists, not_le] at h
    obtain ⟨i, hx⟩ := u5h_cover hp hpd fun i => (h i).le
    rw [u5h_mem_hull3] at hx
    obtain ⟨α, β, hα, hβ, hs, rfl⟩ := hx
    rw [u5h_hmap_fan hconv hp q i hα hβ hs, u5h_hmap_fan hconv hq p i hα hβ hs]

theorem u5h_hmap_image_fan (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p) (q : Plane)
    (i : Fin 4) :
    u5h_hmap v p q '' convexHull ℝ {p, v i, v (i + 1)} = convexHull ℝ {q, v i, v (i + 1)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [u5h_mem_hull3] at hx
    obtain ⟨α, β, hα, hβ, hs, rfl⟩ := hx
    rw [u5h_hmap_fan hconv hp q i hα hβ hs]
    exact u5h_mem_hull3_of _ _ _ hα hβ hs
  · intro hy
    rw [u5h_mem_hull3] at hy
    obtain ⟨α, β, hα, hβ, hs, rfl⟩ := hy
    exact ⟨p + α • (v i - p) + β • (v (i + 1) - p), u5h_mem_hull3_of _ _ _ hα hβ hs,
      u5h_hmap_fan hconv hp q i hα hβ hs⟩

theorem u5h_hmap_hub (hp : u5h_IsHub v p) (q : Plane) : u5h_hmap v p q p = q := by
  unfold u5h_hmap u5h_phi
  have : (u5h_min4 fun i => u5h_ell v p i p) = 1 := by
    rw [u5h_min4_eq (j := 0) fun i => by rw [u5h_ell_hub hp, u5h_ell_hub hp]]
    exact u5h_ell_hub hp 0
  rw [this, max_eq_right zero_le_one, one_smul]; abel

theorem u5h_hmap_vertex (hp : u5h_IsHub v p) (q : Plane) (j : Fin 4) : u5h_hmap v p q (v j) = v j :=
  u5h_hmap_id hp q (i := j) (by rw [u5h_ell_vertex_self])

/-- the linear functional `x ↦ det e x / D` -/
noncomputable def u5h_detL (e : Plane) (D : ℝ) : Plane →ₗ[ℝ] ℝ where
  toFun x := det e x / D
  map_add' x y := by simp only [det, Prod.fst_add, Prod.snd_add]; ring
  map_smul' r x := by
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem u5h_detL_apply (e : Plane) (D : ℝ) (x : Plane) : u5h_detL e D x = det e x / D := rfl

theorem u5h_hmap_affineOn_fan (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p) (q : Plane)
    (i : Fin 4) : AffineOn (u5h_hmap v p q) (convexHull ℝ {p, v i, v (i + 1)}) := by
  refine ⟨LinearMap.id + LinearMap.smulRight
    (u5h_detL (v (i + 1) - v i) (det (v (i + 1) - v i) (p - v i))) (q - p),
    -(det (v (i + 1) - v i) (v i) / det (v (i + 1) - v i) (p - v i)) • (q - p), ?_⟩
  intro x hx
  rw [u5h_mem_hull3] at hx
  obtain ⟨α, β, hα, hβ, hs, rfl⟩ := hx
  have hℓ : u5h_ell v p i (p + α • (v i - p) + β • (v (i + 1) - p)) = 1 - α - β := by
    rw [u5h_ell_bary hp, u5h_ell_vertex_self, u5h_ell_vertex_next]; ring
  unfold u5h_ell at hℓ
  rw [u4h_det_sub_right, sub_div] at hℓ
  unfold u5h_hmap
  rw [u5h_phi_fan hconv hp i hα hβ hs]
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, u5h_detL_apply]
  rw [← hℓ, sub_smul]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul] <;> ring

theorem u5h_hmap_isPositiveAffineOn_fan (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p)
    (hq : u5h_IsHub v q) (i : Fin 4) :
    IsPositiveAffineOn (u5h_hmap v p q) (u4h_mkTri p (v i) (v (i + 1)) (u5h_fan_pos hp i)) := by
  refine ⟨?_, ?_⟩
  · rw [u4h_mkTri_carrier]; exact u5h_hmap_affineOn_fan hconv hp q i
  · simp only [u4h_mkTri_v0, u4h_mkTri_v1, u4h_mkTri_v2, u5h_hmap_hub hp, u5h_hmap_vertex hp]
    exact u5h_fan_pos hq i

end generic

-- ---- piece F ----
macro "u5h_hull_perm" : tactic =>
  `(tactic| (congr 1; ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto))

/-! ### The concrete quadrilateral `a, b', c, o` of the ear cut

`b' = apex τ` lies beyond `b` on the ray from the midpoint `m` of the diagonal, `o = apex (-ε)`
behind the diagonal; the source hub is `m = apex 0`, the target hub is `b = apex 1`. -/

/-- the vertices `a, b', c, o` in counterclockwise order (for `0 < det (b - a) (c - a)`) -/
noncomputable def u5h_quadV (a b c : Plane) (ε τ : ℝ) : Fin 4 → Plane :=
  ![a, u5h_apex a b c τ, c, u5h_apex a b c (-ε)]

@[simp] theorem u5h_quadV_zero (a b c : Plane) (ε τ : ℝ) : u5h_quadV a b c ε τ 0 = a := rfl
@[simp] theorem u5h_quadV_one (a b c : Plane) (ε τ : ℝ) :
    u5h_quadV a b c ε τ 1 = u5h_apex a b c τ := rfl
@[simp] theorem u5h_quadV_two (a b c : Plane) (ε τ : ℝ) : u5h_quadV a b c ε τ 2 = c := rfl
@[simp] theorem u5h_quadV_three (a b c : Plane) (ε τ : ℝ) :
    u5h_quadV a b c ε τ 3 = u5h_apex a b c (-ε) := rfl

section concrete
variable {a b c : Plane} {ε τ : ℝ}

theorem u5h_quadV_conv (hD : 0 < det (b - a) (c - a)) (hε : 0 < ε) (hτ : 1 < τ) :
    u5h_IsConvexQuad (u5h_quadV a b c ε τ) := by
  have hD' : 0 < (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) := hD
  have hτ0 : 0 < τ := by linarith
  have hτ1 : 0 < τ - 1 := by linarith
  intro i j
  fin_cases i <;> fin_cases j <;> simp [u5h_quadV]
  all_goals
    simp only [u5h_apex, u5h_mid, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    nlinarith [mul_pos hε hD', mul_pos hτ0 hD', mul_pos hτ1 hD', hD']

theorem u5h_quadV_hub_mid (hD : 0 < det (b - a) (c - a)) (hε : 0 < ε) (hτ : 1 < τ) :
    u5h_IsHub (u5h_quadV a b c ε τ) (u5h_mid a c) := by
  have hD' : 0 < (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) := hD
  have hτ0 : 0 < τ := by linarith
  have hτ1 : 0 < τ - 1 := by linarith
  intro i
  fin_cases i <;> simp [u5h_quadV]
  all_goals
    simp only [u5h_apex, u5h_mid, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    nlinarith [mul_pos hε hD', mul_pos hτ0 hD', mul_pos hτ1 hD', hD']

theorem u5h_quadV_hub_b (hD : 0 < det (b - a) (c - a)) (hε : 0 < ε) (hτ : 1 < τ) :
    u5h_IsHub (u5h_quadV a b c ε τ) b := by
  have hD' : 0 < (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) := hD
  have hτ0 : 0 < τ := by linarith
  have hτ1 : 0 < τ - 1 := by linarith
  intro i
  fin_cases i <;> simp [u5h_quadV]
  all_goals
    simp only [u5h_apex, u5h_mid, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    nlinarith [mul_pos hε hD', mul_pos hτ0 hD', mul_pos hτ1 hD', hD']

theorem u5h_quadV_onDiag_mid (a b c : Plane) (ε τ : ℝ) :
    u5h_OnDiag (u5h_quadV a b c ε τ) (u5h_mid a c) := by
  left
  refine ⟨1, zero_le_one, ?_⟩
  simp only [u5h_quadV_two, u5h_quadV_zero, u5h_mid, one_smul]
  ext <;> simp <;> ring

theorem u5h_quadV_onDiag_b (hε : 0 < ε) (hτ : 1 < τ) : u5h_OnDiag (u5h_quadV a b c ε τ) b := by
  right
  have hτ1 : 0 < τ - 1 := by linarith
  refine ⟨(1 + ε) / (τ - 1), by positivity, ?_⟩
  simp only [u5h_quadV_three, u5h_quadV_one, u5h_apex, u5h_mid]
  ext <;> simp <;> field_simp <;> ring

theorem u5h_mid_mem_openSegment (a c : Plane) : u5h_mid a c ∈ openSegment ℝ a c := by
  rw [openSegment_eq_image']
  refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp only [u5h_mid]; ext <;> simp <;> ring

theorem u5h_mid_mem_openSegment_ob (a b c : Plane) (hε : 0 < ε) :
    u5h_mid a c ∈ openSegment ℝ (u5h_apex a b c (-ε)) b := by
  rw [openSegment_eq_image']
  refine ⟨ε / (1 + ε), ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩, ?_⟩
  simp only [u5h_apex]; ext <;> simp <;> field_simp <;> ring

end concrete

-- ---- piece G ----
/-- a map that is the identity on a triangle is positive affine on it -/
theorem u5h_isPositiveAffineOn_of_id {f : Plane → Plane} {T : Triangle}
    (h : ∀ x ∈ T.carrier, f x = x) : IsPositiveAffineOn f T := by
  refine ⟨⟨LinearMap.id, 0, fun x hx => by simp [h x hx]⟩, ?_⟩
  rw [h _ (u1h_vertex_mem_carrier T 0), h _ (u1h_vertex_mem_carrier T 1),
    h _ (u1h_vertex_mem_carrier T 2)]
  exact T.pos

section generic
variable {v : Fin 4 → Plane} {p q : Plane}

/-- translating the half-plane clauses of `U3_refine_along_lines` into `det` signs -/
theorem u5h_side_le {S : Set Plane} (e q0 : Plane)
    (h : S ⊆ {x | planeDot (u3h_dir e) x ≤ det e q0}) : ∀ x ∈ S, det e (x - q0) ≤ 0 := by
  intro x hx
  have := h hx
  simp only [mem_ofPred_eq, ← u3h_det_eq_planeDot] at this
  rw [u4h_det_sub_right]; linarith

theorem u5h_side_ge {S : Set Plane} (e q0 : Plane)
    (h : S ⊆ {x | det e q0 ≤ planeDot (u3h_dir e) x}) : ∀ x ∈ S, 0 ≤ det e (x - q0) := by
  intro x hx
  have := h hx
  simp only [mem_ofPred_eq, ← u3h_det_eq_planeDot] at this
  rw [u4h_det_sub_right]; linarith

/-- every triangulation refines to one on which the hub map is positive PL -/
theorem u5h_refine_pl (hconv : u5h_IsConvexQuad v) (hp : u5h_IsHub v p) (hq : u5h_IsHub v q)
    (hd0 : ∃ κ : ℝ, 0 ≤ κ ∧ v 2 - p = -(κ • (v 0 - p)))
    (hd1 : ∃ κ : ℝ, 0 ≤ κ ∧ v 3 - p = -(κ • (v 1 - p)))
    {X : Set Plane} (K : Triangulation X) :
    ∃ K'' : Triangulation X, K''.Refines K ∧ IsPositivePLOn (u5h_hmap v p q) K'' := by
  obtain ⟨κ₀, hκ₀, h02⟩ := hd0
  obtain ⟨κ₁, hκ₁, h13⟩ := hd1
  set E : Fin 6 → Plane := ![v 1 - v 0, v 2 - v 1, v 3 - v 2, v 0 - v 3, v 0 - p, v 1 - p] with hE
  set Q : Fin 6 → Plane := ![v 0, v 1, v 2, v 3, p, p] with hQ
  obtain ⟨K'', href, hsides⟩ :=
    U3_refine_along_lines K (fun j => u3h_dir (E j)) (fun j => det (E j) (Q j))
  refine ⟨K'', href, ?_⟩
  intro T hT
  have hs0 : T.carrier ⊆ {x | planeDot (u3h_dir (v 1 - v 0)) x ≤ det (v 1 - v 0) (v 0)} ∨
      T.carrier ⊆ {x | det (v 1 - v 0) (v 0) ≤ planeDot (u3h_dir (v 1 - v 0)) x} := hsides T hT 0
  have hs1 : T.carrier ⊆ {x | planeDot (u3h_dir (v 2 - v 1)) x ≤ det (v 2 - v 1) (v 1)} ∨
      T.carrier ⊆ {x | det (v 2 - v 1) (v 1) ≤ planeDot (u3h_dir (v 2 - v 1)) x} := hsides T hT 1
  have hs2 : T.carrier ⊆ {x | planeDot (u3h_dir (v 3 - v 2)) x ≤ det (v 3 - v 2) (v 2)} ∨
      T.carrier ⊆ {x | det (v 3 - v 2) (v 2) ≤ planeDot (u3h_dir (v 3 - v 2)) x} := hsides T hT 2
  have hs3 : T.carrier ⊆ {x | planeDot (u3h_dir (v 0 - v 3)) x ≤ det (v 0 - v 3) (v 3)} ∨
      T.carrier ⊆ {x | det (v 0 - v 3) (v 3) ≤ planeDot (u3h_dir (v 0 - v 3)) x} := hsides T hT 3
  have hs4 : T.carrier ⊆ {x | planeDot (u3h_dir (v 0 - p)) x ≤ det (v 0 - p) p} ∨
      T.carrier ⊆ {x | det (v 0 - p) p ≤ planeDot (u3h_dir (v 0 - p)) x} := hsides T hT 4
  have hs5 : T.carrier ⊆ {x | planeDot (u3h_dir (v 1 - p)) x ≤ det (v 1 - p) p} ∨
      T.carrier ⊆ {x | det (v 1 - p) p ≤ planeDot (u3h_dir (v 1 - p)) x} := hsides T hT 5
  by_cases hout : ∃ i : Fin 4, ∀ x ∈ T.carrier, det (v (i + 1) - v i) (x - v i) ≤ 0
  · obtain ⟨i, hi⟩ := hout
    exact u5h_isPositiveAffineOn_of_id fun x hx =>
      u5h_hmap_id hp q ((u5h_ell_nonpos_iff hp i x).mpr (hi x hx))
  · simp only [not_exists, not_forall, not_le] at hout
    have hin0 : ∀ x ∈ T.carrier, 0 ≤ det (v 1 - v 0) (x - v 0) := by
      rcases hs0 with h | h
      · exfalso; obtain ⟨x, hx, hlt⟩ := hout 0
        have hlt' : 0 < det (v 1 - v 0) (x - v 0) := hlt
        have := u5h_side_le _ _ h x hx; linarith
      · exact u5h_side_ge _ _ h
    have hin1 : ∀ x ∈ T.carrier, 0 ≤ det (v 2 - v 1) (x - v 1) := by
      rcases hs1 with h | h
      · exfalso; obtain ⟨x, hx, hlt⟩ := hout 1
        have hlt' : 0 < det (v 2 - v 1) (x - v 1) := hlt
        have := u5h_side_le _ _ h x hx; linarith
      · exact u5h_side_ge _ _ h
    have hin2 : ∀ x ∈ T.carrier, 0 ≤ det (v 3 - v 2) (x - v 2) := by
      rcases hs2 with h | h
      · exfalso; obtain ⟨x, hx, hlt⟩ := hout 2
        have hlt' : 0 < det (v 3 - v 2) (x - v 2) := hlt
        have := u5h_side_le _ _ h x hx; linarith
      · exact u5h_side_ge _ _ h
    have hin3 : ∀ x ∈ T.carrier, 0 ≤ det (v 0 - v 3) (x - v 3) := by
      rcases hs3 with h | h
      · exfalso; obtain ⟨x, hx, hlt⟩ := hout 3
        have hlt' : 0 < det (v 0 - v 3) (x - v 3) := hlt
        have := u5h_side_le _ _ h x hx; linarith
      · exact u5h_side_ge _ _ h
    have hin : ∀ i : Fin 4, ∀ x ∈ T.carrier, 0 ≤ det (v (i + 1) - v i) (x - v i) := by
      intro i; fin_cases i
      · exact hin0
      · exact hin1
      · exact hin2
      · exact hin3
    have hd2 : ∀ x, det (v 2 - p) (x - p) = -(κ₀ * det (v 0 - p) (x - p)) := by
      intro x; rw [h02]; simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    have hd3 : ∀ x, det (v 3 - p) (x - p) = -(κ₁ * det (v 1 - p) (x - p)) := by
      intro x; rw [h13]; simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    -- pick the fan triangle from the sign pattern of the two diagonals
    have hfan : ∃ i : Fin 4, T.carrier ⊆ convexHull ℝ {p, v i, v (i + 1)} := by
      rcases hs4 with h4 | h4 <;> rcases hs5 with h5 | h5
      · -- d₀ ≤ 0, d₁ ≤ 0 : fan 3
        refine ⟨3, fun x hx => (u5h_mem_fan_iff hp 3 x).mpr ⟨?_, hin 3 x hx, ?_⟩⟩
        · rw [hd3]; nlinarith [mul_nonneg hκ₁ (neg_nonneg.mpr (u5h_side_le _ _ h5 x hx))]
        · exact u5h_side_le _ _ h4 x hx
      · -- d₀ ≤ 0, d₁ ≥ 0 : fan 2
        refine ⟨2, fun x hx => (u5h_mem_fan_iff hp 2 x).mpr ⟨?_, hin 2 x hx, ?_⟩⟩
        · rw [hd2]; nlinarith [mul_nonneg hκ₀ (neg_nonneg.mpr (u5h_side_le _ _ h4 x hx))]
        · show det (v 3 - p) (x - p) ≤ 0
          rw [hd3]; nlinarith [mul_nonneg hκ₁ (u5h_side_ge _ _ h5 x hx)]
      · -- d₀ ≥ 0, d₁ ≤ 0 : fan 0
        refine ⟨0, fun x hx => (u5h_mem_fan_iff hp 0 x).mpr ⟨?_, hin 0 x hx, ?_⟩⟩
        · exact u5h_side_ge _ _ h4 x hx
        · exact u5h_side_le _ _ h5 x hx
      · -- d₀ ≥ 0, d₁ ≥ 0 : fan 1
        refine ⟨1, fun x hx => (u5h_mem_fan_iff hp 1 x).mpr ⟨?_, hin 1 x hx, ?_⟩⟩
        · exact u5h_side_ge _ _ h5 x hx
        · show det (v 2 - p) (x - p) ≤ 0
          rw [hd2]; nlinarith [mul_nonneg hκ₀ (u5h_side_ge _ _ h4 x hx)]
    obtain ⟨i, hi⟩ := hfan
    exact U1_isPositiveAffineOn_mono (u5h_hmap_isPositiveAffineOn_fan hconv hp hq i)
      (by rw [u4h_mkTri_carrier]; exact hi)

end generic

-- ---- piece H1 ----
section concrete
variable {a b c : Plane} {ε τ : ℝ}

/-- the ear-cut homeomorphism: the hub map of the quadrilateral `a, b', c, o` moving `m` to `b` -/
noncomputable def u5h_earHomeo (hD : 0 < det (b - a) (c - a)) (hε : 0 < ε) (hτ : 1 < τ) :
    Plane ≃ₜ Plane where
  toFun := u5h_hmap (u5h_quadV a b c ε τ) (u5h_mid a c) b
  invFun := u5h_hmap (u5h_quadV a b c ε τ) b (u5h_mid a c)
  left_inv x := u5h_hmap_inv (u5h_quadV_conv hD hε hτ) (u5h_quadV_hub_mid hD hε hτ)
    (u5h_quadV_onDiag_mid a b c ε τ) (u5h_quadV_hub_b hD hε hτ) x
  right_inv x := u5h_hmap_inv (u5h_quadV_conv hD hε hτ) (u5h_quadV_hub_b hD hε hτ)
    (u5h_quadV_onDiag_b hε hτ) (u5h_quadV_hub_mid hD hε hτ) x
  continuous_toFun := u5h_continuous_hmap _ _ _
  continuous_invFun := u5h_continuous_hmap _ _ _

theorem u5h_earHomeo_apply (hD : 0 < det (b - a) (c - a)) (hε : 0 < ε) (hτ : 1 < τ) (x : Plane) :
    u5h_earHomeo hD hε hτ x = u5h_hmap (u5h_quadV a b c ε τ) (u5h_mid a c) b x := rfl

theorem u5h_quadV_diag0 (a b c : Plane) (ε τ : ℝ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ u5h_quadV a b c ε τ 2 - u5h_mid a c = -(κ • (u5h_quadV a b c ε τ 0 - u5h_mid a c)) := by
  refine ⟨1, zero_le_one, ?_⟩
  simp only [u5h_quadV_two, u5h_quadV_zero, u5h_mid, one_smul]
  ext <;> simp <;> ring

theorem u5h_quadV_diag1 (a b c : Plane) (hε : 0 < ε) (hτ : 1 < τ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ u5h_quadV a b c ε τ 3 - u5h_mid a c = -(κ • (u5h_quadV a b c ε τ 1 - u5h_mid a c)) := by
  have hτ0 : 0 < τ := by linarith
  refine ⟨ε / τ, by positivity, ?_⟩
  simp only [u5h_quadV_three, u5h_quadV_one, u5h_apex]
  ext <;> simp <;> field_simp

/-- the source fans `2, 3` form the triangle `o, a, c` -/
theorem u5h_fans23 (a b c : Plane) (ε τ : ℝ) :
    convexHull ℝ {u5h_mid a c, u5h_quadV a b c ε τ 2, u5h_quadV a b c ε τ (2 + 1)} ∪
      convexHull ℝ {u5h_mid a c, u5h_quadV a b c ε τ 3, u5h_quadV a b c ε τ (3 + 1)} =
      convexHull ℝ {u5h_apex a b c (-ε), a, c} := by
  show convexHull ℝ {u5h_mid a c, c, u5h_apex a b c (-ε)} ∪
      convexHull ℝ {u5h_mid a c, u5h_apex a b c (-ε), a} = convexHull ℝ {u5h_apex a b c (-ε), a, c}
  have hsplit := u5h_hull_split (x := a) (y := c) (z := u5h_apex a b c (-ε)) (u5h_mid_mem_openSegment a c)
  have e1 : convexHull ℝ {u5h_apex a b c (-ε), a, c} = convexHull ℝ {a, c, u5h_apex a b c (-ε)} := by
    u5h_hull_perm
  have e2 : convexHull ℝ {u5h_mid a c, u5h_apex a b c (-ε), a} =
      convexHull ℝ {a, u5h_mid a c, u5h_apex a b c (-ε)} := by u5h_hull_perm
  have e3 : convexHull ℝ {u5h_mid a c, c, u5h_apex a b c (-ε)} =
      convexHull ℝ {u5h_mid a c, c, u5h_apex a b c (-ε)} := rfl
  rw [e1, hsplit, e2, union_comm]

/-- the source fans `0, 1` form the enlarged ear `a, b', c` -/
theorem u5h_fans01 (a b c : Plane) (ε τ : ℝ) :
    convexHull ℝ {u5h_mid a c, u5h_quadV a b c ε τ 0, u5h_quadV a b c ε τ (0 + 1)} ∪
      convexHull ℝ {u5h_mid a c, u5h_quadV a b c ε τ 1, u5h_quadV a b c ε τ (1 + 1)} =
      convexHull ℝ {a, u5h_apex a b c τ, c} := by
  show convexHull ℝ {u5h_mid a c, a, u5h_apex a b c τ} ∪
      convexHull ℝ {u5h_mid a c, u5h_apex a b c τ, c} = convexHull ℝ {a, u5h_apex a b c τ, c}
  have hsplit := u5h_hull_split (x := a) (y := c) (z := u5h_apex a b c τ) (u5h_mid_mem_openSegment a c)
  have e1 : convexHull ℝ {a, u5h_apex a b c τ, c} = convexHull ℝ {a, c, u5h_apex a b c τ} := by
    u5h_hull_perm
  have e2 : convexHull ℝ {u5h_mid a c, a, u5h_apex a b c τ} =
      convexHull ℝ {a, u5h_mid a c, u5h_apex a b c τ} := by u5h_hull_perm
  have e3 : convexHull ℝ {u5h_mid a c, u5h_apex a b c τ, c} =
      convexHull ℝ {u5h_mid a c, c, u5h_apex a b c τ} := by u5h_hull_perm
  rw [e1, hsplit, e2, e3]

/-- the target fans `2, 3` form the quadrilateral `o, a, b, c` = `conv {o,a,c} ∪ conv {a,b,c}` -/
theorem u5h_fans23_target (a b c : Plane) (hε : 0 < ε) (τ : ℝ) :
    convexHull ℝ {b, u5h_quadV a b c ε τ 2, u5h_quadV a b c ε τ (2 + 1)} ∪
      convexHull ℝ {b, u5h_quadV a b c ε τ 3, u5h_quadV a b c ε τ (3 + 1)} =
      convexHull ℝ {u5h_apex a b c (-ε), a, c} ∪ convexHull ℝ {a, b, c} := by
  set o := u5h_apex a b c (-ε) with ho
  set m := u5h_mid a c with hm
  show convexHull ℝ {b, c, o} ∪ convexHull ℝ {b, o, a} = convexHull ℝ {o, a, c} ∪ convexHull ℝ {a, b, c}
  have hm1 : m ∈ openSegment ℝ o b := u5h_mid_mem_openSegment_ob a b c hε
  have hm2 : m ∈ openSegment ℝ a c := u5h_mid_mem_openSegment a c
  have s1 : convexHull ℝ {o, b, a} = convexHull ℝ {o, m, a} ∪ convexHull ℝ {m, b, a} := u5h_hull_split hm1
  have s2 : convexHull ℝ {o, b, c} = convexHull ℝ {o, m, c} ∪ convexHull ℝ {m, b, c} := u5h_hull_split hm1
  have s3 : convexHull ℝ {a, c, o} = convexHull ℝ {a, m, o} ∪ convexHull ℝ {m, c, o} := u5h_hull_split hm2
  have s4 : convexHull ℝ {a, c, b} = convexHull ℝ {a, m, b} ∪ convexHull ℝ {m, c, b} := u5h_hull_split hm2
  have p1 : convexHull ℝ {b, c, o} = convexHull ℝ {o, b, c} := by u5h_hull_perm
  have p2 : convexHull ℝ {b, o, a} = convexHull ℝ {o, b, a} := by u5h_hull_perm
  have p3 : convexHull ℝ {o, a, c} = convexHull ℝ {a, c, o} := by u5h_hull_perm
  have p4 : convexHull ℝ {a, b, c} = convexHull ℝ {a, c, b} := by u5h_hull_perm
  have q1 : convexHull ℝ {o, m, c} = convexHull ℝ {m, c, o} := by u5h_hull_perm
  have q2 : convexHull ℝ {o, m, a} = convexHull ℝ {m, o, a} := by u5h_hull_perm
  have q3 : convexHull ℝ {m, b, a} = convexHull ℝ {m, a, b} := by u5h_hull_perm
  have q4 : convexHull ℝ {a, m, o} = convexHull ℝ {m, o, a} := by u5h_hull_perm
  have q5 : convexHull ℝ {a, m, b} = convexHull ℝ {m, a, b} := by u5h_hull_perm
  have q6 : convexHull ℝ {m, c, b} = convexHull ℝ {m, b, c} := by u5h_hull_perm
  rw [p1, p2, p3, p4, s1, s2, s3, s4, q1, q2, q3, q4, q5, q6]
  ext x; simp only [mem_union]; tauto

end concrete

-- ---- piece H2 ----
theorem u5h_supNorm_lt_of_mem_ball {L : ℝ} {x : Plane} (h : x ∈ Metric.ball (0 : Plane) L) :
    supNorm x < L := by
  rw [Metric.mem_ball, dist_zero_right, ← u4h_supNorm_eq_norm] at h; exact h

theorem u5h_ball_subset_interior_square {L : ℝ} :
    Metric.ball (0 : Plane) L ⊆ interior (square L) := by
  apply interior_maximal _ Metric.isOpen_ball
  intro x hx
  show supNorm x ≤ L
  exact (u5h_supNorm_lt_of_mem_ball hx).le

theorem u5h_fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide +revert

/-- Part H: the ear-cut homeomorphism and its properties (orientation normalised) -/
theorem u5h_core {a b c : Plane} (hD : 0 < det (b - a) (c - a)) {ε τ : ℝ} (hε : 0 < ε) (hτ : 1 < τ)
    {U' : Set Plane} (K' : Triangulation U')
    (hoU : convexHull ℝ {u5h_apex a b c (-ε), a, c} ⊆ U')
    (hcut : convexHull ℝ {a, u5h_apex a b c τ, c} ∩ U' = segment ℝ a c)
    {L : ℝ} (hL : 0 < L) (hUL : U' ⊆ interior (square L)) (hb'L : supNorm (u5h_apex a b c τ) < L) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ convexHull ℝ {a, b, c} ∧
      h '' segment ℝ a c = segment ℝ a b ∪ segment ℝ b c ∧
      (∀ x ∈ frontier U', x ∉ openSegment ℝ a c → h x = x) ∧
      convexHull ℝ {a, b, c} ⊆ interior (square L) := by
  set v := u5h_quadV a b c ε τ with hv
  set m := u5h_mid a c with hm
  set o := u5h_apex a b c (-ε) with ho
  set b' := u5h_apex a b c τ with hb'
  have hconv := u5h_quadV_conv hD hε hτ
  have hpm := u5h_quadV_hub_mid hD hε hτ
  have hpb := u5h_quadV_hub_b hD hε hτ
  have hdm := u5h_quadV_onDiag_mid a b c ε τ
  have hd0 := u5h_quadV_diag0 a b c ε τ
  have hd1 := u5h_quadV_diag1 a b c hε hτ
  set h := u5h_earHomeo hD hε hτ with hh
  have hfun : (h : Plane → Plane) = u5h_hmap v m b := rfl
  -- the quadrilateral as the union of the four source fans
  set Q : Set Plane := ⋃ i, convexHull ℝ {m, v i, v (i + 1)} with hQ
  have hQeq : Q = convexHull ℝ {o, a, c} ∪ convexHull ℝ {a, b', c} := by
    rw [← u5h_fans23 a b c ε τ, ← u5h_fans01 a b c ε τ]
    ext x
    simp only [hQ, mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      rcases u5h_fin4_cases i with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr hi)
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
    · rintro ((h1 | h1) | (h1 | h1))
      exacts [⟨2, h1⟩, ⟨3, h1⟩, ⟨0, h1⟩, ⟨1, h1⟩]
  have hfix : ∀ x, x ∉ Q → h x = x := fun x hx => u5h_hmap_id_of_not_mem hpm hdm b hx
  have hseg_oac : segment ℝ a c ⊆ convexHull ℝ {o, a, c} := by
    rw [show ({o, a, c} : Set Plane) = {a, c, o} by
      ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto]
    exact u4h_segment_subset_hull3 a c o
  have hUQ : U' ∩ Q = convexHull ℝ {o, a, c} := by
    apply Subset.antisymm
    · rintro x ⟨hxU, hxQ⟩
      rw [hQeq] at hxQ
      rcases hxQ with h1 | h1
      · exact h1
      · exact hseg_oac (hcut ▸ ⟨h1, hxU⟩)
    · intro x hx; exact ⟨hoU hx, by rw [hQeq]; exact Or.inl hx⟩
  -- sup-norm bounds
  have hsup : ∀ y ∈ U', supNorm y < L := fun y hy => u3h_interior_square_subset L (hUL hy)
  have haU : a ∈ U' := hoU (subset_convexHull ℝ _ (by simp))
  have hcU : c ∈ U' := hoU (subset_convexHull ℝ _ (by simp))
  have hoU' : o ∈ U' := hoU (subset_convexHull ℝ _ (by simp))
  have hmU : m ∈ U' := hoU (hseg_oac (openSegment_subset_segment ℝ a c (u5h_mid_mem_openSegment a c)))
  have hball : ∀ i, v i ∈ Metric.ball (0 : Plane) L := by
    intro i
    rcases u5h_fin4_cases i with rfl | rfl | rfl | rfl
    · exact u4h_mem_ball_of_supNorm_lt (hsup a haU)
    · exact u4h_mem_ball_of_supNorm_lt hb'L
    · exact u4h_mem_ball_of_supNorm_lt (hsup c hcU)
    · exact u4h_mem_ball_of_supNorm_lt (hsup o hoU')
  have hQball : Q ⊆ Metric.ball (0 : Plane) L := by
    simp only [hQ]
    apply iUnion_subset
    intro i
    apply convexHull_min _ (convex_ball 0 L)
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact u4h_mem_ball_of_supNorm_lt (hsup _ hmU)
    · exact hball i
    · exact hball (i + 1)
  -- the triangulations
  obtain ⟨Ksq⟩ := U2_triangulation_square hL
  obtain ⟨Kh, -, hKh⟩ := u5h_refine_pl hconv hpm hpb hd0 hd1 Ksq
  obtain ⟨Kin, href, hKin⟩ := u5h_refine_pl hconv hpm hpb hd0 hd1 K'
  refine ⟨h, Kh, Kin, hKh, hKin, href, ?_, ?_, ?_, ?_, ?_⟩
  · -- identity outside the square
    intro x hx
    apply hfix
    intro hxQ
    have := u5h_supNorm_lt_of_mem_ball (hQball hxQ)
    linarith
  · -- image of the region
    have h1 : h '' (U' \ Q) = U' \ Q := EqOn.image_eq_self fun x hx => hfix x hx.2
    have h2 : h '' convexHull ℝ {o, a, c} = convexHull ℝ {o, a, c} ∪ convexHull ℝ {a, b, c} := by
      conv_lhs => rw [← u5h_fans23 a b c ε τ]
      rw [image_union, hfun, u5h_hmap_image_fan hconv hpm b 2, u5h_hmap_image_fan hconv hpm b 3]
      exact u5h_fans23_target a b c hε τ
    have e1 : h '' U' = (U' \ Q) ∪ (convexHull ℝ {o, a, c} ∪ convexHull ℝ {a, b, c}) := by
      conv_lhs => rw [← sdiff_union_inter U' Q]
      rw [image_union, h1, hUQ, h2]
    rw [e1]
    conv_rhs => rw [← sdiff_union_inter U' Q]
    rw [hUQ, union_assoc]
  · -- image of the diagonal
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [segment_eq_image'] at hx
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hx
      dsimp only
      rcases le_total θ (1 / 2) with hθ | hθ
      · left
        have hx' : a + θ • (c - a) = m + (0 : ℝ) • (v 3 - m) + (1 - 2 * θ) • (v (3 + 1) - m) := by
          show a + θ • (c - a) = m + (0 : ℝ) • (o - m) + (1 - 2 * θ) • (a - m)
          simp only [hm, u5h_mid]; ext <;> simp <;> ring
        rw [hfun, hx', u5h_hmap_fan hconv hpm b 3 le_rfl (by linarith) (by linarith)]
        show b + (0 : ℝ) • (o - b) + (1 - 2 * θ) • (a - b) ∈ segment ℝ a b
        rw [segment_symm, segment_eq_image']
        exact ⟨1 - 2 * θ, ⟨by linarith, by linarith⟩, by simp⟩
      · right
        have hx' : a + θ • (c - a) = m + (2 * θ - 1) • (v 2 - m) + (0 : ℝ) • (v (2 + 1) - m) := by
          show a + θ • (c - a) = m + (2 * θ - 1) • (c - m) + (0 : ℝ) • (o - m)
          simp only [hm, u5h_mid]; ext <;> simp <;> ring
        rw [hfun, hx', u5h_hmap_fan hconv hpm b 2 (by linarith) le_rfl (by linarith)]
        show b + (2 * θ - 1) • (c - b) + (0 : ℝ) • (o - b) ∈ segment ℝ b c
        rw [segment_eq_image']
        exact ⟨2 * θ - 1, ⟨by linarith, by linarith⟩, by simp⟩
    · rintro y (hy | hy)
      · rw [segment_symm, segment_eq_image'] at hy
        obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hy
        dsimp only
        refine ⟨m + (0 : ℝ) • (v 3 - m) + s • (v (3 + 1) - m), ?_, ?_⟩
        · show m + (0 : ℝ) • (o - m) + s • (a - m) ∈ segment ℝ a c
          rw [segment_eq_image']
          refine ⟨(1 - s) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          simp only [hm, u5h_mid]; ext <;> simp <;> ring
        · rw [hfun, u5h_hmap_fan hconv hpm b 3 le_rfl hs0 (by linarith)]
          show b + (0 : ℝ) • (o - b) + s • (a - b) = b + s • (a - b)
          simp
      · rw [segment_eq_image'] at hy
        obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hy
        dsimp only
        refine ⟨m + s • (v 2 - m) + (0 : ℝ) • (v (2 + 1) - m), ?_, ?_⟩
        · show m + s • (c - m) + (0 : ℝ) • (o - m) ∈ segment ℝ a c
          rw [segment_eq_image']
          refine ⟨(1 + s) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          simp only [hm, u5h_mid]; ext <;> simp <;> ring
        · rw [hfun, u5h_hmap_fan hconv hpm b 2 hs0 le_rfl (by linarith)]
          show b + s • (c - b) + (0 : ℝ) • (o - b) = b + s • (c - b)
          simp
  · -- frontier points off the open diagonal are fixed
    intro x hxF hxs
    by_contra hne
    have hpos : 0 < u5h_phi v m x := by
      have h0 : (0 : ℝ) ≤ u5h_phi v m x := le_max_left _ _
      rcases lt_or_eq_of_le h0 with h' | h'
      · exact h'
      · exfalso; apply hne; rw [hfun]; unfold u5h_hmap; rw [← h', zero_smul, add_zero]
    rw [u5h_phi_pos_iff] at hpos
    set V : Set Plane := {y | ∀ i, 0 < u5h_ell v m i y} with hV
    have hVopen : IsOpen V := by
      have : V = ⋂ i, {y | 0 < u5h_ell v m i y} := by ext y; simp [hV]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (u5h_continuous_ell v m i)
    have hxV : x ∈ V := hpos
    have hxcl : x ∈ closure (V ∩ U'ᶜ) := by
      apply hVopen.inter_closure
      refine ⟨hxV, ?_⟩
      rw [frontier_eq_closure_inter_closure] at hxF
      exact hxF.2
    have hsub : V ∩ U'ᶜ ⊆ convexHull ℝ {a, b', c} := by
      rintro y ⟨hyV, hyU⟩
      obtain ⟨i, hi⟩ := u5h_cover hpm hdm fun i => (hyV i).le
      have hyQ : y ∈ Q := mem_iUnion.mpr ⟨i, hi⟩
      rw [hQeq] at hyQ
      rcases hyQ with h1 | h1
      · exact (hyU (hoU h1)).elim
      · exact h1
    have hxT : x ∈ convexHull ℝ {a, b', c} := by
      have hcl : IsClosed (convexHull ℝ {a, b', c}) :=
        ((Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)).isClosed
      exact hcl.closure_subset_iff.mpr hsub hxcl
    have hxU : x ∈ U' := (U2_isCompact_of_triangulation K').isClosed.frontier_subset hxF
    have hxseg : x ∈ segment ℝ a c := hcut ▸ ⟨hxT, hxU⟩
    rw [← insert_endpoints_openSegment] at hxseg
    simp only [mem_insert_iff] at hxseg
    rcases hxseg with rfl | rfl | h1
    · have h0 : u5h_ell v m 3 x = 0 := u5h_ell_vertex_next v m 3
      linarith [hpos 3]
    · have h0 : u5h_ell v m 1 x = 0 := u5h_ell_vertex_next v m 1
      linarith [hpos 1]
    · exact hxs h1
  · -- the ear lies inside the square
    have hb : b ∈ Metric.ball (0 : Plane) L := by
      have : convexHull ℝ {a, b', c} ⊆ Metric.ball (0 : Plane) L := by
        apply convexHull_min _ (convex_ball 0 L)
        intro y hy
        simp only [mem_insert_iff, mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hball 0
        · exact hball 1
        · exact hball 2
      exact this (u5h_b_mem_enlarged a b c hτ.le)
    apply (convexHull_min _ (convex_ball 0 L)).trans u5h_ball_subset_interior_square
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hball 0
    · exact hb
    · exact hball 2

-- ---- piece I1 ----
/-- two triangles on a common edge and on the same side of it overlap off the edge line -/
theorem u5h_same_side_overlap {a c z w : Plane} (hz : 0 < det (c - a) (z - a))
    (hw : 0 < det (c - a) (w - a)) :
    ∃ x ∈ convexHull ℝ {a, c, z} ∩ convexHull ℝ {a, c, w}, 0 < det (c - a) (x - a) := by
  set m := u5h_mid a c with hm
  have hD : det (c - a) (z - a) ≠ 0 := hz.ne'
  set A := det (w - m) (z - a) / det (c - a) (z - a) with hA
  set B := det (c - a) (w - m) / det (c - a) (z - a) with hB
  have hbasis : w - m = A • (c - a) + B • (z - a) := u5h_basis hD (w - m)
  have hma : det (c - a) (m - a) = 0 := by
    simp only [hm, u5h_mid, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hBpos : 0 < B := by
    apply div_pos _ hz
    have : det (c - a) (w - m) = det (c - a) (w - a) - det (c - a) (m - a) := by
      rw [← u4h_det_sub_right]; congr 1; abel
    rw [this, hma, sub_zero]; exact hw
  set ε := 1 / (2 * (|A| + B) + 2) with hε
  have hεpos : 0 < ε := by positivity
  have hεA : ε * |A| < 1 / 2 := by
    rw [hε, one_div_mul_eq_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg A]
  have hεAB : ε * (|A| + B) < 1 / 2 := by
    rw [hε, one_div_mul_eq_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg A]
  have hA1 : A ≤ |A| := le_abs_self A
  have hA2 : -A ≤ |A| := neg_le_abs A
  refine ⟨a + (1 / 2 + ε * A) • (c - a) + (ε * B) • (z - a), ⟨?_, ?_⟩, ?_⟩
  · apply u5h_mem_hull3_of
    · nlinarith
    · positivity
    · nlinarith
  · have hw' : w - a = (A + 1 / 2) • (c - a) + B • (z - a) := by
      have : w - a = (w - m) + (m - a) := by abel
      rw [this, hbasis]
      simp only [hm, u5h_mid]; ext <;> simp <;> ring
    have : a + (1 / 2 + ε * A) • (c - a) + (ε * B) • (z - a) =
        a + ((1 - ε) / 2) • (c - a) + ε • (w - a) := by
      rw [hw']; ext <;> simp <;> ring
    rw [this]
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one (by positivity)]; nlinarith [abs_nonneg A]
    apply u5h_mem_hull3_of _ _ _ (by linarith) hεpos.le
    linarith
  · have : det (c - a) (a + (1 / 2 + ε * A) • (c - a) + (ε * B) • (z - a) - a) =
        ε * B * det (c - a) (z - a) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [this]; positivity

theorem u5h_det_apex_neg (a b c u q : Plane) (ε : ℝ) :
    det u (u5h_apex a b c (-ε) - q) = det u (u5h_mid a c - q) - ε * det u (b - u5h_mid a c) := by
  simp only [u5h_apex, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem u5h_fin3_cases (j k : Fin 3) : j = k ∨ j = k + 1 ∨ j = k + 2 := by
  revert j k; decide

/-- Part O (normalised vertex labels): a point of the face behind the diagonal -/
theorem u5h_exists_o_aux {a b c : Plane} (hD : det (b - a) (c - a) ≠ 0) {U' : Set Plane}
    (K' : Triangulation U') (hcut : convexHull ℝ {a, b, c} ∩ U' = segment ℝ a c)
    (T' : Triangle) (hT' : T' ∈ K'.faces) (k : Fin 3) (hvk : T'.v k = a)
    (hvk1 : T'.v (k + 1) = c) :
    ∃ ε : ℝ, 0 < ε ∧ u5h_apex a b c (-ε) ∈ interior T'.carrier := by
  set z := T'.v (k + 2) with hz
  set m := u5h_mid a c with hm
  have hpos : 0 < det (c - a) (z - a) := by
    have := u2h_pos_cyc T' k; rwa [hvk, hvk1] at this
  have hma : det (c - a) (m - a) = 0 := by
    simp only [hm, u5h_mid, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  -- `b` lies strictly on the other side of the diagonal
  have hb : det (c - a) (b - a) < 0 := by
    have hne : det (c - a) (b - a) ≠ 0 := by rw [u4h_det_swap']; exact neg_ne_zero.mpr hD
    rcases lt_or_gt_of_ne hne with h | h
    · exact h
    · exfalso
      obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := u5h_same_side_overlap hpos h
      have hsub : convexHull ℝ {a, c, z} ⊆ T'.carrier := by
        apply convexHull_min _ (U1_triangle_convex T')
        intro y hy
        simp only [mem_insert_iff, mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · rw [← hvk]; exact u1h_vertex_mem_carrier T' k
        · rw [← hvk1]; exact u1h_vertex_mem_carrier T' (k + 1)
        · exact u1h_vertex_mem_carrier T' (k + 2)
      have hxU : x ∈ U' := u2h_carrier_subset K' hT' (hsub hx1)
      have hxT : x ∈ convexHull ℝ {a, b, c} := by rw [u5h_hull3_perm_132]; exact hx2
      have hxs : x ∈ segment ℝ a c := hcut ▸ ⟨hxT, hxU⟩
      have := u4h_det_segment_zero hxs
      linarith
  have hbm : det (c - a) (b - m) = det (c - a) (b - a) := by
    have : b - m = (b - a) - (m - a) := by abel
    rw [this, u4h_det_sub_right, hma, sub_zero]
  -- the two other edge functionals are positive at `m`
  have hA1 : 0 < det (z - c) (m - c) := by
    have : det (z - c) (m - c) = (1 / 2) * det (c - a) (z - a) := by
      simp only [hm, u5h_mid, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]; positivity
  have hA2 : 0 < det (a - z) (m - z) := by
    have : det (a - z) (m - z) = (1 / 2) * det (c - a) (z - a) := by
      simp only [hm, u5h_mid, det, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]; positivity
  have ev1 : ∀ᶠ ε in nhds (0 : ℝ), 0 < det (z - c) (m - c) - ε * det (z - c) (b - m) := by
    have : Tendsto (fun ε : ℝ => det (z - c) (m - c) - ε * det (z - c) (b - m)) (nhds 0)
        (nhds (det (z - c) (m - c))) := by
      have hc : Continuous (fun ε : ℝ => det (z - c) (m - c) - ε * det (z - c) (b - m)) := by fun_prop
      simpa using hc.tendsto 0
    exact this.eventually_const_lt hA1
  have ev2 : ∀ᶠ ε in nhds (0 : ℝ), 0 < det (a - z) (m - z) - ε * det (a - z) (b - m) := by
    have : Tendsto (fun ε : ℝ => det (a - z) (m - z) - ε * det (a - z) (b - m)) (nhds 0)
        (nhds (det (a - z) (m - z))) := by
      have hc : Continuous (fun ε : ℝ => det (a - z) (m - z) - ε * det (a - z) (b - m)) := by fun_prop
      simpa using hc.tendsto 0
    exact this.eventually_const_lt hA2
  obtain ⟨ε, ⟨h1, h2⟩, hε⟩ :=
    (((ev1.and ev2).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ nhdsWithin 0 (Ioi 0))).exists
  have hεpos : (0 : ℝ) < ε := hε
  refine ⟨ε, hεpos, ?_⟩
  apply u2h_mem_interior_of_det_pos
  intro j
  have e11 : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  have e21 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  rcases u5h_fin3_cases j k with rfl | rfl | rfl
  · rw [hvk1, hvk, u5h_det_apex_neg, hma, hbm]
    nlinarith
  · rw [e11, hvk1, ← hz, u5h_det_apex_neg]
    exact h1
  · rw [e21, hvk, ← hz, u5h_det_apex_neg]
    exact h2

-- ---- piece I2 ----
/-- Part O: a point of the face at the diagonal lying behind the diagonal (orientation-free) -/
theorem u5h_exists_o {a b c : Plane} (hD : det (b - a) (c - a) ≠ 0) {U' : Set Plane}
    (K' : Triangulation U') (hcut : convexHull ℝ {a, b, c} ∩ U' = segment ℝ a c)
    (T' : Triangle) (hT' : T' ∈ K'.faces) (k : Fin 3) (hk : T'.edgeSeg k = segment ℝ a c) :
    ∃ ε : ℝ, 0 < ε ∧ u5h_apex a b c (-ε) ∈ interior T'.carrier := by
  have hac : a ≠ c := by
    intro h; apply hD; rw [h, sub_self]; simp [det]
  have hk' : segment ℝ (T'.v k) (T'.v (k + 1)) = segment ℝ a c := hk
  have hends := u4h_segment_endpoints hac hk'.symm
  have ha : a ∈ ({T'.v k, T'.v (k + 1)} : Set Plane) := hends ▸ (by simp)
  have hc : c ∈ ({T'.v k, T'.v (k + 1)} : Set Plane) := hends ▸ (by simp)
  simp only [mem_insert_iff, mem_singleton_iff] at ha hc
  rcases ha with ha | ha
  · have hc' : T'.v (k + 1) = c := by
      rcases hc with hc | hc
      · exact absurd (ha.trans hc.symm) hac
      · exact hc.symm
    exact u5h_exists_o_aux hD K' hcut T' hT' k ha.symm hc'
  · have hc' : T'.v k = c := by
      rcases hc with hc | hc
      · exact hc.symm
      · exact absurd (ha.trans hc.symm) hac
    have hD' : det (b - c) (a - c) ≠ 0 := by
      intro h0; apply hD; simp only [det, Prod.fst_sub, Prod.snd_sub] at h0 ⊢; linear_combination -h0
    have hcut' : convexHull ℝ {c, b, a} ∩ U' = segment ℝ c a := by
      rw [u5h_hull3_perm_321, segment_symm]; exact hcut
    obtain ⟨ε, hε, h⟩ := u5h_exists_o_aux hD' K' hcut' T' hT' k hc' ha.symm
    exact ⟨ε, hε, by rwa [u5h_apex_comm] at h⟩

/-- an edge of the cut polygon other than the diagonal meets the diagonal only at its ends -/
theorem u5h_edge_inter_diag [NeZero n] (P' : LabelledTuple n) (hP' : Embedded P') {i : ZMod n}
    (hi : i ≠ -1) : edgeSegment P' i ∩ segment ℝ (P' (-1)) (P' 0) ⊆ {P' (-1), P' 0} := by
  have hdiag : edgeSegment P' (-1) = segment ℝ (P' (-1)) (P' 0) := by
    rw [u4h_edgeSegment_eq_segment, neg_add_cancel]
  rw [← hdiag]
  by_cases h2 : i = -2
  · subst h2
    have e21 : (-2 : ZMod n) + 1 = -1 := by ring
    have hcons := hP'.consecutive (-2)
    rw [e21] at hcons
    rw [hcons]; intro x hx; exact Or.inl hx
  by_cases h3 : i = 0
  · subst h3
    have hcons := hP'.consecutive (-1)
    rw [neg_add_cancel] at hcons
    rw [inter_comm, hcons]; intro x hx; exact Or.inr hx
  · have hrem : remote i (-1) := by
      intro hadj; unfold adjacent at hadj
      rcases hadj with h | h | h
      · exact h3 (by linear_combination -h)
      · exact hi (by linear_combination -h)
      · exact h2 (by linear_combination -h)
    rw [Set.disjoint_iff_inter_eq_empty.mp (hP'.remote_disjoint i (-1) hrem)]
    exact empty_subset _

theorem u5h_not_mem_openSegment [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (hP' : Embedded (deleteVertex P j)) {k : ZMod (n + 1)} (hk1 : k ≠ j - 1) (hk2 : k ≠ j)
    {x : Plane} (hx : x ∈ edgeSegment P k) : x ∉ openSegment ℝ (P (j - 1)) (P (j + 1)) := by
  intro hxo
  obtain ⟨i, hi⟩ := deletionIndex_exhaust j hk2
  have hi' : i ≠ -1 := by
    rintro rfl; rw [deletionIndex_last] at hi; exact hk1 hi.symm
  have hx' : x ∈ edgeSegment (deleteVertex P j) i := by
    rw [u4h_edgeSegment_deleteVertex P j hi', hi]; exact hx
  have hac : P (j - 1) ≠ P (j + 1) := by
    intro h; apply hP'.edge_ne_zero (-1)
    simp only [edge, neg_add_cancel, deleteVertex_zero, deleteVertex_last]; rw [h, sub_self]
  have hmem := u5h_edge_inter_diag _ hP' hi' ⟨hx', by
    rw [deleteVertex_last, deleteVertex_zero]; exact openSegment_subset_segment ℝ _ _ hxo⟩
  rw [deleteVertex_last, deleteVertex_zero] at hmem
  rcases hmem with rfl | rfl
  · exact hac (left_mem_openSegment_iff.mp hxo)
  · exact hac (right_mem_openSegment_iff.mp hxo)

theorem u5h_polygonImage_delete_eq [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    embeddedPolygonImage (deleteVertex P j) =
      {x | ∃ k, k ≠ j - 1 ∧ k ≠ j ∧ x ∈ edgeSegment P k} ∪ segment ℝ (P (j - 1)) (P (j + 1)) := by
  ext x; rw [u4h_mem_polygonImage_deleteVertex]; rfl

theorem u5h_polygonImage_eq [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) :
    embeddedPolygonImage P =
      {x | ∃ k, k ≠ j - 1 ∧ k ≠ j ∧ x ∈ edgeSegment P k} ∪
        (segment ℝ (P (j - 1)) (P j) ∪ segment ℝ (P j) (P (j + 1))) := by
  ext x
  simp only [embeddedPolygonImage, mem_iUnion, mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk⟩
    by_cases h1 : k = j - 1
    · subst h1; right; left; rwa [u4h_edgeSegment_prev] at hk
    by_cases h2 : k = j
    · subst h2; right; right; rwa [u4h_edgeSegment_eq_segment] at hk
    · left; exact ⟨k, h1, h2, hk⟩
  · rintro (⟨k, -, -, hk⟩ | hk | hk)
    · exact ⟨k, hk⟩
    · exact ⟨j - 1, by rwa [u4h_edgeSegment_prev]⟩
    · exact ⟨j, by rwa [u4h_edgeSegment_eq_segment]⟩

/-- clause 6: the ear-cut map carries the cut circle onto the circle of `P` -/
theorem u5h_image_polygonImage [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (hP' : Embedded (deleteVertex P j)) {U' : Set Plane}
    (hU' : frontier U' = embeddedPolygonImage (deleteVertex P j)) (h : Plane → Plane)
    (h6 : h '' segment ℝ (P (j - 1)) (P (j + 1)) =
      segment ℝ (P (j - 1)) (P j) ∪ segment ℝ (P j) (P (j + 1)))
    (h7 : ∀ x ∈ frontier U', x ∉ openSegment ℝ (P (j - 1)) (P (j + 1)) → h x = x) :
    h '' embeddedPolygonImage (deleteVertex P j) = embeddedPolygonImage P := by
  rw [u5h_polygonImage_delete_eq, image_union, h6, u5h_polygonImage_eq P j]
  congr 1
  apply EqOn.image_eq_self
  rintro x ⟨k, hk1, hk2, hk⟩
  apply h7
  · rw [hU', u5h_polygonImage_delete_eq]; exact Or.inl ⟨k, hk1, hk2, hk⟩
  · exact u5h_not_mem_openSegment P j hP' hk1 hk2 hk

/-- assembling the leaf's conclusion from the core outputs -/
theorem u5h_assemble [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (hP' : Embedded (deleteVertex P j)) (U' : Set Plane) (K' : Triangulation U')
    (hU' : frontier U' = embeddedPolygonImage (deleteVertex P j)) {L : ℝ}
    (hU'L : U' ⊆ interior (square L))
    (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U')
    (h1 : IsPositivePLOn h Kh) (h2 : IsPositivePLOn h Kin) (h3 : Kin.Refines K')
    (h4 : ∀ x, L ≤ supNorm x → h x = x)
    (h5 : h '' U' = U' ∪ convexHull ℝ {P (j - 1), P j, P (j + 1)})
    (h6 : h '' segment ℝ (P (j - 1)) (P (j + 1)) =
      segment ℝ (P (j - 1)) (P j) ∪ segment ℝ (P j) (P (j + 1)))
    (h7 : ∀ x ∈ frontier U', x ∉ openSegment ℝ (P (j - 1)) (P (j + 1)) → h x = x)
    (h8 : convexHull ℝ {P (j - 1), P j, P (j + 1)} ⊆ interior (square L)) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ earHull P j ∧
      h '' embeddedPolygonImage (deleteVertex P j) = embeddedPolygonImage P ∧
      frontier (U' ∪ earHull P j) = embeddedPolygonImage P ∧
      U' ∪ earHull P j ⊆ interior (square L) := by
  have h6' := u5h_image_polygonImage P j hP' hU' h h6 h7
  refine ⟨h, Kh, Kin, h1, h2, h3, h4, h5, h6', ?_, union_subset hU'L h8⟩
  unfold earHull
  rw [← h5, ← h.image_frontier, hU', h6']

-- ---- piece J ----
/-- the body of `U5_exists_ear_homeo` -/
theorem u5h_leaf [NeZero n] (P : LabelledTuple (n + 1))
    (j : ZMod (n + 1)) (hP' : Embedded (deleteVertex P j))
    (hturn : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hear : earHull P j ∩ embeddedPolygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)))
    (U' : Set Plane) (K' : Triangulation U') (hU' : frontier U' = embeddedPolygonImage (deleteVertex P j))
    (hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1)))
    (hface : ∃ T ∈ K'.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)))
    {L : ℝ} (hL : InsideModel L P) (hU'L : U' ⊆ interior (square L)) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ earHull P j ∧ h '' embeddedPolygonImage (deleteVertex P j) = embeddedPolygonImage P ∧
      frontier (U' ∪ earHull P j) = embeddedPolygonImage P ∧ U' ∪ earHull P j ⊆ interior (square L) := by
  set a := P (j - 1) with ha
  set b := P j with hb
  set c := P (j + 1) with hc
  have hD : det (b - a) (c - a) ≠ 0 := hturn
  have hUc : IsClosed U' := (U2_isCompact_of_triangulation K').isClosed
  have hL0 : 0 < L := (U4_polygonImage_subset_interior_square P hL).2
  have hbL : supNorm b < L := hL j
  have hcut' : convexHull ℝ {a, b, c} ∩ U' = segment ℝ a c := hcut
  -- Part O: the point `o = apex (-ε)` inside the face at the diagonal
  obtain ⟨T', hT', k, hk⟩ := hface
  obtain ⟨ε, hε, hoint⟩ := u5h_exists_o hD K' hcut' T' hT' k hk
  have hsegT' : segment ℝ a c ⊆ T'.carrier := by
    rw [← hk]; exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)
  have hoU : convexHull ℝ {u5h_apex a b c (-ε), a, c} ⊆ U' := by
    apply (convexHull_min _ (U1_triangle_convex T')).trans (u2h_carrier_subset K' hT')
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact interior_subset hoint
    · exact hsegT' (left_mem_segment ℝ a c)
    · exact hsegT' (right_mem_segment ℝ a c)
  -- Part W: the enlarged ear
  have hDw : det (b - deleteVertex P j (-1)) (deleteVertex P j 0 - deleteVertex P j (-1)) ≠ 0 := by
    rw [deleteVertex_last, deleteVertex_zero]; exact hD
  have hearw : convexHull ℝ {deleteVertex P j (-1), b, deleteVertex P j 0} ∩
      embeddedPolygonImage (deleteVertex P j) = segment ℝ (deleteVertex P j (-1)) (deleteVertex P j 0) := by
    rw [deleteVertex_last, deleteVertex_zero]; exact hear
  have hcutw : convexHull ℝ {deleteVertex P j (-1), b, deleteVertex P j 0} ∩ U' =
      segment ℝ (deleteVertex P j (-1)) (deleteVertex P j 0) := by
    rw [deleteVertex_last, deleteVertex_zero]; exact hcut
  have hev := u5h_wedge_main (deleteVertex P j) hP' b hDw hearw U' hUc hU' hcutw
  rw [deleteVertex_last, deleteVertex_zero] at hev
  have hevL : ∀ᶠ τ in nhds (1 : ℝ), supNorm (u5h_apex a b c τ) < L := by
    have hcont : Continuous fun τ => supNorm (u5h_apex a b c τ) := by
      simp only [u4h_supNorm_eq_norm]; exact (u5h_continuous_apex a b c).norm
    have := hcont.tendsto 1
    rw [u5h_apex_one] at this
    exact this.eventually_lt_const hbL
  obtain ⟨τ, hτcut, hτL, hτ1⟩ :=
    (hev.and ((hevL.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (1 : ℝ) ∈ nhdsWithin 1 (Ioi 1)))).exists
  have hτ1' : (1 : ℝ) < τ := hτ1
  -- orientation
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · -- `a, b, c` clockwise: run the core with `a` and `c` exchanged
    have hD' : 0 < det (b - c) (a - c) := by
      simp only [det, Prod.fst_sub, Prod.snd_sub] at hneg ⊢; linarith
    have hoU' : convexHull ℝ {u5h_apex c b a (-ε), c, a} ⊆ U' := by
      rw [u5h_apex_comm, u5h_hull3_perm_132]; exact hoU
    have hcut'' : convexHull ℝ {c, u5h_apex c b a τ, a} ∩ U' = segment ℝ c a := by
      rw [u5h_apex_comm, u5h_hull3_perm_321, segment_symm]; exact hτcut
    have hτL' : supNorm (u5h_apex c b a τ) < L := by rw [u5h_apex_comm]; exact hτL
    obtain ⟨h, Kh, Kin, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      u5h_core hD' hε hτ1' K' hoU' hcut'' hL0 hU'L hτL'
    rw [u5h_hull3_perm_321 c b a] at h5 h8
    rw [segment_symm ℝ c a, segment_symm ℝ c b, segment_symm ℝ b a, union_comm] at h6
    simp only [openSegment_symm ℝ c a] at h7
    exact u5h_assemble P j hP' U' K' hU' hU'L h Kh Kin h1 h2 h3 h4 h5 h6 h7 h8
  · obtain ⟨h, Kh, Kin, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      u5h_core hpos hε hτ1' K' hoU hτcut hL0 hU'L hτL
    exact u5h_assemble P j hP' U' K' hU' hU'L h Kh Kin h1 h2 h3 h4 h5 h6 h7 h8

end U5_block


/-- U5 (sm-3:437-443 realised ambiently, PLAN_FINAL §3.1): cutting an ear `j` of `P` is realised by
a positive PL homeomorphism `h` of the plane, the identity outside a compact subset of `int Q_L`,
carrying the region `U'` bounded by the cut polygon onto `U' ∪ ear` and the cut circle onto the
circle of `P`.

Assembly correction (wave 1, rule 3, flagged by U4): hypothesis `hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1))`
added (equivalently `P j ∉ U'`).  Without it the statement is false: for a reflex ear (a notch) all
skeleton hypotheses hold with `earHull P j ⊆ U'`, so `U' ∪ earHull P j = U'` and the clause
`frontier (U' ∪ earHull P j) = embeddedPolygonImage P` fails (`frontier U' = embeddedPolygonImage (deleteVertex P j)`).
U6 obtains `hcut` from `u4h_regionOf_ear` with `U' := u4h_regionOf (deleteVertex P j)`
(W1_U4_REPORT.md §4). -/
theorem U5_exists_ear_homeo [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple (n + 1)) (hP : Embedded P)
    (j : ZMod (n + 1)) (hP' : Embedded (deleteVertex P j))
    (hturn : det (P j - P (j - 1)) (P (j + 1) - P (j - 1)) ≠ 0)
    (hear : earHull P j ∩ embeddedPolygonImage (deleteVertex P j) = segment ℝ (P (j - 1)) (P (j + 1)))
    (U' : Set Plane) (K' : Triangulation U') (hU' : frontier U' = embeddedPolygonImage (deleteVertex P j))
    (hcut : earHull P j ∩ U' = segment ℝ (P (j - 1)) (P (j + 1)))
    (hedge : ∀ T ∈ K'.faces, ∀ T' ∈ K'.faces, segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T.carrier →
      segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier)
    (hface : ∃ T ∈ K'.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)))
    {L : ℝ} (hL : InsideModel L P) (hU'L : U' ⊆ interior (square L)) :
    ∃ (h : Plane ≃ₜ Plane) (Kh : Triangulation (square L)) (Kin : Triangulation U'),
      IsPositivePLOn h Kh ∧ IsPositivePLOn h Kin ∧ Kin.Refines K' ∧
      (∀ x, L ≤ supNorm x → h x = x) ∧
      h '' U' = U' ∪ earHull P j ∧ h '' embeddedPolygonImage (deleteVertex P j) = embeddedPolygonImage P ∧
      frontier (U' ∪ earHull P j) = embeddedPolygonImage P ∧ U' ∪ earHull P j ⊆ interior (square L) := by
  exact u5h_leaf P j hP' hturn hear U' K' hU' hcut hface hL hU'L

/-! ### U5: `U5_pushforward_edges` is false as stated (rule 3).  Kernel-checked counterexample
`u5h_pushforward_edges_false` and the corrected form `u5h_pushforward_edges`; see W2_U5_REPORT.md. -/

section U5_block2

-- ---- piece K ----
/-- the statement of the leaf `U5_pushforward_edges`, as a proposition -/
def u5h_pushforward_edges_stmt : Prop :=
  ∀ (n : ℕ) [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (U' : Set Plane) (Kin : Triangulation U') (h : Plane ≃ₜ Plane), IsPositivePLOn h Kin →
    h '' U' = U' ∪ earHull P j →
    h '' embeddedPolygonImage (deleteVertex P j) = embeddedPolygonImage P →
    (∀ i, ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment (deleteVertex P j) i) →
    (∀ i, ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, edgeSegment (deleteVertex P j) i ⊆ T.carrier →
      edgeSegment (deleteVertex P j) i ⊆ T'.carrier → T.carrier = T'.carrier) →
    ∃ K : Triangulation (U' ∪ earHull P j),
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier

/-- the counterexample polygon `A, A, B, C` (a repeated vertex at `j = 1`) -/
def u5h_cexP : LabelledTuple 4 :=
  ![((0:ℝ), (0:ℝ)), ((0:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ)), ((0:ℝ), (1:ℝ))]

theorem u5h_cex_det :
    0 < det (((0:ℝ), (1:ℝ)) - ((1:ℝ), (0:ℝ))) (((0:ℝ), (0:ℝ)) - ((1:ℝ), (0:ℝ))) := by
  simp [det]

/-- the triangle `B, C, A` -/
def u5h_cexT : Triangle := u4h_mkTri ((1:ℝ), (0:ℝ)) ((0:ℝ), (1:ℝ)) ((0:ℝ), (0:ℝ)) u5h_cex_det

/-- `U5_pushforward_edges` is false as stated -/
theorem u5h_pushforward_edges_false : ¬ u5h_pushforward_edges_stmt := by
  intro H
  set A : Plane := ((0:ℝ), (0:ℝ)) with hA
  set B : Plane := ((1:ℝ), (0:ℝ)) with hB
  have hear : earHull u5h_cexP 1 = segment ℝ A B := by
    show convexHull ℝ {A, A, B} = segment ℝ A B
    rw [Set.insert_eq_of_mem (by simp), convexHull_pair]
  have hAT : A ∈ u5h_cexT.carrier := u1h_vertex_mem_carrier u5h_cexT 2
  have hBT : B ∈ u5h_cexT.carrier := u1h_vertex_mem_carrier u5h_cexT 0
  have hsegT : segment ℝ A B ⊆ u5h_cexT.carrier := (U1_triangle_convex _).segment_subset hAT hBT
  have hcases4 : ∀ k : ZMod 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  have hcases3 : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  obtain ⟨K, hK, -⟩ := H 3 u5h_cexP 1 u5h_cexT.carrier (u4h_singleTri u5h_cexT)
    (Homeomorph.refl Plane)
    (by
      intro T hT
      have hT' : T = u5h_cexT := hT
      subst hT'
      exact ⟨⟨LinearMap.id, 0, fun x _ => by simp⟩, by simp only [Homeomorph.refl_apply]; exact u5h_cexT.pos⟩)
    (by
      rw [Set.EqOn.image_eq_self (s := u5h_cexT.carrier) (f := ⇑(Homeomorph.refl Plane))
        (fun x _ => rfl), hear]
      exact (union_eq_left.mpr hsegT).symm)
    (by
      rw [Set.EqOn.image_eq_self (s := embeddedPolygonImage (deleteVertex u5h_cexP 1))
        (f := ⇑(Homeomorph.refl Plane)) (fun x _ => rfl)]
      ext x
      rw [u4h_mem_polygonImage_deleteVertex]
      simp only [embeddedPolygonImage, mem_iUnion]
      constructor
      · rintro (⟨k, -, -, hk⟩ | hk)
        · exact ⟨k, hk⟩
        · refine ⟨1, ?_⟩
          rw [u4h_edgeSegment_eq_segment]; exact hk
      · rintro ⟨k, hk⟩
        rcases hcases4 k with rfl | rfl | rfl | rfl
        · right
          rw [u4h_edgeSegment_eq_segment] at hk
          have : segment ℝ (u5h_cexP 0) (u5h_cexP (0 + 1)) = {A} := by
            show segment ℝ A A = {A}; exact segment_same ℝ A
          rw [this, mem_singleton_iff] at hk; subst hk
          exact left_mem_segment ℝ _ _
        · right; rw [u4h_edgeSegment_eq_segment] at hk; exact hk
        · left; exact ⟨2, by decide, by decide, hk⟩
        · left; exact ⟨3, by decide, by decide, hk⟩)
    (by
      intro i
      refine ⟨u5h_cexT, rfl, ?_⟩
      rcases hcases3 i with rfl | rfl | rfl
      · exact ⟨0, by rw [u4h_edgeSegment_eq_segment]; rfl⟩
      · exact ⟨1, by rw [u4h_edgeSegment_eq_segment]; rfl⟩
      · exact ⟨2, by rw [u4h_edgeSegment_eq_segment]; rfl⟩)
    (by
      intro i T hT T' hT' _ _
      have h1 : T = u5h_cexT := hT
      have h2 : T' = u5h_cexT := hT'
      rw [h1, h2])
  obtain ⟨T, -, k, hk⟩ := hK 0
  have h0 : edgeSegment u5h_cexP 0 = {A} := by
    rw [u4h_edgeSegment_eq_segment]; exact segment_same ℝ A
  rw [h0] at hk
  have h1 : T.v k ∈ ({A} : Set Plane) := hk ▸ left_mem_segment ℝ _ _
  have h2 : T.v (k + 1) ∈ ({A} : Set Plane) := hk ▸ right_mem_segment ℝ _ _
  rw [mem_singleton_iff] at h1 h2
  exact u2h_v_ne T ((by decide : ∀ k : Fin 3, k ≠ k + 1) k) (h1.trans h2.symm)

-- ---- piece L ----
theorem u5h_map_edgeSeg {f : Plane → Plane} {T : Triangle} (hT : IsPositiveAffineOn f T) (k : Fin 3) :
    (T.map f hT).edgeSeg k = segment ℝ (f (T.v k)) (f (T.v (k + 1))) := rfl

/-- the endpoints of an edge segment are distinct -/
theorem u5h_ne_of_edgeSeg (T : Triangle) (k : Fin 3) {x y : Plane}
    (h : T.edgeSeg k = segment ℝ x y) : x ≠ y := by
  intro hxy
  subst hxy
  have h1 : T.v k ∈ segment ℝ x x := h ▸ left_mem_segment ℝ _ _
  have h2 : T.v (k + 1) ∈ segment ℝ x x := h ▸ right_mem_segment ℝ _ _
  rw [segment_same, mem_singleton_iff] at h1 h2
  exact u2h_v_ne T ((by decide : ∀ k : Fin 3, k ≠ k + 1) k) (h1.trans h2.symm)

/-- an edge segment's vertex pair is the given pair -/
theorem u5h_image_segment_endpoints (T : Triangle) (k : Fin 3) {x y : Plane}
    (h : T.edgeSeg k = segment ℝ x y) (f : Plane → Plane) :
    segment ℝ (f (T.v k)) (f (T.v (k + 1))) = segment ℝ (f x) (f y) := by
  have hne : T.v k ≠ T.v (k + 1) := u2h_v_ne T ((by decide : ∀ k : Fin 3, k ≠ k + 1) k)
  have hpair := u4h_segment_endpoints hne h
  have h1 : T.v k ∈ ({x, y} : Set Plane) := hpair ▸ (by simp)
  have h2 : T.v (k + 1) ∈ ({x, y} : Set Plane) := hpair ▸ (by simp)
  simp only [mem_insert_iff, mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2, segment_symm]
  · exact absurd (h1.trans h2.symm) hne

/-- an affine map carries a segment inside its domain to the segment of the images -/
theorem u5h_image_segment_of_affine {f : Plane → Plane} {C : Set Plane} (hf : AffineOn f C)
    (hC : Convex ℝ C) {x y : Plane} (hx : x ∈ C) (hy : y ∈ C) :
    f '' segment ℝ x y = segment ℝ (f x) (f y) := by
  rw [← convexHull_pair, u2h_image_convexHull_of_affineOn hf hC (by
    intro z hz; simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption), image_pair, convexHull_pair]

/-- **Corrected form of `U5_pushforward_edges`** (rule 3).  The leaf is false as stated
(`u5h_pushforward_edges_false`).  What differs: the diagonal `[P (j-1), P (j+1)]` is not a face
edge of `Kin`; instead it is split at a point `m` with `h m = P j` and its two halves are face
edges (`hedge1`, `hedge2`, `huniq1`, `huniq2`), `h` fixes every other edge of the cut polygon
pointwise (`hfix`, `hfa`, `hfc`) — the shape produced by `U5_exists_ear_homeo` — and the clause
`h '' polygonImage (deleteVertex P j) = polygonImage P` is dropped (it follows).  The
conclusion is the leaf's, realised by the pushforward `u2h_pushforward` of `Kin`. -/
theorem u5h_pushforward_edges [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (U' : Set Plane) (Kin : Triangulation U') (h : Plane ≃ₜ Plane) (hh : IsPositivePLOn h Kin)
    (hU : h '' U' = U' ∪ earHull P j)
    (m : Plane) (hm : h m = P j) (hfa : h (P (j - 1)) = P (j - 1)) (hfc : h (P (j + 1)) = P (j + 1))
    (hfix : ∀ i, i ≠ -1 → ∀ x ∈ edgeSegment (deleteVertex P j) i, h x = x)
    (hedge' : ∀ i, i ≠ -1 → ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment (deleteVertex P j) i)
    (hedge1 : ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) m)
    (hedge2 : ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ m (P (j + 1)))
    (huniq' : ∀ i, i ≠ -1 → ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces,
      edgeSegment (deleteVertex P j) i ⊆ T.carrier →
      edgeSegment (deleteVertex P j) i ⊆ T'.carrier → T.carrier = T'.carrier)
    (huniq1 : ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, segment ℝ (P (j - 1)) m ⊆ T.carrier →
      segment ℝ (P (j - 1)) m ⊆ T'.carrier → T.carrier = T'.carrier)
    (huniq2 : ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, segment ℝ m (P (j + 1)) ⊆ T.carrier →
      segment ℝ m (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier) :
    ∃ K : Triangulation (U' ∪ earHull P j),
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier := by
  obtain ⟨K₀, hK₀1, hK₀2⟩ := u2h_pushforward Kin h hh
  set K : Triangulation (U' ∪ earHull P j) :=
    { faces := K₀.faces, finite := K₀.finite, cover := by rw [K₀.cover, hU], inter := K₀.inter }
    with hK
  have hKf : K.faces = K₀.faces := rfl
  -- images of the two halves of the diagonal
  have himg1 : h '' segment ℝ (P (j - 1)) m = segment ℝ (P (j - 1)) (P j) := by
    obtain ⟨T₁, hT₁, k, hk⟩ := hedge1
    have hs : segment ℝ (P (j - 1)) m ⊆ T₁.carrier := by
      rw [← hk]; exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)
    rw [u5h_image_segment_of_affine (hh T₁ hT₁).1 (U1_triangle_convex T₁)
      (hs (left_mem_segment ℝ _ _)) (hs (right_mem_segment ℝ _ _)), hfa, hm]
  have himg2 : h '' segment ℝ m (P (j + 1)) = segment ℝ (P j) (P (j + 1)) := by
    obtain ⟨T₁, hT₁, k, hk⟩ := hedge2
    have hs : segment ℝ m (P (j + 1)) ⊆ T₁.carrier := by
      rw [← hk]; exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)
    rw [u5h_image_segment_of_affine (hh T₁ hT₁).1 (U1_triangle_convex T₁)
      (hs (left_mem_segment ℝ _ _)) (hs (right_mem_segment ℝ _ _)), hfc, hm]
  -- the fixed edges
  have hfixed : ∀ i, i ≠ j - 1 → i ≠ j → ∃ i' : ZMod n, i' ≠ -1 ∧
      edgeSegment P i = edgeSegment (deleteVertex P j) i' := by
    intro i h1 h2
    obtain ⟨i', hi'⟩ := deletionIndex_exhaust j h2
    have hi'ne : i' ≠ -1 := by
      rintro rfl; rw [deletionIndex_last] at hi'; exact h1 hi'.symm
    exact ⟨i', hi'ne, by rw [u4h_edgeSegment_deleteVertex P j hi'ne, hi']⟩
  refine ⟨K, ?_, ?_⟩
  · intro i
    rw [hKf]
    by_cases h1 : i = j - 1
    · subst h1
      obtain ⟨T, hT, k, hk⟩ := hedge1
      obtain ⟨hTa, hTm⟩ := hK₀1 T hT
      refine ⟨T.map h hTa, hTm, k, ?_⟩
      rw [u5h_map_edgeSeg, u5h_image_segment_endpoints T k hk, hfa, hm, u4h_edgeSegment_prev]
    by_cases h2 : i = j
    · rw [h2]
      obtain ⟨T, hT, k, hk⟩ := hedge2
      obtain ⟨hTa, hTm⟩ := hK₀1 T hT
      refine ⟨T.map h hTa, hTm, k, ?_⟩
      rw [u5h_map_edgeSeg, u5h_image_segment_endpoints T k hk, hfc, hm, u4h_edgeSegment_eq_segment]
    · obtain ⟨i', hi'ne, heq⟩ := hfixed i h1 h2
      obtain ⟨T, hT, k, hk⟩ := hedge' i' hi'ne
      obtain ⟨hTa, hTm⟩ := hK₀1 T hT
      refine ⟨T.map h hTa, hTm, k, ?_⟩
      rw [u5h_map_edgeSeg, heq, ← hk]
      have hv1 : T.v k ∈ T.edgeSeg k := left_mem_segment ℝ _ _
      have hv2 : T.v (k + 1) ∈ T.edgeSeg k := right_mem_segment ℝ _ _
      rw [hk] at hv1 hv2
      rw [hfix i' hi'ne _ hv1, hfix i' hi'ne _ hv2]
      rfl
  · intro i F hF F' hF' hsub hsub'
    rw [hKf] at hF hF'
    obtain ⟨T, hT, hTa, rfl⟩ := hK₀2 F hF
    obtain ⟨T', hT', hTa', rfl⟩ := hK₀2 F' hF'
    rw [u2h_map_carrier hTa] at hsub ⊢
    rw [u2h_map_carrier hTa'] at hsub' ⊢
    have key : ∀ (S : Set Plane) (Tc : Set Plane), S ⊆ h '' Tc → h.symm '' S ⊆ Tc := by
      rintro S Tc hS y ⟨x, hx, rfl⟩
      obtain ⟨t, ht, rfl⟩ := hS hx
      rwa [h.symm_apply_apply]
    suffices hTT : T.carrier = T'.carrier by rw [hTT]
    by_cases h1 : i = j - 1
    · subst h1
      have hpre : h.symm '' edgeSegment P (j - 1) = segment ℝ (P (j - 1)) m := by
        rw [u4h_edgeSegment_prev, ← himg1, image_image]
        simp only [Homeomorph.symm_apply_apply, image_id']
      exact huniq1 T hT T' hT' (by rw [← hpre]; exact key _ _ hsub) (by rw [← hpre]; exact key _ _ hsub')
    by_cases h2 : i = j
    · rw [h2] at hsub hsub'
      have hpre : h.symm '' edgeSegment P j = segment ℝ m (P (j + 1)) := by
        rw [u4h_edgeSegment_eq_segment, ← himg2, image_image]
        simp only [Homeomorph.symm_apply_apply, image_id']
      exact huniq2 T hT T' hT' (by rw [← hpre]; exact key _ _ hsub) (by rw [← hpre]; exact key _ _ hsub')
    · obtain ⟨i', hi'ne, heq⟩ := hfixed i h1 h2
      have hpre : h.symm '' edgeSegment P i = edgeSegment (deleteVertex P j) i' := by
        rw [heq]
        apply EqOn.image_eq_self
        intro x hx
        have := hfix i' hi'ne x hx
        calc h.symm x = h.symm (h x) := by rw [this]
          _ = x := h.symm_apply_apply x
      exact huniq' i' hi'ne T hT T' hT' (by rw [← hpre]; exact key _ _ hsub)
        (by rw [← hpre]; exact key _ _ hsub')

end U5_block2

/-- U5: the ear-cut homeomorphism sends the faces of the refined triangulation `Kin` of `U'` to a
triangulation of `U' ∪ ear` in which every edge of `P` is an edge of exactly one face.

Assembly correction (wave 2, rule 3, reported by U5): the skeleton form is false (kernel-checked counterexample
`u5h_pushforward_edges_false : ¬ u5h_pushforward_edges_stmt`, W2_U5_REPORT.md §3: `n = 3`,
`P = (A, A, B, C)`, `j = 1`, `h = id` — the conclusion demands a face edge equal to the point
`edgeSegment P 0 = {A}`).  Corrected form (the shape produced by `U5_exists_ear_homeo`): the diagonal
`[P (j-1), P (j+1)]` is split at a point `m` with `h m = P j` and its two halves are face edges of exactly
one face (`hedge1`, `hedge2`, `huniq1`, `huniq2`); `hedge'`/`huniq'` are required only for `i ≠ -1`; `h`
fixes every other edge of the cut polygon pointwise (`hfix`, `hfa`, `hfc`); the clause
`h '' polygonImage (deleteVertex P j) = polygonImage P` is dropped (it follows).  Conclusion unchanged.
Consumed by nobody (U6 uses only `U5_exists_ear_homeo`). -/
theorem U5_pushforward_edges [NeZero n] (P : LabelledTuple (n + 1)) (j : ZMod (n + 1))
    (U' : Set Plane) (Kin : Triangulation U') (h : Plane ≃ₜ Plane) (hh : IsPositivePLOn h Kin)
    (hU : h '' U' = U' ∪ earHull P j)
    (m : Plane) (hm : h m = P j) (hfa : h (P (j - 1)) = P (j - 1)) (hfc : h (P (j + 1)) = P (j + 1))
    (hfix : ∀ i, i ≠ -1 → ∀ x ∈ edgeSegment (deleteVertex P j) i, h x = x)
    (hedge' : ∀ i, i ≠ -1 → ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment (deleteVertex P j) i)
    (hedge1 : ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) m)
    (hedge2 : ∃ T ∈ Kin.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ m (P (j + 1)))
    (huniq' : ∀ i, i ≠ -1 → ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces,
      edgeSegment (deleteVertex P j) i ⊆ T.carrier →
      edgeSegment (deleteVertex P j) i ⊆ T'.carrier → T.carrier = T'.carrier)
    (huniq1 : ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, segment ℝ (P (j - 1)) m ⊆ T.carrier →
      segment ℝ (P (j - 1)) m ⊆ T'.carrier → T.carrier = T'.carrier)
    (huniq2 : ∀ T ∈ Kin.faces, ∀ T' ∈ Kin.faces, segment ℝ m (P (j + 1)) ⊆ T.carrier →
      segment ℝ m (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier) :
    ∃ K : Triangulation (U' ∪ earHull P j),
      (∀ i, ∃ T ∈ K.faces, ∃ k : Fin 3, T.edgeSeg k = edgeSegment P i) ∧
      ∀ i, ∀ T ∈ K.faces, ∀ T' ∈ K.faces, edgeSegment P i ⊆ T.carrier →
        edgeSegment P i ⊆ T'.carrier → T.carrier = T'.carrier :=
  u5h_pushforward_edges P j U' Kin h hh hU m hm hfa hfc hfix hedge' hedge1 hedge2 huniq' huniq1 huniq2

/-! ### U6 (sequential) — 57a and 57e via the ambient parametrisation -/

/-- The ambient parametrisation of the bounded region (PLAN_FINAL §3.1): a base triangle `T₀` inside
`int Q_L` and a positive PL homeomorphism `H` of the plane (`H = h_m ∘ ⋯ ∘ h_1`), the identity
outside `int Q_L`, PL on a triangulation of `Q_L` and on one of `T₀`, with `H (∂T₀) = C`. -/
structure AmbientParam [NeZero n] (P : LabelledTuple n) (L : ℝ) where
  /-- the base triangle (the last 3-gon of the ear sequence) -/
  T₀ : Triangle
  /-- the composite ear-cut homeomorphism -/
  H : Plane ≃ₜ Plane
  /-- a triangulation of the model square on which `H` is positive PL -/
  K : Triangulation (square L)
  /-- a triangulation of the base triangle on which `H` is positive PL -/
  KT : Triangulation T₀.carrier
  pl : IsPositivePLOn H K
  plT : IsPositivePLOn H KT
  /-- `H` is the identity outside `int Q_L` -/
  fix : ∀ x, L ≤ supNorm x → H x = x
  inside : T₀.carrier ⊆ interior (square L)
  /-- `H (∂T₀) = C` -/
  boundary : H '' frontier T₀.carrier = embeddedPolygonImage P

/-! ### U6 helpers (`u6h_`), 2026-09-19: sphere topology for the ambient parametrisation. -/

/-- The identity is positive affine on every triangle. -/
theorem u6h_isPositiveAffineOn_id (T : Triangle) : IsPositiveAffineOn id T :=
  ⟨⟨LinearMap.id, 0, fun x _ => by simp⟩, T.pos⟩

/-- The identity homeomorphism is positive PL on every triangulation. -/
theorem u6h_isPositivePLOn_refl {X : Set Plane} (K : Triangulation X) :
    IsPositivePLOn (Homeomorph.refl Plane) K := by
  intro T _
  exact u6h_isPositiveAffineOn_id T

/-- A plane homeomorphism fixing every point of sup-norm `≥ L` maps the square `Q_L` into itself. -/
theorem u6h_image_square_subset {L : ℝ} (H : Plane ≃ₜ Plane) (fix : ∀ x, L ≤ supNorm x → H x = x) :
    H '' square L ⊆ square L := by
  rintro y ⟨x, hx, rfl⟩
  by_contra hy
  have hL : L ≤ supNorm (H x) := le_of_lt (not_le.mp hy)
  have h1 : H (H x) = H x := fix _ hL
  have h2 : H x = x := H.injective h1
  exact hy (by rw [h2]; exact hx)

/-- The complement in the sphere of the coe-image of a plane set is the coe-image of the complement
together with `∞`. -/
theorem u6h_compl_image_coe (K : Set Plane) :
    (((↑) : Plane → Sphere) '' K)ᶜ = ((↑) : Plane → Sphere) '' Kᶜ ∪ {∞} := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe x => simp [OnePoint.coe_ne_infty]

theorem u6h_coe_preimage_image (S : Set Plane) :
    ((↑) : Plane → Sphere) ⁻¹' (((↑) : Plane → Sphere) '' S) = S :=
  OnePoint.coe_injective.preimage_image S

theorem u6h_coe_preimage_infty : ((↑) : Plane → Sphere) ⁻¹' {∞} = ∅ := by
  ext x; simp

theorem u6h_infty_notMem_image (S : Set Plane) : ∞ ∉ ((↑) : Plane → Sphere) '' S := by
  rintro ⟨x, -, hx⟩
  exact OnePoint.coe_ne_infty x hx

/-- The complement of a compact plane set is unbounded. -/
theorem u6h_not_isBounded_compl {K : Set Plane} (hK : IsCompact K) : ¬ Bornology.IsBounded Kᶜ := by
  intro h
  have : Bornology.IsBounded (univ : Set Plane) := by
    rw [← union_compl_self K]; exact hK.isBounded.union h
  exact NormedSpace.unbounded_univ ℝ Plane this

/-- `∞` lies in the closure of the coe-image of an unbounded plane set. -/
theorem u6h_infty_mem_closure {S : Set Plane} (hS : ¬ Bornology.IsBounded S) :
    ∞ ∈ closure (((↑) : Plane → Sphere) '' S) := by
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨c, ⟨-, hcc⟩, hct⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp ht
  have hnot : ¬ S ⊆ c := fun h => hS (hcc.isBounded.subset h)
  obtain ⟨x, hxS, hxc⟩ := not_subset.mp hnot
  exact ⟨(x : Sphere), hct (Or.inl ⟨x, hxc, rfl⟩), ⟨x, hxS, rfl⟩⟩

/-- The complement in the sphere of the coe-image of a compact plane set with connected complement
is connected. -/
theorem u6h_isConnected_compl_image {K : Set Plane} (hK : IsCompact K) (hc : IsConnected Kᶜ) :
    IsConnected ((((↑) : Plane → Sphere) '' K)ᶜ) := by
  rw [u6h_compl_image_coe]
  refine ⟨⟨∞, Or.inr rfl⟩, ?_⟩
  have h1 : IsPreconnected (((↑) : Plane → Sphere) '' Kᶜ) :=
    (hc.image _ OnePoint.continuous_coe.continuousOn).isPreconnected
  refine h1.subset_closure subset_union_left ?_
  rintro z (hz | hz)
  · exact subset_closure hz
  · rw [mem_singleton_iff.mp hz]
    exact u6h_infty_mem_closure (u6h_not_isBounded_compl hK)

theorem u6h_isOpen_compl_image {K : Set Plane} (hK : IsCompact K) :
    IsOpen ((((↑) : Plane → Sphere) '' K)ᶜ) :=
  (OnePoint.isClosed_image_coe.mpr ⟨hK.isClosed, hK⟩).isOpen_compl

/-- A set that is the disjoint union of two nonempty open connected sets has exactly two connected
components (`Nat.card` of an infinite type is `0`, so the count is made explicit through
`Nat.card_eq_two_iff`). -/
theorem u6h_card_connectedComponents_two {X : Type*} [TopologicalSpace X] {S A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hd : Disjoint A B) (hcov : A ∪ B = S) : Nat.card (ConnectedComponents S) = 2 := by
  rw [Nat.card_eq_two_iff]
  obtain ⟨a, ha⟩ := hAc.nonempty
  obtain ⟨b, hb⟩ := hBc.nonempty
  have hAS : A ⊆ S := hcov ▸ subset_union_left
  have hBS : B ⊆ S := hcov ▸ subset_union_right
  set A' : Set S := Subtype.val ⁻¹' A with hA'
  set B' : Set S := Subtype.val ⁻¹' B with hB'
  have hA'o : IsOpen A' := hA.preimage continuous_subtype_val
  have hB'o : IsOpen B' := hB.preimage continuous_subtype_val
  have hA'c : IsPreconnected A' := by
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rw [hA', Subtype.image_preimage_coe, inter_eq_right.mpr hAS]
    exact hAc.isPreconnected
  have hB'c : IsPreconnected B' := by
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rw [hB', Subtype.image_preimage_coe, inter_eq_right.mpr hBS]
    exact hBc.isPreconnected
  have hd' : Disjoint A' B' := hd.preimage _
  have hcov' : ∀ z : S, z ∈ A' ∪ B' := fun z => by
    have hz : (z : X) ∈ A ∪ B := hcov ▸ z.2
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz
  refine ⟨((⟨a, hAS ha⟩ : S) : ConnectedComponents S), ((⟨b, hBS hb⟩ : S) : ConnectedComponents S),
    ?_, ?_⟩
  · intro h
    rw [ConnectedComponents.coe_eq_coe'] at h
    have hsub : connectedComponent (⟨b, hBS hb⟩ : S) ⊆ B' :=
      isPreconnected_connectedComponent.subset_right_of_subset_union hA'o hB'o hd'
        (fun z _ => hcov' z) ⟨_, mem_connectedComponent, hb⟩
    exact hd'.notMem_of_mem_left (a := (⟨a, hAS ha⟩ : S)) ha (hsub h)
  · apply eq_univ_of_forall
    intro c
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases hcov' z with hz | hz
    · left
      rw [ConnectedComponents.coe_eq_coe']
      exact hA'c.subset_connectedComponent (x := (⟨a, hAS ha⟩ : S)) ha hz
    · right
      rw [mem_singleton_iff, ConnectedComponents.coe_eq_coe']
      exact hB'c.subset_connectedComponent (x := (⟨b, hBS hb⟩ : S)) hb hz

/-- The complement of the frontier of a triangle: the two components `int T`, `Tᶜ`. -/
theorem u6h_compl_frontier_triangle (T : Triangle) :
    (frontier T.carrier)ᶜ = interior T.carrier ∪ (T.carrier)ᶜ ∧
      IsConnected (interior T.carrier) ∧ IsConnected (T.carrier)ᶜ ∧
      Disjoint (interior T.carrier) (T.carrier)ᶜ := by
  refine ⟨?_, U1_interior_convex_isConnected (U1_triangle_convex T) (U1_triangle_interior_nonempty T),
    U1_compl_compact_convex_isConnected (U1_triangle_convex T) (U1_triangle_isCompact T), ?_⟩
  · rw [(U1_triangle_isCompact T).isClosed.frontier_eq]
    ext x
    simp only [mem_compl_iff, mem_sdiff, not_and, not_not, mem_union]
    tauto
  · exact disjoint_compl_right.mono_left interior_subset

/-- The plane decomposition attached to a homeomorphism `H` and a triangle `T` with
`H (∂T) = C`: the complement of `C` is the disjoint union of the open sets `H (int T)` and
`(H T)ᶜ`, both connected, the first bounded and the second unbounded. -/
theorem u6h_plane_split {P : LabelledTuple n} (H : Plane ≃ₜ Plane) (T : Triangle)
    (hb : H '' frontier T.carrier = embeddedPolygonImage P) :
    (embeddedPolygonImage P)ᶜ = H '' interior T.carrier ∪ (H '' T.carrier)ᶜ ∧
      IsOpen (H '' interior T.carrier) ∧ IsOpen (H '' T.carrier)ᶜ ∧
      IsConnected (H '' interior T.carrier) ∧ IsConnected (H '' T.carrier)ᶜ ∧
      Disjoint (H '' interior T.carrier) (H '' T.carrier)ᶜ ∧ IsCompact (H '' T.carrier) := by
  obtain ⟨hfr, hic, hcc, hdisj⟩ := u6h_compl_frontier_triangle T
  have hK : IsCompact (H '' T.carrier) := (U1_triangle_isCompact T).image H.continuous
  refine ⟨?_, H.isOpenMap _ isOpen_interior, hK.isClosed.isOpen_compl,
    hic.image H H.continuous.continuousOn, ?_, ?_, hK⟩
  · rw [← hb, ← image_compl_eq H.bijective, hfr, image_union, image_compl_eq H.bijective]
  · rw [← image_compl_eq H.bijective]
    exact hcc.image H H.continuous.continuousOn
  · rw [← image_compl_eq H.bijective]
    exact (disjoint_image_iff H.injective).mpr hdisj

/-- The sphere decomposition attached to `H`, `T` with `H (∂T) = C`: `sphereComplement P` is the
disjoint union of the open connected sets `coe '' (H '' int T)` and `(coe '' (H '' T))ᶜ`, the
second containing `∞`. -/
theorem u6h_sphere_split {P : LabelledTuple n} (H : Plane ≃ₜ Plane) (T : Triangle)
    (hb : H '' frontier T.carrier = embeddedPolygonImage P) :
    sphereComplement P = ((↑) : Plane → Sphere) '' (H '' interior T.carrier) ∪
        (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ ∧
      IsOpen (((↑) : Plane → Sphere) '' (H '' interior T.carrier)) ∧
      IsOpen (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ ∧
      IsConnected (((↑) : Plane → Sphere) '' (H '' interior T.carrier)) ∧
      IsConnected (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ ∧
      Disjoint (((↑) : Plane → Sphere) '' (H '' interior T.carrier))
        (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ ∧
      ∞ ∈ (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ := by
  obtain ⟨hcpl, hIo, hEo, hIc, hEc, hdisj, hK⟩ := u6h_plane_split H T hb
  refine ⟨?_, OnePoint.isOpen_image_coe.mpr hIo, u6h_isOpen_compl_image hK,
    hIc.image _ OnePoint.continuous_coe.continuousOn, u6h_isConnected_compl_image hK hEc, ?_,
    u6h_infty_notMem_image _⟩
  · show (((↑) : Plane → Sphere) '' embeddedPolygonImage P)ᶜ = _
    rw [u6h_compl_image_coe, hcpl, image_union, u6h_compl_image_coe, union_assoc]
  · exact disjoint_compl_right.mono_left (image_mono (image_mono interior_subset))

/-- The exterior region is the complement of `coe '' (H '' T)` (the component of `∞`). -/
theorem u6h_exteriorRegion_eq' {P : LabelledTuple n} (H : Plane ≃ₜ Plane) (T : Triangle)
    (hb : H '' frontier T.carrier = embeddedPolygonImage P) :
    exteriorRegion P = (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ := by
  obtain ⟨hS, hIo, hEo, -, hEc, hdisj, hinf⟩ := u6h_sphere_split H T hb
  show connectedComponentIn (sphereComplement P) ∞ = _
  have hinfS : ∞ ∈ sphereComplement P := by rw [hS]; exact Or.inr hinf
  have hsub : connectedComponentIn (sphereComplement P) ∞ ⊆
      ((↑) : Plane → Sphere) '' (H '' interior T.carrier) ∪
        (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ := by
    rw [← hS]; exact connectedComponentIn_subset _ _
  have hEsub : (((↑) : Plane → Sphere) '' (H '' T.carrier))ᶜ ⊆ sphereComplement P := by
    rw [hS]; exact subset_union_right
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_right_of_subset_union hIo hEo hdisj hsub
      ⟨∞, mem_connectedComponentIn hinfS, hinf⟩
  · exact hEc.isPreconnected.subset_connectedComponentIn hinf hEsub

/-- The interior region is `coe '' (H '' int T)`. -/
theorem u6h_interiorRegion_eq' {P : LabelledTuple n} (H : Plane ≃ₜ Plane) (T : Triangle)
    (hb : H '' frontier T.carrier = embeddedPolygonImage P) :
    interiorRegion P = ((↑) : Plane → Sphere) '' (H '' interior T.carrier) := by
  obtain ⟨hS, -, -, -, -, hdisj, -⟩ := u6h_sphere_split H T hb
  show sphereComplement P \ exteriorRegion P = _
  rw [u6h_exteriorRegion_eq' H T hb, hS, union_sdiff_right, hdisj.sdiff_eq_left]

/-- The ear induction (sm-3:437-443): for every embedded polygon with `m + 3` vertices inside `Q_L`
there are a base triangle `T₀ ⊆ int Q_L` and a positive PL homeomorphism `H` of the plane, the
identity outside `int Q_L`, PL on a triangulation of `Q_L` and on one of `T₀`, carrying `T₀` onto
the canonical region `u4h_regionOf P`.  Step: `u4h_exists_convex_ear` chooses a convex vertex-empty
ear `j`, the induction hypothesis parametrises the region of `deleteVertex P j`, and the ear-cut
homeomorphism `U5_exists_ear_homeo` (with `hcut` from `u4h_regionOf_ear`) is composed on top. -/
theorem u6h_ambient_induction (m : ℕ) : ∀ (P : LabelledTuple (m + 3)), Embedded P →
    ∀ (L : ℝ), InsideModel L P →
    ∃ (T₀ : Triangle) (H : Plane ≃ₜ Plane) (K : Triangulation (square L))
      (KT : Triangulation T₀.carrier),
      IsPositivePLOn H K ∧ IsPositivePLOn H KT ∧ (∀ x, L ≤ supNorm x → H x = x) ∧
      T₀.carrier ⊆ interior (square L) ∧ H '' T₀.carrier = u4h_regionOf P := by
  induction m with
  | zero =>
    intro P hP L hL
    have hdet : det (P 1 - P 0) (P 2 - P 0) ≠ 0 := (U4_triangle_base P hP).1
    have hdet' : det (P 1 - P (1 - 1)) (P (1 + 1) - P (1 - 1)) ≠ 0 := by
      rw [sub_self, one_add_one_eq_two]; exact hdet
    obtain ⟨TT, k, hcar, -, -⟩ := u4h_ear_triangle P 1 hdet'
    have hL0 : 0 < L := (u4h_polygonImage_subset_interior_square P hL).2
    obtain ⟨K⟩ := U2_triangulation_square hL0
    obtain ⟨KT⟩ := U2_triangulation_triangle TT
    have hreg : u4h_regionOf P = earHull P 1 := u4h_regionOf_triangle P hP
    refine ⟨TT, Homeomorph.refl Plane, K, KT, u6h_isPositivePLOn_refl K, u6h_isPositivePLOn_refl KT,
      fun x _ => rfl, ?_, ?_⟩
    · rw [hcar, ← hreg]
      exact (u4h_regionOf_spec (by omega) P hP).2.2.2 L hL
    · have e : ⇑(Homeomorph.refl Plane) = id := rfl
      rw [e, image_id, hcar, hreg]
  | succ m ih =>
    intro P hP L hL
    have hn2 : 2 ≤ m + 2 := by omega
    obtain ⟨j, hdet, hV, hconv⟩ := u4h_exists_convex_ear (n' := m + 2) hn2 hP
    have h4 : 4 ≤ m + 1 + 3 := by omega
    have hstrict := u4h_strict_ear_of_vertex_empty hP h4 hdet hV
    have hac := u4h_ends_ne_of_det hdet
    have hP' : Embedded (deleteVertex P j) :=
      u4h_embedded_deleteVertex (n := m + 3) (by omega) hP hac hstrict
    have hL' : InsideModel L (deleteVertex P j) := fun i => hL _
    obtain ⟨T₀, H, K, KT, pl, plT, fix, inside, himg⟩ := ih (deleteVertex P j) hP' L hL'
    obtain ⟨hcut, hunion⟩ := u4h_regionOf_ear (n' := m + 2) hn2 hP hdet hV hconv
    obtain ⟨K', hU', hedge, huniq, hsq⟩ :=
      u4h_U4_exists_triangulation (n := m + 3) (by omega) (deleteVertex P j) hP'
    have hear := u4h_earHull_inter_polygonImage_delete hP hstrict
    have hedge' : ∀ T ∈ K'.faces, ∀ T' ∈ K'.faces,
        segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T.carrier →
        segment ℝ (P (j - 1)) (P (j + 1)) ⊆ T'.carrier → T.carrier = T'.carrier := by
      rw [← u4h_edgeSegment_deleteVertex_last P j]; exact huniq (-1)
    have hface : ∃ T ∈ K'.faces, ∃ k : Fin 3, T.edgeSeg k = segment ℝ (P (j - 1)) (P (j + 1)) := by
      rw [← u4h_edgeSegment_deleteVertex_last P j]; exact hedge (-1)
    obtain ⟨h, Kh, Kin, plh, plin, -, fixh, hhU, -, -, -⟩ :=
      U5_exists_ear_homeo (n := m + 3) (by omega) P hP j hP' hdet hear _ K' hU' hcut hedge' hface
        hL (hsq L hL')
    have hHsq : H '' square L ⊆ square L := u6h_image_square_subset H fix
    obtain ⟨K'', -, pl''⟩ := U3_isPositivePLOn_comp K Kh pl plh hHsq
    have hHT : H '' T₀.carrier ⊆ u4h_regionOf (deleteVertex P j) := himg.le
    obtain ⟨KT'', -, plT''⟩ := U3_isPositivePLOn_comp KT Kin plT plin hHT
    refine ⟨T₀, H.trans h, K'', KT'', ?_, ?_, ?_, inside, ?_⟩
    · exact pl''
    · exact plT''
    · intro x hx
      rw [Homeomorph.trans_apply, fix x hx, fixh x hx]
    · have e : ⇑(H.trans h) = ⇑h ∘ ⇑H := rfl
      rw [e, image_comp, himg, hhU, hunion]

/-- The ear induction for a polygon with `n ≥ 3` vertices. -/
theorem u6h_exists_ambient_aux [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (L : ℝ) (hL : InsideModel L P) :
    ∃ (T₀ : Triangle) (H : Plane ≃ₜ Plane) (K : Triangulation (square L))
      (KT : Triangulation T₀.carrier),
      IsPositivePLOn H K ∧ IsPositivePLOn H KT ∧ (∀ x, L ≤ supNorm x → H x = x) ∧
      T₀.carrier ⊆ interior (square L) ∧ H '' T₀.carrier = u4h_regionOf P := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact u6h_ambient_induction m P hP L hL

/-- U6 (sm-3:437-443, the ear induction assembled): every embedded polygon inside `Q_L` has an
ambient parametrisation. -/
theorem U6_exists_ambientParam [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : Nonempty (AmbientParam P L) := by
  obtain ⟨T₀, H, K, KT, pl, plT, fix, inside, himg⟩ := u6h_exists_ambient_aux hn P hP L hL
  exact ⟨⟨T₀, H, K, KT, pl, plT, fix, inside, by
    rw [Homeomorph.image_frontier, himg, (u4h_regionOf_spec hn P hP).1]⟩⟩

/-- U6: the complement of the frontier of a triangle has exactly the two components `int T₀`, `T₀ᶜ`. -/
theorem U6_compl_frontier_triangle (T : Triangle) :
    (frontier T.carrier)ᶜ = interior T.carrier ∪ (T.carrier)ᶜ ∧
      IsConnected (interior T.carrier) ∧ IsConnected (T.carrier)ᶜ ∧
      Disjoint (interior T.carrier) (T.carrier)ᶜ := by
  exact u6h_compl_frontier_triangle T

/-- U6 (sm-3:486-489 "the region of the point at infinity"): the exterior region is the image of
the complement of the base triangle together with `∞`. -/
theorem U6_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    exteriorRegion P = ((↑) : Plane → Sphere) '' (A.H '' (A.T₀.carrier)ᶜ) ∪ {∞} := by
  rw [u6h_exteriorRegion_eq' A.H A.T₀ A.boundary, u6h_compl_image_coe, image_compl_eq A.H.bijective]

/-- U6: the interior region is the image of the open base triangle. -/
theorem U6_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) {L : ℝ}
    (A : AmbientParam P L) :
    interiorRegion P = ((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier) := by
  exact u6h_interiorRegion_eq' A.H A.T₀ A.boundary

/-- U6: the interior region is open and connected in the sphere. -/
theorem U6_interiorRegion_isConnected [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsConnected (interiorRegion P) ∧ IsOpen (interiorRegion P) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  obtain ⟨-, hIo, -, hIc, -, -, -⟩ := u6h_sphere_split A.H A.T₀ A.boundary
  rw [U6_interiorRegion_eq hn P hP A]
  exact ⟨hIc, hIo⟩

/-- U6 (57a, sm-3:430-431 / 486-489): exactly two complementary regions in the sphere. -/
theorem U6_two_regions [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents (sphereComplement P)) = 2 := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  obtain ⟨hS, hIo, hEo, hIc, hEc, hdisj, -⟩ := u6h_sphere_split A.H A.T₀ A.boundary
  exact u6h_card_connectedComponents_two hIo hEo hIc hEc hdisj hS.symm

/-- U6 (57e, sm-3:434 / 448-456): the region of `∞` is the unbounded one, the other is a bounded
plane region. -/
theorem U6_exterior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ∞ ∈ exteriorRegion P ∧ (∀ z ∈ interiorRegion P, z ≠ ∞) ∧
      Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' interiorRegion P) ∧
      ¬ Bornology.IsBounded (((↑) : Plane → Sphere) ⁻¹' exteriorRegion P) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  have hK : IsCompact (A.H '' A.T₀.carrier) := (U1_triangle_isCompact _).image A.H.continuous
  have hext := u6h_exteriorRegion_eq' A.H A.T₀ A.boundary
  have hint := U6_interiorRegion_eq hn P hP A
  have hinf : ∞ ∈ exteriorRegion P := by rw [hext]; exact u6h_infty_notMem_image _
  refine ⟨hinf, ?_, ?_, ?_⟩
  · intro z hz hzinf
    exact hz.2 (hzinf ▸ hinf)
  · rw [hint, u6h_coe_preimage_image]
    exact hK.isBounded.subset (image_mono interior_subset)
  · rw [hext, preimage_compl, u6h_coe_preimage_image]
    exact u6h_not_isBounded_compl hK

/-- U6 (bridge, plane form of 57a): the exterior region minus `∞` stays connected. -/
theorem U6_two_regions_plane [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    Nat.card (ConnectedComponents ((embeddedPolygonImage P)ᶜ : Set Plane)) = 2 := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  obtain ⟨hcpl, hIo, hEo, hIc, hEc, hdisj, -⟩ := u6h_plane_split A.H A.T₀ A.boundary
  exact u6h_card_connectedComponents_two hIo hEo hIc hEc hdisj hcpl.symm

/-- The circle lies in the closure of each of the two regions (optional interface for U11: it
follows from `U6_interiorRegion_eq` / `U6_exteriorRegion_eq` alone, without U7/U8). -/
theorem u6h_sphereCircle_subset_closure_regionOf [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (s : Side) : sphereCircle P ⊆ closure (regionOf P s) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  have hfr : ((↑) : Plane → Sphere) '' (A.H '' frontier A.T₀.carrier) = sphereCircle P := by
    rw [A.boundary]; rfl
  have h3 : ∀ S : Set Plane, ((↑) : Plane → Sphere) '' closure S ⊆ closure (((↑) : Plane → Sphere) '' S) :=
    fun S => image_closure_subset_closure_image OnePoint.continuous_coe
  cases s with
  | inner =>
    show sphereCircle P ⊆ closure (interiorRegion P)
    rw [U6_interiorRegion_eq hn P hP A, ← hfr]
    have h1 : frontier A.T₀.carrier ⊆ closure (interior A.T₀.carrier) := by
      rw [(U1_triangle_convex A.T₀).closure_interior_eq_closure_of_nonempty_interior
        (U1_triangle_interior_nonempty _)]
      exact frontier_subset_closure
    have h2 : A.H '' closure (interior A.T₀.carrier) ⊆ closure (A.H '' interior A.T₀.carrier) :=
      image_closure_subset_closure_image A.H.continuous
    exact (image_mono (image_mono h1)).trans ((image_mono h2).trans (h3 _))
  | outer =>
    show sphereCircle P ⊆ closure (exteriorRegion P)
    rw [U6_exteriorRegion_eq hn P hP A, ← hfr]
    have h1 : frontier A.T₀.carrier ⊆ closure (A.T₀.carrier)ᶜ := by
      rw [← frontier_compl]; exact frontier_subset_closure
    have h2 : A.H '' closure (A.T₀.carrier)ᶜ ⊆ closure (A.H '' (A.T₀.carrier)ᶜ) :=
      image_closure_subset_closure_image A.H.continuous
    exact ((image_mono (image_mono h1)).trans ((image_mono h2).trans (h3 _))).trans
      (closure_mono subset_union_left)

/-! ### U7 (sequential) — 57b for the interior region -/

/-! ### U7 helpers (`u7h_`), 2026-09-19 (W2_U7): the closed bounded region `closure (interiorRegion P)` is
`coe '' (H (T₀))` (from the U6 black box `U6_interiorRegion_eq`, `H` a homeomorphism, `T₀` convex with nonempty
interior); `H (T₀)` lies strictly inside `Q_L` (`A.inside`, `A.fix`, injectivity), so its cap chart part is empty
(`u3h_seam`) and its plane chart part is `H (T₀)` itself, on which `H⁻¹` is positive PL by `U2_inverse_isPositivePLOn`.
The bridge `U7_isPLDisc_of_isPLDiscSphere` inverts the parametrisation with `U3_isPositivePLFromPlane_inv` and rules
out cap-chart faces (a nondegenerate triangle cannot lie in the seam).  Report: W2_U7_REPORT.md. -/

/-- U7 helper: `H (T₀)` lies strictly inside `Q_L` (`A.inside`, `A.fix`, injectivity of `H`). -/
theorem u7h_supNorm_lt_of_mem_image [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L)
    {w : Plane} (hw : w ∈ A.H '' A.T₀.carrier) : supNorm w < L := by
  obtain ⟨x, hx, rfl⟩ := hw
  have hxL : supNorm x < L := u3h_interior_square_subset L (A.inside hx)
  by_contra hcon
  have hcon : L ≤ supNorm (A.H x) := not_lt.1 hcon
  have h1 : A.H (A.H x) = A.H x := A.fix _ hcon
  have h2 : A.H x = x := A.H.injective h1
  rw [h2] at hcon
  exact absurd hxL (not_lt.2 hcon)

/-- U7 helper: `H (T₀)` lies in `Q_L`. -/
theorem u7h_image_subset_square [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    A.H '' A.T₀.carrier ⊆ square L :=
  fun _ hw => (u7h_supNorm_lt_of_mem_image A hw).le

/-- U7 helper: `H (T₀)` is compact. -/
theorem u7h_image_isCompact [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    IsCompact (A.H '' A.T₀.carrier) :=
  (U1_triangle_isCompact A.T₀).image A.H.continuous

/-- U7 helper: the closure of the open triangle is the triangle. -/
theorem u7h_closure_interior_triangle (T : Triangle) : closure (interior T.carrier) = T.carrier := by
  rw [(U1_triangle_convex T).closure_interior_eq_closure_of_nonempty_interior
    (U1_triangle_interior_nonempty T)]
  exact (U1_triangle_isCompact T).isClosed.closure_eq

/-- U7 helper: closure of `H (int T₀)` is `H (T₀)`. -/
theorem u7h_closure_image_interior [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    closure (A.H '' interior A.T₀.carrier) = A.H '' A.T₀.carrier := by
  rw [← A.H.image_closure, u7h_closure_interior_triangle]

/-- U7 helper: the closure in the sphere of the coercion image of `H (int T₀)`. -/
theorem u7h_closure_coe_image [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    closure (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier)) =
      ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact image_mono (image_mono interior_subset)
    · exact isClosed_image_coe.2 ⟨(u7h_image_isCompact A).isClosed, u7h_image_isCompact A⟩
  · rw [← u7h_closure_image_interior A]
    exact image_closure_subset_closure_image continuous_coe

/-- U7: the closed bounded region is `H (T₀)`. -/
theorem U7_closure_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (interiorRegion P) = ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := by
  rw [U6_interiorRegion_eq hn P hP A]
  exact u7h_closure_coe_image A

/-- U7 (sm-3:490-493, the interior disc): `H (T₀)` is a plane PL disc. -/
theorem U7_isPLDisc_image [NeZero n] (P : LabelledTuple n) {L : ℝ} (A : AmbientParam P L) :
    IsPLDisc (A.H '' A.T₀.carrier) := by
  exact ⟨A.T₀.carrier, A.KT, A.H, U1_triangle_isDisc A.T₀, A.plT, U1_isHomeoOnto_of_homeomorph A.H _⟩

/-- U7 helper: the plane chart part of `coe '' (H (T₀))` is `H (T₀)`. -/
theorem u7h_chartPart_plane [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    chartPart L false (((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier)) = A.H '' A.T₀.carrier := by
  ext w
  constructor
  · rintro ⟨-, hw⟩
    obtain ⟨v, hv, hvw⟩ : ((w : Plane) : Sphere) ∈ ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := hw
    rw [coe_injective hvw] at hv
    exact hv
  · intro hw
    exact ⟨u7h_image_subset_square A hw, ⟨w, hw, rfl⟩⟩

/-- U7 helper: the cap chart part of `coe '' (H (T₀))` is empty (`H (T₀)` lies strictly inside
`Q_L`, the cap chart covers only `‖x‖_∞ ≥ L`). -/
theorem u7h_chartPart_cap [NeZero n] {P : LabelledTuple n} {L : ℝ} (hL : 0 < L) (A : AmbientParam P L) :
    chartPart L true (((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier)) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro y ⟨hy1, hy⟩
  obtain ⟨w, hw, hwy⟩ : capChart L y ∈ ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := hy
  have hwL : w ∈ square L := u7h_image_subset_square A hw
  have hs := u3h_seam hL hwL hy1 hwy
  exact absurd (u7h_supNorm_lt_of_mem_image A hw) (not_lt.2 hs.2.2.1.ge)

/-- U7: the cap chart sees nothing of the closed bounded region. -/
theorem U7_chartPart_cap_empty [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) : chartPart L true (closure (interiorRegion P)) = ∅ := by
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  rw [U7_closure_interiorRegion_eq hn P hP A]
  exact u7h_chartPart_cap (U4_polygonImage_subset_interior_square P hL).2 A

/-- U7 helper: a triangulation of the empty set has no faces, so every map is positive PL on it. -/
theorem u7h_isPositivePLOn_empty (K : Triangulation (∅ : Set Plane)) (f : Plane → Plane) :
    IsPositivePLOn f K := by
  intro T hT
  exact absurd (u2h_carrier_subset K hT (subset_convexHull ℝ _ ⟨0, rfl⟩)) (notMem_empty _)

/-- U7 helper: `H⁻¹ ∘ planeOf` read in the plane chart is `H⁻¹`. -/
theorem u7h_inv_comp_plane_chart [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    (A.H.symm ∘ planeOf) ∘ modelChart L false = A.H.symm := by
  funext x; rfl

/-- U7: `planeOf ∘ H⁻¹` is positive PL to the plane on the closed bounded region. -/
theorem U7_isPositivePLToPlane_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLToPlane L (closure (interiorRegion P)) (A.H.symm ∘ planeOf) := by
  have hL0 : 0 < L := (U4_polygonImage_subset_interior_square P hL).2
  rw [U7_closure_interiorRegion_eq hn P hP A]
  intro b
  cases b
  · rw [u7h_chartPart_plane A, u7h_inv_comp_plane_chart A]
    exact U2_inverse_isPositivePLOn A.KT A.H A.plT
  · rw [u7h_chartPart_cap hL0 A]
    obtain ⟨K⟩ := U2_triangulation_empty
    exact ⟨K, u7h_isPositivePLOn_empty K _⟩

/-- U7 helper: `H⁻¹ ∘ planeOf` is a homeomorphism of `coe '' (H (T₀))` onto `T₀`. -/
theorem u7h_isHomeoOnto_inv [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    IsHomeoOnto (((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier)) A.T₀.carrier
      (A.H.symm ∘ planeOf) := by
  have h2 : IsHomeoOnto (((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier)) (A.H '' A.T₀.carrier)
      planeOf :=
    U1_isHomeoOnto_inv (U1_isHomeoOnto_coe _) (fun x _ => rfl)
  have h4 : IsHomeoOnto (A.H '' A.T₀.carrier) A.T₀.carrier A.H.symm :=
    U1_isHomeoOnto_inv (U1_isHomeoOnto_of_homeomorph A.H _) (fun x _ => A.H.symm_apply_apply x)
  exact U1_isHomeoOnto_comp h2 h4

/-- U7 helper: `H⁻¹ ∘ planeOf` carries the circle onto `∂T₀`. -/
theorem u7h_image_circle [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    (A.H.symm ∘ planeOf) '' sphereCircle P = frontier A.T₀.carrier := by
  rw [sphereCircle, ← A.boundary, image_image, image_image]
  have : (fun x => (A.H.symm ∘ planeOf) ((A.H x : Plane) : Sphere)) = id := by
    funext x
    show A.H.symm (A.H x) = x
    exact A.H.symm_apply_apply x
  rw [this, image_id]

/-- U7 helper: the circle lies in `coe '' (H (T₀))`. -/
theorem u7h_circle_subset [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    sphereCircle P ⊆ ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) := by
  rw [sphereCircle, ← A.boundary]
  exact image_mono (image_mono (U1_triangle_isCompact A.T₀).isClosed.frontier_subset)

/-- U7 (57b interior, sm-3:431 / 490-493): the closure of the bounded region is a PL disc of the
sphere with boundary the circle. -/
theorem U7_pl_discs_inner [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.inner)) (sphereCircle P) := by
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  have hcl : closure (regionOf P Side.inner) = ((↑) : Plane → Sphere) '' (A.H '' A.T₀.carrier) :=
    U7_closure_interiorRegion_eq hn P hP A
  refine ⟨A.T₀.carrier, A.H.symm ∘ planeOf, U1_triangle_isDisc A.T₀, ?_, ?_, u7h_image_circle A, ?_⟩
  · rw [hcl]; exact u7h_circle_subset A
  · rw [hcl]; exact u7h_isHomeoOnto_inv A
  · exact U7_isPositivePLToPlane_inv hn P hP hL A

/-- U7 helper: a nondegenerate triangle cannot lie in the seam `‖y‖_∞ = 1`. -/
theorem u7h_not_subset_seam (T : Triangle) (h : ∀ y ∈ T.carrier, supNorm y = 1) : False := by
  obtain ⟨c, hc⟩ := U1_triangle_interior_nonempty T
  have hsub : T.carrier ⊆ square 1 := fun y hy => (h y hy).le
  have hlt : supNorm c < 1 := u3h_interior_square_subset 1 (interior_mono hsub hc)
  exact absurd (h c (interior_subset hc)) hlt.ne

/-- U7 (bridge): a sphere PL disc lying in the plane chart is a plane PL disc. -/
theorem U7_isPLDisc_of_isPLDiscSphere {L : ℝ} {S B : Set Sphere} (hL : 0 < L)
    (hS : S ⊆ ((↑) : Plane → Sphere) '' square L) (h : IsPLDiscSphere L S B) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' S) := by
  obtain ⟨D, f, hD, -, hf, -, hpl⟩ := h
  obtain ⟨g, ⟨K, hK⟩, hgf, hfg⟩ := U3_isPositivePLFromPlane_inv hL hD hf hpl
  have hfS : f '' S = D := u1h_isHomeoOnto_image hf
  have hgS : ∀ x ∈ D, g x ∈ S := by
    intro x hx
    rw [← hfS] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [hgf z hz]; exact hz
  have hSr : S ⊆ range ((↑) : Plane → Sphere) := hS.trans (image_subset_range _ _)
  refine ⟨D, K, planeOf ∘ g, hD, ?_, ?_⟩
  · intro T hT
    obtain ⟨b', hmem, haff⟩ := hK T hT
    cases b' with
    | false => exact haff
    | true =>
      exfalso
      apply u7h_not_subset_seam (T.map _ haff)
      intro y hy
      rw [u2h_map_carrier haff] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxD : x ∈ D := u2h_carrier_subset K hT hx
      obtain ⟨y₁, hy₁, hy₁x⟩ := hmem x hx
      obtain ⟨w, hw, hwx⟩ := hS (hgS x hxD)
      have hs := u3h_seam hL hw hy₁ (hwx.trans hy₁x.symm)
      show supNorm (modelChartInv L true (g x)) = 1
      rw [← hwx]
      show supNorm (capInvFun L w) = 1
      rw [hs.2.1, u3h_capInvFun_capInvFun hL.ne' hs.1]
      exact hs.2.2.2
  · have h1 : IsHomeoOnto (((↑) : Plane → Sphere) ⁻¹' S) S ((↑) : Plane → Sphere) := by
      have := U1_isHomeoOnto_coe (((↑) : Plane → Sphere) ⁻¹' S)
      rwa [image_preimage_eq_of_subset hSr] at this
    have h2 : IsHomeoOnto (((↑) : Plane → Sphere) ⁻¹' S) D (f ∘ (↑)) := U1_isHomeoOnto_comp h1 hf
    refine U1_isHomeoOnto_inv h2 (fun x hx => ?_)
    show planeOf (g (f (x : Sphere))) = x
    rw [hgf _ hx]; rfl

/-- U7 (bridge): the closed bounded region, as a plane set, is a plane PL disc. -/
theorem U7_isPLDisc_closure_interior [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    IsPLDisc (((↑) : Plane → Sphere) ⁻¹' closure (interiorRegion P)) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  rw [U7_closure_interiorRegion_eq hn P hP A, preimage_image_eq _ coe_injective]
  exact U7_isPLDisc_image P A

/-! ### U8 (sequential) — 57b for the exterior region -/

/-! ### U8 helpers (`u8h_`), 2026-09-19: continuity of the cap chart and its inverse -/

theorem u8h_continuous_supNorm : Continuous supNorm := by
  unfold supNorm; fun_prop

theorem u8h_mem_interior_square_iff {L : ℝ} (x : Plane) : x ∈ interior (square L) ↔ supNorm x < L := by
  constructor
  · exact fun h => u3h_interior_square_subset L h
  · intro h
    exact interior_maximal (t := {y : Plane | supNorm y < L}) (fun y (hy : supNorm y < L) => le_of_lt hy)
      (isOpen_lt u8h_continuous_supNorm continuous_const) h

/-- U8 helper: `capInvFun L` is continuous away from `0`. -/
theorem u8h_continuousAt_capInvFun (L : ℝ) {y : Plane} (hy : y ≠ 0) :
    ContinuousAt (capInvFun L) y := by
  have hN : supNorm y ≠ 0 := (u3h_supNorm_pos hy).ne'
  unfold capInvFun
  refine ContinuousAt.smul (f := fun y : Plane => L / supNorm y ^ 2)
    (g := fun y : Plane => ((y.1, -y.2) : Plane)) ?_ ?_
  · apply ContinuousAt.div continuousAt_const
    · exact (u8h_continuous_supNorm.pow 2).continuousAt
    · exact pow_ne_zero 2 hN
  · fun_prop

/-- U8 helper: a plane set of bounded sup norm. -/
theorem u8h_isCompact_supNorm_le {s : Set Plane} (hs : IsCompact s) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ s, supNorm x ≤ R := by
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have := hR hx
  rw [Metric.mem_closedBall, dist_zero_right, u3h_norm_eq_supNorm] at this
  exact this.trans (le_max_left _ _)

/-- U8 helper: `capInvFun L` tends to `0` at infinity. -/
theorem u8h_tendsto_capInvFun_cocompact {L : ℝ} (hL : 0 < L) :
    Filter.Tendsto (capInvFun L) (Filter.coclosedCompact Plane) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_iff, Filter.hasBasis_coclosedCompact.mem_iff]
  refine ⟨{x | supNorm x ≤ L / ε}, ⟨?_, ?_⟩, ?_⟩
  · exact isClosed_le u8h_continuous_supNorm continuous_const
  · have : {x : Plane | supNorm x ≤ L / ε} = Metric.closedBall 0 (L / ε) := by
      ext x; simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, u3h_norm_eq_supNorm]
    rw [this]; exact isCompact_closedBall _ _
  · intro x hx
    simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp only [supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
      have : 0 < L / ε := div_pos hL hε
      linarith
    simp only [mem_ofPred_eq, dist_zero_right, u3h_norm_eq_supNorm]
    rw [u3h_supNorm_capInvFun hL hx0]
    have hN := u3h_supNorm_pos hx0
    rw [div_lt_iff₀ hN]
    rw [div_lt_iff₀ hε] at hx
    linarith

/-- U8 helper: the cap inverse chart is continuous on the whole sphere. -/
theorem u8h_continuous_capInv {L : ℝ} (hL : 0 < L) :
    ∀ z : Sphere, z ≠ (0 : Plane) → ContinuousAt (modelChartInv L true) z := by
  intro z hz
  induction z using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty']
    show Filter.Tendsto (fun x : Plane => capInvFun L x) _ (nhds 0)
    exact u8h_tendsto_capInvFun_cocompact hL
  | coe x =>
    rw [OnePoint.continuousAt_coe]
    show ContinuousAt (fun x : Plane => capInvFun L x) x
    exact u8h_continuousAt_capInvFun L (fun h => hz (by rw [h]))


/-- U8 helper: `capChart L` is continuous on `Q_1` (at `0` it tends to `∞`). -/
theorem u8h_continuousOn_capChart {L : ℝ} (hL : 0 < L) : ContinuousOn (capChart L) (square 1) := by
  intro y hy
  by_cases hy0 : y = 0
  · subst hy0
    rw [ContinuousWithinAt, show capChart L 0 = ∞ by simp [capChart]]
    rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
    rintro s ⟨-, hsc⟩
    obtain ⟨R, hR0, hR⟩ := u8h_isCompact_supNorm_le hsc
    have hδ : 0 < L / (R + 1) := div_pos hL (by linarith)
    have hnhds : {y : Plane | supNorm y < L / (R + 1)} ∈ nhds (0 : Plane) := by
      apply (isOpen_lt u8h_continuous_supNorm continuous_const).mem_nhds
      show supNorm (0 : Plane) < L / (R + 1)
      rw [show supNorm (0 : Plane) = 0 by simp [supNorm]]
      exact hδ
    filter_upwards [nhdsWithin_le_nhds hnhds] with y hy
    by_cases h0 : y = 0
    · subst h0; simp [capChart]
    · left
      refine ⟨capInvFun L y, fun hmem => ?_, by simp [capChart, h0]⟩
      have h1 := hR _ hmem
      rw [u3h_supNorm_capInvFun hL h0] at h1
      have hN := u3h_supNorm_pos h0
      rw [div_le_iff₀ hN] at h1
      rw [lt_div_iff₀ (by linarith)] at hy
      nlinarith
  · apply ContinuousAt.continuousWithinAt
    have hev : (fun z : Plane => ((capInvFun L z : Plane) : Sphere)) =ᶠ[nhds y] capChart L := by
      filter_upwards [isOpen_ne.mem_nhds hy0] with z hz
      simp [capChart, hz]
    exact (OnePoint.continuous_coe.continuousAt.comp
      (u8h_continuousAt_capInvFun L hy0)).congr_of_eventuallyEq hev.symm

/-! ### U8 helpers: the ambient homeomorphism on the square, `OnePoint.map`, transport of triangulations -/

/-- U8 helper: `H` maps the open square `int Q_L` onto itself (it is the identity outside). -/
theorem u8h_H_image_interior [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    A.H '' interior (square L) = interior (square L) := by
  have key : ∀ x, supNorm x < L → supNorm (A.H x) < L := by
    intro x hx
    by_contra h
    push Not at h
    have h2 : A.H (A.H x) = A.H x := A.fix _ h
    have h3 := A.H.injective h2
    rw [h3] at h
    linarith
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (u8h_mem_interior_square_iff _).2 (key x ((u8h_mem_interior_square_iff x).1 hx))
  · intro hy
    refine ⟨A.H.symm y, ?_, A.H.apply_symm_apply y⟩
    rw [u8h_mem_interior_square_iff]
    by_contra h
    push Not at h
    have := A.fix _ h
    rw [A.H.apply_symm_apply] at this
    have hy' := (u8h_mem_interior_square_iff y).1 hy
    rw [← this] at h
    linarith

theorem u8h_H_symm_fix [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) {x : Plane}
    (hx : L ≤ supNorm x) : A.H.symm x = x := by
  have := A.fix x hx
  rw [← this, A.H.symm_apply_apply, this]

theorem u8h_H_image_square [NeZero n] {P : LabelledTuple n} {L : ℝ} (A : AmbientParam P L) :
    A.H '' square L = square L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases h : supNorm x < L
    · have := (u8h_mem_interior_square_iff x).2 h
      have h2 : A.H x ∈ interior (square L) := by
        rw [← u8h_H_image_interior A]; exact ⟨x, this, rfl⟩
      exact interior_subset h2
    · push Not at h
      rw [A.fix x h]; exact hx
  · intro hy
    by_cases h : supNorm y < L
    · have := (u8h_mem_interior_square_iff y).2 h
      rw [← u8h_H_image_interior A] at this
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, interior_subset hx, rfl⟩
    · push Not at h
      exact ⟨y, hy, A.fix y h⟩

/-- U8 helper: `OnePoint.map` of a plane homeomorphism is a homeomorphism of the sphere. -/
theorem u8h_isHomeoOnto_onePoint_map (e : Plane ≃ₜ Plane) (S : Set Sphere) :
    IsHomeoOnto S (OnePoint.map e '' S) (OnePoint.map e) :=
  ⟨(Homeomorph.onePointCongr e).image S, fun _ => rfl⟩

theorem u8h_onePoint_map_bijective (e : Plane ≃ₜ Plane) : Function.Bijective (OnePoint.map e) :=
  (Homeomorph.onePointCongr e).bijective

theorem u8h_onePoint_map_image_coe (e : Plane ≃ₜ Plane) (S : Set Plane) :
    OnePoint.map e '' (((↑) : Plane → Sphere) '' S) = ((↑) : Plane → Sphere) '' (e '' S) := by
  ext z; constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨(x : Sphere), ⟨x, hx, rfl⟩, rfl⟩

/-! ### U8 helpers (`u8h_f_`): the fan toolkit of U10 (`u10h_rg … u10h_fan_triangulation`, `u10h_gap …
u10h_cover`), copied verbatim with the prefix `u10h_` → `u8h_f_` because U8 precedes U10 in the file
(W2_U8_REPORT.md §4; U12 may dedupe by moving U10's block before U8). -/

/-! #### U10 helpers for `U10_fan_extension` (radial gauge, sectors, marks, fan, cone) -/

/-- U10 helper: the translate of `D` bringing `z` to the origin. -/
def u8h_f_D0 (D : Set Plane) (z : Plane) : Set Plane := (Homeomorph.addRight z) ⁻¹' D

/-- U10 helper: the radial gauge of `D` about `z`. -/
noncomputable def u8h_f_rg (D : Set Plane) (z : Plane) (x : Plane) : ℝ := gauge (u8h_f_D0 D z) (x - z)

theorem u8h_f_mem_D0 {D : Set Plane} {z w : Plane} : w ∈ u8h_f_D0 D z ↔ w + z ∈ D := Iff.rfl

theorem u8h_f_D0_convex {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : Convex ℝ (u8h_f_D0 D z) := by
  have h : u8h_f_D0 D z = (fun x => x + z) ⁻¹' D := by ext w; simp [u8h_f_D0]
  rw [h]; exact hD.convex.translate_preimage_left z

theorem u8h_f_D0_isCompact {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : IsCompact (u8h_f_D0 D z) :=
  (Homeomorph.addRight z).isCompact_preimage.mpr hD.isCompact

theorem u8h_f_D0_interior {D : Set Plane} (z : Plane) :
    interior (u8h_f_D0 D z) = (Homeomorph.addRight z) ⁻¹' interior D :=
  ((Homeomorph.addRight z).preimage_interior D).symm

theorem u8h_f_D0_frontier {D : Set Plane} (z : Plane) :
    frontier (u8h_f_D0 D z) = (Homeomorph.addRight z) ⁻¹' frontier D :=
  ((Homeomorph.addRight z).preimage_frontier D).symm

theorem u8h_f_D0_closure {D : Set Plane} (z : Plane) :
    closure (u8h_f_D0 D z) = (Homeomorph.addRight z) ⁻¹' closure D :=
  ((Homeomorph.addRight z).preimage_closure D).symm

theorem u8h_f_D0_nhds {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : u8h_f_D0 D z ∈ nhds (0 : Plane) := by
  rw [mem_nhds_iff]
  refine ⟨interior (u8h_f_D0 D z), interior_subset, isOpen_interior, ?_⟩
  rw [u8h_f_D0_interior]
  simpa using hz

theorem u8h_f_D0_absorbent {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : Absorbent ℝ (u8h_f_D0 D z) :=
  absorbent_nhds_zero (u8h_f_D0_nhds hz)

theorem u8h_f_D0_bounded {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) :
    Bornology.IsVonNBounded ℝ (u8h_f_D0 D z) :=
  (u8h_f_D0_isCompact hD z).isVonNBounded ℝ

theorem u8h_f_rg_nonneg (D : Set Plane) (z x : Plane) : 0 ≤ u8h_f_rg D z x := gauge_nonneg _

theorem u8h_f_rg_lt_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x < 1 ↔ x ∈ interior D := by
  unfold u8h_f_rg
  rw [gauge_lt_one_iff_mem_interior (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz), u8h_f_D0_interior]
  simp

theorem u8h_f_rg_le_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x ≤ 1 ↔ x ∈ D := by
  unfold u8h_f_rg
  rw [gauge_le_one_iff_mem_closure (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz), u8h_f_D0_closure,
    hD.isCompact.isClosed.closure_eq]
  simp

theorem u8h_f_rg_eq_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x = 1 ↔ x ∈ frontier D := by
  unfold u8h_f_rg
  rw [gauge_eq_one_iff_mem_frontier (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz), u8h_f_D0_frontier]
  simp

theorem u8h_f_rg_eq_zero_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u8h_f_rg D z x = 0 ↔ x = z := by
  unfold u8h_f_rg
  rw [gauge_eq_zero (u8h_f_D0_absorbent hz) (u8h_f_D0_bounded hD z), sub_eq_zero]

theorem u8h_f_rg_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) {x : Plane}
    (hx : x ≠ z) : 0 < u8h_f_rg D z x :=
  lt_of_le_of_ne (u8h_f_rg_nonneg D z x) (fun h => hx ((u8h_f_rg_eq_zero_iff hD hz x).mp h.symm))

theorem u8h_f_rg_self (D : Set Plane) (z : Plane) : u8h_f_rg D z z = 0 := by
  simp [u8h_f_rg, gauge_zero]

theorem u8h_f_rg_smul (D : Set Plane) (z x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    u8h_f_rg D z (z + t • (x - z)) = t * u8h_f_rg D z x := by
  unfold u8h_f_rg
  rw [add_sub_cancel_left, gauge_smul_of_nonneg ht, smul_eq_mul]

theorem u8h_f_rg_continuous {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    Continuous (u8h_f_rg D z) :=
  (continuous_gauge (u8h_f_D0_convex hD z) (u8h_f_D0_nhds hz)).comp (continuous_id.sub continuous_const)

/-- The frontier point on the ray from `z` through `x ≠ z`. -/
noncomputable def u8h_f_ray (D : Set Plane) (z x : Plane) : Plane := z + (u8h_f_rg D z x)⁻¹ • (x - z)

theorem u8h_f_ray_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : u8h_f_ray D z x ∈ frontier D := by
  rw [← u8h_f_rg_eq_one_iff hD hz, u8h_f_ray, u8h_f_rg_smul D z x (inv_nonneg.mpr (u8h_f_rg_nonneg D z x))]
  exact inv_mul_cancel₀ (u8h_f_rg_pos hD hz hx).ne'

theorem u8h_f_ray_spec {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : x = z + u8h_f_rg D z x • (u8h_f_ray D z x - z) := by
  rw [u8h_f_ray, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (u8h_f_rg_pos hD hz hx).ne', one_smul,
    add_sub_cancel]

theorem u8h_f_ray_of_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : u8h_f_ray D z y = y := by
  rw [u8h_f_ray, (u8h_f_rg_eq_one_iff hD hz y).mpr hy, inv_one, one_smul, add_sub_cancel]

theorem u8h_f_frontier_ne {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : y ≠ z := by
  intro h; subst h
  have := (u8h_f_rg_eq_one_iff hD hz y).mpr hy
  rw [u8h_f_rg_self] at this; norm_num at this

theorem u8h_f_frontier_subset {D : Set Plane} (hD : Link.IsDisc D) : frontier D ⊆ D :=
  hD.isCompact.isClosed.frontier_subset

/-! ### det algebra -/

theorem u8h_f_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u8h_f_det_smul_right (u v : Plane) (c : ℝ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u8h_f_det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u8h_f_det_smul_left' (u v : Plane) (c : ℝ) : det (c • u) v = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u8h_f_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u8h_f_det_zero_right (u : Plane) : det u 0 = 0 := by simp [det]

theorem u8h_f_det_zero_left (u : Plane) : det 0 u = 0 := by simp [det]

theorem u8h_f_det_swap' (u v : Plane) : det u v = -det v u := by simp only [det]; ring

theorem u8h_f_cramer {u v : Plane} (h : det u v ≠ 0) (w : Plane) :
    w = (det w v / det u v) • u + (det u w / det u v) • v := by
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring

theorem u8h_f_parallel_of_det_eq_zero {u v : Plane} (hu : u ≠ 0) (h : det u v = 0) :
    ∃ μ : ℝ, v = μ • u := by
  have hn : 0 < u.1 ^ 2 + u.2 ^ 2 := by
    rcases not_and_or.mp (fun hc : u.1 = 0 ∧ u.2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  refine ⟨(u.1 * v.1 + u.2 * v.2) / (u.1 ^ 2 + u.2 ^ 2), ?_⟩
  simp only [det] at h
  ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination (-u.2) * h
  · simp only [Prod.smul_snd, smul_eq_mul]
    field_simp
    linear_combination u.1 * h

/-! ### half-planes are convex -/

theorem u8h_f_convex_det_nonneg (z u : Plane) : Convex ℝ {x : Plane | 0 ≤ det u (x - z)} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det u (x - z) at hx
  change 0 ≤ det u (y - z) at hy
  change 0 ≤ det u (a • x + b • y - z)
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u8h_f_det_add_right, u8h_f_det_smul_right, u8h_f_det_smul_right]
  positivity

theorem u8h_f_convex_det_nonneg' (z v : Plane) : Convex ℝ {x : Plane | 0 ≤ det (x - z) v} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det (x - z) v at hx
  change 0 ≤ det (y - z) v at hy
  change 0 ≤ det (a • x + b • y - z) v
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u8h_f_det_add_left, u8h_f_det_smul_left', u8h_f_det_smul_left']
  positivity

/-! ### a straight frontier piece is not seen edge-on from `z` -/

theorem u8h_f_det_ne_zero_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier D) : det (a - z) (b - z) ≠ 0 := by
  intro h0
  have ha : a ∈ frontier D := hseg (left_mem_segment ℝ a b)
  have hb : b ∈ frontier D := hseg (right_mem_segment ℝ a b)
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u8h_f_frontier_ne hD hz ha)
  obtain ⟨μ, hμ⟩ := u8h_f_parallel_of_det_eq_zero haz h0
  have hb' : b = z + μ • (a - z) := by rw [← hμ]; abel
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · have h1 := (u8h_f_rg_eq_one_iff hD hz b).mpr hb
    rw [hb', u8h_f_rg_smul D z a hμ0, (u8h_f_rg_eq_one_iff hD hz a).mpr ha, mul_one] at h1
    subst h1
    apply hne; rw [hb', one_smul, add_sub_cancel]
  · have h1μ : (1 - μ) ≠ 0 := by linarith
    have hzmem : z ∈ segment ℝ a b := by
      refine ⟨-μ / (1 - μ), 1 / (1 - μ), by
        apply div_nonneg <;> linarith, by
        apply div_nonneg <;> linarith, by
        rw [← add_div, div_eq_one_iff_eq h1μ]; ring, ?_⟩
      rw [hb']
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    have := (u8h_f_rg_eq_one_iff hD hz z).mpr (hseg hzmem)
    rw [u8h_f_rg_self] at this; norm_num at this

/-! ### the sector lemma and the fan characterisation -/

/-- A frontier point in the closed sector spanned (from `z`) by a straight frontier piece `[a, b]`
lies on that piece. -/
theorem u8h_f_frontier_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {y : Plane}
    (hy : y ∈ frontier D) (h1 : 0 ≤ det (a - z) (y - z)) (h2 : 0 ≤ det (y - z) (b - z)) :
    y ∈ segment ℝ a b := by
  set β := det (y - z) (b - z) / det (a - z) (b - z) with hβ
  set γ := det (a - z) (y - z) / det (a - z) (b - z) with hγ
  have hβ0 : 0 ≤ β := div_nonneg h2 hab.le
  have hγ0 : 0 ≤ γ := div_nonneg h1 hab.le
  have hdec : y - z = β • (a - z) + γ • (b - z) := u8h_f_cramer hab.ne' (y - z)
  have hs : 0 < β + γ := by
    rcases (add_nonneg hβ0 hγ0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hβz : β = 0 := by linarith
      have hγz : γ = 0 := by linarith
      rw [hβz, hγz, zero_smul, zero_smul, add_zero] at hdec
      exact u8h_f_frontier_ne hD hz hy (sub_eq_zero.mp hdec)
  set s := β + γ with hs_def
  set w : Plane := (β / s) • a + (γ / s) • b with hw
  have hwseg : w ∈ segment ℝ a b :=
    ⟨β / s, γ / s, div_nonneg hβ0 hs.le, div_nonneg hγ0 hs.le, by rw [← add_div, div_self hs.ne'], rfl⟩
  have hyw : y = z + s • (w - z) := by
    have e1 := congrArg Prod.fst hdec
    have e2 := congrArg Prod.snd hdec
    simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.snd_add,
      Prod.smul_snd] at e1 e2
    ext
    · simp only [hw, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp
      linear_combination e1
    · simp only [hw, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      linear_combination e2
  have hrw : u8h_f_rg D z w = 1 := (u8h_f_rg_eq_one_iff hD hz w).mpr (hseg hwseg)
  have hry : u8h_f_rg D z y = 1 := (u8h_f_rg_eq_one_iff hD hz y).mpr hy
  rw [hyw, u8h_f_rg_smul D z w hs.le, hrw, mul_one] at hry
  rw [hyw, hry, one_smul, add_sub_cancel]
  exact hwseg

/-- The ray point of a point of the closed sector lies on the frontier piece. -/
theorem u8h_f_ray_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {x : Plane}
    (hxz : x ≠ z) (h1 : 0 ≤ det (a - z) (x - z)) (h2 : 0 ≤ det (x - z) (b - z)) :
    u8h_f_ray D z x ∈ segment ℝ a b := by
  have hyz : u8h_f_ray D z x - z = (u8h_f_rg D z x)⁻¹ • (x - z) := by simp [u8h_f_ray]
  have hr0 : 0 ≤ (u8h_f_rg D z x)⁻¹ := inv_nonneg.mpr (u8h_f_rg_nonneg _ _ _)
  refine u8h_f_frontier_mem_segment hD hz hab hseg (u8h_f_ray_mem_frontier hD hz hxz) ?_ ?_
  · rw [hyz, u8h_f_det_smul_right]; exact mul_nonneg hr0 h1
  · rw [hyz, u8h_f_det_smul_left']; exact mul_nonneg hr0 h2

/-- The fan triangle `conv {z, a, b}` over a straight frontier piece is the closed sector cut off
by `D`. -/
theorem u8h_f_mem_fan_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) (x : Plane) :
    x ∈ convexHull ℝ {z, a, b} ↔ 0 ≤ det (a - z) (x - z) ∧ 0 ≤ det (x - z) (b - z) ∧ x ∈ D := by
  constructor
  · intro hx
    have hsub : convexHull ℝ {z, a, b} ⊆
        ({x | 0 ≤ det (a - z) (x - z)} ∩ {x | 0 ≤ det (x - z) (b - z)}) ∩ D := by
      apply convexHull_min
      · intro p hp
        simp only [mem_insert_iff, mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨⟨by simp, by simp⟩, interior_subset hz⟩
        · exact ⟨⟨by simp, hab.le⟩,
            u8h_f_frontier_subset hD (hseg (left_mem_segment ℝ _ _))⟩
        · exact ⟨⟨hab.le, by simp⟩,
            u8h_f_frontier_subset hD (hseg (right_mem_segment ℝ _ _))⟩
      · exact ((u8h_f_convex_det_nonneg z (a - z)).inter (u8h_f_convex_det_nonneg' z (b - z))).inter
          hD.convex
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsub hx
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hxz : x = z
    · subst hxz; exact subset_convexHull ℝ _ (mem_insert _ _)
    · have hyseg := u8h_f_ray_mem_segment hD hz hab hseg hxz h1 h2
      have hxeq := u8h_f_ray_spec hD hz hxz
      have hr1 : u8h_f_rg D z x ≤ 1 := (u8h_f_rg_le_one_iff hD hz x).mpr h3
      have hr0 := u8h_f_rg_nonneg D z x
      have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
      have hymem : u8h_f_ray D z x ∈ convexHull ℝ {z, a, b} :=
        segment_subset_convexHull (by simp) (by simp) hyseg
      have := (convex_convexHull ℝ {z, a, b}) hzmem hymem (sub_nonneg.mpr hr1) hr0 (by ring)
      rw [hxeq]
      convert this using 1
      rw [sub_smul, one_smul, smul_sub]; abel

/-! ### marks and adjacent pairs -/

/-- `(a, b)` is an adjacent pair of marks of `V`: a straight frontier piece seen counterclockwise
from `z` with no mark strictly inside. -/
def u8h_f_Adj (D : Set Plane) (z : Plane) (V : Set Plane) (a b : Plane) : Prop :=
  a ∈ V ∧ b ∈ V ∧ 0 < det (a - z) (b - z) ∧ segment ℝ a b ⊆ frontier D ∧
    ∀ c ∈ V, c ∉ openSegment ℝ a b

theorem u8h_f_openSegment_sub {a b y : Plane} (h : y ∈ openSegment ℝ a b) (z : Plane) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ β + γ = 1 ∧ y - z = β • (a - z) + γ • (b - z) := by
  obtain ⟨β, γ, hβ, hγ, hβγ, rfl⟩ := h
  refine ⟨β, γ, hβ, hγ, hβγ, ?_⟩
  have hz' : z = β • z + γ • z := by rw [← add_smul, hβγ, one_smul]
  calc β • a + γ • b - z = β • a + γ • b - (β • z + γ • z) := by rw [← hz']
    _ = β • (a - z) + γ • (b - z) := by rw [smul_sub, smul_sub]; abel

theorem u8h_f_det_comb_right (u v w : Plane) (β γ : ℝ) :
    det u (β • v + γ • w) = β * det u v + γ * det u w := by
  rw [u8h_f_det_add_right, u8h_f_det_smul_right, u8h_f_det_smul_right]

theorem u8h_f_det_comb_left (u v w : Plane) (β γ : ℝ) :
    det (β • v + γ • w) u = β * det v u + γ * det w u := by
  rw [u8h_f_det_add_left, u8h_f_det_smul_left', u8h_f_det_smul_left']

theorem u8h_f_mem_segment_cases {a b y : Plane} (h : y ∈ segment ℝ a b) :
    y = a ∨ y = b ∨ y ∈ openSegment ℝ a b := by
  rw [← insert_endpoints_openSegment] at h
  simpa using h

/-- Where a mark can lie relative to an adjacent pair. -/
theorem u8h_f_adj_trichotomy {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b : Plane} (hab : u8h_f_Adj D z V a b) {c : Plane}
    (hc : c ∈ V) : c = a ∨ c = b ∨ det (a - z) (c - z) < 0 ∨ det (c - z) (b - z) < 0 := by
  rcases lt_or_ge (det (a - z) (c - z)) 0 with h1 | h1
  · exact Or.inr (Or.inr (Or.inl h1))
  rcases lt_or_ge (det (c - z) (b - z)) 0 with h2 | h2
  · exact Or.inr (Or.inr (Or.inr h2))
  have hcseg := u8h_f_frontier_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 (hV hc) h1 h2
  rcases u8h_f_mem_segment_cases hcseg with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h (hab.2.2.2.2 c hc)

theorem u8h_f_adj_unique_right {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b d : Plane} (hab : u8h_f_Adj D z V a b)
    (had : u8h_f_Adj D z V a d) : b = d := by
  rcases u8h_f_adj_trichotomy hD hz hV hab had.2.1 with h | h | h | h
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using had.2.2.1)
  · exact h.symm
  · exfalso; linarith [had.2.2.1]
  · exfalso
    have hbd : 0 < det (b - z) (d - z) := by rw [u8h_f_det_swap']; linarith
    have hbseg := u8h_f_frontier_mem_segment hD hz had.2.2.1 had.2.2.2.1 (hV hab.2.1) hab.2.2.1.le hbd.le
    rcases u8h_f_mem_segment_cases hbseg with h1 | h1 | h1
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using hab.2.2.1)
    · subst h1; simp at hbd
    · exact had.2.2.2.2 b hab.2.1 h1

theorem u8h_f_adj_unique_left {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c : Plane} (hab : u8h_f_Adj D z V a b)
    (hcb : u8h_f_Adj D z V c b) : a = c := by
  rcases u8h_f_adj_trichotomy hD hz hV hab hcb.1 with h | h | h | h
  · exact h.symm
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using hcb.2.2.1)
  · exfalso
    have hca : 0 < det (c - z) (a - z) := by rw [u8h_f_det_swap']; linarith
    have haseg := u8h_f_frontier_mem_segment hD hz hcb.2.2.1 hcb.2.2.2.1 (hV hab.1) hca.le hab.2.2.1.le
    rcases u8h_f_mem_segment_cases haseg with h1 | h1 | h1
    · subst h1; simp at hca
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u8h_f_det_self] using hab.2.2.1)
    · exact hcb.2.2.2.2 a hab.1 h1
  · exfalso; linarith [hcb.2.2.1]

/-- A point in the open frontier pieces of two adjacent pairs forces the pairs to coincide. -/
theorem u8h_f_adj_eq_of_openSegment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u8h_f_Adj D z V a b)
    (hcd : u8h_f_Adj D z V c d) (h1 : y ∈ openSegment ℝ a b) (h2 : y ∈ openSegment ℝ c d) :
    a = c ∧ b = d := by
  obtain ⟨β, γ, hβ, hγ, -, hY1⟩ := u8h_f_openSegment_sub h1 z
  obtain ⟨β', δ, hβ', hδ, -, hY2⟩ := u8h_f_openSegment_sub h2 z
  have dAB := hab.2.2.1
  have dCD := hcd.2.2.1
  have eAY : det (a - z) (y - z) = γ * det (a - z) (b - z) := by
    rw [hY1, u8h_f_det_comb_right, u8h_f_det_self]; ring
  have eBY : det (b - z) (y - z) = -(β * det (a - z) (b - z)) := by
    rw [hY1, u8h_f_det_comb_right, u8h_f_det_self, u8h_f_det_swap' (b - z) (a - z)]; ring
  have eCY : det (c - z) (y - z) = δ * det (c - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_right, u8h_f_det_self]; ring
  have eYD : det (y - z) (d - z) = β' * det (c - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_left, u8h_f_det_self]; ring
  have eAY' : det (a - z) (y - z) = β' * det (a - z) (c - z) + δ * det (a - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_right]
  have eBY' : det (b - z) (y - z) = β' * det (b - z) (c - z) + δ * det (b - z) (d - z) := by
    rw [hY2, u8h_f_det_comb_right]
  have eYD' : det (y - z) (d - z) = β * det (a - z) (d - z) + γ * det (b - z) (d - z) := by
    rw [hY1, u8h_f_det_comb_left]
  rcases u8h_f_adj_trichotomy hD hz hV hab hcd.1 with hc | hc | hc | hc
  · -- c = a
    subst hc
    refine ⟨rfl, ?_⟩
    rcases u8h_f_adj_trichotomy hD hz hV hab hcd.2.1 with hd | hd | hd | hd
    · exfalso; subst hd
      have := hcd.2.2.1; rw [u8h_f_det_self] at this; exact lt_irrefl _ this
    · exact hd.symm
    · exfalso; linarith [hcd.2.2.1]
    · exfalso
      have hbd : 0 < det (b - z) (d - z) := by rw [u8h_f_det_swap']; linarith
      have hbseg := u8h_f_frontier_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 (hV hab.2.1) dAB.le hbd.le
      rcases u8h_f_mem_segment_cases hbseg with h | h | h
      · subst h; rw [u8h_f_det_self] at dAB; exact lt_irrefl _ dAB
      · subst h; rw [u8h_f_det_self] at hbd; exact lt_irrefl _ hbd
      · exact hcd.2.2.2.2 b hab.2.1 h
  · -- c = b
    exfalso; subst hc
    have : 0 < det (c - z) (y - z) := by rw [eCY]; positivity
    rw [eBY] at this
    have := mul_pos hβ dAB; linarith
  · -- det (a-z) (c-z) < 0 : `a` lies strictly inside the sector `(c, d)`
    exfalso
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < δ * det (a - z) (d - z) := by
        have := mul_pos hγ dAB
        have := mul_neg_of_pos_of_neg hβ' hc
        linarith
      exact (mul_pos_iff_of_pos_left hδ).mp h0
    have hCA : 0 < det (c - z) (a - z) := by rw [u8h_f_det_swap']; linarith
    have haseg := u8h_f_frontier_mem_segment hD hz dCD hcd.2.2.2.1 (hV hab.1) hCA.le hAD.le
    rcases u8h_f_mem_segment_cases haseg with h | h | h
    · subst h; rw [u8h_f_det_self] at hCA; exact lt_irrefl _ hCA
    · subst h; rw [u8h_f_det_self] at hAD; exact lt_irrefl _ hAD
    · exact hcd.2.2.2.2 a hab.1 h
  · -- det (c-z) (b-z) < 0 : `d` lies strictly inside the sector `(a, b)`
    exfalso
    have hBC : 0 < det (b - z) (c - z) := by rw [u8h_f_det_swap']; linarith
    have hBD : det (b - z) (d - z) < 0 := by
      have h0 : δ * det (b - z) (d - z) < 0 := by
        have := mul_pos hβ dAB
        have := mul_pos hβ' hBC
        linarith
      rcases lt_or_ge (det (b - z) (d - z)) 0 with h | h
      · exact h
      · exfalso; linarith [mul_nonneg hδ.le h]
    have hAD : 0 < det (a - z) (d - z) := by
      have h0 : 0 < β * det (a - z) (d - z) := by
        have := mul_pos hβ' dCD
        have := mul_neg_of_pos_of_neg hγ hBD
        linarith
      exact (mul_pos_iff_of_pos_left hβ).mp h0
    have hDB : 0 < det (d - z) (b - z) := by rw [u8h_f_det_swap']; linarith
    have hdseg := u8h_f_frontier_mem_segment hD hz dAB hab.2.2.2.1 (hV hcd.2.1) hAD.le hDB.le
    rcases u8h_f_mem_segment_cases hdseg with h | h | h
    · subst h; rw [u8h_f_det_self] at hAD; exact lt_irrefl _ hAD
    · subst h; rw [u8h_f_det_self] at hDB; exact lt_irrefl _ hDB
    · exact hab.2.2.2.2 d hcd.2.1 h


theorem u8h_f_range_three (z a b : Plane) : range ![z, a, b] = {z, a, b} := by
  ext p
  simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]

/-- The fan faces: one triangle `z a b` per pair with `A a b`. -/
def u8h_f_fanFaces (z : Plane) (A : Plane → Plane → Prop) : Set Triangle :=
  {T | ∃ a b, A a b ∧ T.v = ![z, a, b]}

theorem u8h_f_fanTri_mem {z a b : Plane} {A : Plane → Plane → Prop} (h : A a b)
    (hpos : 0 < det (a - z) (b - z)) :
    (⟨![z, a, b], by simpa using hpos⟩ : Triangle) ∈ u8h_f_fanFaces z A := ⟨a, b, h, rfl⟩

theorem u8h_f_carrier_of_v {T : Triangle} {z a b : Plane} (h : T.v = ![z, a, b]) :
    T.carrier = convexHull ℝ {z, a, b} := by
  rw [Triangle.carrier, h, u8h_f_range_three]

theorem u8h_f_inter_cases {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u8h_f_Adj D z V a b)
    (hcd : u8h_f_Adj D z V c d) (hy1 : y ∈ segment ℝ a b) (hy2 : y ∈ segment ℝ c d) :
    (a = c ∧ b = d) ∨ (y = a ∧ a = d) ∨ (y = b ∧ b = c) := by
  rcases u8h_f_mem_segment_cases hy1 with h1 | h1 | h1 <;>
    rcases u8h_f_mem_segment_cases hy2 with h2 | h2 | h2
  · subst h1; exact Or.inl ⟨h2, u8h_f_adj_unique_right hD hz hV hab (h2 ▸ hcd)⟩
  · exact Or.inr (Or.inl ⟨h1, h1 ▸ h2⟩)
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 a hab.1)
  · exact Or.inr (Or.inr ⟨h1, h1 ▸ h2⟩)
  · subst h1; exact Or.inl ⟨u8h_f_adj_unique_left hD hz hV hab (h2 ▸ hcd), h2⟩
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 b hab.2.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 c hcd.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 d hcd.2.1)
  · exact Or.inl (u8h_f_adj_eq_of_openSegment hD hz hV hab hcd h1 h2)

theorem u8h_f_fan_subset {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) : convexHull ℝ {z, a, b} ⊆ D := by
  apply convexHull_min _ hD.convex
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact interior_subset hz
  · exact u8h_f_frontier_subset hD (hseg (left_mem_segment ℝ _ _))
  · exact u8h_f_frontier_subset hD (hseg (right_mem_segment ℝ _ _))

theorem u8h_f_frontier_nonempty {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    (frontier D).Nonempty :=
  ⟨u8h_f_ray D z (z + (1, 0)), u8h_f_ray_mem_frontier hD hz (by simp)⟩

theorem u8h_f_mem_segment_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ∈ D) (hxz : x ≠ z) : x ∈ segment ℝ z (u8h_f_ray D z x) := by
  have hr0 := u8h_f_rg_nonneg D z x
  have hr1 := (u8h_f_rg_le_one_iff hD hz x).mpr hx
  refine ⟨1 - u8h_f_rg D z x, u8h_f_rg D z x, by linarith, hr0, by ring, ?_⟩
  have := u8h_f_ray_spec hD hz hxz
  rw [smul_sub] at this
  rw [sub_smul, one_smul]
  conv_rhs => rw [this]
  abel

/-- The fan from `z` over the adjacent pairs is a straight triangulation of `D`. -/
theorem u8h_f_fan_triangulation {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hVfin : V.Finite) (hV : V ⊆ frontier D) {A : Plane → Plane → Prop}
    (hA : ∀ a b, A a b → u8h_f_Adj D z V a b)
    (hcov : ∀ y ∈ frontier D, ∃ a b, A a b ∧ y ∈ segment ℝ a b) :
    ∃ K : Triangulation D, K.faces = u8h_f_fanFaces z A := by
  have hface : ∀ T ∈ u8h_f_fanFaces z A, ∃ a b, u8h_f_Adj D z V a b ∧ T.v 0 = z ∧ T.v 1 = a ∧
      T.v 2 = b ∧ T.carrier = convexHull ℝ {z, a, b} := by
    rintro T ⟨a, b, hab, hv⟩
    exact ⟨a, b, hA a b hab, by simp [hv], by simp [hv], by simp [hv], u8h_f_carrier_of_v hv⟩
  refine ⟨⟨u8h_f_fanFaces z A, ?_, ?_, ?_⟩, rfl⟩
  · -- finite
    apply Set.Finite.of_finite_image (f := fun T => (T.v 1, T.v 2))
    · refine (hVfin.prod hVfin).subset ?_
      rintro _ ⟨T, hT, rfl⟩
      obtain ⟨a, b, hab, -, h1, h2, -⟩ := hface T hT
      show T.v 1 ∈ V ∧ T.v 2 ∈ V
      rw [h1, h2]; exact ⟨hab.1, hab.2.1⟩
    · intro T hT T' hT' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨a, b, -, h0, -, -, -⟩ := hface T hT
      obtain ⟨c, d, -, h0', -, -, -⟩ := hface T' hT'
      have : T.v = T'.v := by
        funext i
        fin_cases i
        · simpa using h0.trans h0'.symm
        · exact h.1
        · exact h.2
      cases T; cases T'; simp only at this; subst this; rfl
  · -- cover
    apply Set.Subset.antisymm
    · intro x hx
      simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨T, hT, hxT⟩ := hx
      obtain ⟨a, b, hab, -, -, -, hc⟩ := hface T hT
      rw [hc] at hxT
      exact u8h_f_fan_subset hD hz hab.2.2.2.1 hxT
    · intro x hx
      simp only [mem_iUnion, exists_prop]
      by_cases hxz : x = z
      · subst hxz
        obtain ⟨y0, hy0⟩ := u8h_f_frontier_nonempty hD hz
        obtain ⟨a, b, hab, -⟩ := hcov y0 hy0
        refine ⟨_, u8h_f_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u8h_f_carrier_of_v rfl]
        exact subset_convexHull ℝ _ (mem_insert _ _)
      · obtain ⟨a, b, hab, hyab⟩ := hcov _ (u8h_f_ray_mem_frontier hD hz hxz)
        refine ⟨_, u8h_f_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u8h_f_carrier_of_v rfl]
        have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
        have hymem : u8h_f_ray D z x ∈ convexHull ℝ {z, a, b} :=
          segment_subset_convexHull (by simp) (by simp) hyab
        exact (convex_convexHull ℝ _).segment_subset hzmem hymem (u8h_f_mem_segment_ray hD hz hx hxz)
  · -- inter
    intro T hT T' hT'
    obtain ⟨a, b, hab, h0, h1, h2, hc⟩ := hface T hT
    obtain ⟨c, d, hcd, h0', h1', h2', hc'⟩ := hface T' hT'
    have hrT : range T.v = {z, a, b} := by
      rw [← u8h_f_range_three]; congr 1; funext i; fin_cases i <;> simp [h0, h1, h2]
    have hrT' : range T'.v = {z, c, d} := by
      rw [← u8h_f_range_three]; congr 1; funext i; fin_cases i <;> simp [h0', h1', h2']
    rw [hc, hc', hrT, hrT']
    apply Set.Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      by_cases hxz : x = z
      · subst hxz
        exact subset_convexHull ℝ _ ⟨mem_insert _ _, mem_insert _ _⟩
      · have hx1' := (u8h_f_mem_fan_iff hD hz hab.2.2.1 hab.2.2.2.1 x).mp hx1
        have hx2' := (u8h_f_mem_fan_iff hD hz hcd.2.2.1 hcd.2.2.2.1 x).mp hx2
        have hy1 := u8h_f_ray_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 hxz hx1'.1 hx1'.2.1
        have hy2 := u8h_f_ray_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 hxz hx2'.1 hx2'.2.1
        have hxseg := u8h_f_mem_segment_ray hD hz hx1'.2.2 hxz
        rcases u8h_f_inter_cases hD hz hV hab hcd hy1 hy2 with ⟨rfl, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩
        · rw [inter_self]; exact hx1
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, c, a}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
        · rw [hy] at hxseg
          exact segment_subset_convexHull (s := {z, a, b} ∩ {z, b, d}) ⟨mem_insert _ _, mem_insert _ _⟩
            ⟨by simp, by simp⟩ hxseg
    · exact subset_inter (convexHull_mono inter_subset_left) (convexHull_mono inter_subset_right)

/-! ### the cone map -/


/-- The linear map sending `p ↦ p'`, `q ↦ q'` (for `det p q ≠ 0`), written in `det` coordinates. -/
theorem u8h_f_gap {M : Set ℝ} (hM : M.Finite) (h0 : (0:ℝ) ∈ M) (h1 : (1:ℝ) ∈ M) {θ₀ : ℝ}
    (hθ : θ₀ ∈ Icc (0:ℝ) 1) :
    ∃ θa ∈ M, ∃ θb ∈ M, θa < θb ∧ θa ≤ θ₀ ∧ θ₀ ≤ θb ∧ ∀ θ ∈ M, θa < θ → θ < θb → False := by
  classical
  rcases hθ.2.lt_or_eq with hlt | heq
  · set Fa := hM.toFinset.filter (fun θ => θ ≤ θ₀) with hFa
    set Fb := hM.toFinset.filter (fun θ => θ₀ < θ) with hFb
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0, hθ.1]⟩
    have hbne : Fb.Nonempty := ⟨1, by simp [hFb, h1, hlt]⟩
    have hamem := Finset.max'_mem Fa hane
    have hbmem := Finset.min'_mem Fb hbne
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    simp only [hFb, Finset.mem_filter, Set.Finite.mem_toFinset] at hbmem
    refine ⟨_, hamem.1, _, hbmem.1, by linarith [hamem.2, hbmem.2], hamem.2, hbmem.2.le, ?_⟩
    intro θ hθM hlo hhi
    rcases le_or_gt θ θ₀ with h | h
    · have hmem : θ ∈ Fa := by simp [hFa, hθM, h]
      have := Finset.le_max' Fa θ hmem
      exact absurd hlo (not_lt.mpr this)
    · have hmem : θ ∈ Fb := by simp [hFb, hθM, h]
      have := Finset.min'_le Fb θ hmem
      exact absurd hhi (not_lt.mpr this)
  · subst heq
    set Fa := hM.toFinset.filter (fun θ => θ < 1) with hFa
    have hane : Fa.Nonempty := ⟨0, by simp [hFa, h0]⟩
    have hamem := Finset.max'_mem Fa hane
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    refine ⟨_, hamem.1, 1, h1, hamem.2, hamem.2.le, le_rfl, ?_⟩
    intro θ hθM hlo hhi
    have hmem : θ ∈ Fa := by simp [hFa, hθM, hhi]
    have := Finset.le_max' Fa θ hmem
    exact absurd hlo (not_lt.mpr this)

/-- The marks: all endpoints of the segments of `S`. -/
noncomputable def u8h_f_marks (S : Finset (Plane × Plane)) : Set Plane :=
  ↑(S.image Prod.fst ∪ S.image Prod.snd)

theorem u8h_f_marks_finite (S : Finset (Plane × Plane)) : (u8h_f_marks S).Finite := Finset.finite_toSet _

theorem u8h_f_marks_left {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.1 ∈ u8h_f_marks S := by
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inl ⟨p, hp, rfl⟩

theorem u8h_f_marks_right {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.2 ∈ u8h_f_marks S := by
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inr ⟨p, hp, rfl⟩

theorem u8h_f_marks_subset_frontier {D : Set Plane} {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) : u8h_f_marks S ⊆ frontier D := by
  intro c hc
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image,
    Finset.mem_coe] at hc
  rw [← hS]
  rcases hc with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, left_mem_segment ℝ _ _⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, right_mem_segment ℝ _ _⟩

/-- The adjacent pairs actually used: adjacent marks lying in one segment of `S`. -/
def u8h_f_A (D : Set Plane) (z : Plane) (S : Finset (Plane × Plane)) (a b : Plane) : Prop :=
  u8h_f_Adj D z (u8h_f_marks S) a b ∧ ∃ p ∈ S, segment ℝ a b ⊆ segment ℝ p.1 p.2

theorem u8h_f_cover_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {p : Plane × Plane}
    (hp : p ∈ S) (hne : p.1 ≠ p.2) {y : Plane} (hy : y ∈ segment ℝ p.1 p.2) :
    ∃ a b, u8h_f_A D z S a b ∧ y ∈ segment ℝ a b := by
  have he : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hne.symm
  set f : ℝ → Plane := fun θ => p.1 + θ • (p.2 - p.1) with hf
  have hfinj : Function.Injective f := fun θ₁ θ₂ h => smul_left_injective ℝ he (add_left_cancel h)
  have hsegp : segment ℝ p.1 p.2 = f '' Icc 0 1 := segment_eq_image' ℝ p.1 p.2
  have hsegfr : segment ℝ p.1 p.2 ⊆ frontier D := hS ▸ subset_iUnion₂ (s := fun p _ => segment ℝ p.1 p.2) p hp
  set M : Set ℝ := f ⁻¹' u8h_f_marks S ∩ Icc 0 1 with hM
  have hMfin : M.Finite := ((u8h_f_marks_finite S).preimage hfinj.injOn).subset inter_subset_left
  have h0M : (0:ℝ) ∈ M := ⟨by simp [f, u8h_f_marks_left hp], by simp⟩
  have h1M : (1:ℝ) ∈ M := ⟨by simp [f, u8h_f_marks_right hp], by simp⟩
  rw [hsegp] at hy
  obtain ⟨θ₀, hθ₀, rfl⟩ := hy
  obtain ⟨θa, haM, θb, hbM, hlt, hle1, hle2, hgap⟩ := u8h_f_gap hMfin h0M h1M hθ₀
  have haV : f θa ∈ u8h_f_marks S := haM.1
  have hbV : f θb ∈ u8h_f_marks S := hbM.1
  have hap : f θa ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θa, haM.2, rfl⟩
  have hbp : f θb ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θb, hbM.2, rfl⟩
  have hsub : segment ℝ (f θa) (f θb) ⊆ segment ℝ p.1 p.2 := (convex_segment _ _).segment_subset hap hbp
  have hsegab : segment ℝ (f θa) (f θb) ⊆ frontier D := hsub.trans hsegfr
  have hneab : f θa ≠ f θb := fun h => hlt.ne (hfinj h)
  have hcomb : ∀ lam : ℝ, f θa + lam • (f θb - f θa) = f (θa + lam * (θb - θa)) := by
    intro lam
    simp only [hf]
    ext <;> simp <;> ring
  have hnomark : ∀ c ∈ u8h_f_marks S, c ∉ openSegment ℝ (f θa) (f θb) := by
    intro c hc hco
    rw [openSegment_eq_image'] at hco
    obtain ⟨lam, hlam, rfl⟩ := hco
    beta_reduce at hc
    rw [hcomb] at hc
    have hθc : θa + lam * (θb - θa) ∈ M := by
      refine ⟨hc, ?_, ?_⟩
      · nlinarith [haM.2.1, hlam.1.le, hlt.le]
      · nlinarith [hbM.2.2, hlam.2.le, hlt.le]
    exact hgap _ hθc (by nlinarith [hlam.1]) (by nlinarith [hlam.2])
  have hyab : f θ₀ ∈ segment ℝ (f θa) (f θb) := by
    rw [segment_eq_image']
    refine ⟨(θ₀ - θa) / (θb - θa), ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    beta_reduce
    rw [hcomb]
    congr 1
    have hba : θb - θa ≠ 0 := by linarith
    field_simp
    ring
  have hdet := u8h_f_det_ne_zero_of_segment hD hz hneab hsegab
  rcases hdet.lt_or_gt with hneg | hpos
  · refine ⟨f θb, f θa, ⟨⟨hbV, haV, by rw [u8h_f_det_swap']; linarith, by rw [segment_symm]; exact hsegab,
      fun c hc => by rw [openSegment_symm]; exact hnomark c hc⟩, p, hp, by rw [segment_symm]; exact hsub⟩,
      by rw [segment_symm]; exact hyab⟩
  · exact ⟨f θa, f θb, ⟨⟨haV, hbV, hpos, hsegab, hnomark⟩, p, hp, hsub⟩, hyab⟩

/-! ### frontier points are not isolated; a nondegenerate segment through each -/

/-! ### U8 helpers: sector coordinates and the two triangles of a radial quadrilateral -/

/-- A triangle from three points in positive order. -/
def u8h_mkTri (p q r : Plane) (h : 0 < det (q - p) (r - p)) : Triangle := ⟨![p, q, r], by simpa using h⟩

theorem u8h_mkTri_v0 (p q r : Plane) (h : 0 < det (q - p) (r - p)) : (u8h_mkTri p q r h).v 0 = p := rfl
theorem u8h_mkTri_v1 (p q r : Plane) (h : 0 < det (q - p) (r - p)) : (u8h_mkTri p q r h).v 1 = q := rfl
theorem u8h_mkTri_v2 (p q r : Plane) (h : 0 < det (q - p) (r - p)) : (u8h_mkTri p q r h).v 2 = r := rfl

theorem u8h_mkTri_carrier (p q r : Plane) (h : 0 < det (q - p) (r - p)) :
    (u8h_mkTri p q r h).carrier = convexHull ℝ {p, q, r} := u8h_f_carrier_of_v rfl

theorem u8h_mkTri_range (p q r : Plane) (h : 0 < det (q - p) (r - p)) :
    range (u8h_mkTri p q r h).v = {p, q, r} := u8h_f_range_three p q r

/-- Membership in a triangle by the three `det` signs, for a `u8h_mkTri`. -/
theorem u8h_mem_mkTri (p q r : Plane) (h : 0 < det (q - p) (r - p)) (x : Plane) :
    x ∈ (u8h_mkTri p q r h).carrier ↔
      0 ≤ det (q - p) (x - p) ∧ 0 ≤ det (r - q) (x - q) ∧ 0 ≤ det (p - r) (x - r) := by
  rw [U1_mem_carrier_iff_det]; rfl

theorem u8h_det_combo (A B : Plane) (c₁ c₂ d₁ d₂ : ℝ) :
    det (c₁ • A + c₂ • B) (d₁ • A + d₂ • B) = (c₁ * d₂ - c₂ * d₁) * det A B := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- Positivity of the outer triangle `(z + sa•A, z + A, z + B)`. -/
theorem u8h_pos_tri2 {A B : Plane} (hAB : 0 < det A B) {sa : ℝ} (hsa1 : sa < 1) (z : Plane) :
    0 < det ((z + A) - (z + sa • A)) ((z + B) - (z + sa • A)) := by
  have : det ((z + A) - (z + sa • A)) ((z + B) - (z + sa • A)) = (1 - sa) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [this]; exact mul_pos (by linarith) hAB

/-- Positivity of the inner triangle `(z + sa•A, z + B, z + sb•B)`. -/
theorem u8h_pos_tri1 {A B : Plane} (hAB : 0 < det A B) {sa sb : ℝ} (hsa0 : 0 < sa) (hsb1 : sb < 1)
    (z : Plane) : 0 < det ((z + B) - (z + sa • A)) ((z + sb • B) - (z + sa • A)) := by
  have : det ((z + B) - (z + sa • A)) ((z + sb • B) - (z + sa • A)) = sa * (1 - sb) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [this]; exact mul_pos (mul_pos hsa0 (by linarith)) hAB

/-- The outer triangle in sector coordinates. -/
theorem u8h_mem_tri2 {A B : Plane} (hAB : 0 < det A B) {sa : ℝ} (hsa0 : 0 < sa) (hsa1 : sa < 1)
    (z : Plane) (α β : ℝ) :
    z + α • A + β • B ∈ (u8h_mkTri (z + sa • A) (z + A) (z + B) (u8h_pos_tri2 hAB hsa1 z)).carrier ↔
      0 ≤ β ∧ α + β ≤ 1 ∧ 1 ≤ α / sa + β := by
  rw [u8h_mem_mkTri]
  have e1 : det ((z + A) - (z + sa • A)) ((z + α • A + β • B) - (z + sa • A)) = ((1 - sa) * β) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e2 : det ((z + B) - (z + A)) ((z + α • A + β • B) - (z + A)) = (1 - α - β) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e3 : det ((z + sa • A) - (z + B)) ((z + α • A + β • B) - (z + B)) = (sa * (β - 1) + α) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [e1, e2, e3, mul_nonneg_iff_of_pos_right hAB, mul_nonneg_iff_of_pos_right hAB,
    mul_nonneg_iff_of_pos_right hAB]
  have h1 : 0 ≤ (1 - sa) * β ↔ 0 ≤ β := mul_nonneg_iff_of_pos_left (by linarith)
  rw [h1]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by linarith, ?_⟩
    rw [div_add' _ _ _ hsa0.ne', le_div_iff₀ hsa0]; nlinarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by linarith, ?_⟩
    rw [div_add' _ _ _ hsa0.ne', le_div_iff₀ hsa0] at h3; nlinarith

/-- The inner triangle in sector coordinates. -/
theorem u8h_mem_tri1 {A B : Plane} (hAB : 0 < det A B) {sa sb : ℝ} (hsa0 : 0 < sa) (hsb0 : 0 < sb)
    (hsb1 : sb < 1) (z : Plane) (α β : ℝ) :
    z + α • A + β • B ∈ (u8h_mkTri (z + sa • A) (z + B) (z + sb • B) (u8h_pos_tri1 hAB hsa0 hsb1 z)).carrier ↔
      0 ≤ α ∧ α / sa + β ≤ 1 ∧ 1 ≤ α / sa + β / sb := by
  rw [u8h_mem_mkTri]
  have e1 : det ((z + B) - (z + sa • A)) ((z + α • A + β • B) - (z + sa • A)) = (sa - α - sa * β) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e2 : det ((z + sb • B) - (z + B)) ((z + α • A + β • B) - (z + B)) = ((1 - sb) * α) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have e3 : det ((z + sa • A) - (z + sb • B)) ((z + α • A + β • B) - (z + sb • B)) =
      (sa * (β - sb) + sb * α) * det A B := by
    simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [e1, e2, e3, mul_nonneg_iff_of_pos_right hAB, mul_nonneg_iff_of_pos_right hAB,
    mul_nonneg_iff_of_pos_right hAB]
  have h2 : 0 ≤ (1 - sb) * α ↔ 0 ≤ α := mul_nonneg_iff_of_pos_left (by linarith)
  rw [h2]
  have key1 : α / sa + β ≤ 1 ↔ 0 ≤ sa - α - sa * β := by
    rw [div_add' _ _ _ hsa0.ne', div_le_one hsa0]; constructor <;> intro h <;> nlinarith
  have key2 : 1 ≤ α / sa + β / sb ↔ 0 ≤ sa * (β - sb) + sb * α := by
    rw [div_add_div _ _ hsa0.ne' hsb0.ne', le_div_iff₀ (mul_pos hsa0 hsb0)]
    constructor <;> intro h <;> nlinarith
  rw [key1, key2]
  tauto

/-- The radial quadrilateral is the union of the two triangles. -/
theorem u8h_quad_iff {sa sb : ℝ} (hsa0 : 0 < sa) (hsa1 : sa < 1) (hsb0 : 0 < sb) (hsb1 : sb < 1)
    (α β : ℝ) :
    ((0 ≤ β ∧ α + β ≤ 1 ∧ 1 ≤ α / sa + β) ∨ (0 ≤ α ∧ α / sa + β ≤ 1 ∧ 1 ≤ α / sa + β / sb)) ↔
      (0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ 1 ∧ 1 ≤ α / sa + β / sb) := by
  have hα : α / sa = α * sa⁻¹ := div_eq_mul_inv _ _
  have hβ : β / sb = β * sb⁻¹ := div_eq_mul_inv _ _
  have hsa' : 1 < sa⁻¹ := one_lt_inv_iff₀.2 ⟨hsa0, hsa1⟩
  have hsb' : 1 < sb⁻¹ := one_lt_inv_iff₀.2 ⟨hsb0, hsb1⟩
  rw [hα, hβ]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · have hα0 : 0 ≤ α := by nlinarith
      refine ⟨hα0, h1, h2, ?_⟩
      nlinarith
    · have hβ0 : 0 ≤ β := by
        by_contra hneg; push Not at hneg
        nlinarith
      refine ⟨h1, hβ0, ?_, h3⟩
      nlinarith
  · rintro ⟨h0, h1, h2, h3⟩
    by_cases h : 1 ≤ α * sa⁻¹ + β
    · exact Or.inl ⟨h1, h2, h⟩
    · push Not at h
      exact Or.inr ⟨h0, h.le, h3⟩


/-! ### U8 helpers: nested discs, radial projections, sector coordinates -/

/-- The data of a radial annulus: an inner disc `Din` containing the centre `z` in its interior and
lying inside the interior of the outer disc `Dout`. -/
structure u8h_AnnCtx (z : Plane) (Din Dout : Set Plane) : Prop where
  hin : Link.IsDisc Din
  hout : Link.IsDisc Dout
  hz : z ∈ interior Din
  hsub : Din ⊆ interior Dout

namespace u8h_AnnCtx

variable {z : Plane} {Din Dout : Set Plane} (C : u8h_AnnCtx z Din Dout)
include C

theorem hz' : z ∈ interior Dout := C.hsub (interior_subset C.hz)

theorem notMem_of_frontier {a : Plane} (ha : a ∈ frontier Dout) : a ∉ Din := fun h =>
  ha.2 (C.hsub h)

theorem ne_of_frontier {a : Plane} (ha : a ∈ frontier Dout) : a ≠ z := u8h_f_frontier_ne C.hout C.hz' ha

theorem rgin_gt_one {a : Plane} (ha : a ∈ frontier Dout) : 1 < u8h_f_rg Din z a := by
  have := C.notMem_of_frontier ha
  rw [← u8h_f_rg_le_one_iff C.hin C.hz] at this
  push Not at this; exact this

/-- The radial scale `s_a = 1 / rg_in a` of the inner point on the ray through `a`. -/
noncomputable def _root_.SM.u8h_s (Din : Set Plane) (z a : Plane) : ℝ := (u8h_f_rg Din z a)⁻¹

theorem s_pos {a : Plane} (ha : a ∈ frontier Dout) : 0 < u8h_s Din z a :=
  inv_pos.2 (lt_trans one_pos (C.rgin_gt_one ha))

theorem s_lt_one {a : Plane} (ha : a ∈ frontier Dout) : u8h_s Din z a < 1 :=
  inv_lt_one_of_one_lt₀ (C.rgin_gt_one ha)

omit C in
theorem ray_eq (a : Plane) : u8h_f_ray Din z a = z + u8h_s Din z a • (a - z) := rfl

theorem ray_mem_frontier {a : Plane} (ha : a ∈ frontier Dout) : u8h_f_ray Din z a ∈ frontier Din :=
  u8h_f_ray_mem_frontier C.hin C.hz (C.ne_of_frontier ha)

theorem rgout_ray {a : Plane} (ha : a ∈ frontier Dout) :
    u8h_f_rg Dout z (u8h_f_ray Din z a) = u8h_s Din z a := by
  rw [ray_eq, u8h_f_rg_smul _ _ _ (C.s_pos ha).le, (u8h_f_rg_eq_one_iff C.hout C.hz' a).2 ha, mul_one]

/-- The outer radial projection of the inner point is the point itself. -/
theorem rayout_ray {a : Plane} (ha : a ∈ frontier Dout) : u8h_f_ray Dout z (u8h_f_ray Din z a) = a := by
  rw [u8h_f_ray, C.rgout_ray ha, ray_eq, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (C.s_pos ha).ne', one_smul, add_sub_cancel]

theorem ray_ne {a : Plane} (ha : a ∈ frontier Dout) : u8h_f_ray Din z a ≠ z :=
  u8h_f_frontier_ne C.hin C.hz (C.ray_mem_frontier ha)

omit C in
theorem ray_sub (a : Plane) : u8h_f_ray Din z a - z = u8h_s Din z a • (a - z) := by
  rw [ray_eq, add_sub_cancel_left]

theorem det_ray_ray {a b : Plane} (ha : a ∈ frontier Dout) (hb : b ∈ frontier Dout)
    (hab : 0 < det (a - z) (b - z)) :
    0 < det (u8h_f_ray Din z a - z) (u8h_f_ray Din z b - z) := by
  rw [ray_sub, ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right]
  exact mul_pos (C.s_pos ha) (mul_pos (C.s_pos hb) hab)

end u8h_AnnCtx

/-- Gauge linearity on a sector whose boundary piece is straight. -/
theorem u8h_rg_sector {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    u8h_f_rg D z (z + α • (a - z) + β • (b - z)) = α + β := by
  rcases eq_or_lt_of_le (add_nonneg hα hβ) with h0 | hpos
  · have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    subst hα0; subst hβ0
    simp [u8h_f_rg_self]
  · set t := α + β with ht
    set c : Plane := (α / t) • a + (β / t) • b with hc
    have hcseg : c ∈ segment ℝ a b :=
      ⟨α / t, β / t, div_nonneg hα hpos.le, div_nonneg hβ hpos.le, by rw [← add_div, div_self hpos.ne'], rfl⟩
    have hrc : u8h_f_rg D z c = 1 := (u8h_f_rg_eq_one_iff hD hz c).2 (hseg hcseg)
    have e : z + α • (a - z) + β • (b - z) = z + t • (c - z) := by
      rw [hc]
      have h1 : (α / t) • a + (β / t) • b - z = (α / t) • (a - z) + (β / t) • (b - z) := by
        have : z = (α / t) • z + (β / t) • z := by
          rw [← add_smul, ← add_div, div_self hpos.ne', one_smul]
        conv_lhs => rw [this]
        rw [smul_sub, smul_sub]; abel
      rw [h1, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne',
        add_assoc]
    rw [e, u8h_f_rg_smul D z c hpos.le, hrc, mul_one]

/-- Cramer coordinates of `x - z` in the basis `A, B`. -/
theorem u8h_coord {A B : Plane} (hAB : det A B ≠ 0) (z x : Plane) :
    x = z + (det (x - z) B / det A B) • A + (det A (x - z) / det A B) • B := by
  have := u8h_f_cramer hAB (x - z)
  rw [add_assoc, ← this, add_sub_cancel]


/-! ### U8 helpers: the radial annulus triangulation (faces over the adjacent pairs of a fan) -/

/-- The faces of the radial annulus triangulation: for each adjacent pair `(a, b)` of outer marks the
outer triangle `(Pt a, a, b)` and the inner triangle `(Pt a, b, Pt b)`, where `Pt = u8h_f_ray Din z`. -/
def u8h_annFaces (z : Plane) (Din : Set Plane) (A : Plane → Plane → Prop) : Set Triangle :=
  {T | ∃ a b, A a b ∧
    (T.v = ![u8h_f_ray Din z a, a, b] ∨ T.v = ![u8h_f_ray Din z a, b, u8h_f_ray Din z b])}

/-- The hypotheses of the annulus triangulation: nested discs, a finite set of marks on the outer
frontier, an adjacency relation `A` contained in `u8h_f_Adj` and covering the outer frontier, and
straightness of the inner frontier between the radial projections of adjacent marks. -/
structure u8h_AnnData (z : Plane) (Din Dout : Set Plane) (V : Set Plane) (A : Plane → Plane → Prop) :
    Prop where
  ctx : u8h_AnnCtx z Din Dout
  hVfin : V.Finite
  hV : V ⊆ frontier Dout
  hA : ∀ a b, A a b → u8h_f_Adj Dout z V a b
  hcov : ∀ y ∈ frontier Dout, ∃ a b, A a b ∧ y ∈ segment ℝ a b
  hstraight : ∀ a b, A a b → segment ℝ (u8h_f_ray Din z a) (u8h_f_ray Din z b) ⊆ frontier Din

theorem u8h_det_sub_ray (z a b : Plane) (sa : ℝ) :
    det (a - (z + sa • (a - z))) (b - (z + sa • (a - z))) = (1 - sa) * det (a - z) (b - z) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]; ring

theorem u8h_det_sub_ray' (z a b : Plane) (sa sb : ℝ) :
    det (b - (z + sa • (a - z))) ((z + sb • (b - z)) - (z + sa • (a - z))) =
      sa * (1 - sb) * det (a - z) (b - z) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]; ring

/-- Sector coordinates of a point with respect to the pair `(a, b)` around `z`. -/
noncomputable def u8h_α (z a b x : Plane) : ℝ := det (x - z) (b - z) / det (a - z) (b - z)
noncomputable def u8h_β (z a b x : Plane) : ℝ := det (a - z) (x - z) / det (a - z) (b - z)

theorem u8h_div_nonneg_iff {p q : ℝ} (hq : 0 < q) : 0 ≤ p / q ↔ 0 ≤ p := by
  constructor
  · intro h; by_contra hn; push Not at hn
    have := div_neg_of_neg_of_pos hn hq; linarith
  · intro h; exact div_nonneg h hq.le

namespace u8h_AnnData

variable {z : Plane} {Din Dout V : Set Plane} {A : Plane → Plane → Prop} (D : u8h_AnnData z Din Dout V A)
include D

theorem C : u8h_AnnCtx z Din Dout := D.ctx
theorem hin : Link.IsDisc Din := D.ctx.hin
theorem hout : Link.IsDisc Dout := D.ctx.hout
theorem hz : z ∈ interior Din := D.ctx.hz

theorem ha {a b : Plane} (h : A a b) : a ∈ frontier Dout := D.hV (D.hA a b h).1
theorem hb {a b : Plane} (h : A a b) : b ∈ frontier Dout := D.hV (D.hA a b h).2.1
theorem hab {a b : Plane} (h : A a b) : 0 < det (a - z) (b - z) := (D.hA a b h).2.2.1
theorem hseg {a b : Plane} (h : A a b) : segment ℝ a b ⊆ frontier Dout := (D.hA a b h).2.2.2.1
theorem hnomark {a b : Plane} (h : A a b) : ∀ c ∈ V, c ∉ openSegment ℝ a b := (D.hA a b h).2.2.2.2

theorem pos2 {a b : Plane} (h : A a b) :
    0 < det (a - u8h_f_ray Din z a) (b - u8h_f_ray Din z a) := by
  rw [u8h_AnnCtx.ray_eq, u8h_det_sub_ray]
  exact mul_pos (by linarith [D.C.s_lt_one (D.ha h)]) (D.hab h)

theorem pos1 {a b : Plane} (h : A a b) :
    0 < det (b - u8h_f_ray Din z a) (u8h_f_ray Din z b - u8h_f_ray Din z a) := by
  rw [u8h_AnnCtx.ray_eq, u8h_AnnCtx.ray_eq, u8h_det_sub_ray']
  exact mul_pos (mul_pos (D.C.s_pos (D.ha h)) (by linarith [D.C.s_lt_one (D.hb h)])) (D.hab h)

/-- The outer face of the pair `(a, b)`. -/
noncomputable def tri2 {a b : Plane} (h : A a b) : Triangle := u8h_mkTri _ _ _ (D.pos2 h)
/-- The inner face of the pair `(a, b)`. -/
noncomputable def tri1 {a b : Plane} (h : A a b) : Triangle := u8h_mkTri _ _ _ (D.pos1 h)

theorem tri2_v {a b : Plane} (h : A a b) : (D.tri2 h).v = ![u8h_f_ray Din z a, a, b] := rfl
theorem tri1_v {a b : Plane} (h : A a b) :
    (D.tri1 h).v = ![u8h_f_ray Din z a, b, u8h_f_ray Din z b] := rfl

theorem tri2_mem {a b : Plane} (h : A a b) : D.tri2 h ∈ u8h_annFaces z Din A := ⟨a, b, h, Or.inl rfl⟩
theorem tri1_mem {a b : Plane} (h : A a b) : D.tri1 h ∈ u8h_annFaces z Din A := ⟨a, b, h, Or.inr rfl⟩

theorem tri2_carrier {a b : Plane} (h : A a b) :
    (D.tri2 h).carrier = convexHull ℝ {u8h_f_ray Din z a, a, b} := u8h_f_carrier_of_v rfl
theorem tri1_carrier {a b : Plane} (h : A a b) :
    (D.tri1 h).carrier = convexHull ℝ {u8h_f_ray Din z a, b, u8h_f_ray Din z b} := u8h_f_carrier_of_v rfl

/-- Every annulus face is one of the two faces of its pair (as a carrier). -/
theorem carrier_cases {T : Triangle} (hT : T ∈ u8h_annFaces z Din A) :
    ∃ a b, ∃ h : A a b, T.carrier = (D.tri2 h).carrier ∨ T.carrier = (D.tri1 h).carrier := by
  obtain ⟨a, b, h, hv | hv⟩ := hT
  · exact ⟨a, b, h, Or.inl (by rw [u8h_f_carrier_of_v hv, D.tri2_carrier])⟩
  · exact ⟨a, b, h, Or.inr (by rw [u8h_f_carrier_of_v hv, D.tri1_carrier])⟩

theorem range_cases {T : Triangle} (hT : T ∈ u8h_annFaces z Din A) :
    ∃ a b, ∃ h : A a b, range T.v = range (D.tri2 h).v ∨ range T.v = range (D.tri1 h).v := by
  obtain ⟨a, b, h, hv | hv⟩ := hT
  · exact ⟨a, b, h, Or.inl (by rw [hv]; rfl)⟩
  · exact ⟨a, b, h, Or.inr (by rw [hv]; rfl)⟩

theorem coord {a b : Plane} (h : A a b) (x : Plane) :
    x = z + u8h_α z a b x • (a - z) + u8h_β z a b x • (b - z) := u8h_coord (D.hab h).ne' z x

theorem α_nonneg_iff {a b : Plane} (h : A a b) (x : Plane) : 0 ≤ u8h_α z a b x ↔ 0 ≤ det (x - z) (b - z) :=
  u8h_div_nonneg_iff (D.hab h)
theorem β_nonneg_iff {a b : Plane} (h : A a b) (x : Plane) : 0 ≤ u8h_β z a b x ↔ 0 ≤ det (a - z) (x - z) :=
  u8h_div_nonneg_iff (D.hab h)

/-- Membership in the outer face, in sector coordinates. -/
theorem mem_tri2_iff {a b : Plane} (h : A a b) (x : Plane) :
    x ∈ (D.tri2 h).carrier ↔ 0 ≤ u8h_β z a b x ∧ u8h_α z a b x + u8h_β z a b x ≤ 1 ∧ 1 ≤ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x := by
  have key := u8h_mem_tri2 (D.hab h) (D.C.s_pos (D.ha h)) (D.C.s_lt_one (D.ha h)) z (u8h_α z a b x) (u8h_β z a b x)
  rw [u8h_mkTri_carrier, add_sub_cancel, add_sub_cancel, ← u8h_AnnCtx.ray_eq, ← D.tri2_carrier h,
    ← D.coord h x] at key
  exact key

/-- Membership in the inner face, in sector coordinates. -/
theorem mem_tri1_iff {a b : Plane} (h : A a b) (x : Plane) :
    x ∈ (D.tri1 h).carrier ↔ 0 ≤ u8h_α z a b x ∧ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x ≤ 1 ∧
      1 ≤ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x / u8h_s Din z b := by
  have key := u8h_mem_tri1 (D.hab h) (D.C.s_pos (D.ha h)) (D.C.s_pos (D.hb h)) (D.C.s_lt_one (D.hb h)) z
    (u8h_α z a b x) (u8h_β z a b x)
  rw [u8h_mkTri_carrier, add_sub_cancel, ← u8h_AnnCtx.ray_eq, ← u8h_AnnCtx.ray_eq, ← D.tri1_carrier h,
    ← D.coord h x] at key
  exact key

/-- The outer gauge in sector coordinates. -/
theorem rgout_coord {a b : Plane} (h : A a b) {x : Plane} (hα : 0 ≤ u8h_α z a b x) (hβ : 0 ≤ u8h_β z a b x) :
    u8h_f_rg Dout z x = u8h_α z a b x + u8h_β z a b x := by
  conv_lhs => rw [D.coord h x]
  exact u8h_rg_sector D.hout D.C.hz' (D.hseg h) hα hβ

/-- The inner gauge in sector coordinates. -/
theorem rgin_coord {a b : Plane} (h : A a b) {x : Plane} (hα : 0 ≤ u8h_α z a b x) (hβ : 0 ≤ u8h_β z a b x) :
    u8h_f_rg Din z x = u8h_α z a b x / u8h_s Din z a + u8h_β z a b x / u8h_s Din z b := by
  have hsa := D.C.s_pos (D.ha h)
  have hsb := D.C.s_pos (D.hb h)
  have e : x = z + (u8h_α z a b x / u8h_s Din z a) • (u8h_f_ray Din z a - z) +
      (u8h_β z a b x / u8h_s Din z b) • (u8h_f_ray Din z b - z) := by
    rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, smul_smul, smul_smul, div_mul_cancel₀ _ hsa.ne',
      div_mul_cancel₀ _ hsb.ne']
    exact D.coord h x
  conv_lhs => rw [e]
  exact u8h_rg_sector D.hin D.hz (D.hstraight a b h) (div_nonneg hα hsa.le) (div_nonneg hβ hsb.le)

/-- The quadrilateral of the pair `(a, b)`: the union of its two faces, in sector coordinates. -/
theorem mem_quad_iff {a b : Plane} (h : A a b) (x : Plane) :
    x ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier ↔
      0 ≤ u8h_α z a b x ∧ 0 ≤ u8h_β z a b x ∧ u8h_α z a b x + u8h_β z a b x ≤ 1 ∧
        1 ≤ u8h_α z a b x / u8h_s Din z a + u8h_β z a b x / u8h_s Din z b := by
  rw [mem_union, D.mem_tri2_iff, D.mem_tri1_iff]
  exact u8h_quad_iff (D.C.s_pos (D.ha h)) (D.C.s_lt_one (D.ha h)) (D.C.s_pos (D.hb h)) (D.C.s_lt_one (D.hb h)) _ _

/-- A point of the quadrilateral lies in the annulus. -/
theorem quad_subset {a b : Plane} (h : A a b) :
    (D.tri2 h).carrier ∪ (D.tri1 h).carrier ⊆ Dout \ interior Din := by
  intro x hx
  obtain ⟨h0, h1, h2, h3⟩ := (D.mem_quad_iff h x).1 hx
  refine ⟨?_, ?_⟩
  · rw [← u8h_f_rg_le_one_iff D.hout D.C.hz', D.rgout_coord h h0 h1]; exact h2
  · rw [← u8h_f_rg_lt_one_iff D.hin D.hz, D.rgin_coord h h0 h1]; linarith

/-- The fan triangulation of the outer disc by the adjacent pairs. -/
theorem fan : ∃ K : Triangulation Dout, K.faces = u8h_f_fanFaces z A :=
  u8h_f_fan_triangulation D.hout D.C.hz' D.hVfin D.hV D.hA D.hcov

/-- Every point of the annulus lies in the quadrilateral of some adjacent pair. -/
theorem cover_of_mem {x : Plane} (hx : x ∈ Dout \ interior Din) :
    ∃ a b, ∃ h : A a b, x ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier := by
  obtain ⟨K, hK⟩ := D.fan
  have hxK : x ∈ ⋃ T ∈ K.faces, T.carrier := by rw [K.cover]; exact hx.1
  obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hxK
  rw [hK] at hT
  obtain ⟨a, b, h, hv⟩ := hT
  rw [u8h_f_carrier_of_v hv, u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hxT
  obtain ⟨h1, h2, h3⟩ := hxT
  refine ⟨a, b, h, (D.mem_quad_iff h x).2 ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (D.α_nonneg_iff h x).2 h2
  · exact (D.β_nonneg_iff h x).2 h1
  · rw [← D.rgout_coord h ((D.α_nonneg_iff h x).2 h2) ((D.β_nonneg_iff h x).2 h1),
      u8h_f_rg_le_one_iff D.hout D.C.hz']; exact h3
  · rw [← D.rgin_coord h ((D.α_nonneg_iff h x).2 h2) ((D.β_nonneg_iff h x).2 h1)]
    have := hx.2
    rw [← u8h_f_rg_lt_one_iff D.hin D.hz] at this
    push Not at this; exact this

end u8h_AnnData

namespace u8h_AnnData

variable {z : Plane} {Din Dout V : Set Plane} {A : Plane → Plane → Prop} (D : u8h_AnnData z Din Dout V A)
include D

/-- The fan face of the pair `(a, b)` in the outer disc. -/
noncomputable def fanTri {a b : Plane} (h : A a b) : Triangle := u8h_mkTri z a b (D.hab h)

theorem fanTri_carrier {a b : Plane} (h : A a b) : (D.fanTri h).carrier = convexHull ℝ {z, a, b} :=
  u8h_mkTri_carrier _ _ _ _

theorem fanTri_mem {K : Triangulation Dout} (hK : K.faces = u8h_f_fanFaces z A) {a b : Plane} (h : A a b) :
    D.fanTri h ∈ K.faces := by
  rw [hK]; exact ⟨a, b, h, rfl⟩

theorem ray_mem_fan {a b : Plane} (h : A a b) : u8h_f_ray Din z a ∈ convexHull ℝ {z, a, b} := by
  have hs0 := (D.C.s_pos (D.ha h)).le
  have hs1 := (D.C.s_lt_one (D.ha h)).le
  have : u8h_f_ray Din z a ∈ segment ℝ z a :=
    ⟨1 - u8h_s Din z a, u8h_s Din z a, by linarith, hs0, by ring, by
      rw [u8h_AnnCtx.ray_eq, smul_sub]; module⟩
  exact segment_subset_convexHull (by simp) (by simp) this

theorem ray_mem_fan' {a b : Plane} (h : A a b) : u8h_f_ray Din z b ∈ convexHull ℝ {z, a, b} := by
  have hs0 := (D.C.s_pos (D.hb h)).le
  have hs1 := (D.C.s_lt_one (D.hb h)).le
  have : u8h_f_ray Din z b ∈ segment ℝ z b :=
    ⟨1 - u8h_s Din z b, u8h_s Din z b, by linarith, hs0, by ring, by
      rw [u8h_AnnCtx.ray_eq, smul_sub]; module⟩
  exact segment_subset_convexHull (by simp) (by simp) this

theorem tri2_subset_fan {a b : Plane} (h : A a b) : (D.tri2 h).carrier ⊆ convexHull ℝ {z, a, b} := by
  rw [D.tri2_carrier]
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro w hw
  simp only [mem_insert_iff, mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact D.ray_mem_fan h
  · exact subset_convexHull ℝ _ (by simp)
  · exact subset_convexHull ℝ _ (by simp)

theorem tri1_subset_fan {a b : Plane} (h : A a b) : (D.tri1 h).carrier ⊆ convexHull ℝ {z, a, b} := by
  rw [D.tri1_carrier]
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro w hw
  simp only [mem_insert_iff, mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact D.ray_mem_fan h
  · exact subset_convexHull ℝ _ (by simp)
  · exact D.ray_mem_fan' h

theorem quad_subset_fan {a b : Plane} (h : A a b) :
    (D.tri2 h).carrier ∪ (D.tri1 h).carrier ⊆ convexHull ℝ {z, a, b} :=
  union_subset (D.tri2_subset_fan h) (D.tri1_subset_fan h)

/-- (V1) an outer mark lying in the quadrilateral of `(a, b)` is `a` or `b`. -/
theorem mark_of_mem_quad {a b c : Plane} (h : A a b) (hc : c ∈ V)
    (hcq : c ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier) : c = a ∨ c = b := by
  have hcf := D.quad_subset_fan h hcq
  rw [u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hcf
  have hcs := u8h_f_frontier_mem_segment D.hout D.C.hz' (D.hab h) (D.hseg h) (D.hV hc) hcf.1 hcf.2.1
  rcases u8h_f_mem_segment_cases hcs with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 (D.hnomark h c hc)

/-- (V2) the inner point of an outer mark lying in the quadrilateral of `(a, b)` is `Pt a` or `Pt b`. -/
theorem ray_of_mem_quad {a b c : Plane} (h : A a b) (hc : c ∈ V)
    (hcq : u8h_f_ray Din z c ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier) :
    u8h_f_ray Din z c = u8h_f_ray Din z a ∨ u8h_f_ray Din z c = u8h_f_ray Din z b := by
  have hcf := D.quad_subset_fan h hcq
  rw [u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hcf
  have hne : u8h_f_ray Din z c ≠ z := D.C.ray_ne (D.hV hc)
  have hcs := u8h_f_ray_mem_segment D.hout D.C.hz' (D.hab h) (D.hseg h) hne hcf.1 hcf.2.1
  rw [D.C.rayout_ray (D.hV hc)] at hcs
  rcases u8h_f_mem_segment_cases hcs with h1 | h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1])
  · exact absurd h1 (D.hnomark h c hc)

/-- (V3) the outer mark `a` is not in the inner face. -/
theorem a_notMem_tri1 {a b : Plane} (h : A a b) : a ∉ (D.tri1 h).carrier := by
  rw [D.mem_tri1_iff]
  have hα : u8h_α z a b a = 1 := div_self (D.hab h).ne'
  have hβ : u8h_β z a b a = 0 := by rw [u8h_β, u8h_f_det_self, zero_div]
  rw [hα, hβ, add_zero]
  rintro ⟨-, h1, -⟩
  have hs := D.C.s_pos (D.ha h)
  rw [div_le_one hs] at h1
  linarith [D.C.s_lt_one (D.ha h)]

/-- (V4) the inner point `Pt b` is not in the outer face. -/
theorem ray_b_notMem_tri2 {a b : Plane} (h : A a b) : u8h_f_ray Din z b ∉ (D.tri2 h).carrier := by
  rw [D.mem_tri2_iff]
  have hα : u8h_α z a b (u8h_f_ray Din z b) = 0 := by
    rw [u8h_α, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_self, mul_zero, zero_div]
  have hβ : u8h_β z a b (u8h_f_ray Din z b) = u8h_s Din z b := by
    rw [u8h_β, u8h_AnnCtx.ray_sub, u8h_f_det_smul_right, mul_div_assoc, div_self (D.hab h).ne', mul_one]
  rw [hα, hβ, zero_div, zero_add]
  rintro ⟨-, -, h1⟩
  linarith [D.C.s_lt_one (D.hb h)]

/-- The vertex condition of the gluing criterion. -/
theorem vert_mem {T T' : Triangle} (hT : T ∈ u8h_annFaces z Din A) (hT' : T' ∈ u8h_annFaces z Din A)
    (j : Fin 3) (hj : T'.v j ∈ T.carrier) : T'.v j ∈ range T.v := by
  obtain ⟨a, b, h, hcar⟩ := D.carrier_cases hT
  obtain ⟨a', b', h', hr'⟩ := D.range_cases hT'
  have hw : T'.v j ∈ range T'.v := mem_range_self j
  have ha' : a' ∈ V := (D.hA a' b' h').1
  have hb' : b' ∈ V := (D.hA a' b' h').2.1
  -- the vertex is an outer mark or the inner point of an outer mark
  have hcases : (∃ c ∈ V, T'.v j = c) ∨ (∃ c ∈ V, T'.v j = u8h_f_ray Din z c) := by
    rcases hr' with hr' | hr'
    · rw [hr', D.tri2_v, u8h_f_range_three] at hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with hw | hw | hw
      · exact Or.inr ⟨a', ha', hw⟩
      · exact Or.inl ⟨a', ha', hw⟩
      · exact Or.inl ⟨b', hb', hw⟩
    · rw [hr', D.tri1_v, u8h_f_range_three] at hw
      simp only [mem_insert_iff, mem_singleton_iff] at hw
      rcases hw with hw | hw | hw
      · exact Or.inr ⟨a', ha', hw⟩
      · exact Or.inl ⟨b', hb', hw⟩
      · exact Or.inr ⟨b', hb', hw⟩
  rcases hcar with hcar | hcar
  · -- `T` is the outer face of `(a, b)`
    have hrT : range T.v = range (D.tri2 h).v := u3h_range_eq_of_carrier_eq hcar
    rw [hcar] at hj
    have hq : T'.v j ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier := Or.inl hj
    rw [hrT, D.tri2_v, u8h_f_range_three]
    rcases hcases with ⟨c, hcV, hwc⟩ | ⟨c, hcV, hwc⟩
    · rw [hwc] at hq ⊢
      rcases D.mark_of_mem_quad h hcV hq with rfl | rfl <;> simp
    · rw [hwc] at hq hj ⊢
      rcases D.ray_of_mem_quad h hcV hq with hcc | hcc
      · rw [hcc]; simp
      · rw [hcc] at hj; exact absurd hj (D.ray_b_notMem_tri2 h)
  · -- `T` is the inner face of `(a, b)`
    have hrT : range T.v = range (D.tri1 h).v := u3h_range_eq_of_carrier_eq hcar
    rw [hcar] at hj
    have hq : T'.v j ∈ (D.tri2 h).carrier ∪ (D.tri1 h).carrier := Or.inr hj
    rw [hrT, D.tri1_v, u8h_f_range_three]
    rcases hcases with ⟨c, hcV, hwc⟩ | ⟨c, hcV, hwc⟩
    · rw [hwc] at hq hj ⊢
      rcases D.mark_of_mem_quad h hcV hq with rfl | rfl
      · exact absurd hj (D.a_notMem_tri1 h)
      · simp
    · rw [hwc] at hq ⊢
      rcases D.ray_of_mem_quad h hcV hq with hcc | hcc <;> rw [hcc] <;> simp



/-- Two adjacent pairs spanning the same fan face are equal. -/
theorem pair_eq_of_range {a b a' b' : Plane} (h : A a b) (h' : A a' b')
    (hr : ({z, a, b} : Set Plane) = {z, a', b'}) : a = a' ∧ b = b' := by
  have haz : a ≠ z := D.C.ne_of_frontier (D.ha h)
  have hbz : b ≠ z := D.C.ne_of_frontier (D.hb h)
  have hab_ne : a ≠ b := fun e => by
    have := D.hab h; rw [e, u8h_f_det_self] at this; exact lt_irrefl _ this
  have ha : a ∈ ({z, a', b'} : Set Plane) := by rw [← hr]; simp
  have hb : b ∈ ({z, a', b'} : Set Plane) := by rw [← hr]; simp
  simp only [mem_insert_iff, mem_singleton_iff] at ha hb
  rcases ha with ha | ha | ha
  · exact absurd ha haz
  · rcases hb with hb | hb | hb
    · exact absurd hb hbz
    · exact absurd (ha.trans hb.symm) hab_ne
    · exact ⟨ha, hb⟩
  · rcases hb with hb | hb | hb
    · exact absurd hb hbz
    · exfalso
      have h1 := D.hab h
      have h2 := D.hab h'
      rw [ha, hb, u8h_f_det_swap'] at h1
      linarith
    · exact absurd (ha.trans hb.symm) hab_ne

/-- The two faces of a pair are separated by their common diagonal. -/
theorem diag_sep {a b : Plane} (h : A a b) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p ((D.tri2 h).v i) ≤ r) ∧
      ∀ i, r ≤ planeDot p ((D.tri1 h).v i) := by
  set Pa := u8h_f_ray Din z a with hPa
  set Pb := u8h_f_ray Din z b with hPb
  have hne : b - Pa ≠ 0 := by
    intro e; have := D.pos1 h; rw [← hPa, ← hPb, e, u8h_f_det_zero_left] at this; exact lt_irrefl _ this
  have key : ∀ x, planeDot (u3h_dir (b - Pa)) x - planeDot (u3h_dir (b - Pa)) Pa = det (b - Pa) (x - Pa) := by
    intro x; rw [u3h_det_eq_planeDot, u3h_planeDot_sub]
  refine ⟨u3h_dir (b - Pa), planeDot (u3h_dir (b - Pa)) Pa, u3h_dir_ne_zero hne, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact le_refl _
    · show planeDot (u3h_dir (b - Pa)) a ≤ _
      have h1 := key a
      have h2 := D.pos2 h
      rw [← hPa] at h2
      rw [u8h_f_det_swap'] at h1
      linarith
    · show planeDot (u3h_dir (b - Pa)) b ≤ _
      have h1 := key b
      rw [u8h_f_det_self] at h1
      linarith
  · intro i
    fin_cases i
    · exact le_refl _
    · show _ ≤ planeDot (u3h_dir (b - Pa)) b
      have h1 := key b
      rw [u8h_f_det_self] at h1
      linarith
    · show _ ≤ planeDot (u3h_dir (b - Pa)) Pb
      have h1 := key Pb
      have h2 := D.pos1 h
      rw [← hPa, ← hPb] at h2
      linarith

/-- The separation condition of the gluing criterion. -/
theorem sep {T T' : Triangle} (hT : T ∈ u8h_annFaces z Din A) (hT' : T' ∈ u8h_annFaces z Din A)
    (hne : T.carrier ≠ T'.carrier) :
    ∃ (p : Plane) (r : ℝ), p ≠ 0 ∧ (∀ i, planeDot p (T.v i) ≤ r) ∧ ∀ i, r ≤ planeDot p (T'.v i) := by
  obtain ⟨K, hK⟩ := D.fan
  obtain ⟨a, b, h, hc⟩ := D.carrier_cases hT
  obtain ⟨a', b', h', hc'⟩ := D.carrier_cases hT'
  have hvT : ∀ i, T.v i ∈ T.carrier := fun i => subset_convexHull ℝ _ (mem_range_self i)
  have hvT' : ∀ i, T'.v i ∈ T'.carrier := fun i => subset_convexHull ℝ _ (mem_range_self i)
  have hsubT : T.carrier ⊆ convexHull ℝ {z, a, b} := by
    rcases hc with hc | hc
    · rw [hc]; exact D.tri2_subset_fan h
    · rw [hc]; exact D.tri1_subset_fan h
  have hsubT' : T'.carrier ⊆ convexHull ℝ {z, a', b'} := by
    rcases hc' with hc' | hc'
    · rw [hc']; exact D.tri2_subset_fan h'
    · rw [hc']; exact D.tri1_subset_fan h'
  by_cases hF : (D.fanTri h).carrier = (D.fanTri h').carrier
  · have hr := u3h_range_eq_of_carrier_eq hF
    rw [fanTri, fanTri, u8h_mkTri_range, u8h_mkTri_range] at hr
    obtain ⟨rfl, rfl⟩ := D.pair_eq_of_range h h' hr
    obtain ⟨p, r, hp, h1, h2⟩ := D.diag_sep h
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · exact absurd (hc.trans hc'.symm) hne
    · refine ⟨p, r, hp, fun i => ?_, fun i => ?_⟩
      · exact u3h_carrier_subset_le _ h1 (hc ▸ hvT i)
      · exact u3h_carrier_subset_ge _ h2 (hc' ▸ hvT' i)
    · refine ⟨-p, -r, neg_ne_zero.2 hp, fun i => ?_, fun i => ?_⟩
      · rw [u3h_planeDot_neg_left]
        have := u3h_carrier_subset_ge _ h2 (hc ▸ hvT i)
        simp only [mem_ofPred_eq] at this; linarith
      · rw [u3h_planeDot_neg_left]
        have := u3h_carrier_subset_le _ h1 (hc' ▸ hvT' i)
        simp only [mem_ofPred_eq] at this; linarith
    · exact absurd (hc.trans hc'.symm) hne
  · obtain ⟨p, r, hp, h1, h2⟩ := u3h_faces_separated K (D.fanTri_mem hK h) (D.fanTri_mem hK h') hF
    refine ⟨p, r, hp, fun i => ?_, fun i => ?_⟩
    · have := hsubT (hvT i)
      rw [← D.fanTri_carrier h] at this
      exact u3h_carrier_subset_le _ h1 this
    · have := hsubT' (hvT' i)
      rw [← D.fanTri_carrier h'] at this
      exact u3h_carrier_subset_ge _ h2 this

theorem faces_finite : (u8h_annFaces z Din A).Finite := by
  have hS : {p : Plane × Plane | A p.1 p.2}.Finite := by
    apply (D.hVfin.prod D.hVfin).subset
    rintro ⟨a, b⟩ h; exact ⟨(D.hA a b h).1, (D.hA a b h).2.1⟩
  have himg : Triangle.v '' u8h_annFaces z Din A ⊆
      (fun p : Plane × Plane => ![u8h_f_ray Din z p.1, p.1, p.2]) '' {p | A p.1 p.2} ∪
      (fun p : Plane × Plane => ![u8h_f_ray Din z p.1, p.2, u8h_f_ray Din z p.2]) '' {p | A p.1 p.2} := by
    rintro _ ⟨T, ⟨a, b, h, hv | hv⟩, rfl⟩
    · exact Or.inl ⟨(a, b), h, hv.symm⟩
    · exact Or.inr ⟨(a, b), h, hv.symm⟩
  refine Set.Finite.of_finite_image (f := Triangle.v) (((hS.image _).union (hS.image _)).subset himg) ?_
  rintro ⟨v, hv⟩ _ ⟨v', hv'⟩ _ hTT'
  simp only at hTT'
  subst hTT'; rfl

theorem cover_eq : (⋃ T ∈ u8h_annFaces z Din A, T.carrier) = Dout \ interior Din := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hx
    obtain ⟨a, b, h, hc⟩ := D.carrier_cases hT
    apply D.quad_subset h
    rcases hc with hc | hc
    · exact Or.inl (hc ▸ hxT)
    · exact Or.inr (hc ▸ hxT)
  · intro x hx
    obtain ⟨a, b, h, hq⟩ := D.cover_of_mem hx
    rcases hq with hq | hq
    · exact mem_iUnion₂.2 ⟨_, D.tri2_mem h, hq⟩
    · exact mem_iUnion₂.2 ⟨_, D.tri1_mem h, hq⟩

/-- **The radial annulus triangulation.** -/
theorem triangulation : ∃ K : Triangulation (Dout \ interior Din), K.faces = u8h_annFaces z Din A :=
  ⟨⟨u8h_annFaces z Din A, D.faces_finite, D.cover_eq,
    u3h_inter_of_family (fun _ hT _ hT' hne => D.sep hT hT' hne)
      (fun _ hT _ hT' j hj => D.vert_mem hT hT' j hj)⟩, rfl⟩

/-- Every point of the inner frontier lies on the inner edge of some pair. -/
theorem frontier_in_cover {y : Plane} (hy : y ∈ frontier Din) :
    ∃ a b, ∃ _ : A a b, y ∈ segment ℝ (u8h_f_ray Din z a) (u8h_f_ray Din z b) := by
  have hyD : y ∈ Din := D.hin.2.1.isClosed.frontier_subset hy
  have hy' : y ∈ Dout \ interior Din := ⟨interior_subset (D.ctx.hsub hyD), hy.2⟩
  obtain ⟨a, b, h, hq⟩ := D.cover_of_mem hy'
  have hf := D.quad_subset_fan h hq
  rw [u8h_f_mem_fan_iff D.hout D.C.hz' (D.hab h) (D.hseg h)] at hf
  have h1 : 0 ≤ det (u8h_f_ray Din z a - z) (y - z) := by
    rw [u8h_AnnCtx.ray_sub, u8h_f_det_smul_left']; exact mul_nonneg (D.C.s_pos (D.ha h)).le hf.1
  have h2 : 0 ≤ det (y - z) (u8h_f_ray Din z b - z) := by
    rw [u8h_AnnCtx.ray_sub, u8h_f_det_smul_right]; exact mul_nonneg (D.C.s_pos (D.hb h)).le hf.2.1
  exact ⟨a, b, h, u8h_f_frontier_mem_segment D.hin D.hz (D.C.det_ray_ray (D.ha h) (D.hb h) (D.hab h))
    (D.hstraight a b h) hy h1 h2⟩

end u8h_AnnData

/-! ### U8 helpers: the model square as a disc, its frontier and corners -/

theorem u8h_isClosed_square (L : ℝ) : IsClosed (square L) :=
  isClosed_le u8h_continuous_supNorm continuous_const

theorem u8h_frontier_square (L : ℝ) : frontier (square L) = {x | supNorm x = L} := by
  ext x
  rw [(u8h_isClosed_square L).frontier_eq, mem_sdiff, u8h_mem_interior_square_iff]
  simp only [square, mem_ofPred_eq, not_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2
  · intro h; exact ⟨h.le, h.ge⟩

theorem u8h_mem_frontier_square {L : ℝ} {x : Plane} : x ∈ frontier (square L) ↔ supNorm x = L := by
  rw [u8h_frontier_square]; rfl

/-- The four corners of `Q_L`, counterclockwise from `(L, -L)`. -/
def u8h_corner (L : ℝ) : Fin 4 → Plane := ![(L, -L), (L, L), (-L, L), (-L, -L)]

theorem u8h_supNorm_eq_of_abs {x : Plane} {L : ℝ} (h1 : |x.1| ≤ L) (h2 : |x.2| ≤ L)
    (h : |x.1| = L ∨ |x.2| = L) : supNorm x = L := by
  unfold supNorm
  rcases h with h | h
  · rw [max_eq_left (h ▸ h2), h]
  · rw [max_eq_right (h ▸ h1), h]

/-- A side of the square lies on its frontier. -/
theorem u8h_side_subset_frontier {L : ℝ} (hL : 0 < L) (j : Fin 4) :
    segment ℝ (u8h_corner L j) (u8h_corner L (j + 1)) ⊆ frontier (square L) := by
  intro x hx
  rw [u8h_mem_frontier_square]
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  have hL' : |L| = L := abs_of_pos hL
  fin_cases j <;> simp only [u8h_corner, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Fin.reduceAdd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] <;>
  · apply u8h_supNorm_eq_of_abs <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      first
      | (left; rw [show s * L + t * L = L by rw [← add_mul, hst, one_mul]]; exact hL')
      | (right; rw [show s * L + t * L = L by rw [← add_mul, hst, one_mul]]; exact hL')
      | (left; rw [show s * -L + t * -L = -L by rw [← add_mul, hst, one_mul]]; rw [abs_neg]; exact hL')
      | (right; rw [show s * -L + t * -L = -L by rw [← add_mul, hst, one_mul]]; rw [abs_neg]; exact hL')
      | (rw [abs_le]; constructor <;> nlinarith [abs_nonneg s, abs_nonneg t])


/-- A point of the frontier lies on one of the four sides. -/
theorem u8h_frontier_subset_sides {L : ℝ} (hL : 0 < L) {x : Plane} (hx : x ∈ frontier (square L)) :
    ∃ j : Fin 4, x ∈ segment ℝ (u8h_corner L j) (u8h_corner L (j + 1)) := by
  rw [u8h_mem_frontier_square] at hx
  have h1 : |x.1| ≤ L := hx ▸ le_max_left _ _
  have h2 : |x.2| ≤ L := hx ▸ le_max_right _ _
  rw [abs_le] at h1 h2
  have hL2 : (0 : ℝ) < 2 * L := by linarith
  rcases max_choice |x.1| |x.2| with h | h
  · have hx' : |x.1| = L := by rw [← h]; exact hx
    rcases abs_eq (hL.le) |>.1 hx' with h' | h'
    · -- right side, from (L, -L) to (L, L)
      refine ⟨0, (L - x.2) / (2 * L), (x.2 + L) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((L - x.2) / (2 * L)) • ((L, -L) : Plane) + ((x.2 + L) / (2 * L)) • ((L, L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith
    · -- left side, from (-L, L) to (-L, -L)
      refine ⟨2, (x.2 + L) / (2 * L), (L - x.2) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((x.2 + L) / (2 * L)) • ((-L, L) : Plane) + ((L - x.2) / (2 * L)) • ((-L, -L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith
  · have hx' : |x.2| = L := by rw [← h]; exact hx
    rcases abs_eq (hL.le) |>.1 hx' with h' | h'
    · -- top side, from (L, L) to (-L, L)
      refine ⟨1, (x.1 + L) / (2 * L), (L - x.1) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((x.1 + L) / (2 * L)) • ((L, L) : Plane) + ((L - x.1) / (2 * L)) • ((-L, L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith
    · -- bottom side, from (-L, -L) to (L, -L)
      refine ⟨3, (L - x.1) / (2 * L), (x.1 + L) / (2 * L), div_nonneg (by linarith) hL2.le,
        div_nonneg (by linarith) hL2.le, ?_, ?_⟩
      · field_simp; ring
      · show ((L - x.1) / (2 * L)) • ((-L, -L) : Plane) + ((x.1 + L) / (2 * L)) • ((L, -L) : Plane) = x
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
          field_simp <;> ring_nf <;> linarith

theorem u8h_frontier_square_eq_sides {L : ℝ} (hL : 0 < L) :
    (⋃ j : Fin 4, segment ℝ (u8h_corner L j) (u8h_corner L (j + 1))) = frontier (square L) := by
  apply Subset.antisymm
  · exact iUnion_subset fun j => u8h_side_subset_frontier hL j
  · intro x hx
    obtain ⟨j, hj⟩ := u8h_frontier_subset_sides hL hx
    exact mem_iUnion.2 ⟨j, hj⟩


/-! ### U8 helpers: `det` algebra around a centre -/

/-- Expansion of `det V B` in the basis `A, M`. -/
theorem u8h_cramer_det {A M : Plane} (hAM : det A M ≠ 0) (V B : Plane) :
    det V B = (det V M / det A M) * det A B + (det A V / det A M) * det M B := by
  conv_lhs => rw [u8h_f_cramer hAM V]
  rw [u8h_f_det_comb_left]

/-- The `det` signs of a point of a segment seen from a centre. -/
theorem u8h_det_of_mem_segment {z p q y : Plane} (hy : y ∈ segment ℝ p q) (hpq : 0 ≤ det (p - z) (q - z)) :
    0 ≤ det (p - z) (y - z) ∧ 0 ≤ det (y - z) (q - z) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hy
  have e : s • p + t • q - z = s • (p - z) + t • (q - z) := by
    have : z = s • z + t • z := by rw [← add_smul, hst, one_smul]
    conv_lhs => rw [this]
    rw [smul_sub, smul_sub]; abel
  rw [e, u8h_f_det_comb_right, u8h_f_det_comb_left, u8h_f_det_self, u8h_f_det_self]
  constructor
  · nlinarith
  · nlinarith

/-- Two frontier points on the same ray from an interior point coincide. -/
theorem u8h_eq_of_det_zero {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a a' : Plane} (ha : a ∈ frontier D) (ha' : a' ∈ frontier D) (h0 : det (a' - z) (a - z) = 0)
    {y : Plane} (hy : 0 < det (a - z) (y - z)) (hy' : 0 ≤ det (a' - z) (y - z)) : a' = a := by
  have hne : a' - z ≠ 0 := sub_ne_zero.2 (u8h_f_frontier_ne hD hz ha')
  obtain ⟨t, ht⟩ := u8h_f_parallel_of_det_eq_zero hne h0
  have htpos : 0 < t := by
    rw [ht, u8h_f_det_smul_left'] at hy
    by_contra hneg; push Not at hneg
    nlinarith
  have h1 : u8h_f_rg D z a = t * u8h_f_rg D z a' := by
    have : a = z + t • (a' - z) := by rw [← ht]; abel
    rw [this, u8h_f_rg_smul _ _ _ htpos.le]
  rw [(u8h_f_rg_eq_one_iff hD hz a).2 ha, (u8h_f_rg_eq_one_iff hD hz a').2 ha', mul_one] at h1
  rw [← h1, one_smul] at ht
  exact (sub_left_inj.1 ht).symm

/-- The sign of `det (a - z) (b - z)` is the same for all interior points `z` (for a frontier piece
`[a, b]`). -/
theorem u8h_det_sign_const {D : Set Plane} (hD : Link.IsDisc D) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D) {a b : Plane} (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier D)
    (hpos : 0 < det (a - z) (b - z)) : 0 < det (a - z') (b - z') := by
  have hne' := u8h_f_det_ne_zero_of_segment hD hz' hne hseg
  rcases lt_or_gt_of_ne hne' with hneg | hpos'
  · exfalso
    set f : Plane → ℝ := fun w => det (a - w) (b - w) with hf
    have haff : ∀ w w' : Plane, ∀ t : ℝ, f (w + t • (w' - w)) = f w + t * (f w' - f w) := by
      intro w w' t
      simp only [hf, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    have hfz : 0 < f z := hpos
    have hfz' : f z' < 0 := hneg
    set t := f z / (f z - f z') with ht
    have hden : 0 < f z - f z' := by linarith
    have ht0 : 0 ≤ t := div_nonneg hfz.le hden.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hden]; linarith
    have hw : z + t • (z' - z) ∈ interior D :=
      (Convex.interior hD.1) hz hz' (by linarith : 0 ≤ 1 - t) ht0 (by ring) |> fun h => by
        convert h using 1; rw [smul_sub]; module
    have h0 : f (z + t • (z' - z)) = 0 := by
      rw [haff, ht]; field_simp; ring
    exact u8h_f_det_ne_zero_of_segment hD hw hne hseg h0
  · exact hpos'

/-- The inner projection of the outer projection of an inner frontier point is the point. -/
theorem u8h_AnnCtx.rayin_rayout {z : Plane} {Din Dout : Set Plane} (C : u8h_AnnCtx z Din Dout) {v : Plane}
    (hv : v ∈ frontier Din) : u8h_f_ray Din z (u8h_f_ray Dout z v) = v := by
  have hvz : v ≠ z := u8h_f_frontier_ne C.hin C.hz hv
  have hr : 0 < u8h_f_rg Dout z v := u8h_f_rg_pos C.hout C.hz' hvz
  have e : u8h_f_ray Dout z v = z + (u8h_f_rg Dout z v)⁻¹ • (v - z) := rfl
  rw [u8h_f_ray, e, u8h_f_rg_smul _ _ _ (inv_pos.2 hr).le, (u8h_f_rg_eq_one_iff C.hin C.hz v).2 hv, mul_one,
    inv_inv, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]


/-! ### U8 helpers: the seam reflection `ρ_L x = (x₁ / L, -x₂ / L)` -/

/-- The affine seam map: `capInvFun L` restricted to `∂Q_L`, extended linearly. -/
noncomputable def u8h_ρ (L : ℝ) (x : Plane) : Plane := (x.1 / L, -x.2 / L)

theorem u8h_ρ_smul (L c : ℝ) (x : Plane) : u8h_ρ L (c • x) = c • u8h_ρ L x := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_add (L : ℝ) (x y : Plane) : u8h_ρ L (x + y) = u8h_ρ L x + u8h_ρ L y := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_sub (L : ℝ) (x y : Plane) : u8h_ρ L (x - y) = u8h_ρ L x - u8h_ρ L y := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_zero (L : ℝ) : u8h_ρ L 0 = 0 := by ext <;> simp [u8h_ρ]

theorem u8h_det_ρ (L : ℝ) (x y : Plane) : det (u8h_ρ L x) (u8h_ρ L y) = -(det x y / L ^ 2) := by
  simp only [u8h_ρ, det]; ring

theorem u8h_supNorm_ρ {L : ℝ} (hL : 0 < L) (x : Plane) : supNorm (u8h_ρ L x) = supNorm x / L := by
  simp only [u8h_ρ, supNorm, abs_div, abs_neg, abs_of_pos hL]
  rcases le_total |x.1| |x.2| with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hL.le)]
  · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h hL.le)]

theorem u8h_ρ_injective {L : ℝ} (hL : 0 < L) : Function.Injective (u8h_ρ L) := by
  intro x y h
  simp only [u8h_ρ, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [div_left_inj' hL.ne'] at h1 h2
  exact Prod.ext h1 (neg_inj.1 h2)

theorem u8h_ρ_ρ (L : ℝ) (x : Plane) : u8h_ρ L (u8h_ρ L x) = (L ^ 2)⁻¹ • x := by
  ext <;> simp [u8h_ρ] <;> ring

theorem u8h_ρ_mem_segment {L : ℝ} (hL : 0 < L) {a b y : Plane} :
    u8h_ρ L y ∈ segment ℝ (u8h_ρ L a) (u8h_ρ L b) ↔ y ∈ segment ℝ a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, h⟩
    refine ⟨s, t, hs, ht, hst, u8h_ρ_injective hL ?_⟩
    rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul, h]
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul]⟩

theorem u8h_ρ_mem_openSegment {L : ℝ} (hL : 0 < L) {a b y : Plane} :
    u8h_ρ L y ∈ openSegment ℝ (u8h_ρ L a) (u8h_ρ L b) ↔ y ∈ openSegment ℝ a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, h⟩
    refine ⟨s, t, hs, ht, hst, u8h_ρ_injective hL ?_⟩
    rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul, h]
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [u8h_ρ_add, u8h_ρ_smul, u8h_ρ_smul]⟩

theorem u8h_ρ_image_segment {L : ℝ} (hL : 0 < L) (a b : Plane) :
    u8h_ρ L '' segment ℝ a b = segment ℝ (u8h_ρ L a) (u8h_ρ L b) := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩; exact (u8h_ρ_mem_segment hL).2 hx
  · intro hy
    refine ⟨(L ^ 2) • u8h_ρ L y, ?_, ?_⟩
    · rw [← u8h_ρ_mem_segment hL, u8h_ρ_smul, u8h_ρ_ρ, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hL.ne'),
        one_smul]; exact hy
    · rw [u8h_ρ_smul, u8h_ρ_ρ, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hL.ne'), one_smul]

/-- On the seam the cap inverse is `ρ`. -/
theorem u8h_capInvFun_eq_ρ {L : ℝ} (hL : 0 < L) {x : Plane} (hx : supNorm x = L) :
    capInvFun L x = u8h_ρ L x := by
  simp only [capInvFun, u8h_ρ, hx]
  ext <;> simp <;> field_simp

/-! ### U8 helpers: the remaining piece of the fan toolkit (`u10h_cover`, copied) -/

theorem u8h_f_ray_continuousAt {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : ContinuousAt (u8h_f_ray D z) x := by
  have : u8h_f_ray D z = fun x => z + (u8h_f_rg D z x)⁻¹ • (x - z) := rfl
  rw [this]
  exact continuousAt_const.add
    ((((u8h_f_rg_continuous hD hz).continuousAt).inv₀ (u8h_f_rg_pos hD hz hx).ne').smul
      (continuousAt_id.sub continuousAt_const))

theorem u8h_f_not_isolated {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ frontier D, w ≠ y ∧ dist w y < ε := by
  have hyz := u8h_f_frontier_ne hD hz hy
  have hu : y - z ≠ 0 := sub_ne_zero.mpr hyz
  set v : Plane := (-(y - z).2, (y - z).1) with hv
  have hdet : 0 < det (y - z) v := by
    have : det (y - z) v = (y - z).1 ^ 2 + (y - z).2 ^ 2 := by simp only [det, hv]; ring
    rw [this]
    rcases not_and_or.mp (fun hc : (y - z).1 = 0 ∧ (y - z).2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  set g : ℝ → Plane := fun t => u8h_f_ray D z (y + t • v) with hg
  have hg0 : g 0 = y := by simp [hg, u8h_f_ray_of_frontier hD hz hy]
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun t : ℝ => y + t • v) 0 := continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have h2 : ContinuousAt (u8h_f_ray D z) (y + (0:ℝ) • v) := by
      rw [zero_smul, add_zero]; exact u8h_f_ray_continuousAt hD hz hyz
    exact ContinuousAt.comp (f := fun t : ℝ => y + t • v) h2 h1
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hgc ε hε
  have hpt : y + (δ / 2) • v ≠ z := by
    intro h
    have : det (y - z) (y + (δ / 2) • v - z) = 0 := by rw [h, sub_self, u8h_f_det_zero_right]
    rw [add_sub_right_comm, u8h_f_det_add_right, u8h_f_det_self, u8h_f_det_smul_right] at this
    have : 0 < δ / 2 * det (y - z) v := by positivity
    linarith
  refine ⟨g (δ / 2), u8h_f_ray_mem_frontier hD hz hpt, ?_, ?_⟩
  · intro h
    have h1 : det (y - z) (g (δ / 2) - z) = 0 := by rw [h, u8h_f_det_self]
    have h2 : g (δ / 2) - z = (u8h_f_rg D z (y + (δ / 2) • v))⁻¹ • ((δ / 2) • v + (y - z)) := by
      simp only [hg, u8h_f_ray, add_sub_cancel_left]; congr 1; abel
    rw [h2, u8h_f_det_smul_right, u8h_f_det_add_right, u8h_f_det_smul_right, u8h_f_det_self, add_zero] at h1
    have hr := u8h_f_rg_pos hD hz hpt
    have : 0 < (u8h_f_rg D z (y + (δ / 2) • v))⁻¹ * (δ / 2 * det (y - z) v) := by positivity
    linarith
  · have := hδε (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rwa [hg0] at this

theorem u8h_f_isClosed_segment (a b : Plane) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem u8h_f_exists_nondeg {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ p ∈ S, p.1 ≠ p.2 ∧ y ∈ segment ℝ p.1 p.2 := by
  classical
  by_contra hcon
  have hdeg : ∀ p ∈ S, y ∈ segment ℝ p.1 p.2 → p.1 = p.2 := fun p hp hyp =>
    by_contra fun hne => hcon ⟨p, hp, hne, hyp⟩
  set U : Set Plane := ⋃ p ∈ S.filter (fun p => y ∉ segment ℝ p.1 p.2), segment ℝ p.1 p.2 with hU
  have hUc : IsClosed U := isClosed_biUnion_finset (fun p _ => u8h_f_isClosed_segment _ _)
  have hyU : y ∉ U := by
    intro h
    rw [hU, mem_iUnion₂] at h
    obtain ⟨p, hp, hyp⟩ := h
    exact (Finset.mem_filter.mp hp).2 hyp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUc.isOpen_compl y hyU
  obtain ⟨w, hw, hwy, hwd⟩ := u8h_f_not_isolated hD hz hy hε
  rw [← hS, mem_iUnion₂] at hw
  obtain ⟨p, hp, hwp⟩ := hw
  by_cases hyp : y ∈ segment ℝ p.1 p.2
  · have h12 := hdeg p hp hyp
    rw [h12, segment_same] at hyp hwp
    exact hwy (hwp.trans hyp.symm)
  · have hwU : w ∈ U := by
      rw [hU, mem_iUnion₂]
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hyp⟩, hwp⟩
    exact hball (Metric.mem_ball.mpr hwd) hwU

/-! ### coverage, a third mark, positivity from the cyclic order -/

theorem u8h_f_cover {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ a b, u8h_f_A D z S a b ∧ y ∈ segment ℝ a b := by
  obtain ⟨p, hp, hne, hyp⟩ := u8h_f_exists_nondeg hD hz hS hy
  exact u8h_f_cover_of_segment hD hz hS hp hne hyp


/-- The gauge of the square `Q_r` about the origin is `‖x‖_∞ / r`. -/
theorem u8h_rg_square {r : ℝ} (hr : 0 < r) (x : Plane) : u8h_f_rg (square r) 0 x = supNorm x / r := by
  have hD := U1_square_isDisc hr
  have h0 : (0 : Plane) ∈ interior (square r) := by
    rw [u8h_mem_interior_square_iff]; simp [supNorm, hr]
  by_cases hx : x = 0
  · subst hx; rw [u8h_f_rg_self]; simp [supNorm]
  · have hN := u3h_supNorm_pos hx
    set y : Plane := (r / supNorm x) • x with hy
    have hyfr : y ∈ frontier (square r) := by
      rw [u8h_mem_frontier_square, hy, u3h_supNorm_smul, abs_of_pos (div_pos hr hN), div_mul_cancel₀ _ hN.ne']
    have hc : supNorm x / r * (r / supNorm x) = 1 := by field_simp
    have e : x = 0 + (supNorm x / r) • (y - 0) := by
      rw [hy, sub_zero, zero_add, smul_smul, hc, one_smul]
    conv_lhs => rw [e]
    rw [u8h_f_rg_smul _ _ _ (div_pos hN hr).le, (u8h_f_rg_eq_one_iff hD h0 y).2 hyfr, mul_one]

theorem u8h_zero_mem_interior_square {r : ℝ} (hr : 0 < r) : (0 : Plane) ∈ interior (square r) := by
  rw [u8h_mem_interior_square_iff]; simp [supNorm, hr]

/-! ### U8: the source annulus `Q_L \ int T₀` -/

/-- A fixed interior point of the base triangle. -/
noncomputable def u8h_o (T₀ : Triangle) : Plane := Classical.choose (U1_triangle_interior_nonempty T₀)

theorem u8h_o_mem (T₀ : Triangle) : u8h_o T₀ ∈ interior T₀.carrier :=
  Classical.choose_spec (U1_triangle_interior_nonempty T₀)

/-- The nested-disc context of the source annulus. -/
theorem u8h_ctx {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_AnnCtx (u8h_o T₀) T₀.carrier (square L) :=
  ⟨U1_triangle_isDisc T₀, U1_square_isDisc hL, u8h_o_mem T₀, hT⟩

theorem u8h_vertex_mem_frontier (T₀ : Triangle) (i : Fin 3) : T₀.v i ∈ frontier T₀.carrier := by
  rw [U1_frontier_triangle]
  exact mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩

theorem u8h_vertex_ne_o (T₀ : Triangle) (i : Fin 3) : T₀.v i ≠ u8h_o T₀ := fun h =>
  (u8h_vertex_mem_frontier T₀ i).2 (h ▸ u8h_o_mem T₀)

/-- The outer radial projections of the vertices of `T₀`. -/
noncomputable def u8h_q (L : ℝ) (T₀ : Triangle) (i : Fin 3) : Plane :=
  u8h_f_ray (square L) (u8h_o T₀) (T₀.v i)

theorem u8h_q_mem_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    (i : Fin 3) : u8h_q L T₀ i ∈ frontier (square L) :=
  u8h_f_ray_mem_frontier (U1_square_isDisc hL) (u8h_ctx hL T₀ hT).hz' (u8h_vertex_ne_o T₀ i)

/-- The inner projection of `q i` is the vertex `v i`. -/
theorem u8h_ray_q {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) (i : Fin 3) :
    u8h_f_ray T₀.carrier (u8h_o T₀) (u8h_q L T₀ i) = T₀.v i :=
  (u8h_ctx hL T₀ hT).rayin_rayout (u8h_vertex_mem_frontier T₀ i)

open Classical in
/-- The frontier pieces of the source: the four sides and the three vertex projections as
degenerate pieces (so that they are marks). -/
noncomputable def u8h_S (L : ℝ) (T₀ : Triangle) : Finset (Plane × Plane) :=
  Finset.univ.image (fun j : Fin 4 => (u8h_corner L j, u8h_corner L (j + 1))) ∪
    Finset.univ.image (fun i : Fin 3 => (u8h_q L T₀ i, u8h_q L T₀ i))

theorem u8h_S_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (⋃ p ∈ u8h_S L T₀, segment ℝ p.1 p.2) = frontier (square L) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
      exact u8h_side_subset_frontier hL j hxp
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [segment_same] at hxp
      rw [mem_singleton_iff] at hxp
      rw [hxp]; exact u8h_q_mem_frontier hL T₀ hT i
  · intro x hx
    obtain ⟨j, hj⟩ := u8h_frontier_subset_sides hL hx
    exact mem_iUnion₂.2 ⟨(u8h_corner L j, u8h_corner L (j + 1)),
      Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)), hj⟩

/-- The outer marks and the adjacency relation of the source fan. -/
noncomputable def u8h_V (L : ℝ) (T₀ : Triangle) : Set Plane := u8h_f_marks (u8h_S L T₀)
def u8h_A (L : ℝ) (T₀ : Triangle) (a b : Plane) : Prop := u8h_f_A (square L) (u8h_o T₀) (u8h_S L T₀) a b

theorem u8h_q_mem_V (L : ℝ) (T₀ : Triangle) (i : Fin 3) : u8h_q L T₀ i ∈ u8h_V L T₀ :=
  u8h_f_marks_left (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)))

theorem u8h_V_finite (L : ℝ) (T₀ : Triangle) : (u8h_V L T₀).Finite := u8h_f_marks_finite _

theorem u8h_V_subset {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_V L T₀ ⊆ frontier (square L) := u8h_f_marks_subset_frontier (u8h_S_cover hL T₀ hT)

theorem u8h_A_adj (L : ℝ) (T₀ : Triangle) (a b : Plane) (h : u8h_A L T₀ a b) :
    u8h_f_Adj (square L) (u8h_o T₀) (u8h_V L T₀) a b := h.1

theorem u8h_A_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ y ∈ frontier (square L), ∃ a b, u8h_A L T₀ a b ∧ y ∈ segment ℝ a b := fun _ hy =>
  u8h_f_cover (U1_square_isDisc hL) (u8h_ctx hL T₀ hT).hz' (u8h_S_cover hL T₀ hT) hy

/-- The source annulus data, given straightness of the inner frontier between adjacent marks. -/
theorem u8h_srcData {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    (hstraight : ∀ a b, u8h_A L T₀ a b →
      segment ℝ (u8h_f_ray T₀.carrier (u8h_o T₀) a) (u8h_f_ray T₀.carrier (u8h_o T₀) b) ⊆ frontier T₀.carrier) :
    u8h_AnnData (u8h_o T₀) T₀.carrier (square L) (u8h_V L T₀) (u8h_A L T₀) :=
  ⟨u8h_ctx hL T₀ hT, u8h_V_finite L T₀, u8h_V_subset hL T₀ hT, u8h_A_adj L T₀, u8h_A_cover hL T₀ hT, hstraight⟩

/-! ### U8 helpers: the face-wise affine map glued from a vertex assignment -/

/-- Two affine maps of the plane agreeing on a set agree on its convex hull. -/
theorem u8h_affine_eq_on_hull {f g : Plane → Plane} (hf : AffineOn f univ) (hg : AffineOn g univ)
    {S : Set Plane} (h : ∀ v ∈ S, f v = g v) : ∀ x ∈ convexHull ℝ S, f x = g x := by
  obtain ⟨M, b, hM⟩ := hf
  obtain ⟨M', b', hM'⟩ := hg
  have hconv : Convex ℝ {x | f x = g x} := by
    intro x hx y hy s t hs ht hst
    simp only [mem_ofPred_eq] at hx hy ⊢
    rw [hM _ (mem_univ _), hM' _ (mem_univ _)] at hx hy ⊢
    rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    have ht' : t = 1 - s := by linarith
    subst ht'
    have e1 : s • M x + (1 - s) • M y + b = s • (M x + b) + (1 - s) • (M y + b) := by module
    have e2 : s • M' x + (1 - s) • M' y + b' = s • (M' x + b') + (1 - s) • (M' y + b') := by module
    rw [e1, e2, hx, hy]
  exact fun x hx => convexHull_min h hconv hx

/-- The affine map of the plane taking the vertices of `T` to their `w`-values. -/
noncomputable def u8h_aff (T : Triangle) (w : Plane → Plane) : Plane → Plane :=
  Classical.choose (U1_exists_affine_of_triangle T (w ∘ T.v))

theorem u8h_aff_affine (T : Triangle) (w : Plane → Plane) : AffineOn (u8h_aff T w) univ :=
  (Classical.choose_spec (U1_exists_affine_of_triangle T (w ∘ T.v))).1

theorem u8h_aff_vertex (T : Triangle) (w : Plane → Plane) (i : Fin 3) : u8h_aff T w (T.v i) = w (T.v i) :=
  (Classical.choose_spec (U1_exists_affine_of_triangle T (w ∘ T.v))).2 i

open Classical in
/-- The glued map: on each face of `K` the affine map of that face. -/
noncomputable def u8h_glue {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) (x : Plane) : Plane :=
  if h : ∃ T, T ∈ K.faces ∧ x ∈ T.carrier then u8h_aff (Classical.choose h) w x else 0

/-- Two face maps agree on the intersection of their faces. -/
theorem u8h_aff_eq_of_inter {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) {T T' : Triangle}
    (hT : T ∈ K.faces) (hT' : T' ∈ K.faces) {x : Plane} (hx : x ∈ T.carrier) (hx' : x ∈ T'.carrier) :
    u8h_aff T w x = u8h_aff T' w x := by
  have hmem : x ∈ convexHull ℝ (range T.v ∩ range T'.v) := by rw [← K.inter T hT T' hT']; exact ⟨hx, hx'⟩
  refine u8h_affine_eq_on_hull (u8h_aff_affine T w) (u8h_aff_affine T' w) ?_ x hmem
  rintro v ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
  rw [u8h_aff_vertex, ← hj, u8h_aff_vertex, hj]

theorem u8h_glue_eq {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) {T : Triangle}
    (hT : T ∈ K.faces) {x : Plane} (hx : x ∈ T.carrier) : u8h_glue K w x = u8h_aff T w x := by
  have h : ∃ T, T ∈ K.faces ∧ x ∈ T.carrier := ⟨T, hT, hx⟩
  rw [u8h_glue, dite_eq_left h]
  have hs := Classical.choose_spec h
  exact u8h_aff_eq_of_inter K w hs.1 hT hs.2 hx

theorem u8h_glue_vertex {X : Set Plane} (K : Triangulation X) (w : Plane → Plane) {T : Triangle}
    (hT : T ∈ K.faces) (i : Fin 3) : u8h_glue K w (T.v i) = w (T.v i) := by
  rw [u8h_glue_eq K w hT (subset_convexHull ℝ _ (mem_range_self i)), u8h_aff_vertex]

/-- The glued map is positive PL when the vertex images are positively oriented on every face. -/
theorem u8h_glue_isPositivePLOn {X : Set Plane} (K : Triangulation X) (w : Plane → Plane)
    (hpos : ∀ T ∈ K.faces, 0 < det (w (T.v 1) - w (T.v 0)) (w (T.v 2) - w (T.v 0))) :
    IsPositivePLOn (u8h_glue K w) K := by
  intro T hT
  have haff : IsPositiveAffineOn (u8h_aff T w) T := by
    refine U1_isPositiveAffineOn_of_det T (u8h_aff_affine T w) ?_
    rw [u8h_aff_vertex, u8h_aff_vertex, u8h_aff_vertex]; exact hpos T hT
  exact u3h_isPositiveAffineOn_congr (fun x hx => (u8h_glue_eq K w hT hx).symm) haff

/-- A positive affine map is injective on its face. -/
theorem u8h_injOn_of_isPositiveAffineOn {f : Plane → Plane} {T : Triangle} (h : IsPositiveAffineOn f T) :
    InjOn f T.carrier := by
  obtain ⟨M, c, hMc⟩ := id h.1
  have hdet := u3h_detM_pos T h hMc
  obtain ⟨N, hN⟩ := u3h_exists_linear_inverse M hdet.ne'
  intro x hx y hy hxy
  rw [hMc x hx, hMc y hy] at hxy
  have : M x = M y := add_right_cancel hxy
  rw [← hN x, this, hN]

/-- The image of a face under a face-wise affine map is the face of the vertex images. -/
theorem u8h_image_face {f : Plane → Plane} {T : Triangle} (h : IsPositiveAffineOn f T) :
    f '' T.carrier = convexHull ℝ (f '' range T.v) :=
  u2h_image_convexHull_of_affineOn h.1 (U1_triangle_convex T) (subset_convexHull ℝ _)

/-- **Bijection lemma**: a face-wise positive affine map carrying faces of `K` onto faces of `K'`,
surjectively on faces and injectively on vertices, is a bijection of the carriers. -/
theorem u8h_bij_of_faces {X X' : Set Plane} (K : Triangulation X) (K' : Triangulation X') {g : Plane → Plane}
    (hg : IsPositivePLOn g K)
    (himg : ∀ T ∈ K.faces, ∃ T' ∈ K'.faces, g '' T.carrier = T'.carrier)
    (hsurj : ∀ T' ∈ K'.faces, ∃ T ∈ K.faces, g '' T.carrier = T'.carrier)
    (hvinj : ∀ T ∈ K.faces, ∀ T' ∈ K.faces, ∀ i j, g (T.v i) = g (T'.v j) → T.v i = T'.v j) :
    InjOn g X ∧ g '' X = X' := by
  have hmemX : ∀ x ∈ X, ∃ T ∈ K.faces, x ∈ T.carrier := by
    intro x hx; rw [← K.cover] at hx
    obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hx
    exact ⟨T, hT, hxT⟩
  have hsubX' : ∀ T' ∈ K'.faces, T'.carrier ⊆ X' := by
    intro T' hT'
    have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT'
    rwa [K'.cover] at this
  have hsubX : ∀ T ∈ K.faces, T.carrier ⊆ X := by
    intro T hT
    have := subset_biUnion_of_mem (u := fun T : Triangle => T.carrier) hT
    rwa [K.cover] at this
  constructor
  · intro x hx y hy hxy
    obtain ⟨T, hT, hxT⟩ := hmemX x hx
    obtain ⟨T₂, hT₂, hyT⟩ := hmemX y hy
    obtain ⟨T', hT', hTT'⟩ := himg T hT
    obtain ⟨T₂', hT₂', hTT₂'⟩ := himg T₂ hT₂
    have hp : g x ∈ T'.carrier ∩ T₂'.carrier := ⟨hTT' ▸ ⟨x, hxT, rfl⟩, hTT₂' ▸ ⟨y, hyT, hxy.symm⟩⟩
    rw [K'.inter T' hT' T₂' hT₂'] at hp
    -- the vertex sets of the image faces are the images of the vertex sets
    have hr : ∀ {S S' : Triangle}, S ∈ K.faces → g '' S.carrier = S'.carrier →
        range S'.v = g '' range S.v := by
      intro S S' hS hSS'
      have e : (S.map g (hg S hS)).carrier = S'.carrier := by rw [← u3h_image_carrier S (hg S hS), hSS']
      rw [← u3h_range_eq_of_carrier_eq e]
      exact range_comp g S.v
    rw [hr hT hTT', hr hT₂ hTT₂'] at hp
    have hint : g '' range T.v ∩ g '' range T₂.v = g '' (range T.v ∩ range T₂.v) := by
      apply Subset.antisymm
      · rintro p ⟨⟨u, ⟨i, rfl⟩, rfl⟩, ⟨v, ⟨j, rfl⟩, huv⟩⟩
        have := hvinj T hT T₂ hT₂ i j huv.symm
        exact ⟨T.v i, ⟨⟨i, rfl⟩, ⟨j, this.symm⟩⟩, rfl⟩
      · exact Set.image_inter_subset g _ _
    rw [hint] at hp
    have hS : range T.v ∩ range T₂.v ⊆ T.carrier := inter_subset_left.trans (subset_convexHull ℝ _)
    rw [← u2h_image_convexHull_of_affineOn (hg T hT).1 (U1_triangle_convex T) hS,
      ← K.inter T hT T₂ hT₂] at hp
    obtain ⟨u, ⟨huT, huT₂⟩, hu⟩ := hp
    have h1 : x = u := u8h_injOn_of_isPositiveAffineOn (hg T hT) hxT huT hu.symm
    have h2 : y = u := u8h_injOn_of_isPositiveAffineOn (hg T₂ hT₂) hyT huT₂ (hxy.symm.trans hu.symm)
    rw [h1, h2]
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨T, hT, hxT⟩ := hmemX x hx
      obtain ⟨T', hT', hTT'⟩ := himg T hT
      exact hsubX' T' hT' (hTT' ▸ ⟨x, hxT, rfl⟩)
    · intro x' hx'
      rw [← K'.cover] at hx'
      obtain ⟨T', hT', hx'T⟩ := mem_iUnion₂.1 hx'
      obtain ⟨T, hT, hTT'⟩ := hsurj T' hT'
      rw [← hTT'] at hx'T
      obtain ⟨x, hxT, rfl⟩ := hx'T
      exact ⟨x, hsubX T hT hxT, rfl⟩


/-! ### U8: the target annulus `Q_2 \ int Q_1` with the reflected marks -/

/-- The target marks `ρ_{L/2}(V) = 2 ρ_L (V) ⊆ ∂Q_2`. -/
noncomputable def u8h_V' (L : ℝ) (T₀ : Triangle) : Set Plane := u8h_ρ (L / 2) '' u8h_V L T₀

/-- The target adjacency: the reflected source adjacency, with the order reversed. -/
def u8h_A' (L : ℝ) (T₀ : Triangle) (a' b' : Plane) : Prop :=
  ∃ a b, u8h_A L T₀ a b ∧ a' = u8h_ρ (L / 2) b ∧ b' = u8h_ρ (L / 2) a

theorem u8h_half_pos {L : ℝ} (hL : 0 < L) : 0 < L / 2 := by linarith

theorem u8h_ctx' : u8h_AnnCtx (0 : Plane) (square 1) (square 2) :=
  ⟨U1_square_isDisc one_pos, U1_square_isDisc two_pos, u8h_zero_mem_interior_square one_pos, fun x hx => by
    rw [u8h_mem_interior_square_iff]; have : supNorm x ≤ 1 := hx; linarith⟩

theorem u8h_supNorm_ρ' {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    supNorm (u8h_ρ (L / 2) c) = 2 := by
  rw [u8h_supNorm_ρ (u8h_half_pos hL), u8h_mem_frontier_square.1 hc]; field_simp

theorem u8h_ρ'_mem_frontier {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_ρ (L / 2) c ∈ frontier (square 2) := by
  rw [u8h_mem_frontier_square]; exact u8h_supNorm_ρ' hL hc

theorem u8h_ρ_mem_frontier_one {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_ρ L c ∈ frontier (square 1) := by
  rw [u8h_mem_frontier_square, u8h_supNorm_ρ hL, u8h_mem_frontier_square.1 hc, div_self hL.ne']

/-- The inner projection of a target mark `ρ_{L/2} c` is `ρ_L c`. -/
theorem u8h_ray_ρ' {L : ℝ} (hL : 0 < L) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_f_ray (square 1) 0 (u8h_ρ (L / 2) c) = u8h_ρ L c := by
  rw [u8h_f_ray, u8h_rg_square one_pos, u8h_supNorm_ρ' hL hc, div_one, sub_zero, zero_add]
  ext <;> simp [u8h_ρ] <;> field_simp

theorem u8h_V'_subset {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_V' L T₀ ⊆ frontier (square 2) := by
  rintro _ ⟨c, hc, rfl⟩
  exact u8h_ρ'_mem_frontier hL (u8h_V_subset hL T₀ hT hc)

/-- `det a b > 0` about the origin for adjacent source marks. -/
theorem u8h_det_origin_pos {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) : 0 < det a b := by
  have hadj := u8h_A_adj L T₀ a b h
  have hne : a ≠ b := fun e => by
    have := hadj.2.2.1; rw [e, u8h_f_det_self] at this; exact lt_irrefl _ this
  have := u8h_det_sign_const (U1_square_isDisc hL) (u8h_ctx hL T₀ hT).hz' (u8h_zero_mem_interior_square hL)
    hne hadj.2.2.2.1 hadj.2.2.1
  simpa using this

theorem u8h_A'_adj {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    (a' b' : Plane) (h : u8h_A' L T₀ a' b') : u8h_f_Adj (square 2) 0 (u8h_V' L T₀) a' b' := by
  obtain ⟨a, b, h, rfl, rfl⟩ := h
  have hadj := u8h_A_adj L T₀ a b h
  have hL2 := u8h_half_pos hL
  refine ⟨⟨b, hadj.2.1, rfl⟩, ⟨a, hadj.1, rfl⟩, ?_, ?_, ?_⟩
  · rw [sub_zero, sub_zero, u8h_det_ρ, u8h_f_det_swap' b a]
    have := u8h_det_origin_pos hL T₀ hT h
    have h2 : 0 < (L / 2) ^ 2 := by positivity
    rw [neg_div, neg_neg]; exact div_pos this h2
  · intro x hx
    rw [segment_symm, ← u8h_ρ_image_segment hL2] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact u8h_ρ'_mem_frontier hL (hadj.2.2.2.1 hy)
  · rintro _ ⟨c, hc, rfl⟩ hmem
    rw [u8h_ρ_mem_openSegment hL2, openSegment_symm] at hmem
    exact hadj.2.2.2.2 c hc hmem

theorem u8h_A'_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ y' ∈ frontier (square 2), ∃ a' b', u8h_A' L T₀ a' b' ∧ y' ∈ segment ℝ a' b' := by
  intro y' hy'
  have hL2 := u8h_half_pos hL
  set y : Plane := ((L / 2) ^ 2) • u8h_ρ (L / 2) y' with hy
  have hyy : u8h_ρ (L / 2) y = y' := by
    rw [hy, u8h_ρ_smul, u8h_ρ_ρ, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hL2.ne'), one_smul]
  have hyfr : y ∈ frontier (square L) := by
    rw [u8h_mem_frontier_square, hy, u3h_supNorm_smul, u8h_supNorm_ρ hL2, u8h_mem_frontier_square.1 hy',
      abs_of_pos (by positivity)]
    field_simp
  obtain ⟨a, b, h, hseg⟩ := u8h_A_cover hL T₀ hT y hyfr
  refine ⟨u8h_ρ (L / 2) b, u8h_ρ (L / 2) a, ⟨a, b, h, rfl, rfl⟩, ?_⟩
  rw [← hyy, segment_symm, u8h_ρ_mem_segment hL2]; exact hseg

theorem u8h_A'_straight {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ a' b', u8h_A' L T₀ a' b' →
      segment ℝ (u8h_f_ray (square 1) 0 a') (u8h_f_ray (square 1) 0 b') ⊆ frontier (square 1) := by
  rintro _ _ ⟨a, b, h, rfl, rfl⟩
  have hadj := u8h_A_adj L T₀ a b h
  have ha := u8h_V_subset hL T₀ hT hadj.1
  have hb := u8h_V_subset hL T₀ hT hadj.2.1
  rw [u8h_ray_ρ' hL hb, u8h_ray_ρ' hL ha]
  intro x hx
  rw [segment_symm, ← u8h_ρ_image_segment hL] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact u8h_ρ_mem_frontier_one hL (hadj.2.2.2.1 hy)

/-- The target annulus data. -/
theorem u8h_tgtData {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_AnnData (0 : Plane) (square 1) (square 2) (u8h_V' L T₀) (u8h_A' L T₀) :=
  ⟨u8h_ctx', (u8h_V_finite L T₀).image _, u8h_V'_subset hL T₀ hT, u8h_A'_adj hL T₀ hT, u8h_A'_cover hL T₀ hT,
    u8h_A'_straight hL T₀ hT⟩


/-! ### U8: straightness of `∂T₀` between adjacent outer marks -/

/-- Two frontier points on the same ray from an interior point coincide (anchor on the right). -/
theorem u8h_eq_of_det_zero' {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a a' : Plane} (ha : a ∈ frontier D) (ha' : a' ∈ frontier D) (h0 : det (a' - z) (a - z) = 0)
    {y : Plane} (hy : 0 < det (y - z) (a - z)) (hy' : 0 ≤ det (y - z) (a' - z)) : a' = a := by
  have hne : a' - z ≠ 0 := sub_ne_zero.2 (u8h_f_frontier_ne hD hz ha')
  obtain ⟨t, ht⟩ := u8h_f_parallel_of_det_eq_zero hne h0
  have htpos : 0 < t := by
    rw [ht, u8h_f_det_smul_right] at hy
    by_contra hneg; push Not at hneg
    nlinarith
  have h1 : u8h_f_rg D z a = t * u8h_f_rg D z a' := by
    have : a = z + t • (a' - z) := by rw [← ht]; abel
    rw [this, u8h_f_rg_smul _ _ _ htpos.le]
  rw [(u8h_f_rg_eq_one_iff hD hz a).2 ha, (u8h_f_rg_eq_one_iff hD hz a').2 ha', mul_one] at h1
  rw [← h1, one_smul] at ht
  exact (sub_left_inj.1 ht).symm

open Classical in
/-- The frontier pieces of `T₀`: its three edges and the inner projections of all outer marks. -/
noncomputable def u8h_ST (L : ℝ) (T₀ : Triangle) : Finset (Plane × Plane) :=
  Finset.univ.image (fun i : Fin 3 => (T₀.v i, T₀.v (i + 1))) ∪
    (u8h_V_finite L T₀).toFinset.image
      (fun c => (u8h_f_ray T₀.carrier (u8h_o T₀) c, u8h_f_ray T₀.carrier (u8h_o T₀) c))

theorem u8h_ST_cover {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (⋃ p ∈ u8h_ST L T₀, segment ℝ p.1 p.2) = frontier T₀.carrier := by
  have C := u8h_ctx hL T₀ hT
  apply Subset.antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      rw [U1_frontier_triangle]; exact mem_iUnion.2 ⟨i, hxp⟩
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
      rw [Set.Finite.mem_toFinset] at hc
      rw [segment_same, mem_singleton_iff] at hxp
      rw [hxp]; exact C.ray_mem_frontier (u8h_V_subset hL T₀ hT hc)
  · intro x hx
    rw [U1_frontier_triangle] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact mem_iUnion₂.2 ⟨(T₀.v i, T₀.v (i + 1)),
      Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)), hi⟩

theorem u8h_ray_mem_marksT {L : ℝ} (T₀ : Triangle) {c : Plane} (hc : c ∈ u8h_V L T₀) :
    u8h_f_ray T₀.carrier (u8h_o T₀) c ∈ u8h_f_marks (u8h_ST L T₀) :=
  u8h_f_marks_left (Finset.mem_union.2 (Or.inr (Finset.mem_image.2
    ⟨c, (Set.Finite.mem_toFinset _).2 hc, rfl⟩)))

theorem u8h_marksT_eq {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {m : Plane} (hm : m ∈ u8h_f_marks (u8h_ST L T₀)) :
    ∃ c ∈ u8h_V L T₀, m = u8h_f_ray T₀.carrier (u8h_o T₀) c := by
  simp only [u8h_f_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe] at hm
  rcases hm with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ <;> rcases Finset.mem_union.1 hp with hp | hp
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨u8h_q L T₀ i, u8h_q_mem_V L T₀ i, (u8h_ray_q hL T₀ hT i).symm⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨c, (Set.Finite.mem_toFinset _).1 hc, rfl⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨u8h_q L T₀ (i + 1), u8h_q_mem_V L T₀ (i + 1), (u8h_ray_q hL T₀ hT (i + 1)).symm⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨c, (Set.Finite.mem_toFinset _).1 hc, rfl⟩


/-- **Straightness of the inner frontier**: between the inner projections of two adjacent outer
marks, the frontier of `T₀` is a straight segment. -/
theorem u8h_src_straight {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ a b, u8h_A L T₀ a b →
      segment ℝ (u8h_f_ray T₀.carrier (u8h_o T₀) a) (u8h_f_ray T₀.carrier (u8h_o T₀) b) ⊆
        frontier T₀.carrier := by
  intro a b h
  have C := u8h_ctx hL T₀ hT
  set o := u8h_o T₀ with ho
  have hadj := u8h_A_adj L T₀ a b h
  have haV : a ∈ u8h_V L T₀ := hadj.1
  have hbV : b ∈ u8h_V L T₀ := hadj.2.1
  have hab : 0 < det (a - o) (b - o) := hadj.2.2.1
  have hseg : segment ℝ a b ⊆ frontier (square L) := hadj.2.2.2.1
  have hnomark := hadj.2.2.2.2
  have ha : a ∈ frontier (square L) := u8h_V_subset hL T₀ hT haV
  have hb : b ∈ frontier (square L) := u8h_V_subset hL T₀ hT hbV
  have hPta : u8h_f_ray T₀.carrier o a ∈ frontier T₀.carrier := C.ray_mem_frontier ha
  have hPtb : u8h_f_ray T₀.carrier o b ∈ frontier T₀.carrier := C.ray_mem_frontier hb
  have hsa := C.s_pos ha
  have hsb := C.s_pos hb
  -- the anchor `y`: the inner frontier point on the bisecting ray
  set m : Plane := a + b - o with hm
  have hm1 : det (a - o) (m - o) = det (a - o) (b - o) := by
    simp only [hm, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  have hm2 : det (m - o) (b - o) = det (a - o) (b - o) := by
    simp only [hm, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  have hmo : m ≠ o := by
    intro e; rw [e, sub_self, u8h_f_det_zero_right] at hm1; linarith
  set y := u8h_f_ray T₀.carrier o m with hy
  have hyfr : y ∈ frontier T₀.carrier := u8h_f_ray_mem_frontier C.hin C.hz hmo
  have hrm : 0 < u8h_f_rg T₀.carrier o m := u8h_f_rg_pos C.hin C.hz hmo
  have hysub : y - o = (u8h_f_rg T₀.carrier o m)⁻¹ • (m - o) := by rw [hy, u8h_f_ray, add_sub_cancel_left]
  have F2 : 0 < det (a - o) (y - o) := by
    rw [hysub, u8h_f_det_smul_right, hm1]; exact mul_pos (inv_pos.2 hrm) hab
  have F3 : 0 < det (y - o) (b - o) := by
    rw [hysub, u8h_f_det_smul_left', hm2]; exact mul_pos (inv_pos.2 hrm) hab
  -- the inner adjacent pair covering `y`
  obtain ⟨a₁, b₁, hA₁, hy₁⟩ := u8h_f_cover C.hin C.hz (u8h_ST_cover hL T₀ hT) hyfr
  have hAdj₁ := hA₁.1
  obtain ⟨a', ha'V, rfl⟩ := u8h_marksT_eq hL T₀ hT hAdj₁.1
  obtain ⟨b', hb'V, rfl⟩ := u8h_marksT_eq hL T₀ hT hAdj₁.2.1
  simp only [← ho] at hA₁ hy₁ hAdj₁
  have ha' : a' ∈ frontier (square L) := u8h_V_subset hL T₀ hT ha'V
  have hb' : b' ∈ frontier (square L) := u8h_V_subset hL T₀ hT hb'V
  have hsa' := C.s_pos ha'
  have hsb' := C.s_pos hb'
  have hseg₁ : segment ℝ (u8h_f_ray T₀.carrier o a') (u8h_f_ray T₀.carrier o b') ⊆ frontier T₀.carrier := hAdj₁.2.2.2.1
  have hdet₁ : 0 < det (u8h_f_ray T₀.carrier o a' - o) (u8h_f_ray T₀.carrier o b' - o) := hAdj₁.2.2.1
  have F4 : 0 < det (a' - o) (b' - o) := by
    rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right] at hdet₁
    exact pos_of_mul_pos_right (pos_of_mul_pos_right hdet₁ hsa'.le) hsb'.le
  obtain ⟨F5', F6'⟩ := u8h_det_of_mem_segment (z := o) hy₁ hdet₁.le
  have F5 : 0 ≤ det (a' - o) (y - o) := by
    rw [u8h_AnnCtx.ray_sub a', u8h_f_det_smul_left'] at F5'
    exact nonneg_of_mul_nonneg_right F5' hsa'
  have F6 : 0 ≤ det (y - o) (b' - o) := by
    rw [u8h_AnnCtx.ray_sub b', u8h_f_det_smul_right] at F6'
    exact nonneg_of_mul_nonneg_right F6' hsb'
  -- a mark strictly inside the sector `(a, b)` is impossible
  have hno : ∀ c ∈ u8h_V L T₀, 0 < det (a - o) (c - o) → 0 < det (c - o) (b - o) → False := by
    intro c hcV h1 h2
    have hc : c ∈ frontier (square L) := u8h_V_subset hL T₀ hT hcV
    have hcs := u8h_f_frontier_mem_segment C.hout C.hz' hab hseg hc h1.le h2.le
    rcases u8h_f_mem_segment_cases hcs with e | e | e
    · rw [e, u8h_f_det_self] at h1; exact lt_irrefl _ h1
    · rw [e, u8h_f_det_self] at h2; exact lt_irrefl _ h2
    · exact hnomark c hcV e
  -- a mark strictly inside the inner sector `(u8h_f_ray T₀.carrier o a', u8h_f_ray T₀.carrier o b')` is impossible
  have hno₁ : ∀ c ∈ u8h_V L T₀, 0 < det (a' - o) (c - o) → 0 < det (c - o) (b' - o) → False := by
    intro c hcV h1 h2
    have hc : c ∈ frontier (square L) := u8h_V_subset hL T₀ hT hcV
    have hsc := C.s_pos hc
    have h1' : 0 ≤ det (u8h_f_ray T₀.carrier o a' - o) (u8h_f_ray T₀.carrier o c - o) := by
      rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right]
      positivity
    have h2' : 0 ≤ det (u8h_f_ray T₀.carrier o c - o) (u8h_f_ray T₀.carrier o b' - o) := by
      rw [u8h_AnnCtx.ray_sub, u8h_AnnCtx.ray_sub, u8h_f_det_smul_left', u8h_f_det_smul_right]
      positivity
    have hcs := u8h_f_frontier_mem_segment C.hin C.hz hdet₁ hseg₁ (C.ray_mem_frontier hc) h1' h2'
    rcases u8h_f_mem_segment_cases hcs with e | e | e
    · have h0 : det (a' - o) (u8h_f_ray T₀.carrier o c - o) = det (a' - o) (u8h_f_ray T₀.carrier o a' - o) := by rw [e]
      rw [u8h_AnnCtx.ray_sub c, u8h_AnnCtx.ray_sub a', u8h_f_det_smul_right, u8h_f_det_smul_right,
        u8h_f_det_self, mul_zero] at h0
      have : det (a' - o) (c - o) = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd h hsc.ne'
        · exact h
      linarith
    · have h0 : det (u8h_f_ray T₀.carrier o c - o) (b' - o) = det (u8h_f_ray T₀.carrier o b' - o) (b' - o) := by rw [e]
      rw [u8h_AnnCtx.ray_sub c, u8h_AnnCtx.ray_sub b', u8h_f_det_smul_left', u8h_f_det_smul_left',
        u8h_f_det_self, mul_zero] at h0
      have : det (c - o) (b' - o) = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd h hsc.ne'
        · exact h
      linarith
    · exact hAdj₁.2.2.2.2 (u8h_f_ray T₀.carrier o c) (u8h_ray_mem_marksT T₀ hcV) e
  -- Step 1: `a'` is not strictly after `a`
  have S1 : det (a - o) (a' - o) ≤ 0 := by
    by_contra hpos; push Not at hpos
    apply hno a' ha'V hpos
    rw [u8h_cramer_det F2.ne' (a' - o) (b - o)]
    have h1 : 0 ≤ det (a' - o) (y - o) / det (a - o) (y - o) * det (a - o) (b - o) := by positivity
    have h2 : 0 < det (a - o) (a' - o) / det (a - o) (y - o) * det (y - o) (b - o) := by positivity
    linarith
  -- Step 2: `b'` is not strictly before `b`
  have S2 : det (b' - o) (b - o) ≤ 0 := by
    by_contra hpos; push Not at hpos
    apply hno b' hb'V _ hpos
    have e := u8h_cramer_det F3.ne' (b' - o) (a - o)
    have t1 : det (b' - o) (b - o) / det (y - o) (b - o) * det (y - o) (a - o) < 0 := by
      have hq : 0 < det (b' - o) (b - o) / det (y - o) (b - o) := div_pos hpos F3
      have : det (y - o) (a - o) < 0 := by rw [u8h_f_det_swap']; linarith
      exact mul_neg_of_pos_of_neg hq this
    have t2 : det (y - o) (b' - o) / det (y - o) (b - o) * det (b - o) (a - o) ≤ 0 := by
      have hq : 0 ≤ det (y - o) (b' - o) / det (y - o) (b - o) := div_nonneg F6 F3.le
      have : det (b - o) (a - o) ≤ 0 := by rw [u8h_f_det_swap']; linarith
      exact mul_nonpos_of_nonneg_of_nonpos hq this
    have : det (b' - o) (a - o) < 0 := by rw [e]; linarith
    rw [u8h_f_det_swap'] at this; linarith
  -- Step 3: `a' = a`
  have hay : 0 < det (a' - o) (y - o) := by
    rcases eq_or_lt_of_le F5 with h0 | h0
    · exfalso
      have hne : a' - o ≠ 0 := sub_ne_zero.2 (C.ne_of_frontier ha')
      obtain ⟨t, ht⟩ := u8h_f_parallel_of_det_eq_zero hne h0.symm
      have hF2 := F2
      rw [ht, u8h_f_det_smul_right] at hF2
      have hF6 := F6
      rw [ht, u8h_f_det_smul_left'] at hF6
      have ht0 : 0 ≤ t := by
        by_contra hneg; push Not at hneg
        nlinarith [F4]
      nlinarith [S1]
    · exact h0
  have S3 : det (a' - o) (a - o) = 0 := by
    by_contra hne0
    have hpos : 0 < det (a' - o) (a - o) := by
      rcases lt_or_gt_of_ne hne0 with h | h
      · exfalso; rw [u8h_f_det_swap'] at h; linarith
      · exact h
    apply hno₁ a haV hpos
    rw [u8h_cramer_det hay.ne' (a - o) (b' - o)]
    have h1 : 0 < det (a - o) (y - o) / det (a' - o) (y - o) * det (a' - o) (b' - o) := by positivity
    have h2 : 0 ≤ det (a' - o) (a - o) / det (a' - o) (y - o) * det (y - o) (b' - o) := by positivity
    linarith
  have hEa : a' = a := u8h_eq_of_det_zero C.hout C.hz' ha ha' S3 F2 F5
  subst hEa
  -- Step 4: `b' = b`
  have S4 : det (b - o) (b' - o) = 0 := by
    by_contra hne0
    have hpos : 0 < det (b - o) (b' - o) := by
      rcases lt_or_gt_of_ne hne0 with h | h
      · exfalso; rw [u8h_f_det_swap'] at h; linarith
      · exact h
    exact hno₁ b hbV hab hpos
  have hEb : b' = b := by
    apply u8h_eq_of_det_zero' C.hout C.hz' hb hb' _ F3 F6
    rw [u8h_f_det_swap']; linarith
  subst hEb
  exact hseg₁

/-! ### U8: the annulus map `g_A : Q_L \ int T₀ → Q_2 \ int Q_1` -/

theorem u8h_ρ_half (L : ℝ) (x : Plane) : u8h_ρ (L / 2) x = (2 : ℝ) • u8h_ρ L x := by
  ext <;> simp [u8h_ρ] <;> ring

/-- The source annulus data. -/
theorem u8h_D {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_AnnData (u8h_o T₀) T₀.carrier (square L) (u8h_V L T₀) (u8h_A L T₀) :=
  u8h_srcData hL T₀ hT (u8h_src_straight hL T₀ hT)

/-- The source annulus triangulation. -/
noncomputable def u8h_K {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Triangulation (square L \ interior T₀.carrier) :=
  Classical.choose (u8h_D hL T₀ hT).triangulation

theorem u8h_K_faces {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (u8h_K hL T₀ hT).faces = u8h_annFaces (u8h_o T₀) T₀.carrier (u8h_A L T₀) :=
  Classical.choose_spec (u8h_D hL T₀ hT).triangulation

/-- The target annulus triangulation. -/
noncomputable def u8h_K' {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Triangulation (square 2 \ interior (square 1)) :=
  Classical.choose (u8h_tgtData hL T₀ hT).triangulation

theorem u8h_K'_faces {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    (u8h_K' hL T₀ hT).faces = u8h_annFaces 0 (square 1) (u8h_A' L T₀) :=
  Classical.choose_spec (u8h_tgtData hL T₀ hT).triangulation

open Classical in
/-- The vertex assignment: outer marks go to `ρ_L (∂Q_L) = ∂Q_1`, inner points to `ρ_{L/2}` of their
outer projections (on `∂Q_2`). -/
noncomputable def u8h_w (L : ℝ) (T₀ : Triangle) (x : Plane) : Plane :=
  if x ∈ frontier (square L) then u8h_ρ L x else u8h_ρ (L / 2) (u8h_f_ray (square L) (u8h_o T₀) x)

theorem u8h_w_mark {L : ℝ} (T₀ : Triangle) {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_w L T₀ c = u8h_ρ L c := by
  rw [u8h_w, ite_eq_left hc]

theorem u8h_ray_notMem_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {c : Plane} (hc : c ∈ frontier (square L)) :
    u8h_f_ray T₀.carrier (u8h_o T₀) c ∉ frontier (square L) := by
  intro h
  have C := u8h_ctx hL T₀ hT
  have h1 : u8h_f_ray T₀.carrier (u8h_o T₀) c ∈ interior (square L) :=
    hT (C.hin.2.1.isClosed.frontier_subset (C.ray_mem_frontier hc))
  exact h.2 h1

theorem u8h_w_ray {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) {c : Plane}
    (hc : c ∈ frontier (square L)) :
    u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) c) = u8h_ρ (L / 2) c := by
  rw [u8h_w, ite_eq_right (u8h_ray_notMem_frontier hL T₀ hT hc), (u8h_ctx hL T₀ hT).rayout_ray hc]

/-- The annulus map. -/
noncomputable def u8h_g {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Plane → Plane :=
  u8h_glue (u8h_K hL T₀ hT) (u8h_w L T₀)

theorem u8h_face_v {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) :
    ∃ a b, u8h_A L T₀ a b ∧
      (T.v = ![u8h_f_ray T₀.carrier (u8h_o T₀) a, a, b] ∨
        T.v = ![u8h_f_ray T₀.carrier (u8h_o T₀) a, b, u8h_f_ray T₀.carrier (u8h_o T₀) b]) := by
  rw [u8h_K_faces] at hTK; exact hTK

theorem u8h_A_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) : a ∈ frontier (square L) ∧ b ∈ frontier (square L) :=
  ⟨u8h_V_subset hL T₀ hT (u8h_A_adj L T₀ a b h).1, u8h_V_subset hL T₀ hT (u8h_A_adj L T₀ a b h).2.1⟩

/-- The vertex images of the two faces of a pair. -/
theorem u8h_w_tri2 {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) a) = (2 : ℝ) • u8h_ρ L a ∧
      u8h_w L T₀ a = u8h_ρ L a ∧ u8h_w L T₀ b = u8h_ρ L b := by
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  exact ⟨by rw [u8h_w_ray hL T₀ hT ha, u8h_ρ_half], u8h_w_mark T₀ ha, u8h_w_mark T₀ hb⟩

theorem u8h_w_tri1 {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) a) = (2 : ℝ) • u8h_ρ L a ∧
      u8h_w L T₀ b = u8h_ρ L b ∧ u8h_w L T₀ (u8h_f_ray T₀.carrier (u8h_o T₀) b) = (2 : ℝ) • u8h_ρ L b := by
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  exact ⟨by rw [u8h_w_ray hL T₀ hT ha, u8h_ρ_half], u8h_w_mark T₀ hb, by rw [u8h_w_ray hL T₀ hT hb, u8h_ρ_half]⟩

/-- Positivity of the vertex images on every source face. -/
theorem u8h_w_pos {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T ∈ (u8h_K hL T₀ hT).faces,
      0 < det (u8h_w L T₀ (T.v 1) - u8h_w L T₀ (T.v 0)) (u8h_w L T₀ (T.v 2) - u8h_w L T₀ (T.v 0)) := by
  intro T hTK
  obtain ⟨a, b, h, hv | hv⟩ := u8h_face_v hL T₀ hT hTK
  · have hab := u8h_det_origin_pos hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri2 hL T₀ hT h
    rw [hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2]
    have : det (u8h_ρ L a - (2 : ℝ) • u8h_ρ L a) (u8h_ρ L b - (2 : ℝ) • u8h_ρ L a) =
        det ((-1 : ℝ) • u8h_ρ L a + (0 : ℝ) • u8h_ρ L b) ((-2 : ℝ) • u8h_ρ L a + (1 : ℝ) • u8h_ρ L b) := by
      congr 1 <;> module
    rw [this, u8h_det_combo, u8h_det_ρ]
    have h2 : 0 < L ^ 2 := by positivity
    have : 0 < det a b / L ^ 2 := div_pos hab h2
    nlinarith
  · have hab := u8h_det_origin_pos hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri1 hL T₀ hT h
    rw [hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2]
    have : det (u8h_ρ L b - (2 : ℝ) • u8h_ρ L a) ((2 : ℝ) • u8h_ρ L b - (2 : ℝ) • u8h_ρ L a) =
        det ((-2 : ℝ) • u8h_ρ L a + (1 : ℝ) • u8h_ρ L b) ((-2 : ℝ) • u8h_ρ L a + (2 : ℝ) • u8h_ρ L b) := by
      congr 1 <;> module
    rw [this, u8h_det_combo, u8h_det_ρ]
    have h2 : 0 < L ^ 2 := by positivity
    have : 0 < det a b / L ^ 2 := div_pos hab h2
    nlinarith

/-- The annulus map is positive PL on the source triangulation. -/
theorem u8h_g_isPositivePLOn {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    IsPositivePLOn (u8h_g hL T₀ hT) (u8h_K hL T₀ hT) :=
  u8h_glue_isPositivePLOn _ _ (u8h_w_pos hL T₀ hT)


/-- `g` at the vertices of a source face. -/
theorem u8h_g_vertex {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) (i : Fin 3) :
    u8h_g hL T₀ hT (T.v i) = u8h_w L T₀ (T.v i) :=
  u8h_glue_vertex _ _ hTK i

theorem u8h_image_three {f : Plane → Plane} (p q r : Plane) : f '' {p, q, r} = {f p, f q, f r} := by
  rw [image_insert_eq, image_insert_eq, image_singleton]

/-- The image of a source face is the face of its vertex images. -/
theorem u8h_g_image_face {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) :
    u8h_g hL T₀ hT '' T.carrier =
      convexHull ℝ {u8h_w L T₀ (T.v 0), u8h_w L T₀ (T.v 1), u8h_w L T₀ (T.v 2)} := by
  rw [u8h_image_face (u8h_g_isPositivePLOn hL T₀ hT T hTK)]
  congr 1
  have hr : range T.v = {T.v 0, T.v 1, T.v 2} := by
    ext w; simp only [mem_range, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  rw [hr, u8h_image_three, u8h_g_vertex hL T₀ hT hTK, u8h_g_vertex hL T₀ hT hTK, u8h_g_vertex hL T₀ hT hTK]

/-- The target adjacency of the reflected pair. -/
theorem u8h_A'_of {L : ℝ} (T₀ : Triangle) {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_A' L T₀ (u8h_ρ (L / 2) b) (u8h_ρ (L / 2) a) := ⟨a, b, h, rfl, rfl⟩

/-- Every source face maps onto a target face. -/
theorem u8h_g_himg {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T ∈ (u8h_K hL T₀ hT).faces, ∃ T' ∈ (u8h_K' hL T₀ hT).faces, u8h_g hL T₀ hT '' T.carrier = T'.carrier := by
  intro T hTK
  have D' := u8h_tgtData hL T₀ hT
  obtain ⟨a, b, h, hv | hv⟩ := u8h_face_v hL T₀ hT hTK
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri2 hL T₀ hT h
    refine ⟨D'.tri1 (u8h_A'_of T₀ h), by rw [u8h_K'_faces]; exact D'.tri1_mem _, ?_⟩
    rw [u8h_g_image_face hL T₀ hT hTK, D'.tri1_carrier, hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, u8h_ray_ρ' hL ha, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri1 hL T₀ hT h
    refine ⟨D'.tri2 (u8h_A'_of T₀ h), by rw [u8h_K'_faces]; exact D'.tri2_mem _, ?_⟩
    rw [u8h_g_image_face hL T₀ hT hTK, D'.tri2_carrier, hv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, ← u8h_ρ_half, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto

/-- Every target face is the image of a source face. -/
theorem u8h_g_hsurj {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T' ∈ (u8h_K' hL T₀ hT).faces, ∃ T ∈ (u8h_K hL T₀ hT).faces, u8h_g hL T₀ hT '' T.carrier = T'.carrier := by
  intro T' hT'
  have D := u8h_D hL T₀ hT
  rw [u8h_K'_faces] at hT'
  obtain ⟨a', b', ⟨a, b, h, rfl, rfl⟩, hv' | hv'⟩ := hT'
  · -- `T' = (Pt' (ρ' b), ρ' b, ρ' a)` is the image of the inner source face
    obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri1 hL T₀ hT h
    refine ⟨D.tri1 h, by rw [u8h_K_faces]; exact D.tri1_mem h, ?_⟩
    have hTK : D.tri1 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri1_mem h
    rw [u8h_g_image_face hL T₀ hT hTK, u8h_f_carrier_of_v hv', D.tri1_v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, ← u8h_ρ_half, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    obtain ⟨e0, e1, e2⟩ := u8h_w_tri2 hL T₀ hT h
    refine ⟨D.tri2 h, by rw [u8h_K_faces]; exact D.tri2_mem h, ?_⟩
    have hTK : D.tri2 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri2_mem h
    rw [u8h_g_image_face hL T₀ hT hTK, u8h_f_carrier_of_v hv', D.tri2_v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [e0, e1, e2, u8h_ray_ρ' hL hb, u8h_ray_ρ' hL ha, ← u8h_ρ_half]
    congr 1
    ext w; simp only [mem_insert_iff, mem_singleton_iff]; tauto

/-- Every vertex of a source face is an outer mark or the inner point of an outer mark. -/
theorem u8h_vertex_cases {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {T : Triangle} (hTK : T ∈ (u8h_K hL T₀ hT).faces) (i : Fin 3) :
    (T.v i ∈ frontier (square L)) ∨
      (∃ c ∈ frontier (square L), T.v i = u8h_f_ray T₀.carrier (u8h_o T₀) c) := by
  obtain ⟨a, b, h, hv | hv⟩ := u8h_face_v hL T₀ hT hTK
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    rw [hv]; fin_cases i
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl ha
    · exact Or.inl hb
  · obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
    rw [hv]; fin_cases i
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inl hb
    · exact Or.inr ⟨b, hb, rfl⟩

/-- `w` is injective on the vertices. -/
theorem u8h_g_hvinj {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ∀ T ∈ (u8h_K hL T₀ hT).faces, ∀ T' ∈ (u8h_K hL T₀ hT).faces, ∀ i j,
      u8h_g hL T₀ hT (T.v i) = u8h_g hL T₀ hT (T'.v j) → T.v i = T'.v j := by
  intro T hTK T' hT'K i j hij
  rw [u8h_g_vertex hL T₀ hT hTK, u8h_g_vertex hL T₀ hT hT'K] at hij
  have hL2 := u8h_half_pos hL
  rcases u8h_vertex_cases hL T₀ hT hTK i with hc | ⟨c, hc, hci⟩ <;>
    rcases u8h_vertex_cases hL T₀ hT hT'K j with hc' | ⟨c', hc', hcj⟩
  · rw [u8h_w_mark T₀ hc, u8h_w_mark T₀ hc'] at hij
    exact u8h_ρ_injective hL hij
  · exfalso
    rw [hcj, u8h_w_mark T₀ hc, u8h_w_ray hL T₀ hT hc'] at hij
    have := congrArg supNorm hij
    rw [u8h_supNorm_ρ hL, u8h_supNorm_ρ' hL hc', u8h_mem_frontier_square.1 hc, div_self hL.ne'] at this
    norm_num at this
  · exfalso
    rw [hci, u8h_w_mark T₀ hc', u8h_w_ray hL T₀ hT hc] at hij
    have := congrArg supNorm hij
    rw [u8h_supNorm_ρ hL, u8h_supNorm_ρ' hL hc, u8h_mem_frontier_square.1 hc', div_self hL.ne'] at this
    norm_num at this
  · rw [hci, hcj, u8h_w_ray hL T₀ hT hc, u8h_w_ray hL T₀ hT hc'] at hij
    rw [hci, hcj, u8h_ρ_injective hL2 hij]

/-- **The annulus map is a bijection** `Q_L \ int T₀ → Q_2 \ int Q_1`. -/
theorem u8h_g_bij {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    InjOn (u8h_g hL T₀ hT) (square L \ interior T₀.carrier) ∧
      u8h_g hL T₀ hT '' (square L \ interior T₀.carrier) = square 2 \ interior (square 1) :=
  u8h_bij_of_faces (u8h_K hL T₀ hT) (u8h_K' hL T₀ hT) (u8h_g_isPositivePLOn hL T₀ hT)
    (u8h_g_himg hL T₀ hT) (u8h_g_hsurj hL T₀ hT) (u8h_g_hvinj hL T₀ hT)


/-- `ρ_L` as a linear map. -/
noncomputable def u8h_ρ_linear (L : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun := u8h_ρ L
  map_add' := u8h_ρ_add L
  map_smul' := fun c x => by simpa using u8h_ρ_smul L c x

theorem u8h_ρ_affineOn (L : ℝ) : AffineOn (u8h_ρ L) univ :=
  ⟨u8h_ρ_linear L, 0, fun x _ => by rw [add_zero]; rfl⟩

/-- `g` agrees with `ρ_L` on the seam `∂Q_L`. -/
theorem u8h_g_seam {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) {x : Plane}
    (hx : x ∈ frontier (square L)) : u8h_g hL T₀ hT x = u8h_ρ L x := by
  have D := u8h_D hL T₀ hT
  obtain ⟨a, b, h, hxs⟩ := u8h_A_cover hL T₀ hT x hx
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  have hTK : D.tri2 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri2_mem h
  have hsub : segment ℝ a b ⊆ (D.tri2 h).carrier := by
    rw [D.tri2_carrier]; exact segment_subset_convexHull (by simp) (by simp)
  rw [u8h_g, u8h_glue_eq _ _ hTK (hsub hxs)]
  have hagree : ∀ v ∈ ({a, b} : Set Plane), u8h_aff (D.tri2 h) (u8h_w L T₀) v = u8h_ρ L v := by
    intro v hv
    simp only [mem_insert_iff, mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · have e := u8h_aff_vertex (D.tri2 h) (u8h_w L T₀) 1
      have e1 : (D.tri2 h).v 1 = v := rfl
      rw [e1] at e
      rw [e, u8h_w_mark T₀ ha]
    · have e := u8h_aff_vertex (D.tri2 h) (u8h_w L T₀) 2
      have e2 : (D.tri2 h).v 2 = v := rfl
      rw [e2] at e
      rw [e, u8h_w_mark T₀ hb]
  exact u8h_affine_eq_on_hull (u8h_aff_affine _ _) (u8h_ρ_affineOn L) hagree x
    (by rw [convexHull_pair]; exact hxs)

/-- The image of an inner edge `[Pt a, Pt b]` under `g` is `[ρ_{L/2} a, ρ_{L/2} b] ⊆ ∂Q_2`. -/
theorem u8h_g_image_inner_edge {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {a b : Plane} (h : u8h_A L T₀ a b) :
    u8h_g hL T₀ hT '' segment ℝ (u8h_f_ray T₀.carrier (u8h_o T₀) a) (u8h_f_ray T₀.carrier (u8h_o T₀) b) =
      segment ℝ (u8h_ρ (L / 2) a) (u8h_ρ (L / 2) b) := by
  have D := u8h_D hL T₀ hT
  obtain ⟨ha, hb⟩ := u8h_A_frontier hL T₀ hT h
  have hTK : D.tri1 h ∈ (u8h_K hL T₀ hT).faces := by rw [u8h_K_faces]; exact D.tri1_mem h
  have haff : IsPositiveAffineOn (u8h_g hL T₀ hT) (D.tri1 h) := u8h_g_isPositivePLOn hL T₀ hT _ hTK
  have hsub : ({u8h_f_ray T₀.carrier (u8h_o T₀) a, u8h_f_ray T₀.carrier (u8h_o T₀) b} : Set Plane) ⊆
      (D.tri1 h).carrier := by
    rw [D.tri1_carrier]
    intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact subset_convexHull ℝ _ (by simp)
    · exact subset_convexHull ℝ _ (by simp)
  rw [← convexHull_pair, u2h_image_convexHull_of_affineOn haff.1 (U1_triangle_convex _) hsub, image_pair,
    convexHull_pair]
  have e0 := u8h_g_vertex hL T₀ hT hTK 0
  have e2 := u8h_g_vertex hL T₀ hT hTK 2
  have v0 : (D.tri1 h).v 0 = u8h_f_ray T₀.carrier (u8h_o T₀) a := rfl
  have v2 : (D.tri1 h).v 2 = u8h_f_ray T₀.carrier (u8h_o T₀) b := rfl
  rw [v0] at e0; rw [v2] at e2
  rw [e0, e2, u8h_w_ray hL T₀ hT ha, u8h_w_ray hL T₀ hT hb]

/-- **The image of `∂T₀` is `∂Q_2`.** -/
theorem u8h_g_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_g hL T₀ hT '' frontier T₀.carrier = frontier (square 2) := by
  have D := u8h_D hL T₀ hT
  have hL2 := u8h_half_pos hL
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, b, h, hys⟩ := D.frontier_in_cover hy
    have hmem : u8h_g hL T₀ hT y ∈ segment ℝ (u8h_ρ (L / 2) a) (u8h_ρ (L / 2) b) := by
      rw [← u8h_g_image_inner_edge hL T₀ hT h]; exact ⟨y, hys, rfl⟩
    rw [← u8h_ρ_image_segment hL2] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    rw [← hw']
    exact u8h_ρ'_mem_frontier hL ((u8h_A_adj L T₀ a b h).2.2.2.1 hw)
  · intro y' hy'
    obtain ⟨a', b', hA', hseg⟩ := u8h_A'_cover hL T₀ hT y' hy'
    obtain ⟨a, b, h, ha', hb'⟩ := hA'
    rw [ha', hb', segment_symm, ← u8h_g_image_inner_edge hL T₀ hT h] at hseg
    obtain ⟨y, hy, rfl⟩ := hseg
    exact ⟨y, u8h_src_straight hL T₀ hT a b h hy, rfl⟩

/-! ### U8: the exterior fan map on the sphere -/

/-- Transport of a triangulation along a set equality. -/
def u8h_triangulation_congr {X Y : Set Plane} (h : X = Y) (K : Triangulation X) : Triangulation Y :=
  ⟨K.faces, K.finite, h ▸ K.cover, K.inter⟩

theorem u8h_isPositiveAffineOn_id (T : Triangle) : IsPositiveAffineOn id T :=
  ⟨⟨LinearMap.id, 0, fun x _ => by simp⟩, T.pos⟩

/-- U8 helper: the plane chart part of the model exterior of `T₀` is `Q_L \ int T₀`. -/
theorem u8h_chartPart_false_exterior {L : ℝ} (T₀ : Triangle) :
    chartPart L false (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ = square L \ interior T₀.carrier := by
  ext x
  simp only [chartPart, modelDomain, modelChart, mem_inter_iff, mem_preimage, mem_compl_iff, mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨x, h, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨y, hy, hyx⟩ => h2 (by rw [OnePoint.coe_eq_coe] at hyx; rw [← hyx]; exact hy)⟩

/-- U8 helper: the cap chart part of a set containing the closed exterior of `Q_L` and `∞` is `Q_1`. -/
theorem u8h_chartPart_true_eq {L : ℝ} (hL : 0 < L) {S : Set Sphere} (hinf : ∞ ∈ S)
    (hS : ∀ x : Plane, L ≤ supNorm x → (x : Sphere) ∈ S) : chartPart L true S = square 1 := by
  ext y
  simp only [chartPart, modelDomain, modelChart, mem_inter_iff, mem_preimage]
  refine ⟨fun h => h.1, fun hy => ⟨hy, ?_⟩⟩
  by_cases h0 : y = 0
  · subst h0; simpa [capChart] using hinf
  · simp only [capChart, h0, ↓reduceIte]
    apply hS
    rw [u3h_supNorm_capInvFun hL h0, le_div_iff₀ (u3h_supNorm_pos h0)]
    have : supNorm y ≤ 1 := hy
    nlinarith

/-- The exterior fan map: the annulus map on `Q_L`, the cap inverse (`capInvFun`) outside, `0` at `∞`. -/
noncomputable def u8h_gS {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    Sphere → Plane
  | ∞ => 0
  | (x : Plane) => if supNorm x ≤ L then u8h_g hL T₀ hT x else capInvFun L x

theorem u8h_gS_infty {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT ∞ = 0 := rfl

theorem u8h_gS_coe {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) (x : Plane) :
    u8h_gS hL T₀ hT x = if supNorm x ≤ L then u8h_g hL T₀ hT x else capInvFun L x := rfl

theorem u8h_gS_coe_of_le {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {x : Plane} (hx : supNorm x ≤ L) : u8h_gS hL T₀ hT x = u8h_g hL T₀ hT x := by
  rw [u8h_gS_coe, ite_eq_left hx]

/-- Outside `int Q_L` the fan map is the cap inverse. -/
theorem u8h_gS_coe_of_ge {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {x : Plane} (hx : L ≤ supNorm x) : u8h_gS hL T₀ hT x = capInvFun L x := by
  rw [u8h_gS_coe]
  split_ifs with h
  · have hxL : supNorm x = L := le_antisymm h hx
    rw [u8h_g_seam hL T₀ hT (u8h_mem_frontier_square.2 hxL), u8h_capInvFun_eq_ρ hL hxL]
  · rfl

theorem u8h_ρ_seam_inv {L : ℝ} (hL : 0 < L) (y : Plane) : u8h_ρ L (L • (y.1, -y.2)) = y := by
  ext <;> simp [u8h_ρ] <;> field_simp

/-- The fan map read in the cap chart is the identity. -/
theorem u8h_gS_capChart {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {y : Plane} (hy : y ∈ square 1) : u8h_gS hL T₀ hT (capChart L y) = y := by
  by_cases h0 : y = 0
  · subst h0; simp [capChart, u8h_gS_infty]
  · have hy1 : supNorm y ≤ 1 := hy
    have hN := u3h_supNorm_pos h0
    have hge : L ≤ supNorm (capInvFun L y) := by
      rw [u3h_supNorm_capInvFun hL h0, le_div_iff₀ hN]; nlinarith
    simp only [capChart, h0, ↓reduceIte]
    rw [u8h_gS_coe_of_ge hL T₀ hT hge, u3h_capInvFun_capInvFun hL.ne' h0]

/-- The model exterior of `T₀`. -/
def u8h_E (T₀ : Triangle) : Set Sphere := (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ

theorem u8h_infty_mem_E (T₀ : Triangle) : ∞ ∈ u8h_E T₀ := OnePoint.infty_notMem_image_coe

theorem u8h_coe_mem_E {T₀ : Triangle} {x : Plane} : (x : Sphere) ∈ u8h_E T₀ ↔ x ∉ interior T₀.carrier := by
  simp only [u8h_E, mem_compl_iff, mem_image, OnePoint.coe_eq_coe, exists_eq_right]

theorem u8h_coe_mem_E_of_ge {L : ℝ} (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) {x : Plane}
    (hx : L ≤ supNorm x) : (x : Sphere) ∈ u8h_E T₀ := by
  rw [u8h_coe_mem_E]
  intro h
  have := (u8h_mem_interior_square_iff x).1 (hT (interior_subset h))
  linarith

/-- **The fan map is positive PL in the two model charts.** -/
theorem u8h_gS_isPositivePLToPlane {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    IsPositivePLToPlane L (u8h_E T₀) (u8h_gS hL T₀ hT) := by
  intro b
  cases b
  · -- plane chart: the annulus triangulation
    refine ⟨u8h_triangulation_congr (u8h_chartPart_false_exterior T₀).symm (u8h_K hL T₀ hT), fun T hT' => ?_⟩
    have hT'' : T ∈ (u8h_K hL T₀ hT).faces := hT'
    refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (u8h_g_isPositivePLOn hL T₀ hT T hT'')
    have hxs : x ∈ square L := (u3h_face_subset_chartPart (K := u8h_triangulation_congr
      (u8h_chartPart_false_exterior T₀).symm (u8h_K hL T₀ hT)) hT' hx).1
    show u8h_g hL T₀ hT x = u8h_gS hL T₀ hT x
    rw [u8h_gS_coe_of_le hL T₀ hT hxs]
  · -- cap chart: the identity
    have hset : square 1 = chartPart L true (u8h_E T₀) := by
      rw [u8h_chartPart_true_eq hL (u8h_infty_mem_E T₀) (fun x hx => u8h_coe_mem_E_of_ge T₀ hT hx)]
    obtain ⟨K⟩ := U2_triangulation_square (one_pos : (0 : ℝ) < 1)
    refine ⟨u8h_triangulation_congr hset K, fun T hT' => ?_⟩
    refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (u8h_isPositiveAffineOn_id T)
    have hxs : x ∈ square 1 := (u3h_face_subset_chartPart (K := u8h_triangulation_congr hset K) hT' hx).1
    show x = u8h_gS hL T₀ hT (capChart L x)
    rw [u8h_gS_capChart hL T₀ hT hxs]

/-- **The boundary clause**: `∂T₀ ↦ ∂Q_2`. -/
theorem u8h_gS_frontier {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' (((↑) : Plane → Sphere) '' frontier T₀.carrier) = frontier (square 2) := by
  rw [← u8h_g_frontier hL T₀ hT, ← image_comp]
  apply image_congr
  intro x hx
  have hxs : x ∈ square L := interior_subset (hT (T₀.carrier |> fun _ =>
    (U1_triangle_isCompact T₀).isClosed.frontier_subset hx))
  exact u8h_gS_coe_of_le hL T₀ hT hxs


/-! ### U8 helpers: compactness builder for `IsHomeoOnto`, continuity of the cap inverse -/

theorem u8h_continuousOn_of_isHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : ContinuousOn f S := by
  obtain ⟨e, he⟩ := h
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_subtype_val.comp e.continuous).congr fun x => he x

/-- A continuous injection of a compact set onto a set of a T₂ space is `IsHomeoOnto`. -/
theorem u8h_isHomeoOnto_of_compact {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    {S : Set α} {S' : Set β} {f : α → β} (hS : IsCompact S) (hf : ContinuousOn f S) (hinj : InjOn f S)
    (himg : f '' S = S') : IsHomeoOnto S S' f := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (Equiv.Set.imageOfInjOn f S hinj) := by
    apply Continuous.subtype_mk
    exact hf.domRestrict
  refine ⟨(hc.homeoOfEquivCompactToT2).trans (Homeomorph.setCongr himg), fun z => rfl⟩

/-- The closed cap `coe '' {L ≤ ‖x‖_∞} ∪ {∞}` is closed. -/
theorem u8h_isClosed_cap {L : ℝ} :
    IsClosed (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) := by
  have : ((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞} = (((↑) : Plane → Sphere) '' {x | supNorm x < L})ᶜ := by
    ext z
    induction z using OnePoint.rec with
    | infty => simp
    | coe x =>
      simp only [mem_union, mem_image, OnePoint.coe_eq_coe, exists_eq_right, mem_ofPred_eq,
        mem_singleton_iff, mem_compl_iff, not_lt]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (OnePoint.coe_ne_infty x)
      · exact Or.inl
  rw [this]
  exact (OnePoint.isOpen_image_coe.2 (isOpen_lt u8h_continuous_supNorm continuous_const)).isClosed_compl

/-- The closed annulus `Q_L \ int T₀` is compact. -/
theorem u8h_isCompact_annulus {L : ℝ} (hL : 0 < L) (T₀ : Triangle) :
    IsCompact (square L \ interior T₀.carrier) :=
  (U1_square_isDisc hL).2.1.of_isClosed_subset
    ((isClosed_le u8h_continuous_supNorm continuous_const).inter isOpen_interior.isClosed_compl)
    sdiff_subset

/-- U8 (chart algebra, PLAN_FINAL §4): the sup-norm inversion is an involution off `0`. -/
theorem U8_capInvFun_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    capInvFun L (capInvFun L y) = y := by
  exact u3h_capInvFun_capInvFun hL.ne' hy

/-- U8: `‖capInvFun L y‖_∞ = L / ‖y‖_∞`. -/
theorem U8_supNorm_capInvFun {L : ℝ} (hL : 0 < L) {y : Plane} (hy : y ≠ 0) :
    supNorm (capInvFun L y) = L / supNorm y := by
  exact u3h_supNorm_capInvFun hL hy

/-- U8 (sm-3:448-456 "the actual one-point-compactified exterior"): the cap chart is a homeomorphism
of `Q_1` onto the closed exterior of `Q_L` together with `∞`. -/
theorem U8_capChart_isHomeoOnto {L : ℝ} (hL : 0 < L) :
    IsHomeoOnto (square 1) (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) (capChart L) := by
  refine u1h_isHomeoOnto_of_inv (g := modelChartInv L true) (u8h_continuousOn_capChart hL) ?_ ?_ ?_
    (fun y _ => u3h_chartInv_chart hL.ne' true y) ?_
  · intro z hz
    apply ContinuousAt.continuousWithinAt
    apply u8h_continuous_capInv hL
    rcases hz with ⟨x, hx, rfl⟩ | hz
    · intro h
      rw [OnePoint.coe_eq_coe] at h
      subst h
      simp only [mem_ofPred_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
      linarith
    · rw [mem_singleton_iff] at hz; subst hz; exact OnePoint.infty_ne_coe _
  · intro y hy
    by_cases h0 : y = 0
    · subst h0; right; simp [capChart]
    · left
      refine ⟨capInvFun L y, ?_, by simp [capChart, h0]⟩
      show L ≤ supNorm (capInvFun L y)
      rw [u3h_supNorm_capInvFun hL h0]
      have hN := u3h_supNorm_pos h0
      rw [le_div_iff₀ hN]
      have : supNorm y ≤ 1 := hy
      nlinarith
  · rintro z (⟨x, hx, rfl⟩ | hz)
    · show supNorm (capInvFun L x) ≤ 1
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp only [mem_ofPred_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
        linarith
      rw [u3h_supNorm_capInvFun hL hx0, div_le_one (u3h_supNorm_pos hx0)]
      exact hx
    · rw [mem_singleton_iff] at hz; subst hz
      show supNorm 0 ≤ 1
      simp [supNorm]
  · rintro z (⟨x, hx, rfl⟩ | hz)
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp only [mem_ofPred_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
        linarith
      show capChart L (capInvFun L x) = (x : Sphere)
      simp [capChart, u3h_capInvFun_ne_zero hL hx0, u3h_capInvFun_capInvFun hL.ne' hx0]
    · rw [mem_singleton_iff] at hz; subst hz
      show capChart L 0 = ∞
      simp [capChart]

/-- U8: on the seam `‖y‖_∞ = 1` the cap chart is the affine map `y ↦ L • (y₁, −y₂)`. -/
theorem U8_capInvFun_seam {L : ℝ} {y : Plane} (hy : supNorm y = 1) :
    capInvFun L y = L • (y.1, -y.2) := by
  exact u3h_capInvFun_seam hy

/-! ### U8: the exterior fan map is a homeomorphism onto `Q_2` -/

theorem u8h_cap_eq {L : ℝ} (hL : 0 < L) :
    capChart L '' square 1 = ((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞} :=
  u1h_isHomeoOnto_image (U8_capChart_isHomeoOnto hL)

theorem u8h_notMem_interior_of_ge {L : ℝ} (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {x : Plane} (hx : L ≤ supNorm x) : x ∉ interior T₀.carrier := by
  intro h
  have := (u8h_mem_interior_square_iff x).1 (hT (interior_subset h))
  linarith

/-- The model exterior is the union of the closed annulus and the closed cap. -/
theorem u8h_E_eq {L : ℝ} (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_E T₀ = ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier) ∪
      (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [u8h_infty_mem_E]
  | coe x =>
    rw [u8h_coe_mem_E]
    simp only [mem_union, mem_image, OnePoint.coe_eq_coe, exists_eq_right, mem_sdiff, mem_ofPred_eq,
      mem_singleton_iff]
    constructor
    · intro h
      by_cases hx : supNorm x ≤ L
      · exact Or.inl ⟨hx, h⟩
      · push Not at hx; exact Or.inr (Or.inl hx.le)
    · rintro (⟨-, h⟩ | (h | h))
      · exact h
      · exact u8h_notMem_interior_of_ge T₀ hT h
      · exact absurd h (OnePoint.coe_ne_infty x)

theorem u8h_gS_continuousOn {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    ContinuousOn (u8h_gS hL T₀ hT) (u8h_E T₀) := by
  rw [u8h_E_eq T₀ hT]
  apply ContinuousOn.union_of_isClosed
  · have hA : ContinuousOn (u8h_g hL T₀ hT) (square L \ interior T₀.carrier) :=
      U2_continuousOn_of_isPositivePLOn (u8h_K hL T₀ hT) (u8h_g_isPositivePLOn hL T₀ hT)
    have hpl : ContinuousOn planeOf (((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier)) :=
      u8h_continuousOn_of_isHomeoOnto (U1_isHomeoOnto_inv (U1_isHomeoOnto_coe _) (fun x _ => rfl))
    have hmaps : MapsTo planeOf (((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier))
        (square L \ interior T₀.carrier) := by rintro _ ⟨x, hx, rfl⟩; exact hx
    refine (hA.comp hpl hmaps).congr ?_
    rintro _ ⟨x, hx, rfl⟩
    show u8h_gS hL T₀ hT x = u8h_g hL T₀ hT (planeOf x)
    rw [u8h_gS_coe_of_le hL T₀ hT hx.1]; rfl
  · have hcont : ContinuousOn (modelChartInv L true)
        (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) := by
      intro z hz
      apply ContinuousAt.continuousWithinAt
      apply u8h_continuous_capInv hL
      rcases hz with ⟨x, hx, rfl⟩ | hz
      · intro h
        rw [OnePoint.coe_eq_coe] at h
        subst h
        simp only [mem_ofPred_eq, supNorm, Prod.fst_zero, Prod.snd_zero, abs_zero, max_self] at hx
        linarith
      · rw [mem_singleton_iff] at hz; subst hz; exact OnePoint.infty_ne_coe _
    refine hcont.congr ?_
    rintro z (⟨x, hx, rfl⟩ | hz)
    · show u8h_gS hL T₀ hT x = capInvFun L x
      exact u8h_gS_coe_of_ge hL T₀ hT hx
    · rw [mem_singleton_iff] at hz; subst hz; rfl
  · exact OnePoint.isClosed_image_coe.2
      ⟨(isClosed_le u8h_continuous_supNorm continuous_const).inter isOpen_interior.isClosed_compl,
        u8h_isCompact_annulus hL T₀⟩
  · exact u8h_isClosed_cap

theorem u8h_gS_image_cap {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' (((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞}) = square 1 := by
  rw [← u8h_cap_eq hL, ← image_comp]
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    show u8h_gS hL T₀ hT (capChart L y) ∈ square 1
    rw [u8h_gS_capChart hL T₀ hT hy]; exact hy
  · intro y hy; exact ⟨y, hy, u8h_gS_capChart hL T₀ hT hy⟩

theorem u8h_gS_image_annulus {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' (((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier)) =
      square 2 \ interior (square 1) := by
  rw [← image_comp, ← (u8h_g_bij hL T₀ hT).2]
  apply image_congr
  intro x hx
  exact u8h_gS_coe_of_le hL T₀ hT hx.1

theorem u8h_gS_image {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    u8h_gS hL T₀ hT '' u8h_E T₀ = square 2 := by
  rw [u8h_E_eq T₀ hT, image_union, u8h_gS_image_cap hL T₀ hT, u8h_gS_image_annulus hL T₀ hT]
  ext x
  simp only [mem_union, mem_sdiff]
  constructor
  · rintro (⟨h, -⟩ | h)
    · exact h
    · show supNorm x ≤ 2
      have : supNorm x ≤ 1 := h
      linarith
  · intro h
    by_cases hx : x ∈ square 1
    · exact Or.inr hx
    · exact Or.inl ⟨h, fun hi => hx (interior_subset hi)⟩

/-- A cap point whose image is not in `int Q_1` lies on the seam, hence in the closed annulus. -/
theorem u8h_cap_seam_case {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L))
    {z : Sphere} (hz : z ∈ ((↑) : Plane → Sphere) '' {x | L ≤ supNorm x} ∪ {∞})
    (hg : u8h_gS hL T₀ hT z ∉ interior (square 1)) :
    z ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier) := by
  rw [← u8h_cap_eq hL] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [u8h_gS_capChart hL T₀ hT hy, u8h_mem_interior_square_iff, not_lt] at hg
  have hy1 : supNorm y = 1 := le_antisymm hy hg
  have hy0 : y ≠ 0 := by rintro rfl; simp [supNorm] at hy1
  have hx : supNorm (capInvFun L y) = L := by rw [u3h_supNorm_capInvFun hL hy0, hy1, div_one]
  refine ⟨capInvFun L y, ⟨hx.le, u8h_notMem_interior_of_ge T₀ hT hx.ge⟩, ?_⟩
  simp [capChart, hy0]

theorem u8h_gS_injOn {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    InjOn (u8h_gS hL T₀ hT) (u8h_E T₀) := by
  have hbij := u8h_g_bij hL T₀ hT
  have hann : ∀ z ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier),
      ∀ z' ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier),
        u8h_gS hL T₀ hT z = u8h_gS hL T₀ hT z' → z = z' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ heq
    rw [u8h_gS_coe_of_le hL T₀ hT hx.1, u8h_gS_coe_of_le hL T₀ hT hx'.1] at heq
    rw [hbij.1 hx hx' heq]
  have hannB : ∀ z ∈ ((↑) : Plane → Sphere) '' (square L \ interior T₀.carrier),
      u8h_gS hL T₀ hT z ∉ interior (square 1) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [u8h_gS_coe_of_le hL T₀ hT hx.1]
    have : u8h_g hL T₀ hT x ∈ square 2 \ interior (square 1) := hbij.2 ▸ ⟨x, hx, rfl⟩
    exact this.2
  intro z hz z' hz' heq
  rw [u8h_E_eq T₀ hT] at hz hz'
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact hann z hz z' hz' heq
  · exact hann z hz z' (u8h_cap_seam_case hL T₀ hT hz' (heq ▸ hannB z hz)) heq
  · exact hann z (u8h_cap_seam_case hL T₀ hT hz (heq ▸ hannB z' hz')) z' hz' heq
  · rw [← u8h_cap_eq hL] at hz hz'
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨y', hy', rfl⟩ := hz'
    rw [u8h_gS_capChart hL T₀ hT hy, u8h_gS_capChart hL T₀ hT hy'] at heq
    rw [heq]

theorem u8h_isCompact_E (T₀ : Triangle) : IsCompact (u8h_E T₀) :=
  (OnePoint.isOpen_image_coe.2 isOpen_interior).isClosed_compl.isCompact

/-- **The exterior fan map is a homeomorphism of the model exterior onto `Q_2`.** -/
theorem u8h_gS_isHomeoOnto {L : ℝ} (hL : 0 < L) (T₀ : Triangle) (hT : T₀.carrier ⊆ interior (square L)) :
    IsHomeoOnto (u8h_E T₀) (square 2) (u8h_gS hL T₀ hT) :=
  u8h_isHomeoOnto_of_compact (u8h_isCompact_E T₀) (u8h_gS_continuousOn hL T₀ hT) (u8h_gS_injOn hL T₀ hT)
    (u8h_gS_image hL T₀ hT)

/-- U8 (the 11-ray fan, PLAN_FINAL §3.3): the model exterior `Sphere \ int T₀` of a triangle inside
`int Q_L` is carried onto the square `Q_2` by a homeomorphism that is positive PL in the two model
charts and sends `∂T₀` onto `∂Q_2`. -/
theorem U8_exists_exterior_fan {L : ℝ} (hL : 0 < L) (T₀ : Triangle)
    (hT : T₀.carrier ⊆ interior (square L)) :
    ∃ g : Sphere → Plane,
      IsHomeoOnto (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ (square 2) g ∧
      IsPositivePLToPlane L (((↑) : Plane → Sphere) '' interior T₀.carrier)ᶜ g ∧
      g '' (((↑) : Plane → Sphere) '' frontier T₀.carrier) = frontier (square 2) := by
  exact ⟨u8h_gS hL T₀ hT, u8h_gS_isHomeoOnto hL T₀ hT, u8h_gS_isPositivePLToPlane hL T₀ hT,
    u8h_gS_frontier hL T₀ hT⟩

/-- U8: the closed exterior region is the sphere minus the open image triangle. -/
theorem U8_closure_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) :
    closure (exteriorRegion P) = (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier))ᶜ := by
  have hext := U6_exteriorRegion_eq hn P hP A
  have hopen : IsOpen (((↑) : Plane → Sphere) '' (A.H '' interior A.T₀.carrier)) :=
    OnePoint.isOpen_image_coe.2 (A.H.isOpenMap _ isOpen_interior)
  apply Subset.antisymm
  · apply closure_minimal _ hopen.isClosed_compl
    rw [hext]
    rintro z (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | hz)
    · rintro ⟨_, ⟨x', hx', rfl⟩, h⟩
      rw [OnePoint.coe_eq_coe] at h
      have := A.H.injective h
      subst this
      exact hx (interior_subset hx')
    · rw [mem_singleton_iff] at hz; subst hz
      exact OnePoint.infty_notMem_image_coe
  · intro z hz
    induction z using OnePoint.rec with
    | infty => exact subset_closure (by rw [hext]; exact Or.inr rfl)
    | coe y =>
      have hy : y ∉ A.H '' interior A.T₀.carrier := fun h => hz ⟨y, h, rfl⟩
      have hy' : A.H.symm y ∈ closure (A.T₀.carrier)ᶜ := by
        rw [closure_compl]
        intro h; apply hy
        exact ⟨A.H.symm y, h, A.H.apply_symm_apply y⟩
      have h2 : y ∈ closure (A.H '' (A.T₀.carrier)ᶜ) := by
        rw [← A.H.image_closure]
        exact ⟨A.H.symm y, hy', A.H.apply_symm_apply y⟩
      have h3 : ((y : Plane) : Sphere) ∈ closure (((↑) : Plane → Sphere) '' (A.H '' (A.T₀.carrier)ᶜ)) :=
        image_closure_subset_closure_image OnePoint.continuous_coe ⟨y, h2, rfl⟩
      refine closure_mono ?_ h3
      rw [hext]; exact subset_union_left

theorem u8h_closure_ext_mem_coe [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) {x : Plane} (hx : L ≤ supNorm x) :
    (x : Sphere) ∈ closure (exteriorRegion P) := by
  rw [U8_closure_exteriorRegion_eq hn P hP A]
  rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
  rw [OnePoint.coe_eq_coe] at h
  have : A.H w ∈ interior (square L) := by
    rw [← u8h_H_image_interior A]; exact ⟨w, A.inside (interior_subset hw), rfl⟩
  rw [h, u8h_mem_interior_square_iff] at this
  linarith

/-- U8: `H⁻¹` extended by the identity at `∞` is a positive PL sphere map (model `L` to model `L`)
on the closed exterior region. -/
theorem U8_isPositivePLSphereMap_inv [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (hL : InsideModel L P) (A : AmbientParam P L) :
    IsPositivePLSphereMap L L (closure (exteriorRegion P)) (OnePoint.map A.H.symm) ∧
      IsHomeoOnto (closure (exteriorRegion P)) (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ
        (OnePoint.map A.H.symm) := by
  have hL0 : 0 < L := lt_of_le_of_lt (u3h_supNorm_nonneg _) (hL 0)
  have hcl := U8_closure_exteriorRegion_eq hn P hP A
  set F := OnePoint.map A.H.symm with hF
  have himg : F '' closure (exteriorRegion P) = (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ := by
    rw [hcl, Set.image_compl_eq (u8h_onePoint_map_bijective _), u8h_onePoint_map_image_coe]
    have hss : A.H.symm '' (A.H '' interior A.T₀.carrier) = interior A.T₀.carrier := by
      ext v; constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; simpa using hu
      · intro hv; exact ⟨A.H v, ⟨v, hv, rfl⟩, A.H.symm_apply_apply v⟩
    rw [hss]
  constructor
  · intro b
    cases b
    · -- plane chart
      obtain ⟨g, -, hpl, -⟩ := U8_exists_exterior_fan hL0 A.T₀ A.inside
      obtain ⟨K₀, -⟩ := hpl false
      rw [u8h_chartPart_false_exterior] at K₀
      obtain ⟨K₁, hK₁, hfaces⟩ := U3_refine_into K₀ A.K sdiff_subset
      have hH : IsPositivePLOn A.H K₁ := by
        intro T hT
        obtain ⟨T', hT', hsub⟩ := hfaces T hT
        exact U1_isPositiveAffineOn_mono (A.pl T' hT') hsub
      obtain ⟨K₂, hK₂⟩ := U2_inverse_isPositivePLOn K₁ A.H hH
      have hset : A.H '' (square L \ interior A.T₀.carrier) =
          chartPart L false (closure (exteriorRegion P)) := by
        rw [hcl, Set.image_sdiff A.H.injective, u8h_H_image_square]
        ext x
        simp only [chartPart, modelDomain, modelChart, mem_inter_iff, mem_preimage, mem_compl_iff, mem_sdiff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨y, hy, hyx⟩ => h2 (by rw [OnePoint.coe_eq_coe] at hyx; rw [← hyx]; exact hy)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨x, h, rfl⟩⟩
      refine ⟨u8h_triangulation_congr hset K₂, fun T hT => ⟨false, fun x hx => ?_, ?_⟩⟩
      · have hxs : x ∈ square L := by
          have := u3h_face_subset_chartPart (u8h_triangulation_congr hset K₂) hT hx
          exact this.1
        refine ⟨A.H.symm x, ?_, rfl⟩
        rw [← u8h_H_image_square A] at hxs
        obtain ⟨w, hw, rfl⟩ := hxs
        rw [A.H.symm_apply_apply]; exact hw
      · exact u3h_isPositiveAffineOn_congr (fun x _ => rfl) (hK₂ T hT)
    · -- cap chart
      have hset : square 1 = chartPart L true (closure (exteriorRegion P)) := by
        rw [u8h_chartPart_true_eq hL0]
        · exact subset_closure (by rw [exteriorRegion]; exact mem_connectedComponentIn (by
            show ∞ ∉ sphereCircle P; exact OnePoint.infty_notMem_image_coe))
        · exact fun x hx => u8h_closure_ext_mem_coe hn P hP A hx
      obtain ⟨K⟩ := U2_triangulation_square (one_pos : (0 : ℝ) < 1)
      refine ⟨u8h_triangulation_congr hset K, fun T hT => ⟨true, fun x hx => ?_, ?_⟩⟩
      · have hxs : x ∈ square 1 := u3h_face_subset_chartPart (u8h_triangulation_congr hset K) hT hx |>.1
        refine ⟨x, hxs, ?_⟩
        show capChart L x = F (capChart L x)
        by_cases h0 : x = 0
        · subst h0; simp [capChart, F]
        · simp only [capChart, h0, ↓reduceIte, F, OnePoint.map_some]
          rw [u8h_H_symm_fix A]
          rw [u3h_supNorm_capInvFun hL0 h0, le_div_iff₀ (u3h_supNorm_pos h0)]
          have : supNorm x ≤ 1 := hxs
          nlinarith
      · refine u3h_isPositiveAffineOn_congr (fun x hx => ?_) (u8h_isPositiveAffineOn_id T)
        have hxs : x ∈ square 1 := u3h_face_subset_chartPart (u8h_triangulation_congr hset K) hT hx |>.1
        show x = modelChartInv L true (F (capChart L x))
        by_cases h0 : x = 0
        · subst h0; simp [capChart, F, modelChartInv]
        · have hfix : A.H.symm (capInvFun L x) = capInvFun L x := by
            rw [u8h_H_symm_fix A]
            rw [u3h_supNorm_capInvFun hL0 h0, le_div_iff₀ (u3h_supNorm_pos h0)]
            have : supNorm x ≤ 1 := hxs
            nlinarith
          simp only [capChart, h0, ↓reduceIte, F, OnePoint.map_some, hfix]
          show x = capInvFun L (capInvFun L x)
          rw [u3h_capInvFun_capInvFun hL0.ne' h0]
  · rw [← himg]
    exact u8h_isHomeoOnto_onePoint_map A.H.symm _

/-- U8 (57b exterior, sm-3:431 / 448-456 / 490-493): the closure of the exterior region is a PL disc
of the sphere with boundary the circle. -/
theorem U8_pl_discs_outer [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) : IsPLDiscSphere L (closure (regionOf P Side.outer)) (sphereCircle P) := by
  have hL0 : 0 < L := lt_of_le_of_lt (u3h_supNorm_nonneg _) (hL 0)
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  obtain ⟨g, hg1, hg2, hg3⟩ := U8_exists_exterior_fan hL0 A.T₀ A.inside
  obtain ⟨hF1, hF2⟩ := U8_isPositivePLSphereMap_inv hn P hP hL A
  have hcl := U8_closure_exteriorRegion_eq hn P hP A
  show IsPLDiscSphere L (closure (exteriorRegion P)) (sphereCircle P)
  have hFimg : OnePoint.map A.H.symm '' closure (exteriorRegion P) =
      (((↑) : Plane → Sphere) '' interior A.T₀.carrier)ᶜ := u1h_isHomeoOnto_image hF2
  have hcirc : sphereCircle P = ((↑) : Plane → Sphere) '' (A.H '' frontier A.T₀.carrier) := by
    rw [sphereCircle, A.boundary]
  refine ⟨square 2, g ∘ OnePoint.map A.H.symm, U1_square_isDisc two_pos, ?_, ?_, ?_, ?_⟩
  · rw [hcirc, hcl]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨y, hy, rfl⟩, h⟩
    rw [OnePoint.coe_eq_coe] at h
    have := A.H.injective h
    subst this
    exact hx.2 hy
  · exact U1_isHomeoOnto_comp hF2 hg1
  · rw [image_comp, hcirc, u8h_onePoint_map_image_coe, ← hg3]
    congr 2
    ext v; constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; simpa using hu
    · intro hv; exact ⟨A.H v, ⟨v, hv, rfl⟩, A.H.symm_apply_apply v⟩
  · exact U3_isPositivePLToPlane_comp hF1 hFimg.le hg2

/-! ### U9 (sequential) — orientation bookkeeping (FR-TD-9) -/

/-- U9: the left normal `(−u₂, u₁)` of a direction `u`. -/
def leftNormal (u : Plane) : Plane := (-u.2, u.1)

/-- U9: the bounded region lies on the left of edge `i` (a short left normal from the midpoint of
the edge enters the interior region). -/
def InteriorOnLeft [NeZero n] (P : LabelledTuple n) (i : ZMod n) : Prop :=
  ∃ ε > 0, ∀ t ∈ Ioo (0 : ℝ) ε,
    (((1 / 2 : ℝ) • (P i + P (i + 1)) + t • leftNormal (edge P i) : Plane) : Sphere) ∈ interiorRegion P

/-- U9: `b` lies strictly between `a` and `c` in the counterclockwise cyclic order around `z`
(two-of-three `det` signs). -/
def CyclicPos (z a b c : Plane) : Prop :=
  (0 < det (a - z) (b - z) ∧ 0 < det (b - z) (c - z)) ∨
  (0 < det (b - z) (c - z) ∧ 0 < det (c - z) (a - z)) ∨
  (0 < det (c - z) (a - z) ∧ 0 < det (a - z) (b - z))

/-! #### U9 helpers (wave 2, `u9h_`): blocks A-F, placed before the first U9 leaf.
A: `det` algebra and `CyclicPos` basics; B: facts about a convex disc and its frontier (ray uniqueness,
totality of the cyclic order, supporting line of a frontier segment); C: the canonical region
`u4h_regionOf P` equals `A.H '' T₀` (via the U6 black boxes), hence `interiorRegion P = coe '' interior
(u4h_regionOf P)` and the plane traces of both closed regions; D: the face of the region at an edge and
the local half-plane structure at an edge midpoint; E: `σ = 1 ↔ 0 < rotationNumber P` at the lexmin
vertex; F: the traversal read in `f`, the connectedness dichotomy on increasing triples, and the local
evaluation at the midpoint of edge `0`.  Report: W2_U9_REPORT.md. -/

/-! #### U9 helpers, block A: `det` algebra and `CyclicPos` basics -/

theorem u9h_det_swap (u v : Plane) : det u v = -det v u := by simp only [det]; ring

theorem u9h_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u9h_det_zero_left (v : Plane) : det 0 v = 0 := by simp only [det, Prod.fst_zero, Prod.snd_zero]; ring

theorem u9h_det_smul_right (u v : Plane) (t : ℝ) : det u (t • v) = t * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u9h_det_smul_left (u v : Plane) (t : ℝ) : det (t • u) v = t * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u9h_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u9h_det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u9h_det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u9h_det_neg_left (u v : Plane) : det (-u) v = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

/-- `det u (leftNormal u) = ‖u‖²`. -/
theorem u9h_det_leftNormal (u : Plane) : det u (leftNormal u) = u.1 * u.1 + u.2 * u.2 := by
  simp only [det, leftNormal]; ring

theorem u9h_det_leftNormal_pos {u : Plane} (hu : u ≠ 0) : 0 < det u (leftNormal u) := by
  rw [u9h_det_leftNormal]
  rcases ne_or_eq u.1 0 with h1 | h1
  · have := mul_self_pos.mpr h1; nlinarith [mul_self_nonneg u.2]
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    have := mul_self_pos.mpr h2; nlinarith [mul_self_nonneg u.1]

/-- A vector with `det u v = 0` is a multiple of the nonzero `u`. -/
theorem u9h_parallel_of_det_eq_zero {u v : Plane} (hu : u ≠ 0) (h : det u v = 0) :
    ∃ μ : ℝ, v = μ • u := by
  simp only [det] at h
  rcases ne_or_eq u.1 0 with h1 | h1
  · refine ⟨v.1 / u.1, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
    · simp only [Prod.smul_snd, smul_eq_mul]; field_simp; linear_combination h
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    refine ⟨v.2 / u.2, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]; rw [h1] at h ⊢; field_simp; linear_combination -h
    · simp only [Prod.smul_snd, smul_eq_mul]; field_simp

theorem u9h_cyclicPos_rotate {z a b c : Plane} (h : CyclicPos z a b c) : CyclicPos z b c a := by
  unfold CyclicPos at *; tauto

theorem u9h_cyclicPos_antisymm {z a b c : Plane} (h1 : CyclicPos z a b c) (h2 : CyclicPos z a c b) :
    False := by
  unfold CyclicPos at *
  have e1 := u9h_det_swap (a - z) (b - z)
  have e2 := u9h_det_swap (b - z) (c - z)
  have e3 := u9h_det_swap (c - z) (a - z)
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem u9h_cyclicPos_ne {z a b c : Plane} (h : CyclicPos z a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> unfold CyclicPos at h
  · have := u9h_det_self (a - z); have := u9h_det_swap (a - z) (c - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u9h_det_self (b - z); have := u9h_det_swap (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u9h_det_self (a - z); have := u9h_det_swap (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

/-- Three collinear points `a, a + s v, a + 2s v` (`s > 0`) are in positive cyclic order around `z`
iff `det (a - z) v > 0`, and not in positive order when `det (a - z) v < 0`. -/
theorem u9h_cyclicPos_collinear (z a v : Plane) {s : ℝ} (hs : 0 < s) :
    (0 < det (a - z) v → CyclicPos z a (a + s • v) (a + (2 * s) • v)) ∧
    (det (a - z) v < 0 → ¬ CyclicPos z a (a + s • v) (a + (2 * s) • v)) := by
  have e1 : det (a - z) (a + s • v - z) = s * det (a - z) v := by
    have : a + s • v - z = (a - z) + s • v := by abel
    rw [this, u9h_det_add_right, u9h_det_self, u9h_det_smul_right]; ring
  have e2 : det (a + s • v - z) (a + (2 * s) • v - z) = s * det (a - z) v := by
    have h1 : a + s • v - z = (a - z) + s • v := by abel
    have h2 : a + (2 * s) • v - z = (a - z) + (2 * s) • v := by abel
    rw [h1, h2, u9h_det_add_left, u9h_det_add_right, u9h_det_add_right, u9h_det_self,
      u9h_det_smul_right, u9h_det_smul_right, u9h_det_smul_left, u9h_det_smul_left, u9h_det_self,
      u9h_det_swap v (a - z)]
    ring
  have e3 : det (a + (2 * s) • v - z) (a - z) = -(2 * s) * det (a - z) v := by
    have h2 : a + (2 * s) • v - z = (a - z) + (2 * s) • v := by abel
    rw [h2, u9h_det_add_left, u9h_det_self, u9h_det_smul_left, u9h_det_swap v (a - z)]; ring
  unfold CyclicPos
  rw [e1, e2, e3]
  constructor
  · intro h; exact Or.inl ⟨mul_pos hs h, mul_pos hs h⟩
  · intro h hc
    have h1 : s * det (a - z) v < 0 := mul_neg_of_pos_of_neg hs h
    rcases hc with ⟨h2, _⟩ | ⟨h2, _⟩ | ⟨_, h2⟩ <;> linarith

/-- Continuity of `det` in a pair of continuous arguments. -/
theorem u9h_continuous_det {X : Type*} [TopologicalSpace X] {f g : X → Plane} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => det (f x) (g x) := by
  simp only [det]
  exact ((continuous_fst.comp hf).mul (continuous_snd.comp hg)).sub
    ((continuous_snd.comp hf).mul (continuous_fst.comp hg))

/-- The `CyclicPos` predicate along three continuous maps is an open condition. -/
theorem u9h_isOpen_cyclicPos {X : Type*} [TopologicalSpace X] (z : Plane) {F G H : X → Plane}
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    IsOpen {x | CyclicPos z (F x) (G x) (H x)} := by
  have h1 : IsOpen {x | 0 < det (F x - z) (G x - z)} :=
    isOpen_lt continuous_const (u9h_continuous_det (hF.sub continuous_const) (hG.sub continuous_const))
  have h2 : IsOpen {x | 0 < det (G x - z) (H x - z)} :=
    isOpen_lt continuous_const (u9h_continuous_det (hG.sub continuous_const) (hH.sub continuous_const))
  have h3 : IsOpen {x | 0 < det (H x - z) (F x - z)} :=
    isOpen_lt continuous_const (u9h_continuous_det (hH.sub continuous_const) (hF.sub continuous_const))
  have : {x | CyclicPos z (F x) (G x) (H x)} =
      ({x | 0 < det (F x - z) (G x - z)} ∩ {x | 0 < det (G x - z) (H x - z)}) ∪
      ({x | 0 < det (G x - z) (H x - z)} ∩ {x | 0 < det (H x - z) (F x - z)}) ∪
      ({x | 0 < det (H x - z) (F x - z)} ∩ {x | 0 < det (F x - z) (G x - z)}) := by
    ext x; simp only [CyclicPos, mem_ofPred_eq, mem_union, mem_inter_iff]; tauto
  rw [this]
  exact ((h1.inter h2).union (h2.inter h3)).union (h3.inter h1)

/-! #### U9 helpers, block B: facts about a convex disc `D` and its frontier -/

theorem u9h_frontier_ne_interior {D : Set Plane} {p z : Plane} (hp : p ∈ frontier D)
    (hz : z ∈ interior D) : p ≠ z := by
  rintro rfl; exact hp.2 hz

/-- Two frontier points on one ray from an interior point coincide. -/
theorem u9h_ray_unique {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p r : Plane} (hp : p ∈ frontier D) (hr : r ∈ frontier D) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : r - z = μ • (p - z)) : r = p := by
  have hr' : r = z + μ • (p - z) := by rw [← h]; abel
  rcases lt_trichotomy μ 1 with h1 | h1 | h1
  · exfalso
    rcases hμ.lt_or_eq with h0 | h0
    · have hmem : r ∈ openSegment ℝ z p := by
        refine ⟨1 - μ, μ, by linarith, h0, by ring, ?_⟩
        rw [hr', smul_sub, sub_smul, one_smul]; abel
      exact hr.2 (hD.1.openSegment_interior_closure_subset_interior hz hp.1 hmem)
    · rw [← h0, zero_smul, add_zero] at hr'; exact hr.2 (hr' ▸ hz)
  · rw [h1, one_smul] at hr'; rw [hr']; abel
  · exfalso
    have hμ0 : μ ≠ 0 := by linarith
    have hmem : p ∈ openSegment ℝ z r := by
      refine ⟨1 - 1 / μ, 1 / μ, ?_, by positivity, by ring, ?_⟩
      · rw [sub_pos, div_lt_one (by linarith)]; exact h1
      · rw [hr', smul_add, smul_smul, one_div, inv_mul_cancel₀ hμ0, one_smul, sub_smul, one_smul]
        abel
    exact hp.2 (hD.1.openSegment_interior_closure_subset_interior hz hr.1 hmem)

theorem u9h_antipodal {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hne : q ≠ p)
    (h0 : det (p - z) (q - z) = 0) : ∃ lam : ℝ, 0 < lam ∧ q - z = -(lam • (p - z)) := by
  obtain ⟨μ, hμ⟩ := u9h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u9h_frontier_ne_interior hp hz)) h0
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · exact absurd (u9h_ray_unique hD hz hp hq hμ0 hμ) hne
  · exact ⟨-μ, by linarith, by rw [hμ, neg_smul, neg_neg]⟩

theorem u9h_det_prod_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hqp : q ≠ p)
    (hrp : r ≠ p) (hrq : r ≠ q) (h0 : det (p - z) (q - z) = 0) :
    0 < det (q - z) (r - z) * det (r - z) (p - z) := by
  obtain ⟨lam, hlam, hq'⟩ := u9h_antipodal hD hz hp hq hqp h0
  have e : det (q - z) (r - z) = lam * det (r - z) (p - z) := by
    rw [hq', ← neg_smul, u9h_det_smul_left, u9h_det_swap (p - z) (r - z)]; ring
  rw [e, mul_assoc]
  have hne : det (r - z) (p - z) ≠ 0 := by
    intro h
    have h' : det (p - z) (r - z) = 0 := by rw [u9h_det_swap]; linarith
    obtain ⟨μ, hμ⟩ :=
      u9h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u9h_frontier_ne_interior hp hz)) h'
    rcases le_or_gt 0 μ with hμ0 | hμ0
    · exact hrp (u9h_ray_unique hD hz hp hr hμ0 hμ)
    · apply hrq
      refine u9h_ray_unique hD hz hq hr (μ := -μ / lam) (div_nonneg (by linarith) hlam.le) ?_
      rw [hμ, hq', smul_neg, smul_smul]
      have : -μ / lam * lam = -μ := div_mul_cancel₀ _ hlam.ne'
      rw [this, neg_smul, neg_neg]
  have : 0 < det (r - z) (p - z) * det (r - z) (p - z) := mul_self_pos.mpr hne
  positivity

/-- Totality of the cyclic order on the frontier of a convex disc around an interior point. -/
theorem u9h_cyclicPos_total {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hpq : p ≠ q)
    (hqr : q ≠ r) (hpr : p ≠ r) : CyclicPos z p q r ∨ CyclicPos z p r q := by
  have e1 := u9h_det_swap (q - z) (p - z)
  have e2 := u9h_det_swap (r - z) (q - z)
  have e3 := u9h_det_swap (p - z) (r - z)
  unfold CyclicPos
  rw [e1, e2, e3]
  simp only [neg_pos]
  by_cases hA : det (p - z) (q - z) = 0
  · have := u9h_det_prod_pos hD hz hp hq hr hpq.symm hpr.symm hqr.symm hA
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  by_cases hB : det (q - z) (r - z) = 0
  · have := u9h_det_prod_pos hD hz hq hr hp hqr.symm hpq hpr hB
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  by_cases hC : det (r - z) (p - z) = 0
  · have := u9h_det_prod_pos hD hz hr hp hq hpr hqr hpq.symm hC
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> tauto
  rcases lt_or_gt_of_ne hA with hA | hA <;> rcases lt_or_gt_of_ne hB with hB | hB <;>
    rcases lt_or_gt_of_ne hC with hC | hC <;> tauto

/-! #### U9 helpers, block B (continued): supporting line of a frontier segment -/

/-- The zero set of an affine `det` functional is convex. -/
theorem u9h_convex_det_eq_zero (u w : Plane) : Convex ℝ {x : Plane | det u (x - w) = 0} := by
  intro x hx y hy s t hs ht hst
  simp only [mem_ofPred_eq] at hx hy ⊢
  have hw : w = s • w + t • w := by rw [← add_smul, hst, one_smul]
  have : s • x + t • y - w = s • (x - w) + t • (y - w) := by
    rw [smul_sub, smul_sub]; conv_lhs => rw [hw]
    abel
  rw [this, u9h_det_add_right, u9h_det_smul_right, u9h_det_smul_right, hx, hy]; ring

/-- A closed convex disc containing a frontier segment `{a + s v | s ∈ [0, δ]}` lies on one side of
the line through it. -/
theorem u9h_supporting_line {D : Set Plane} (hD : Link.IsDisc D) {a v : Plane} {δ : ℝ}
    (hδ : 0 < δ) (hfr : ∀ s ∈ Icc (0:ℝ) δ, a + s • v ∈ frontier D) :
    (∀ x ∈ D, 0 ≤ det v (x - a)) ∨ (∀ x ∈ D, det v (x - a) ≤ 0) := by
  have hcl : IsClosed D := hD.2.1.isClosed
  have hfrD : ∀ s ∈ Icc (0:ℝ) δ, a + s • v ∈ D := fun s hs => hcl.frontier_subset (hfr s hs)
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [not_forall, not_le, exists_prop] at h1 h2
  obtain ⟨x₁, hx₁, hd₁⟩ := h1
  obtain ⟨x₂, hx₂, hd₂⟩ := h2
  set p : Plane := a with hp
  set q : Plane := a + δ • v with hq
  set m : Plane := a + (δ / 2) • v with hm
  have hpD : p ∈ D := by have := hfrD 0 ⟨le_rfl, hδ.le⟩; rwa [zero_smul, add_zero] at this
  have hqD : q ∈ D := hfrD δ ⟨hδ.le, le_rfl⟩
  have hmfr : m ∈ frontier D := hfr (δ / 2) ⟨by positivity, by linarith⟩
  -- the two triangles `(p, q, x₂)` and `(q, p, x₁)`
  have hT1 : 0 < det (q - p) (x₂ - p) := by
    have : q - p = δ • v := by rw [hq, hp]; abel
    rw [this, u9h_det_smul_left]; exact mul_pos hδ hd₂
  have hT2 : 0 < det (p - q) (x₁ - q) := by
    have e : det (p - q) (x₁ - q) = -(δ * det v (x₁ - a)) := by
      simp only [hp, hq, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; nlinarith
  have hsub1 : convexHull ℝ {p, q, x₂} ⊆ D := by
    apply convexHull_min _ hD.1
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hsub2 : convexHull ℝ {q, p, x₁} ⊆ D := by
    apply convexHull_min _ hD.1
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  -- an open neighbourhood of `m` inside the union of the two triangles
  set O : Set Plane := {x | 0 < det (x₂ - q) (x - q)} ∩ {x | 0 < det (p - x₂) (x - x₂)} ∩
    ({x | 0 < det (x₁ - p) (x - p)} ∩ {x | 0 < det (q - x₁) (x - x₁)}) with hO
  have hOopen : IsOpen O :=
    ((u1h_isOpen_det_pos _ _).inter (u1h_isOpen_det_pos _ _)).inter
      ((u1h_isOpen_det_pos _ _).inter (u1h_isOpen_det_pos _ _))
  have hmO : m ∈ O := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [mem_ofPred_eq]
    · have e : det (x₂ - q) (m - q) = (δ / 2) * det v (x₂ - a) := by
        simp only [hm, hq, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; positivity
    · have e : det (p - x₂) (m - x₂) = (δ / 2) * det v (x₂ - a) := by
        simp only [hm, hp, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; positivity
    · have e : det (x₁ - p) (m - p) = -((δ / 2) * det v (x₁ - a)) := by
        simp only [hm, hp, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; nlinarith
    · have e : det (q - x₁) (m - x₁) = -((δ / 2) * det v (x₁ - a)) := by
        simp only [hm, hq, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; nlinarith
  have hOD : O ⊆ D := by
    rintro x ⟨⟨hx1, hx2⟩, hx3, hx4⟩
    simp only [mem_ofPred_eq] at hx1 hx2 hx3 hx4
    rcases le_or_gt 0 (det v (x - a)) with hs | hs
    · apply hsub1
      rw [u4h_mem_hull3_iff_det hT1]
      refine ⟨?_, hx1.le, hx2.le⟩
      have : q - p = δ • v := by rw [hq, hp]; abel
      rw [this, u9h_det_smul_left]; exact mul_nonneg hδ.le (by rw [hp]; exact hs)
    · apply hsub2
      rw [u4h_mem_hull3_iff_det hT2]
      refine ⟨?_, hx3.le, hx4.le⟩
      have e : det (p - q) (x - q) = -(δ * det v (x - a)) := by
        simp only [hp, hq, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; nlinarith
  exact hmfr.2 (interior_maximal hOD hOopen hmO)

/-- An interior point of the disc is not on the line through a frontier segment. -/
theorem u9h_interior_off_line {D : Set Plane} (hD : Link.IsDisc D) {a v : Plane} {δ : ℝ}
    (hδ : 0 < δ) (hv : v ≠ 0) (hfr : ∀ s ∈ Icc (0:ℝ) δ, a + s • v ∈ frontier D) {z : Plane}
    (hz : z ∈ interior D) : det v (z - a) ≠ 0 := by
  intro h0
  obtain ⟨lam, hlam⟩ := u9h_parallel_of_det_eq_zero hv h0
  have ha : a ∈ frontier D := by
    have := hfr 0 ⟨le_rfl, hδ.le⟩; rwa [zero_smul, add_zero] at this
  have hz' : z = a + lam • v := by rw [← hlam]; abel
  rcases lt_trichotomy lam 0 with hl | hl | hl
  · -- `a` lies strictly between `z` and `a + δ v`
    have hmem : a ∈ openSegment ℝ z (a + δ • v) := by
      refine ⟨1 - (-lam) / (δ - lam), (-lam) / (δ - lam), ?_, by apply div_pos <;> linarith, by ring, ?_⟩
      · rw [sub_pos, div_lt_one (by linarith)]; linarith
      · have hne : δ - lam ≠ 0 := by linarith
        have e1 : (1 - -lam / (δ - lam)) * lam + -lam / (δ - lam) * δ = 0 := by
          field_simp; ring
        rw [hz']; simp only [smul_add, smul_smul]
        rw [add_add_add_comm, ← add_smul, ← add_smul, sub_add_cancel, one_smul, e1, zero_smul, add_zero]
    have hqcl : a + δ • v ∈ closure D := (hfr δ ⟨hδ.le, le_rfl⟩).1
    exact ha.2 (hD.1.openSegment_interior_closure_subset_interior hz hqcl hmem)
  · rw [hl, zero_smul, add_zero] at hz'; exact ha.2 (hz' ▸ hz)
  · -- the frontier point `a + s v`, `s = min lam δ / 2`, lies strictly between `a` and `z`
    set s : ℝ := min lam δ / 2 with hs
    have hs0 : 0 < s := by rw [hs]; exact half_pos (lt_min hl hδ)
    have hsl : s < lam := by rw [hs]; linarith [min_le_left lam δ]
    have hsδ : s ≤ δ := by rw [hs]; linarith [min_le_right lam δ]
    have hfr' : a + s • v ∈ frontier D := hfr s ⟨hs0.le, hsδ⟩
    have hmem : a + s • v ∈ openSegment ℝ a z := by
      refine ⟨1 - s / lam, s / lam, ?_, by positivity, by ring, ?_⟩
      · rw [sub_pos, div_lt_one hl]; exact hsl
      · rw [hz', smul_add, smul_smul, div_mul_cancel₀ _ hl.ne', sub_smul, one_smul]; abel
    exact hfr'.2 (hD.1.openSegment_closure_interior_subset_interior ha.1 hz hmem)

/-! #### U9 helpers, block C: the canonical region `u4h_regionOf P` and the two complementary regions
(via the U6 black boxes `U6_exists_ambientParam`, `U6_interiorRegion_eq`) -/

/-- Two closed bounded plane sets with the same frontier, the second with connected interior and
connected complement, the first with nonempty interior, have the same interior. -/
theorem u9h_interior_eq_of_frontier_eq {U W : Set Plane} (hU : IsClosed U) (hUc : IsCompact U)
    (hUne : (interior U).Nonempty) (hW : IsClosed W) (hWc : IsCompact W)
    (hfr : frontier U = frontier W) (hWi : IsPreconnected (interior W)) (hWe : IsPreconnected Wᶜ) :
    interior U = interior W := by
  have hdisj : Disjoint (interior U) Uᶜ := disjoint_compl_right.mono_left interior_subset
  -- a point of `Uᶜ ∩ Wᶜ`
  obtain ⟨R, hR0, hRb⟩ := (hUc.union hWc).isBounded.subset_closedBall_lt 0 0
  have hfar : ((R + 1, 0) : Plane) ∉ U ∪ W := by
    intro h
    have := hRb h
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ R + 1), abs_zero, max_eq_left (by linarith)] at this
    linarith
  -- points off the common frontier are interior to `U` or outside `U`
  have hsplit : ∀ x, x ∉ frontier U → x ∈ interior U ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · left
      rw [hU.frontier_eq] at hx
      by_contra hxi
      exact hx ⟨hxU, hxi⟩
    · exact Or.inr hxU
  -- step 1: `Wᶜ ⊆ Uᶜ`
  have h1 : Wᶜ ⊆ interior U ∪ Uᶜ := by
    intro x hx
    apply hsplit
    rw [hfr]
    intro hxf
    exact hx (hW.frontier_subset hxf)
  have hWU : Wᶜ ⊆ Uᶜ := by
    rcases hWe.subset_or_subset isOpen_interior hU.isOpen_compl hdisj h1 with h | h
    · exfalso
      have hx : ((R + 1, 0) : Plane) ∈ Wᶜ := fun hW' => hfar (Or.inr hW')
      exact hfar (Or.inl (interior_subset (h hx)))
    · exact h
  have hUW : U ⊆ W := compl_subset_compl.mp hWU
  -- step 2
  have h2 : interior U ⊆ interior W := interior_mono hUW
  -- step 3
  have h3 : interior W ⊆ interior U ∪ Uᶜ := by
    intro x hx
    apply hsplit
    rw [hfr]
    exact fun hxf => hxf.2 hx
  rcases hWi.subset_or_subset isOpen_interior hU.isOpen_compl hdisj h3 with h | h
  · exact Subset.antisymm h2 h
  · exfalso
    obtain ⟨x, hx⟩ := hUne
    exact h (h2 hx) (interior_subset hx)

/-- The plane set `A.H '' T₀` of an ambient parametrisation is the canonical region. -/
theorem u9h_regionOf_eq_image [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {L : ℝ} (A : AmbientParam P L) : u4h_regionOf P = A.H '' A.T₀.carrier := by
  obtain ⟨hfrU, hUc, -, -⟩ := u4h_regionOf_spec hn P hP
  obtain ⟨K, -, hedge, -, -⟩ := u4h_U4_exists_triangulation hn P hP
  have hUcl : IsClosed (u4h_regionOf P) := hUc.isClosed
  have hUne : (interior (u4h_regionOf P)).Nonempty := by
    obtain ⟨T, hT, -⟩ := hedge 0
    exact (U1_triangle_interior_nonempty T).mono (U2_interior_face_subset_interior K hT)
  have hWc : IsCompact (A.H '' A.T₀.carrier) := (U1_triangle_isCompact _).image A.H.continuous
  have hWcl : IsClosed (A.H '' A.T₀.carrier) := hWc.isClosed
  have hfrW : frontier (A.H '' A.T₀.carrier) = embeddedPolygonImage P := by
    rw [← Homeomorph.image_frontier]; exact A.boundary
  have hWi : IsPreconnected (interior (A.H '' A.T₀.carrier)) := by
    rw [← Homeomorph.image_interior]
    exact ((U1_interior_convex_isConnected (U1_triangle_convex _)
      (U1_triangle_interior_nonempty _)).image A.H A.H.continuous.continuousOn).isPreconnected
  have hWe : IsPreconnected (A.H '' A.T₀.carrier)ᶜ := by
    rw [← Homeomorph.image_compl]
    exact ((U1_compl_compact_convex_isConnected (U1_triangle_convex _)
      (U1_triangle_isCompact _)).image A.H A.H.continuous.continuousOn).isPreconnected
  have hint := u9h_interior_eq_of_frontier_eq hUcl hUc hUne hWcl hWc (hfrU.trans hfrW.symm) hWi hWe
  rw [← hUcl.closure_eq, closure_eq_interior_union_frontier, hint, hfrU, ← hfrW,
    ← closure_eq_interior_union_frontier, hWcl.closure_eq]

/-- The interior region is the coercion image of the interior of the canonical region. -/
theorem u9h_interiorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    interiorRegion P = ((↑) : Plane → Sphere) '' interior (u4h_regionOf P) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  rw [U6_interiorRegion_eq hn P hP A, u9h_regionOf_eq_image hn P hP A, ← Homeomorph.image_interior]

theorem u9h_coe_mem_interiorRegion_iff [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (x : Plane) :
    ((x : Plane) : Sphere) ∈ interiorRegion P ↔ x ∈ interior (u4h_regionOf P) := by
  rw [u9h_interiorRegion_eq hn P hP]
  constructor
  · rintro ⟨y, hy, hxy⟩; rwa [← OnePoint.coe_injective hxy]
  · intro h; exact ⟨x, h, rfl⟩

/-! #### U9 helpers, block C (continued): the exterior region and the plane traces of the closed regions -/

theorem u9h_infty_mem_sphereComplement (P : LabelledTuple n) : ∞ ∈ sphereComplement P := by
  rintro ⟨x, -, hx⟩; exact OnePoint.coe_ne_infty x hx

theorem u9h_coe_mem_sphereComplement_iff (P : LabelledTuple n) (x : Plane) :
    ((x : Plane) : Sphere) ∈ sphereComplement P ↔ x ∉ embeddedPolygonImage P := by
  constructor
  · intro h hx; exact h ⟨x, hx, rfl⟩
  · rintro h ⟨y, hy, hxy⟩; exact h (OnePoint.coe_injective hxy ▸ hy)

theorem u9h_exteriorRegion_eq_diff (P : LabelledTuple n) :
    exteriorRegion P = sphereComplement P \ interiorRegion P := by
  unfold interiorRegion
  exact (sdiff_sdiff_cancel_left (connectedComponentIn_subset (sphereComplement P) ∞)).symm

/-- The exterior region is the coercion image of the complement of the canonical region, with `∞`. -/
theorem u9h_exteriorRegion_eq [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    exteriorRegion P = ((↑) : Plane → Sphere) '' (u4h_regionOf P)ᶜ ∪ {∞} := by
  obtain ⟨hfrU, hUc, -, -⟩ := u4h_regionOf_spec hn P hP
  have hUcl : IsClosed (u4h_regionOf P) := hUc.isClosed
  rw [u9h_exteriorRegion_eq_diff]
  ext z
  induction z using OnePoint.rec with
  | infty =>
    simp only [mem_sdiff, mem_union, mem_singleton_iff, or_true, iff_true]
    refine ⟨u9h_infty_mem_sphereComplement P, ?_⟩
    rw [u9h_interiorRegion_eq hn P hP]
    rintro ⟨x, -, hx⟩; exact OnePoint.coe_ne_infty x hx
  | coe x =>
    simp only [mem_sdiff, mem_union, mem_singleton_iff, OnePoint.coe_ne_infty, or_false,
      u9h_coe_mem_sphereComplement_iff, u9h_coe_mem_interiorRegion_iff hn P hP]
    constructor
    · rintro ⟨hC, hi⟩
      refine ⟨x, fun hxU => ?_, rfl⟩
      rw [← hUcl.closure_eq, closure_eq_interior_union_frontier, hfrU] at hxU
      rcases hxU with h | h
      · exact hi h
      · exact hC h
    · rintro ⟨y, hy, hxy⟩
      rw [OnePoint.coe_injective hxy] at hy
      exact ⟨fun hC => hy (hUcl.frontier_subset (hfrU ▸ hC)), fun hi => hy (interior_subset hi)⟩

theorem u9h_preimage_closure_image (S : Set Plane) :
    ((↑) : Plane → Sphere) ⁻¹' closure (((↑) : Plane → Sphere) '' S) = closure S :=
  (OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image S).symm

/-- The plane trace of the closed interior region is the canonical region. -/
theorem u9h_trace_inner [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ((↑) : Plane → Sphere) ⁻¹' closure (regionOf P Side.inner) = u4h_regionOf P := by
  obtain ⟨K, -, -, -, -⟩ := u4h_U4_exists_triangulation hn P hP
  show ((↑) : Plane → Sphere) ⁻¹' closure (interiorRegion P) = u4h_regionOf P
  rw [u9h_interiorRegion_eq hn P hP, u9h_preimage_closure_image,
    u4h_triangulation_closure_interior K]

/-- The plane trace of the closed exterior region is the complement of the open canonical region. -/
theorem u9h_trace_outer [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) :
    ((↑) : Plane → Sphere) ⁻¹' closure (regionOf P Side.outer) = (interior (u4h_regionOf P))ᶜ := by
  show ((↑) : Plane → Sphere) ⁻¹' closure (exteriorRegion P) = (interior (u4h_regionOf P))ᶜ
  rw [u9h_exteriorRegion_eq hn P hP, closure_union, closure_singleton, preimage_union,
    u9h_preimage_closure_image, closure_compl]
  have : ((↑) : Plane → Sphere) ⁻¹' ({∞} : Set Sphere) = ∅ := by
    ext x; simp
  rw [this, union_empty]

/-- The plane trace of either closed region, by side. -/
def u9h_trace [NeZero n] (P : LabelledTuple n) : Side → Set Plane
  | .inner => u4h_regionOf P
  | .outer => (interior (u4h_regionOf P))ᶜ

theorem u9h_preimage_closure_regionOf [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) : ((↑) : Plane → Sphere) ⁻¹' closure (regionOf P s) = u9h_trace P s := by
  cases s
  · exact u9h_trace_inner hn P hP
  · exact u9h_trace_outer hn P hP

theorem u9h_coe_mem_closure_regionOf_iff [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (s : Side) (x : Plane) :
    ((x : Plane) : Sphere) ∈ closure (regionOf P s) ↔ x ∈ u9h_trace P s := by
  rw [← mem_preimage, u9h_preimage_closure_regionOf hn P hP s]

/-- The circle lies in the trace of either closed region. -/
theorem u9h_polygonImage_subset_trace [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) : embeddedPolygonImage P ⊆ u9h_trace P s := by
  obtain ⟨hfrU, hUc, -, -⟩ := u4h_regionOf_spec hn P hP
  intro x hx
  rw [← hfrU] at hx
  cases s
  · exact hUc.isClosed.frontier_subset hx
  · exact hx.2

/-- The circle lies in the closure of either region. -/
theorem u9h_circle_subset_closure [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) : sphereCircle P ⊆ closure (regionOf P s) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [u9h_coe_mem_closure_regionOf_iff hn P hP s]
  exact u9h_polygonImage_subset_trace hn P hP s hx

theorem u9h_coe_traversal_mem_circle [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    ((traversal P x : Plane) : Sphere) ∈ sphereCircle P :=
  ⟨traversal P x, by rw [← U4_range_traversal P]; exact mem_range_self x, rfl⟩

/-! #### U9 helpers, block D: the face of a region at an edge -/

/-- Equal segments have the same endpoints (up to order). -/
theorem u9h_segment_eq_iff {a b c d : Plane} (h : segment ℝ a b = segment ℝ c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  have hc : c ∈ segment ℝ a b := h.symm ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h.symm ▸ right_mem_segment ℝ c d
  rw [segment_eq_image'] at ha hb hc hd
  obtain ⟨α, ⟨hα0, hα1⟩, hα⟩ := ha
  obtain ⟨β, ⟨hβ0, hβ1⟩, hβ⟩ := hb
  obtain ⟨γ, ⟨hγ0, hγ1⟩, hγ⟩ := hc
  obtain ⟨γ', ⟨hγ'0, hγ'1⟩, hγ'⟩ := hd
  simp only [] at hα hβ hγ hγ'
  by_cases hcd : d - c = 0
  · have hdc : d = c := sub_eq_zero.mp hcd
    rw [hcd, smul_zero, add_zero] at hα hβ
    exact Or.inl ⟨hα.symm, by rw [← hβ, hdc]⟩
  have e1 : (α + γ * (β - α)) • (d - c) = 0 := by
    have : (α + γ * (β - α)) • (d - c) = (a + γ • (b - a)) - c := by
      rw [← hα, ← hβ]; module
    rw [this, hγ, sub_self]
  have e2 : (α + γ' * (β - α)) • (d - c) = (1:ℝ) • (d - c) := by
    have : (α + γ' * (β - α)) • (d - c) = (a + γ' • (b - a)) - c := by
      rw [← hα, ← hβ]; module
    rw [this, hγ', one_smul]
  have h1 : α + γ * (β - α) = 0 := (smul_eq_zero.mp e1).resolve_right hcd
  have h2 : α + γ' * (β - α) = 1 := smul_left_injective ℝ hcd e2
  rcases le_or_gt α β with hab | hab
  · have hα' : α = 0 := by nlinarith
    have hβ' : β = 1 := by nlinarith
    left
    rw [hα', zero_smul, add_zero] at hα
    rw [hβ', one_smul, add_sub_cancel] at hβ
    exact ⟨hα.symm, hβ.symm⟩
  · have hα' : α = 1 := by nlinarith
    have hβ' : β = 0 := by nlinarith
    right
    rw [hα', one_smul, add_sub_cancel] at hα
    rw [hβ', zero_smul, add_zero] at hβ
    exact ⟨hα.symm, hβ.symm⟩

theorem u9h_fin3_cases (j k : Fin 3) : j = k ∨ j = k + 1 ∨ j = k + 2 := by revert j k; decide

theorem u9h_range_v (T : Triangle) (k : Fin 3) :
    range T.v = {T.v k, T.v (k + 1), T.v (k + 2)} := by
  ext x
  simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    rcases u9h_fin3_cases j k with h | h | h <;> rw [h] <;> tauto
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

/-- The carrier of a triangle whose edge `k` is the segment `[p, q]`. -/
theorem u9h_carrier_eq_of_edgeSeg (T : Triangle) (k : Fin 3) {p q : Plane}
    (h : T.edgeSeg k = segment ℝ p q) : T.carrier = convexHull ℝ {p, q, T.v (k + 2)} := by
  unfold Triangle.carrier
  rw [u9h_range_v T k]
  have e : ({T.v k, T.v (k + 1), T.v (k + 2)} : Set Plane) = {T.v k, T.v (k + 1)} ∪ {T.v (k + 2)} := by
    ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]; tauto
  have e' : ({p, q, T.v (k + 2)} : Set Plane) = {p, q} ∪ {T.v (k + 2)} := by
    ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]; tauto
  have h' : segment ℝ (T.v k) (T.v (k + 1)) = segment ℝ p q := h
  rw [e, e', ← convexHull_convexHull_union_left, convexHull_pair, h', ← convexHull_pair,
    convexHull_convexHull_union_left]

/-- The face of a region at edge `i`: its carrier is the hull of the edge and an apex on the
`σ`-side of the edge, and its vertex set is the edge's endpoints with the apex. -/
theorem u9h_edge_face {P : LabelledTuple n} (R : u4h_Region P) (i : ZMod n) :
    ∃ T ∈ R.K.faces, ∃ a : Plane, T.carrier = convexHull ℝ {P i, P (i + 1), a} ∧
      range T.v = {P i, P (i + 1), a} ∧ 0 < R.σ * det (P (i + 1) - P i) (a - P i) := by
  obtain ⟨T, hT, k, hk⟩ := R.edge_face i
  have hside := R.side i T hT k hk
  rw [u4h_edgeSegment_eq_segment] at hk
  refine ⟨T, hT, T.v (k + 2), u9h_carrier_eq_of_edgeSeg T k hk, ?_, hside⟩
  rw [u9h_range_v T k]
  rcases u9h_segment_eq_iff hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; ext x; simp only [mem_insert_iff, mem_singleton_iff]; tauto

/-! #### U9 helpers, block D (continued): local structure of a triangle at an edge midpoint -/

theorem u9h_det_mid_apex_q (p q a : Plane) :
    det (a - q) ((1/2:ℝ) • (p + q) - q) = (1/2) * det (q - p) (a - p) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem u9h_det_mid_apex_p (p q a : Plane) :
    det (a - p) ((1/2:ℝ) • (p + q) - p) = -((1/2) * det (q - p) (a - p)) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem u9h_det_edge_mid (p q x : Plane) :
    det (q - p) (x - p) = det (q - p) (x - (1/2:ℝ) • (p + q)) := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]; ring

theorem u9h_det_edge_swap (p q x : Plane) : det (p - q) (x - q) = -det (q - p) (x - p) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

theorem u9h_mid_mem_segment (p q : Plane) : (1/2:ℝ) • (p + q) ∈ segment ℝ p q :=
  ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by rw [smul_add]⟩

theorem u9h_mid_mem_hull3 (p q a : Plane) : (1/2:ℝ) • (p + q) ∈ convexHull ℝ {p, q, a} :=
  segment_subset_convexHull (mem_insert _ _) (mem_insert_of_mem _ (mem_insert _ _))
    (u9h_mid_mem_segment p q)

theorem u9h_hull3_comm (p q a : Plane) : convexHull ℝ {p, q, a} = convexHull ℝ {q, p, a} := by
  rw [Set.insert_comm]

/-- Near the midpoint of the edge `[p, q]` of the positive triangle `(p, q, a)`, the points strictly
on the side of `a` are interior. -/
theorem u9h_hull3_local_interior {p q a : Plane} (hD : 0 < det (q - p) (a - p)) :
    ∃ ρ > 0, ∀ x, dist x ((1/2:ℝ) • (p + q)) < ρ → 0 < det (q - p) (x - p) →
      x ∈ interior (convexHull ℝ {p, q, a}) := by
  have hO : IsOpen ({x | 0 < det (a - q) (x - q)} ∩ {x | 0 < det (p - a) (x - a)}) :=
    (u1h_isOpen_det_pos _ _).inter (u1h_isOpen_det_pos _ _)
  have hm : (1/2:ℝ) • (p + q) ∈ {x | 0 < det (a - q) (x - q)} ∩ {x | 0 < det (p - a) (x - a)} := by
    refine ⟨?_, ?_⟩ <;> simp only [mem_ofPred_eq]
    · rw [u9h_det_mid_apex_q]; positivity
    · have e : det (p - a) ((1/2:ℝ) • (p + q) - a) = (1/2) * det (q - p) (a - p) := by
        simp only [det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hO _ hm
  refine ⟨ρ, hρ, fun x hx hpos => ?_⟩
  have hx' := hball hx
  simp only [mem_inter_iff, mem_ofPred_eq] at hx'
  rw [u4h_interior_hull3 hD]
  exact ⟨hpos, hx'.1, hx'.2⟩

/-- Both sides of the edge `[p, q]` of the triangle `(p, q, a)` with `a` on the `σ`-side: the
triangle lies in the closed `σ`-half-plane, and near the midpoint the open `σ`-half-plane is interior. -/
theorem u9h_hull3_side {p q a : Plane} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hD : 0 < σ * det (q - p) (a - p)) :
    (∀ x ∈ convexHull ℝ {p, q, a}, 0 ≤ σ * det (q - p) (x - p)) ∧
    ∃ ρ > 0, ∀ x, dist x ((1/2:ℝ) • (p + q)) < ρ → 0 < σ * det (q - p) (x - p) →
      x ∈ interior (convexHull ℝ {p, q, a}) := by
  rcases hσ with rfl | rfl
  · rw [one_mul] at hD
    simp only [one_mul]
    exact ⟨fun x hx => ((u4h_mem_hull3_iff_det hD x).1 hx).1, u9h_hull3_local_interior hD⟩
  · have hD' : 0 < det (p - q) (a - q) := by rw [u9h_det_edge_swap]; linarith
    rw [u9h_hull3_comm]
    simp only [neg_one_mul, ← u9h_det_edge_swap, add_comm p q]
    exact ⟨fun x hx => ((u4h_mem_hull3_iff_det hD' x).1 hx).1, u9h_hull3_local_interior hD'⟩

/-- Near the midpoint of edge `i`, the region is the face at that edge. -/
theorem u9h_local_face {P : LabelledTuple n} (R : u4h_Region P) (i : ZMod n) {T : Triangle}
    (hT : T ∈ R.K.faces) {a : Plane} (hTc : T.carrier = convexHull ℝ {P i, P (i + 1), a})
    (hTv : range T.v = {P i, P (i + 1), a}) (hD : det (P (i + 1) - P i) (a - P i) ≠ 0) :
    ∃ ρ > 0, ∀ x, dist x ((1/2:ℝ) • (P i + P (i + 1))) < ρ → x ∈ R.U → x ∈ T.carrier := by
  set m : Plane := (1/2:ℝ) • (P i + P (i + 1)) with hm
  have hmT : m ∈ T.carrier := by rw [hTc]; exact u9h_mid_mem_hull3 _ _ _
  have hmU : m ∈ R.U := R.face_subset hT hmT
  have hedgeT : edgeSegment P i ⊆ T.carrier := by
    rw [hTc, u4h_edgeSegment_eq_segment]
    exact segment_subset_convexHull (mem_insert _ _) (mem_insert_of_mem _ (mem_insert _ _))
  obtain ⟨ε, hε, hloc⟩ := U2_local_structure R.K hmU
  refine ⟨ε, hε, fun x hx hxU => ?_⟩
  have hx' : x ∈ Metric.ball m ε ∩ R.U := ⟨hx, hxU⟩
  rw [hloc] at hx'
  obtain ⟨-, hx'⟩ := hx'
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop] at hx'
  obtain ⟨T', ⟨hT', hmT'⟩, hxT'⟩ := hx'
  -- the common face of `T` and `T'` contains `m`, hence both endpoints of the edge
  have hinter := R.K.inter T hT T' hT'
  have hmS : m ∈ convexHull ℝ (range T.v ∩ range T'.v) := hinter ▸ ⟨hmT, hmT'⟩
  have hp : P i ∈ range T'.v := by
    by_contra hp
    have hsub : range T.v ∩ range T'.v ⊆ {x | det (a - P (i + 1)) (x - P (i + 1)) = 0} := by
      rintro y ⟨hy1, hy2⟩
      rw [hTv] at hy1
      simp only [mem_insert_iff, mem_singleton_iff] at hy1
      simp only [mem_ofPred_eq]
      rcases hy1 with rfl | rfl | rfl
      · exact absurd hy2 hp
      · rw [sub_self]; simp [det]
      · exact u9h_det_self _
    have := convexHull_min hsub (u9h_convex_det_eq_zero _ _) hmS
    simp only [mem_ofPred_eq, hm, u9h_det_mid_apex_q] at this
    exact hD (by linarith)
  have hq : P (i + 1) ∈ range T'.v := by
    by_contra hq
    have hsub : range T.v ∩ range T'.v ⊆ {x | det (a - P i) (x - P i) = 0} := by
      rintro y ⟨hy1, hy2⟩
      rw [hTv] at hy1
      simp only [mem_insert_iff, mem_singleton_iff] at hy1
      simp only [mem_ofPred_eq]
      rcases hy1 with rfl | rfl | rfl
      · rw [sub_self]; simp [det]
      · exact absurd hy2 hq
      · exact u9h_det_self _
    have := convexHull_min hsub (u9h_convex_det_eq_zero _ _) hmS
    simp only [mem_ofPred_eq, hm, u9h_det_mid_apex_p] at this
    exact hD (by linarith)
  have hedgeT' : edgeSegment P i ⊆ T'.carrier := by
    rw [u4h_edgeSegment_eq_segment]
    exact segment_subset_convexHull hp hq
  rw [R.edge_unique i T hT T' hT' hedgeT hedgeT']
  exact hxT'

/-! #### U9 helpers, block D (end): the region and the traces near an edge midpoint -/

/-- The sign of the side of an edge on which region `s` lies: `σ` for the interior, `-σ` for
the exterior. -/
def u9h_sideSign {P : LabelledTuple n} (R : u4h_Region P) : Side → ℝ
  | .inner => R.σ
  | .outer => -R.σ

theorem u9h_sideSign_pm {P : LabelledTuple n} (R : u4h_Region P) (s : Side) :
    u9h_sideSign R s = 1 ∨ u9h_sideSign R s = -1 := by
  cases s
  · exact R.σ_pm
  · rcases R.σ_pm with h | h
    · right; show -R.σ = -1; rw [h]
    · left; show -R.σ = 1; rw [h, neg_neg]

theorem u9h_sigma_ne_zero {P : LabelledTuple n} (R : u4h_Region P) : R.σ ≠ 0 := by
  rcases R.σ_pm with h | h <;> rw [h] <;> norm_num

/-- Local structure of the region `R.U` at the midpoint of edge `i`: it lies in the closed
`σ`-half-plane of the edge, and the open `σ`-half-plane is interior near the midpoint. -/
theorem u9h_region_local {P : LabelledTuple n} (R : u4h_Region P) (i : ZMod n) :
    ∃ ρ > 0, (∀ x, dist x ((1/2:ℝ) • (P i + P (i + 1))) < ρ → x ∈ R.U →
        0 ≤ R.σ * det (P (i + 1) - P i) (x - (1/2:ℝ) • (P i + P (i + 1)))) ∧
      (∀ x, dist x ((1/2:ℝ) • (P i + P (i + 1))) < ρ →
        0 < R.σ * det (P (i + 1) - P i) (x - (1/2:ℝ) • (P i + P (i + 1))) → x ∈ interior R.U) := by
  obtain ⟨T, hT, a, hTc, hTv, hside⟩ := u9h_edge_face R i
  have hD : det (P (i + 1) - P i) (a - P i) ≠ 0 := by
    intro h; rw [h, mul_zero] at hside; exact lt_irrefl _ hside
  obtain ⟨hnonneg, ρ₁, hρ₁, hint⟩ := u9h_hull3_side R.σ_pm hside
  obtain ⟨ρ₂, hρ₂, hface⟩ := u9h_local_face R i hT hTc hTv hD
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun x hx hxU => ?_, fun x hx hpos => ?_⟩
  · have hxT : x ∈ T.carrier := hface x (hx.trans_le (min_le_right _ _)) hxU
    rw [hTc] at hxT
    rw [← u9h_det_edge_mid]
    exact hnonneg x hxT
  · rw [← u9h_det_edge_mid] at hpos
    have := hint x (hx.trans_le (min_le_left _ _)) hpos
    rw [← hTc] at this
    exact interior_mono (R.face_subset hT) this

/-- Local structure of the trace of the closed region `s` at the midpoint of edge `i`: it lies in
the closed half-plane on the `sideSign` side of the edge. -/
theorem u9h_trace_local [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) (s : Side) (i : ZMod n) :
    ∃ ρ > 0, ∀ x, dist x ((1/2:ℝ) • (P i + P (i + 1))) < ρ → x ∈ u9h_trace P s →
      0 ≤ u9h_sideSign R s * det (P (i + 1) - P i) (x - (1/2:ℝ) • (P i + P (i + 1))) := by
  obtain ⟨ρ, hρ, h1, h2⟩ := u9h_region_local R i
  have hU : R.U = u4h_regionOf P := u4h_region_U_eq_regionOf hn hP R
  refine ⟨ρ, hρ, fun x hx hxs => ?_⟩
  cases s
  · show 0 ≤ R.σ * _
    exact h1 x hx (hU ▸ hxs)
  · show 0 ≤ -R.σ * _
    by_contra hcon
    have hpos : 0 < R.σ * det (P (i + 1) - P i) (x - (1/2:ℝ) • (P i + P (i + 1))) := by linarith
    have := h2 x hx hpos
    rw [hU] at this
    exact hxs this

theorem u9h_dist_mid_add (m ν : Plane) {t : ℝ} (ht : 0 < t) : dist (m + t • ν) m = t * ‖ν‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]

/-- "Interior on the left of edge `i`" is exactly `σ = 1`. -/
theorem u9h_interiorOnLeft_iff_sigma [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) (i : ZMod n) : InteriorOnLeft P i ↔ R.σ = 1 := by
  have he : edge P i = P (i + 1) - P i := rfl
  have hne : P (i + 1) - P i ≠ 0 := he ▸ hP.edge_ne_zero i
  set ν : Plane := leftNormal (P (i + 1) - P i) with hν
  set m : Plane := (1/2:ℝ) • (P i + P (i + 1)) with hm
  have hdν : 0 < det (P (i + 1) - P i) ν := u9h_det_leftNormal_pos hne
  have hU : R.U = u4h_regionOf P := u4h_region_U_eq_regionOf hn hP R
  obtain ⟨ρ, hρ, h1, h2⟩ := u9h_region_local R i
  have hν1 : 0 < ‖ν‖ + 1 := by positivity
  have hdet : ∀ t : ℝ, det (P (i + 1) - P i) (m + t • ν - m) = t * det (P (i + 1) - P i) ν := by
    intro t; rw [add_sub_cancel_left, u9h_det_smul_right]
  unfold InteriorOnLeft
  rw [he]
  constructor
  · rintro ⟨ε, hε, hall⟩
    by_contra hσ
    have hσ' : R.σ = -1 := R.σ_pm.resolve_left hσ
    set t : ℝ := min (ε / 2) (ρ / (2 * (‖ν‖ + 1))) with ht
    have ht0 : 0 < t := lt_min (by positivity) (by positivity)
    have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
    have htρ : t * ‖ν‖ < ρ := by
      have h1' : t ≤ ρ / (2 * (‖ν‖ + 1)) := min_le_right _ _
      have h2' : t * ‖ν‖ ≤ t * (‖ν‖ + 1) := by nlinarith [norm_nonneg ν]
      have h3' : t * (‖ν‖ + 1) ≤ ρ / 2 := by
        calc t * (‖ν‖ + 1) ≤ ρ / (2 * (‖ν‖ + 1)) * (‖ν‖ + 1) := by nlinarith
          _ = ρ / 2 := by field_simp
      linarith
    have hmem := hall t ⟨ht0, htε⟩
    rw [u9h_coe_mem_interiorRegion_iff hn P hP, ← hU] at hmem
    have := h1 (m + t • ν) (by rw [u9h_dist_mid_add _ _ ht0]; exact htρ) (interior_subset hmem)
    rw [hdet, hσ'] at this
    nlinarith
  · intro hσ
    refine ⟨ρ / (‖ν‖ + 1), by positivity, fun t ht => ?_⟩
    obtain ⟨ht0, htε⟩ := ht
    have htρ : t * ‖ν‖ < ρ := by
      have : t * (‖ν‖ + 1) < ρ := by rwa [lt_div_iff₀ hν1] at htε
      nlinarith [norm_nonneg ν]
    rw [u9h_coe_mem_interiorRegion_iff hn P hP, ← hU]
    apply h2 (m + t • ν) (by rw [u9h_dist_mid_add _ _ ht0]; exact htρ)
    rw [hdet, hσ, one_mul]
    exact mul_pos ht0 hdν

/-! #### U9 helpers, block E: the side sign `σ` is the sign of the rotation number -/

/-- The lexicographically least vertex is a supporting vertex for `N = (1, 0)`. -/
theorem u9h_lexmin_supporting {P : LabelledTuple n} {v : ZMod n}
    (hv : ∀ k, k ≠ v → u4h_Lex (P v) (P k)) : IsSupportingVertex P (1, 0) v := by
  refine ⟨by simp, fun j => ?_⟩
  simp only [planeDot, Prod.fst_sub, Prod.snd_sub, one_mul, zero_mul, add_zero]
  by_cases hj : j = v
  · rw [hj]; simp
  · rcases hv j hj with h | ⟨h, -⟩
    · linarith
    · linarith

theorem u9h_turn_pos_iff {P : LabelledTuple n} (hreg : Regular P) (i : ZMod n) :
    0 < principalTurn P i ↔ 0 < det (edge P (i - 1)) (edge P i) := by
  have h := principalAngle_sign (hreg i)
  unfold principalTurn
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

theorem u9h_turn_neg_iff {P : LabelledTuple n} (hreg : Regular P) (i : ZMod n) :
    principalTurn P i < 0 ↔ det (edge P (i - 1)) (edge P i) < 0 := by
  have h := principalAngle_sign (hreg i)
  unfold principalTurn
  rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h]

/-- `σ = 1` iff the rotation number is positive (read at the lexicographically least vertex with
`cb_embedded_rotation.orientation`). -/
theorem u9h_sigma_eq_one_iff_rot [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) : R.σ = 1 ↔ 0 < rotationNumber P := by
  obtain ⟨v, hv⟩ := u4h_exists_lexmin hP
  have hturn := u4h_region_lexmin_turn hn hP R hv
  have he1 : edge P (v - 1) = P v - P (v - 1) := by
    show P (v - 1 + 1) - P (v - 1) = _; rw [sub_add_cancel]
  have he2 : edge P v = P (v + 1) - P v := rfl
  rw [← he1, ← he2] at hturn
  have hreg := hP.regular hn
  have hdata := cb_embedded_rotation hn P hreg hP
  have hor := hdata.orientation (1, 0) v (u9h_lexmin_supporting hv)
  constructor
  · intro hσ
    rw [hσ, one_mul] at hturn
    rw [hor.1 ((u9h_turn_pos_iff hreg v).2 hturn)]
    exact one_pos
  · intro hrot
    rcases R.σ_pm with hσ | hσ
    · exact hσ
    · exfalso
      rw [hσ] at hturn
      have hneg : det (edge P (v - 1)) (edge P v) < 0 := by linarith
      have := hor.2 ((u9h_turn_neg_iff hreg v).2 hneg)
      rw [this] at hrot
      norm_num at hrot

/-- The interior is on the left of edge `i` iff the rotation number is positive. -/
theorem u9h_interiorOnLeft_iff_rot [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (i : ZMod n) : InteriorOnLeft P i ↔ 0 < rotationNumber P := by
  obtain ⟨R⟩ := u4h_region_exists n hn P hP
  rw [u9h_interiorOnLeft_iff_sigma hn hP R i, u9h_sigma_eq_one_iff_rot hn hP R]

/-- `sideSign R s = 1` iff the traversal is positive for the side `s`. -/
theorem u9h_sideSign_eq_one_iff [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P)
    (R : u4h_Region P) (s : Side) : u9h_sideSign R s = 1 ↔ traversalPositiveFor P s := by
  have h := u9h_sigma_eq_one_iff_rot hn hP R
  unfold traversalPositiveFor
  cases s
  · show R.σ = 1 ↔ _
    simp only [iff_true]; exact h
  · show -R.σ = 1 ↔ _
    have : (Side.outer = Side.inner) ↔ False := ⟨fun h => Side.noConfusion h, False.elim⟩
    rw [this, iff_false, ← h]
    rcases R.σ_pm with hσ | hσ <;> rw [hσ] <;> norm_num

/-! #### U9 leaf-level: the first three leaves -/

theorem u9h_U9_interiorOnLeft_consistent [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i j : ZMod n) : InteriorOnLeft P i ↔ InteriorOnLeft P j := by
  rw [u9h_interiorOnLeft_iff_rot hn hP i, u9h_interiorOnLeft_iff_rot hn hP j]

theorem u9h_U9_interiorOnLeft_iff_turn [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {N : Plane} {i : ZMod n} (hs : IsSupportingVertex P N i) (ht : principalTurn P i ≠ 0) :
    InteriorOnLeft P i ↔ 0 < principalTurn P i := by
  rw [u9h_interiorOnLeft_iff_rot hn hP i]
  have hor := (cb_embedded_rotation hn P (hP.regular hn) hP).orientation N i hs
  constructor
  · intro hrot
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · rw [hor.2 hneg] at hrot; norm_num at hrot
    · exact hpos
  · intro hpos
    rw [hor.1 hpos]; exact one_pos

/-! #### U9 helpers, block F: the traversal read in the parametrisation `f`, and the triple domain -/

theorem u9h_continuousOn_of_isHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : ContinuousOn f S := by
  obtain ⟨e, he⟩ := h
  rw [continuousOn_iff_continuous_domRestrict]
  have : S.domRestrict f = fun x => (e x : β) := by funext x; exact (he x).symm
  rw [this]
  exact continuous_subtype_val.comp e.continuous

theorem u9h_isHomeoOnto_injOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : InjOn f S := by
  obtain ⟨e, he⟩ := h
  intro x hx y hy hxy
  have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (by rw [he, he]; exact hxy)
  exact congrArg Subtype.val (e.injective this)

theorem u9h_isHomeoOnto_mapsTo {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : MapsTo f S S' := by
  obtain ⟨e, he⟩ := h
  intro x hx
  rw [← he ⟨x, hx⟩]
  exact (e ⟨x, hx⟩).2

/-- The traversal of `P` read in `f`. -/
noncomputable def u9h_F (P : LabelledTuple n) (f : Sphere → Plane) (t : ℝ) : Plane :=
  f ((traversal P t : Plane) : Sphere)

theorem u9h_F_continuous [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (s : Side)
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f) :
    Continuous (u9h_F P f) :=
  (u9h_continuousOn_of_isHomeoOnto hf).comp_continuous
    (OnePoint.continuous_coe.comp (continuous_traversal P))
    (fun t => u9h_circle_subset_closure hn P hP s (u9h_coe_traversal_mem_circle P t))

theorem u9h_F_mem_frontier [NeZero n] (P : LabelledTuple n) {D : Set Plane} {f : Sphere → Plane}
    (hB : f '' sphereCircle P = frontier D) (t : ℝ) : u9h_F P f t ∈ frontier D :=
  hB ▸ mem_image_of_mem f (u9h_coe_traversal_mem_circle P t)

/-- Distinct parameters of one period give distinct traversal points. -/
theorem u9h_traversal_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P) {x y : ℝ}
    (hxy : x < y) (hyx : y < x + n) : traversal P x ≠ traversal P y := by
  intro h
  obtain ⟨m, hm⟩ := hP.traversal_injective hn h
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : (0:ℝ) < m * n := by linarith
  have h2 : (m:ℝ) * n < 1 * n := by linarith
  have hm0 : (0:ℝ) < m := pos_of_mul_pos_left h1 hn0.le
  have hm1 : (m:ℝ) < 1 := lt_of_mul_lt_mul_right h2 hn0.le
  have hm0' : (0:ℤ) < m := by exact_mod_cast hm0
  have hm1' : m < (1:ℤ) := by exact_mod_cast hm1
  omega

theorem u9h_F_ne [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (s : Side)
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f) {x y : ℝ}
    (hxy : x < y) (hyx : y < x + n) : u9h_F P f x ≠ u9h_F P f y := by
  intro h
  have hinj := u9h_isHomeoOnto_injOn hf
  have hx := u9h_circle_subset_closure hn P hP s (u9h_coe_traversal_mem_circle P x)
  have hy := u9h_circle_subset_closure hn P hP s (u9h_coe_traversal_mem_circle P y)
  have := OnePoint.coe_injective (hinj hx hy h)
  exact u9h_traversal_ne hn hP hxy hyx this

/-- The domain of increasing triples in one period. -/
def u9h_Ω (n : ℕ) : Set (ℝ × ℝ × ℝ) := {q | q.1 < q.2.1 ∧ q.2.1 < q.2.2 ∧ q.2.2 < q.1 + n}

theorem u9h_convex_combo_lt {a b c d s t : ℝ} (hab : a < b) (hcd : c < d) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) : s * a + t * c < s * b + t * d := by
  rcases hs.lt_or_eq with hs' | hs'
  · nlinarith [mul_le_mul_of_nonneg_left hcd.le ht]
  · rw [← hs'] at hst ⊢
    rw [zero_add] at hst
    rw [hst]; linarith

theorem u9h_Ω_convex (n : ℕ) : Convex ℝ (u9h_Ω n) := by
  intro q hq r hr s t hs ht hst
  simp only [u9h_Ω, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hq hr ⊢
  obtain ⟨hq1, hq2, hq3⟩ := hq
  obtain ⟨hr1, hr2, hr3⟩ := hr
  refine ⟨u9h_convex_combo_lt hq1 hr1 hs ht hst, u9h_convex_combo_lt hq2 hr2 hs ht hst, ?_⟩
  have := u9h_convex_combo_lt hq3 hr3 hs ht hst
  have e : s * (q.1 + n) + t * (r.1 + n) = s * q.1 + t * r.1 + n := by
    rw [mul_add, mul_add]; linear_combination (n:ℝ) * hst
  linarith

theorem u9h_Ω_preconnected (n : ℕ) : IsPreconnected (u9h_Ω n) := (u9h_Ω_convex n).isPreconnected

/-- Dichotomy: an injective (per period) continuous loop on the frontier of a convex disc either
carries every increasing triple to positive cyclic order, or none. -/
theorem u9h_cyclic_dichotomy {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {F : ℝ → Plane} (hF : Continuous F) (hfr : ∀ t, F t ∈ frontier D)
    (hinj : ∀ x y : ℝ, x < y → y < x + n → F x ≠ F y) :
    (∀ x y w : ℝ, x < y → y < w → w < x + n → CyclicPos z (F x) (F y) (F w)) ∨
    (∀ x y w : ℝ, x < y → y < w → w < x + n → ¬ CyclicPos z (F x) (F y) (F w)) := by
  set S₁ : Set (ℝ × ℝ × ℝ) := {q | CyclicPos z (F q.1) (F q.2.1) (F q.2.2)} with hS₁
  set S₂ : Set (ℝ × ℝ × ℝ) := {q | CyclicPos z (F q.1) (F q.2.2) (F q.2.1)} with hS₂
  have c1 : Continuous fun q : ℝ × ℝ × ℝ => F q.1 := hF.comp continuous_fst
  have c2 : Continuous fun q : ℝ × ℝ × ℝ => F q.2.1 := hF.comp (continuous_fst.comp continuous_snd)
  have c3 : Continuous fun q : ℝ × ℝ × ℝ => F q.2.2 := hF.comp (continuous_snd.comp continuous_snd)
  have hS₁o : IsOpen S₁ := u9h_isOpen_cyclicPos z c1 c2 c3
  have hS₂o : IsOpen S₂ := u9h_isOpen_cyclicPos z c1 c3 c2
  have hdisj : Disjoint S₁ S₂ := Set.disjoint_left.mpr fun q h1 h2 => u9h_cyclicPos_antisymm h1 h2
  have hsub : u9h_Ω n ⊆ S₁ ∪ S₂ := by
    rintro ⟨x, y, w⟩ ⟨hxy, hyw, hwx⟩
    simp only at hxy hyw hwx
    have hxn : (x:ℝ) < x + n := by linarith
    exact u9h_cyclicPos_total hD hz (hfr x) (hfr y) (hfr w) (hinj x y hxy (by linarith))
      (hinj y w hyw (by linarith)) (hinj x w (hxy.trans hyw) hwx)
  rcases (u9h_Ω_preconnected n).subset_or_subset hS₁o hS₂o hdisj hsub with h | h
  · exact Or.inl fun x y w hxy hyw hwx => h (show (x, y, w) ∈ u9h_Ω n from ⟨hxy, hyw, hwx⟩)
  · exact Or.inr fun x y w hxy hyw hwx hc =>
      u9h_cyclicPos_antisymm hc (h (show (x, y, w) ∈ u9h_Ω n from ⟨hxy, hyw, hwx⟩))

/-! #### U9 helpers, block F (continued): faces of a triangulation along a segment -/

/-- A short initial piece of a segment inside `X` lies in one face of `K`. -/
theorem u9h_face_along {X : Set Plane} (K : Triangulation X) {x₀ u : Plane} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hseg : ∀ s ∈ Icc (0:ℝ) δ₀, x₀ + s • u ∈ X) :
    ∃ T ∈ K.faces, ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ s ∈ Icc (0:ℝ) δ, x₀ + s • u ∈ T.carrier := by
  have hx₀ : x₀ ∈ X := by have := hseg 0 ⟨le_rfl, hδ₀.le⟩; rwa [zero_smul, add_zero] at this
  obtain ⟨ε, hε, hloc⟩ := U2_local_structure K hx₀
  have hu1 : 0 < ‖u‖ + 1 := by positivity
  set δ : ℝ := min δ₀ (ε / (2 * (‖u‖ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min hδ₀ (by positivity)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hy : x₀ + δ • u ∈ Metric.ball x₀ ε ∩ X := by
    refine ⟨?_, hseg δ ⟨hδ0.le, hδδ₀⟩⟩
    rw [Metric.mem_ball, u9h_dist_mid_add _ _ hδ0]
    have h1 : δ ≤ ε / (2 * (‖u‖ + 1)) := min_le_right _ _
    have h2 : δ * ‖u‖ ≤ δ * (‖u‖ + 1) := by nlinarith [norm_nonneg u]
    have h3 : δ * (‖u‖ + 1) ≤ ε / 2 := by
      calc δ * (‖u‖ + 1) ≤ ε / (2 * (‖u‖ + 1)) * (‖u‖ + 1) := by nlinarith
        _ = ε / 2 := by field_simp
    linarith
  rw [hloc] at hy
  obtain ⟨-, hy⟩ := hy
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop] at hy
  obtain ⟨T, ⟨hT, hx₀T⟩, hyT⟩ := hy
  refine ⟨T, hT, δ, hδ0, hδδ₀, fun s hs => ?_⟩
  have hmem : x₀ + s • u ∈ segment ℝ x₀ (x₀ + δ • u) := by
    rw [segment_eq_image']
    refine ⟨s / δ, ⟨div_nonneg hs.1 hδ0.le, (div_le_one hδ0).mpr hs.2⟩, ?_⟩
    simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hδ0.ne']
  exact (U1_triangle_convex T).segment_subset hx₀T hyT hmem

/-- The linear part of a positive affine map on a triangle has positive determinant. -/
theorem u9h_affine_det_pos {g : Plane → Plane} {T : Triangle} (h : IsPositiveAffineOn g T)
    {M : Plane →ₗ[ℝ] Plane} {b : Plane} (hM : ∀ x ∈ T.carrier, g x = M x + b) :
    0 < det (M (1, 0)) (M (0, 1)) := by
  have hv : ∀ j : Fin 3, T.v j ∈ T.carrier := fun j => subset_convexHull ℝ _ (mem_range_self j)
  have h2 := h.2
  rw [hM _ (hv 1), hM _ (hv 0), hM _ (hv 2)] at h2
  have e1 : M (T.v 1) + b - (M (T.v 0) + b) = M (T.v 1 - T.v 0) := by rw [map_sub]; abel
  have e2 : M (T.v 2) + b - (M (T.v 0) + b) = M (T.v 2 - T.v 0) := by rw [map_sub]; abel
  rw [e1, e2, u1h_det_linear] at h2
  exact (mul_pos_iff_of_pos_right T.pos).mp h2

/-- A convex subset of `X` through `m` lies in the closed half-plane that `X` occupies near `m`. -/
theorem u9h_convex_local_halfplane {T X : Set Plane} (hT : Convex ℝ T) (hTX : T ⊆ X) {m e : Plane}
    (hm : m ∈ T) {σ ρ : ℝ} (hρ : 0 < ρ)
    (hloc : ∀ x, dist x m < ρ → x ∈ X → 0 ≤ σ * det e (x - m)) :
    ∀ x ∈ T, 0 ≤ σ * det e (x - m) := by
  intro x hx
  by_contra hneg
  rw [not_le] at hneg
  have hxm1 : 0 < ‖x - m‖ + 1 := by positivity
  set lam : ℝ := min 1 (ρ / (2 * (‖x - m‖ + 1))) with hlam
  have hl0 : 0 < lam := lt_min one_pos (by positivity)
  have hl1 : lam ≤ 1 := min_le_left _ _
  have hyT : m + lam • (x - m) ∈ T := hT.add_smul_sub_mem hm hx ⟨hl0.le, hl1⟩
  have hdist : dist (m + lam • (x - m)) m < ρ := by
    rw [u9h_dist_mid_add _ _ hl0]
    have h1 : lam ≤ ρ / (2 * (‖x - m‖ + 1)) := min_le_right _ _
    have h2 : lam * ‖x - m‖ ≤ lam * (‖x - m‖ + 1) := by nlinarith [norm_nonneg (x - m)]
    have h3 : lam * (‖x - m‖ + 1) ≤ ρ / 2 := by
      calc lam * (‖x - m‖ + 1) ≤ ρ / (2 * (‖x - m‖ + 1)) * (‖x - m‖ + 1) := by nlinarith
        _ = ρ / 2 := by field_simp
    linarith
  have := hloc _ hdist (hTX hyT)
  rw [add_sub_cancel_left, u9h_det_smul_right] at this
  nlinarith

/-- A nondegenerate triangle has a vertex off any given line through `m` with direction `e ≠ 0`. -/
theorem u9h_exists_vertex_off_line (T : Triangle) {e m : Plane} (he : e ≠ 0) :
    ∃ j : Fin 3, det e (T.v j - m) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨μ0, h0⟩ := u9h_parallel_of_det_eq_zero he (h 0)
  obtain ⟨μ1, h1⟩ := u9h_parallel_of_det_eq_zero he (h 1)
  obtain ⟨μ2, h2⟩ := u9h_parallel_of_det_eq_zero he (h 2)
  have hpos := T.pos
  have e1 : T.v 1 - T.v 0 = (μ1 - μ0) • e := by
    rw [sub_smul, ← h1, ← h0]; abel
  have e2 : T.v 2 - T.v 0 = (μ2 - μ0) • e := by
    rw [sub_smul, ← h2, ← h0]; abel
  rw [e1, e2, u9h_det_smul_left, u9h_det_smul_right, u9h_det_self, mul_zero, mul_zero] at hpos
  exact lt_irrefl _ hpos

/-! #### U9 helpers, block F (continued): the traversal near the midpoint of edge `0` -/

theorem u9h_traversal_half [NeZero n] (P : LabelledTuple n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) :
    traversal P (1/2 + s) = (1/2:ℝ) • (P 0 + P (0 + 1)) + s • (P (0 + 1) - P 0) := by
  have h := traversal_int_add P 0 (t := 1/2 + s) (by linarith) (by linarith)
  simp only [Int.cast_zero, zero_add] at h
  rw [h]
  show P 0 + (1/2 + s) • (P (0 + 1) - P 0) = _
  module

theorem u9h_edge_point_mem_chartPart [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) {L : ℝ} (hL : InsideModel L P) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    (1/2:ℝ) • (P 0 + P (0 + 1)) + t • (P (0 + 1) - P 0) ∈
      chartPart L false (closure (regionOf P s)) := by
  rw [← u9h_traversal_half P ht0 ht1]
  refine ⟨?_, ?_⟩
  · show supNorm (traversal P (1/2 + t)) ≤ L
    have hC : traversal P (1/2 + t) ∈ embeddedPolygonImage P := by
      rw [← U4_range_traversal P]; exact mem_range_self _
    have := interior_subset ((U4_polygonImage_subset_interior_square P hL).1 hC)
    exact this
  · show ((traversal P (1/2 + t) : Plane) : Sphere) ∈ closure (regionOf P s)
    exact u9h_circle_subset_closure hn P hP s (u9h_coe_traversal_mem_circle P _)

theorem u9h_mem_trace_of_mem_chartPart [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) {L : ℝ} {x : Plane} (hx : x ∈ chartPart L false (closure (regionOf P s))) :
    x ∈ u9h_trace P s := by
  have h2 : ((x : Plane) : Sphere) ∈ closure (regionOf P s) := hx.2
  rwa [u9h_coe_mem_closure_regionOf_iff hn P hP s] at h2

theorem u9h_F_half [NeZero n] (P : LabelledTuple n) (f : Sphere → Plane) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1/2) :
    u9h_F P f (1/2 + s) =
      f ((((1/2:ℝ) • (P 0 + P (0 + 1)) + s • (P (0 + 1) - P 0) : Plane)) : Sphere) := by
  unfold u9h_F; rw [u9h_traversal_half P hs0 hs1]

/-! #### U9 helpers, block F (continued): local evaluation of the cyclic order at edge `0` -/

theorem u9h_det_sub_comm (a z v : Plane) : det (a - z) v = det v (z - a) := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

/-- Local evaluation: the three collinear traversal points `γ(½), γ(½ + δ/2), γ(½ + δ)` read in `f`
are in positive cyclic order around `z` iff region `s` lies on the left of edge `0`. -/
theorem u9h_local_eval [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (R : u4h_Region P) (s : Side) {L : ℝ} (hL : InsideModel L P) {D : Set Plane}
    {f : Sphere → Plane} (hD : Link.IsDisc D) (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hB : f '' sphereCircle P = frontier D) (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    {z : Plane} (hz : z ∈ interior D) :
    ∃ x y w : ℝ, x < y ∧ y < w ∧ w < x + n ∧
      (u9h_sideSign R s = 1 → CyclicPos z (u9h_F P f x) (u9h_F P f y) (u9h_F P f w)) ∧
      (u9h_sideSign R s = -1 → ¬ CyclicPos z (u9h_F P f x) (u9h_F P f y) (u9h_F P f w)) := by
  set p : Plane := P 0 with hp
  set q : Plane := P (0 + 1) with hq
  set e : Plane := q - p with he
  set m : Plane := (1/2:ℝ) • (p + q) with hm
  set σ' : ℝ := u9h_sideSign R s with hσ'
  have hσpm : σ' = 1 ∨ σ' = -1 := u9h_sideSign_pm R s
  have he0 : e ≠ 0 := hP.edge_ne_zero 0
  -- the plane-chart triangulation and the local half-plane of the trace
  obtain ⟨K, hK⟩ := hpl false
  obtain ⟨ρ, hρ, hloc⟩ := u9h_trace_local hn hP R s 0
  have hlocX : ∀ x, dist x m < ρ → x ∈ chartPart L false (closure (regionOf P s)) →
      0 ≤ σ' * det e (x - m) := fun x hx hxX =>
    hloc x hx (u9h_mem_trace_of_mem_chartPart hn P hP s hxX)
  -- a face containing an initial piece of the edge from `m`
  have hseg : ∀ t ∈ Icc (0:ℝ) (1/2), m + t • e ∈ chartPart L false (closure (regionOf P s)) :=
    fun t ht => u9h_edge_point_mem_chartPart hn P hP s hL ht.1 ht.2
  obtain ⟨T, hT, δ, hδ0, hδ1, hTseg⟩ := u9h_face_along K (by norm_num : (0:ℝ) < 1/2) hseg
  have hmT : m ∈ T.carrier := by
    have := hTseg 0 ⟨le_rfl, hδ0.le⟩; rwa [zero_smul, add_zero] at this
  -- `f ∘ coe` is affine on `T`
  have hTaff := hK T hT
  obtain ⟨M, b, hMb⟩ := hTaff.1
  have hMb' : ∀ x ∈ T.carrier, f (x : Sphere) = M x + b := hMb
  have hdetM : 0 < det (M (1, 0)) (M (0, 1)) := u9h_affine_det_pos hTaff hMb
  -- the image points on the edge
  set a : Plane := f (m : Sphere) with ha
  have haM : a = M m + b := hMb' m hmT
  have hFt : ∀ t ∈ Icc (0:ℝ) δ, u9h_F P f (1/2 + t) = a + t • M e := by
    intro t ht
    rw [u9h_F_half P f ht.1 (ht.2.trans hδ1), hMb' _ (hTseg t ht), M.map_add m (t • e),
      M.map_smul t e, haM]
    abel
  have hF0 : u9h_F P f (1/2) = a := by
    have := hFt 0 ⟨le_rfl, hδ0.le⟩; rwa [add_zero, zero_smul, add_zero] at this
  have hfr' : ∀ t ∈ Icc (0:ℝ) δ, a + t • M e ∈ frontier D := fun t ht =>
    hFt t ht ▸ u9h_F_mem_frontier P hB _
  -- `T` lies in the closed `σ'`-half-plane and has a vertex strictly inside it
  have hTX : T.carrier ⊆ chartPart L false (closure (regionOf P s)) := u4h_carrier_subset K hT
  have hThalf : ∀ x ∈ T.carrier, 0 ≤ σ' * det e (x - m) :=
    u9h_convex_local_halfplane (U1_triangle_convex T) hTX hmT hρ hlocX
  obtain ⟨j, hj⟩ := u9h_exists_vertex_off_line T (m := m) he0
  have hvj : T.v j ∈ T.carrier := subset_convexHull ℝ _ (mem_range_self j)
  have hvpos : 0 < σ' * det e (T.v j - m) := by
    refine lt_of_le_of_ne (hThalf _ hvj) fun h => hj ?_
    rcases hσpm with h' | h' <;> rw [h'] at h <;> linarith
  -- its image lies in `D`, strictly on the `σ'`-side of the image line
  have hfvj : f (T.v j : Sphere) ∈ D := u9h_isHomeoOnto_mapsTo hf (hTX hvj).2
  have himg : det (M e) (f (T.v j : Sphere) - a) =
      det (M (1, 0)) (M (0, 1)) * det e (T.v j - m) := by
    rw [hMb' _ hvj, haM]
    have : M (T.v j) + b - (M m + b) = M (T.v j - m) := by rw [M.map_sub (T.v j) m]; abel
    rw [this, u1h_det_linear]
  have hMe : M e ≠ 0 := by
    intro h0
    have : det (M e) (f (T.v j : Sphere) - a) = 0 := by rw [h0, u9h_det_zero_left]
    rw [himg] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hdetM.ne'
    · exact hj h1
  have hz0 : det (M e) (z - a) ≠ 0 := u9h_interior_off_line hD hδ0 hMe hfr' hz
  have hpos : 0 < σ' * det (M e) (f (T.v j : Sphere) - a) := by
    rw [himg, mul_left_comm]; exact mul_pos hdetM hvpos
  have hkey : 0 < σ' * det (M e) (z - a) := by
    rcases u9h_supporting_line hD hδ0 hfr' with hside | hside
    · have h2 := hside _ (interior_subset hz)
      have hσ1 : σ' = 1 := by
        rcases hσpm with h | h
        · exact h
        · exfalso; have h1 := hside _ hfvj; rw [h] at hpos; linarith
      rw [hσ1, one_mul]; exact lt_of_le_of_ne h2 (Ne.symm hz0)
    · have h2 := hside _ (interior_subset hz)
      have hσ1 : σ' = -1 := by
        rcases hσpm with h | h
        · exfalso; have h1 := hside _ hfvj; rw [h] at hpos; linarith
        · exact h
      rw [hσ1]; have := lt_of_le_of_ne h2 hz0; linarith
  -- the collinear triple
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hcol := u9h_cyclicPos_collinear z a (M e) (half_pos hδ0)
  have h2δ : 2 * (δ / 2) = δ := by ring
  rw [h2δ] at hcol
  have hswap : det (a - z) (M e) = det (M e) (z - a) := u9h_det_sub_comm a z (M e)
  refine ⟨1/2, 1/2 + δ/2, 1/2 + δ, by linarith, by linarith, by linarith, ?_, ?_⟩
  · intro hσ1
    rw [hF0, hFt (δ/2) ⟨by positivity, by linarith⟩, hFt δ ⟨hδ0.le, le_rfl⟩]
    apply hcol.1
    rw [hswap]; rw [hσ1, one_mul] at hkey; exact hkey
  · intro hσ1
    rw [hF0, hFt (δ/2) ⟨by positivity, by linarith⟩, hFt δ ⟨hδ0.le, le_rfl⟩]
    apply hcol.2
    rw [hswap]; rw [hσ1] at hkey; linarith

/-! #### U9 leaf-level: the last two leaves -/

theorem u9h_U9_traversalPositiveFor_iff_cyclicPos [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (s : Side) {L : ℝ} (hL : InsideModel L P) {D : Set Plane} {f : Sphere → Plane}
    (hD : Link.IsDisc D) (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hB : f '' sphereCircle P = frontier D) (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    {z : Plane} (hz : z ∈ interior D) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    traversalPositiveFor P s ↔
      CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) := by
  obtain ⟨R⟩ := u4h_region_exists n hn P hP
  have hiff := u9h_sideSign_eq_one_iff hn hP R s
  have hpm := u9h_sideSign_pm R s
  have hdich := u9h_cyclic_dichotomy hD hz (u9h_F_continuous hn P hP s hf)
    (u9h_F_mem_frontier P hB) (fun x y hxy hyx => u9h_F_ne hn P hP s hf hxy hyx)
  obtain ⟨x₀, y₀, w₀, h1, h2, h3, hpos, hneg⟩ := u9h_local_eval hn P hP R s hL hD hf hB hpl hz
  show traversalPositiveFor P s ↔ CyclicPos z (u9h_F P f x) (u9h_F P f y) (u9h_F P f w)
  rcases hdich with hall | hnone
  · refine ⟨fun _ => hall x y w hxy hyw hwx, fun _ => ?_⟩
    by_contra hnot
    have hσ : u9h_sideSign R s = -1 := hpm.resolve_left fun h => hnot (hiff.mp h)
    exact hneg hσ (hall x₀ y₀ w₀ h1 h2 h3)
  · refine ⟨fun htrav => ?_, fun hc => absurd hc (hnone x y w hxy hyw hwx)⟩
    exact absurd (hpos (hiff.mpr htrav)) (hnone x₀ y₀ w₀ h1 h2 h3)

theorem u9h_U9_lift_preserves_cyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n)
    (P : LabelledTuple n) (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P')
    (s s' : Side) {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {φ : ℝ → ℝ}
    (hφ : IsPositiveBoundaryLift P s P' s' φ) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n)
    (h : CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
      (f ((traversal P w : Plane) : Sphere))) :
    CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
      (f' ((traversal P' (φ w) : Plane) : Sphere)) := by
  have htrav : traversalPositiveFor P s :=
    (u9h_U9_traversalPositiveFor_iff_cyclicPos hn P hP s hL hD hf hB hpl hz hxy hyw hwx).mpr h
  by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨hmono, hper⟩ := hφ.same hsame
    have h1 : φ x < φ y := hmono hxy
    have h2 : φ y < φ w := hmono hyw
    have h3 : φ w < φ x + n' := by have := hmono hwx; rwa [hper] at this
    exact (u9h_U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz'
      h1 h2 h3).mp (hsame.mp htrav)
  · obtain ⟨hanti, hper⟩ := hφ.opposite hsame
    have h1 : φ y < φ x := hanti hxy
    have h2 : φ w < φ y := hanti hyw
    have h3 : φ x - n' < φ w := by have := hanti hwx; rwa [hper] at this
    have hnot' : ¬ traversalPositiveFor P' s' := fun h' => hsame ⟨fun _ => h', fun _ => htrav⟩
    have hiff' := u9h_U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz'
      h2 h1 (by linarith)
    have hnc : ¬ CyclicPos z' (u9h_F P' f' (φ w)) (u9h_F P' f' (φ y)) (u9h_F P' f' (φ x)) :=
      fun hc => hnot' (hiff'.mpr hc)
    have hfr : ∀ t, u9h_F P' f' t ∈ frontier D' := u9h_F_mem_frontier P' hB'
    have hne1 : u9h_F P' f' (φ w) ≠ u9h_F P' f' (φ x) :=
      u9h_F_ne hn' P' hP' s' hf' (h2.trans h1) (by linarith)
    have hne2 : u9h_F P' f' (φ x) ≠ u9h_F P' f' (φ y) :=
      (u9h_F_ne hn' P' hP' s' hf' h1 (by linarith)).symm
    have hne3 : u9h_F P' f' (φ w) ≠ u9h_F P' f' (φ y) :=
      u9h_F_ne hn' P' hP' s' hf' h2 (by linarith)
    rcases u9h_cyclicPos_total hD' hz' (hfr (φ w)) (hfr (φ x)) (hfr (φ y)) hne1 hne2 hne3 with hc | hc
    · exact u9h_cyclicPos_rotate hc
    · exact absurd hc hnc

/-- U9: "interior on the left of edge `i`" is the sign of the face of the ear triangulation adjacent
to that edge; it is the same for all edges (consistency along the ear induction). -/
theorem U9_interiorOnLeft_consistent [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i j : ZMod n) : InteriorOnLeft P i ↔ InteriorOnLeft P j := by
  exact u9h_U9_interiorOnLeft_consistent hn P hP i j

/-- U9 (sm-3:4762-4764 read at a supporting vertex): at a supporting vertex with nonzero turn the
interior is on the left iff the turn is positive. -/
theorem U9_interiorOnLeft_iff_turn [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {N : Plane} {i : ZMod n} (hs : IsSupportingVertex P N i) (ht : principalTurn P i ≠ 0) :
    InteriorOnLeft P i ↔ 0 < principalTurn P i := by
  exact u9h_U9_interiorOnLeft_iff_turn hn P hP hs ht

/-- U9 (with `cb_embedded_rotation.orientation`): the interior is on the left of the traversal iff
the rotation number is positive. -/
theorem U9_interiorOnLeft_iff_rotation [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (i : ZMod n) : InteriorOnLeft P i ↔ 0 < rotationNumber P := by
  exact u9h_interiorOnLeft_iff_rot hn hP i

/-- U9 (the convention of `traversalPositiveFor`, FR-TD-9): a positive PL parametrisation `f` of the
closed region `s` onto a convex model `D` carries the traversal, read around an interior point `z`,
to the counterclockwise cyclic order exactly when `traversalPositiveFor P s`. -/
theorem U9_traversalPositiveFor_iff_cyclicPos [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (s : Side) {L : ℝ} (hL : InsideModel L P) {D : Set Plane} {f : Sphere → Plane}
    (hD : Link.IsDisc D) (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hB : f '' sphereCircle P = frontier D) (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    {z : Plane} (hz : z ∈ interior D) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    traversalPositiveFor P s ↔
      CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) := by
  exact u9h_U9_traversalPositiveFor_iff_cyclicPos hn P hP s hL hD hf hB hpl hz hxy hyw hwx

/-- U9 (positivity of the boundary map, sm-3:431-434 "positive"): a positive boundary lift, read in
two positive parametrisations, preserves the counterclockwise cyclic order. -/
theorem U9_lift_preserves_cyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {φ : ℝ → ℝ}
    (hφ : IsPositiveBoundaryLift P s P' s' φ) {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n)
    (h : CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
      (f ((traversal P w : Plane) : Sphere))) :
    CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
      (f' ((traversal P' (φ w) : Plane) : Sphere)) := by
  exact u9h_U9_lift_preserves_cyclicPos hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hz hz' hφ hxy hyw hwx h


end SM
