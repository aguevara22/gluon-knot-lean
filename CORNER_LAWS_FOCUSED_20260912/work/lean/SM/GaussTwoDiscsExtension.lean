-- Ported 14:52Z 2026-09-19 from work/drafts/twodiscs/W2_Assembled.lean by the pod executor (files prepared by the U12 assembler)
import SM.GaussTwoDiscsAmbient

/-! # Row 57 lem:gauss-two-discs — units U10-U11 (lane C, then sequential)

U10 57c: finite positive PL boundary maps extend to positive PL disc maps (`U10_pl_extension`); U11 57d:
continuous positive boundary maps extend to topological disc maps (`U11_top_extension`).  Every leaf is
proved.  Provenance: `SM.GaussTwoDiscsDefs`. -/

namespace SM

open Set OnePoint

variable {n : ℕ}

/-! ### U10 (lane C convex model, then sequential) — 57c -/

/-- U10: `β` is finite PL on the frontier of `D`: affine on each of finitely many segments covering
`frontier D`. -/
def IsFinitePLOnFrontier (D : Set Plane) (β : Plane → Plane) : Prop :=
  ∃ s : Finset (Plane × Plane), (⋃ p ∈ s, segment ℝ p.1 p.2) = frontier D ∧
    ∀ p ∈ s, AffineOn β (segment ℝ p.1 p.2)

/-- U10: `β` preserves the counterclockwise cyclic order of `frontier D` around `z` (to that of
`frontier D'` around `z'`). -/
def PreservesCyclicPos (D : Set Plane) (z z' : Plane) (β : Plane → Plane) : Prop :=
  ∀ a ∈ frontier D, ∀ b ∈ frontier D, ∀ c ∈ frontier D,
    CyclicPos z a b c → CyclicPos z' (β a) (β b) (β c)

/-! #### U10 helpers for `U10_fan_extension` (radial gauge, sectors, marks, fan, cone) -/

/-- U10 helper: the translate of `D` bringing `z` to the origin. -/
def u10h_D0 (D : Set Plane) (z : Plane) : Set Plane := (Homeomorph.addRight z) ⁻¹' D

/-- U10 helper: the radial gauge of `D` about `z`. -/
noncomputable def u10h_rg (D : Set Plane) (z : Plane) (x : Plane) : ℝ := gauge (u10h_D0 D z) (x - z)

theorem u10h_mem_D0 {D : Set Plane} {z w : Plane} : w ∈ u10h_D0 D z ↔ w + z ∈ D := Iff.rfl

theorem u10h_D0_convex {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : Convex ℝ (u10h_D0 D z) := by
  have h : u10h_D0 D z = (fun x => x + z) ⁻¹' D := by ext w; simp [u10h_D0]
  rw [h]; exact hD.convex.translate_preimage_left z

theorem u10h_D0_isCompact {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) : IsCompact (u10h_D0 D z) :=
  (Homeomorph.addRight z).isCompact_preimage.mpr hD.isCompact

theorem u10h_D0_interior {D : Set Plane} (z : Plane) :
    interior (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' interior D :=
  ((Homeomorph.addRight z).preimage_interior D).symm

theorem u10h_D0_frontier {D : Set Plane} (z : Plane) :
    frontier (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' frontier D :=
  ((Homeomorph.addRight z).preimage_frontier D).symm

theorem u10h_D0_closure {D : Set Plane} (z : Plane) :
    closure (u10h_D0 D z) = (Homeomorph.addRight z) ⁻¹' closure D :=
  ((Homeomorph.addRight z).preimage_closure D).symm

theorem u10h_D0_nhds {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : u10h_D0 D z ∈ nhds (0 : Plane) := by
  rw [mem_nhds_iff]
  refine ⟨interior (u10h_D0 D z), interior_subset, isOpen_interior, ?_⟩
  rw [u10h_D0_interior]
  simpa using hz

theorem u10h_D0_absorbent {D : Set Plane} {z : Plane} (hz : z ∈ interior D) : Absorbent ℝ (u10h_D0 D z) :=
  absorbent_nhds_zero (u10h_D0_nhds hz)

theorem u10h_D0_bounded {D : Set Plane} (hD : Link.IsDisc D) (z : Plane) :
    Bornology.IsVonNBounded ℝ (u10h_D0 D z) :=
  (u10h_D0_isCompact hD z).isVonNBounded ℝ

theorem u10h_rg_nonneg (D : Set Plane) (z x : Plane) : 0 ≤ u10h_rg D z x := gauge_nonneg _

theorem u10h_rg_lt_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x < 1 ↔ x ∈ interior D := by
  unfold u10h_rg
  rw [gauge_lt_one_iff_mem_interior (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_interior]
  simp

theorem u10h_rg_le_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x ≤ 1 ↔ x ∈ D := by
  unfold u10h_rg
  rw [gauge_le_one_iff_mem_closure (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_closure,
    hD.isCompact.isClosed.closure_eq]
  simp

theorem u10h_rg_eq_one_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x = 1 ↔ x ∈ frontier D := by
  unfold u10h_rg
  rw [gauge_eq_one_iff_mem_frontier (u10h_D0_convex hD z) (u10h_D0_nhds hz), u10h_D0_frontier]
  simp

theorem u10h_rg_eq_zero_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) (x : Plane) :
    u10h_rg D z x = 0 ↔ x = z := by
  unfold u10h_rg
  rw [gauge_eq_zero (u10h_D0_absorbent hz) (u10h_D0_bounded hD z), sub_eq_zero]

theorem u10h_rg_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) {x : Plane}
    (hx : x ≠ z) : 0 < u10h_rg D z x :=
  lt_of_le_of_ne (u10h_rg_nonneg D z x) (fun h => hx ((u10h_rg_eq_zero_iff hD hz x).mp h.symm))

theorem u10h_rg_self (D : Set Plane) (z : Plane) : u10h_rg D z z = 0 := by
  simp [u10h_rg, gauge_zero]

theorem u10h_rg_smul (D : Set Plane) (z x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    u10h_rg D z (z + t • (x - z)) = t * u10h_rg D z x := by
  unfold u10h_rg
  rw [add_sub_cancel_left, gauge_smul_of_nonneg ht, smul_eq_mul]

theorem u10h_rg_continuous {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    Continuous (u10h_rg D z) :=
  (continuous_gauge (u10h_D0_convex hD z) (u10h_D0_nhds hz)).comp (continuous_id.sub continuous_const)

/-- The frontier point on the ray from `z` through `x ≠ z`. -/
noncomputable def u10h_ray (D : Set Plane) (z x : Plane) : Plane := z + (u10h_rg D z x)⁻¹ • (x - z)

theorem u10h_ray_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : u10h_ray D z x ∈ frontier D := by
  rw [← u10h_rg_eq_one_iff hD hz, u10h_ray, u10h_rg_smul D z x (inv_nonneg.mpr (u10h_rg_nonneg D z x))]
  exact inv_mul_cancel₀ (u10h_rg_pos hD hz hx).ne'

theorem u10h_ray_spec {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : x = z + u10h_rg D z x • (u10h_ray D z x - z) := by
  rw [u10h_ray, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (u10h_rg_pos hD hz hx).ne', one_smul,
    add_sub_cancel]

theorem u10h_ray_of_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : u10h_ray D z y = y := by
  rw [u10h_ray, (u10h_rg_eq_one_iff hD hz y).mpr hy, inv_one, one_smul, add_sub_cancel]

theorem u10h_frontier_ne {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) : y ≠ z := by
  intro h; subst h
  have := (u10h_rg_eq_one_iff hD hz y).mpr hy
  rw [u10h_rg_self] at this; norm_num at this

theorem u10h_frontier_subset {D : Set Plane} (hD : Link.IsDisc D) : frontier D ⊆ D :=
  hD.isCompact.isClosed.frontier_subset

/-! ### det algebra -/

theorem u10h_det_add_right (u v w : Plane) : det u (v + w) = det u v + det u w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u10h_det_smul_right (u v : Plane) (c : ℝ) : det u (c • v) = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u10h_det_add_left (u v w : Plane) : det (u + v) w = det u w + det v w := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

theorem u10h_det_smul_left' (u v : Plane) (c : ℝ) : det (c • u) v = c * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem u10h_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

theorem u10h_det_zero_right (u : Plane) : det u 0 = 0 := by simp [det]

theorem u10h_det_zero_left (u : Plane) : det 0 u = 0 := by simp [det]

theorem u10h_det_swap' (u v : Plane) : det u v = -det v u := by simp only [det]; ring

theorem u10h_cramer {u v : Plane} (h : det u v ≠ 0) (w : Plane) :
    w = (det w v / det u v) • u + (det u w / det u v) • v := by
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, div_mul_eq_mul_div, ← add_div]
    rw [eq_div_iff h]; unfold det; ring

theorem u10h_parallel_of_det_eq_zero {u v : Plane} (hu : u ≠ 0) (h : det u v = 0) :
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

theorem u10h_convex_det_nonneg (z u : Plane) : Convex ℝ {x : Plane | 0 ≤ det u (x - z)} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det u (x - z) at hx
  change 0 ≤ det u (y - z) at hy
  change 0 ≤ det u (a • x + b • y - z)
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u10h_det_add_right, u10h_det_smul_right, u10h_det_smul_right]
  positivity

theorem u10h_convex_det_nonneg' (z v : Plane) : Convex ℝ {x : Plane | 0 ≤ det (x - z) v} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ det (x - z) v at hx
  change 0 ≤ det (y - z) v at hy
  change 0 ≤ det (a • x + b • y - z) v
  have hz' : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
  have : a • x + b • y - z = a • (x - z) + b • (y - z) := by
    calc a • x + b • y - z = a • x + b • y - (a • z + b • z) := by rw [← hz']
      _ = a • (x - z) + b • (y - z) := by rw [smul_sub, smul_sub]; abel
  rw [this, u10h_det_add_left, u10h_det_smul_left', u10h_det_smul_left']
  positivity

/-! ### a straight frontier piece is not seen edge-on from `z` -/

theorem u10h_det_ne_zero_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier D) : det (a - z) (b - z) ≠ 0 := by
  intro h0
  have ha : a ∈ frontier D := hseg (left_mem_segment ℝ a b)
  have hb : b ∈ frontier D := hseg (right_mem_segment ℝ a b)
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u10h_frontier_ne hD hz ha)
  obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero haz h0
  have hb' : b = z + μ • (a - z) := by rw [← hμ]; abel
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · have h1 := (u10h_rg_eq_one_iff hD hz b).mpr hb
    rw [hb', u10h_rg_smul D z a hμ0, (u10h_rg_eq_one_iff hD hz a).mpr ha, mul_one] at h1
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
    have := (u10h_rg_eq_one_iff hD hz z).mpr (hseg hzmem)
    rw [u10h_rg_self] at this; norm_num at this

/-! ### the sector lemma and the fan characterisation -/

/-- A frontier point in the closed sector spanned (from `z`) by a straight frontier piece `[a, b]`
lies on that piece. -/
theorem u10h_frontier_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {y : Plane}
    (hy : y ∈ frontier D) (h1 : 0 ≤ det (a - z) (y - z)) (h2 : 0 ≤ det (y - z) (b - z)) :
    y ∈ segment ℝ a b := by
  set β := det (y - z) (b - z) / det (a - z) (b - z) with hβ
  set γ := det (a - z) (y - z) / det (a - z) (b - z) with hγ
  have hβ0 : 0 ≤ β := div_nonneg h2 hab.le
  have hγ0 : 0 ≤ γ := div_nonneg h1 hab.le
  have hdec : y - z = β • (a - z) + γ • (b - z) := u10h_cramer hab.ne' (y - z)
  have hs : 0 < β + γ := by
    rcases (add_nonneg hβ0 hγ0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hβz : β = 0 := by linarith
      have hγz : γ = 0 := by linarith
      rw [hβz, hγz, zero_smul, zero_smul, add_zero] at hdec
      exact u10h_frontier_ne hD hz hy (sub_eq_zero.mp hdec)
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
  have hrw : u10h_rg D z w = 1 := (u10h_rg_eq_one_iff hD hz w).mpr (hseg hwseg)
  have hry : u10h_rg D z y = 1 := (u10h_rg_eq_one_iff hD hz y).mpr hy
  rw [hyw, u10h_rg_smul D z w hs.le, hrw, mul_one] at hry
  rw [hyw, hry, one_smul, add_sub_cancel]
  exact hwseg

/-- The ray point of a point of the closed sector lies on the frontier piece. -/
theorem u10h_ray_mem_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hab : 0 < det (a - z) (b - z)) (hseg : segment ℝ a b ⊆ frontier D) {x : Plane}
    (hxz : x ≠ z) (h1 : 0 ≤ det (a - z) (x - z)) (h2 : 0 ≤ det (x - z) (b - z)) :
    u10h_ray D z x ∈ segment ℝ a b := by
  have hyz : u10h_ray D z x - z = (u10h_rg D z x)⁻¹ • (x - z) := by simp [u10h_ray]
  have hr0 : 0 ≤ (u10h_rg D z x)⁻¹ := inv_nonneg.mpr (u10h_rg_nonneg _ _ _)
  refine u10h_frontier_mem_segment hD hz hab hseg (u10h_ray_mem_frontier hD hz hxz) ?_ ?_
  · rw [hyz, u10h_det_smul_right]; exact mul_nonneg hr0 h1
  · rw [hyz, u10h_det_smul_left']; exact mul_nonneg hr0 h2

/-- The fan triangle `conv {z, a, b}` over a straight frontier piece is the closed sector cut off
by `D`. -/
theorem u10h_mem_fan_iff {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
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
            u10h_frontier_subset hD (hseg (left_mem_segment ℝ _ _))⟩
        · exact ⟨⟨hab.le, by simp⟩,
            u10h_frontier_subset hD (hseg (right_mem_segment ℝ _ _))⟩
      · exact ((u10h_convex_det_nonneg z (a - z)).inter (u10h_convex_det_nonneg' z (b - z))).inter
          hD.convex
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsub hx
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hxz : x = z
    · subst hxz; exact subset_convexHull ℝ _ (mem_insert _ _)
    · have hyseg := u10h_ray_mem_segment hD hz hab hseg hxz h1 h2
      have hxeq := u10h_ray_spec hD hz hxz
      have hr1 : u10h_rg D z x ≤ 1 := (u10h_rg_le_one_iff hD hz x).mpr h3
      have hr0 := u10h_rg_nonneg D z x
      have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
      have hymem : u10h_ray D z x ∈ convexHull ℝ {z, a, b} :=
        segment_subset_convexHull (by simp) (by simp) hyseg
      have := (convex_convexHull ℝ {z, a, b}) hzmem hymem (sub_nonneg.mpr hr1) hr0 (by ring)
      rw [hxeq]
      convert this using 1
      rw [sub_smul, one_smul, smul_sub]; abel

/-! ### marks and adjacent pairs -/

/-- `(a, b)` is an adjacent pair of marks of `V`: a straight frontier piece seen counterclockwise
from `z` with no mark strictly inside. -/
def u10h_Adj (D : Set Plane) (z : Plane) (V : Set Plane) (a b : Plane) : Prop :=
  a ∈ V ∧ b ∈ V ∧ 0 < det (a - z) (b - z) ∧ segment ℝ a b ⊆ frontier D ∧
    ∀ c ∈ V, c ∉ openSegment ℝ a b

theorem u10h_openSegment_sub {a b y : Plane} (h : y ∈ openSegment ℝ a b) (z : Plane) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ β + γ = 1 ∧ y - z = β • (a - z) + γ • (b - z) := by
  obtain ⟨β, γ, hβ, hγ, hβγ, rfl⟩ := h
  refine ⟨β, γ, hβ, hγ, hβγ, ?_⟩
  have hz' : z = β • z + γ • z := by rw [← add_smul, hβγ, one_smul]
  calc β • a + γ • b - z = β • a + γ • b - (β • z + γ • z) := by rw [← hz']
    _ = β • (a - z) + γ • (b - z) := by rw [smul_sub, smul_sub]; abel

theorem u10h_det_comb_right (u v w : Plane) (β γ : ℝ) :
    det u (β • v + γ • w) = β * det u v + γ * det u w := by
  rw [u10h_det_add_right, u10h_det_smul_right, u10h_det_smul_right]

theorem u10h_det_comb_left (u v w : Plane) (β γ : ℝ) :
    det (β • v + γ • w) u = β * det v u + γ * det w u := by
  rw [u10h_det_add_left, u10h_det_smul_left', u10h_det_smul_left']

theorem u10h_mem_segment_cases {a b y : Plane} (h : y ∈ segment ℝ a b) :
    y = a ∨ y = b ∨ y ∈ openSegment ℝ a b := by
  rw [← insert_endpoints_openSegment] at h
  simpa using h

/-- Where a mark can lie relative to an adjacent pair. -/
theorem u10h_adj_trichotomy {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b : Plane} (hab : u10h_Adj D z V a b) {c : Plane}
    (hc : c ∈ V) : c = a ∨ c = b ∨ det (a - z) (c - z) < 0 ∨ det (c - z) (b - z) < 0 := by
  rcases lt_or_ge (det (a - z) (c - z)) 0 with h1 | h1
  · exact Or.inr (Or.inr (Or.inl h1))
  rcases lt_or_ge (det (c - z) (b - z)) 0 with h2 | h2
  · exact Or.inr (Or.inr (Or.inr h2))
  have hcseg := u10h_frontier_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 (hV hc) h1 h2
  rcases u10h_mem_segment_cases hcseg with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h (hab.2.2.2.2 c hc)

theorem u10h_adj_unique_right {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b d : Plane} (hab : u10h_Adj D z V a b)
    (had : u10h_Adj D z V a d) : b = d := by
  rcases u10h_adj_trichotomy hD hz hV hab had.2.1 with h | h | h | h
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using had.2.2.1)
  · exact h.symm
  · exfalso; linarith [had.2.2.1]
  · exfalso
    have hbd : 0 < det (b - z) (d - z) := by rw [u10h_det_swap']; linarith
    have hbseg := u10h_frontier_mem_segment hD hz had.2.2.1 had.2.2.2.1 (hV hab.2.1) hab.2.2.1.le hbd.le
    rcases u10h_mem_segment_cases hbseg with h1 | h1 | h1
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hab.2.2.1)
    · subst h1; simp at hbd
    · exact had.2.2.2.2 b hab.2.1 h1

theorem u10h_adj_unique_left {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c : Plane} (hab : u10h_Adj D z V a b)
    (hcb : u10h_Adj D z V c b) : a = c := by
  rcases u10h_adj_trichotomy hD hz hV hab hcb.1 with h | h | h | h
  · exact h.symm
  · exfalso; subst h; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hcb.2.2.1)
  · exfalso
    have hca : 0 < det (c - z) (a - z) := by rw [u10h_det_swap']; linarith
    have haseg := u10h_frontier_mem_segment hD hz hcb.2.2.1 hcb.2.2.2.1 (hV hab.1) hca.le hab.2.2.1.le
    rcases u10h_mem_segment_cases haseg with h1 | h1 | h1
    · subst h1; simp at hca
    · subst h1; exact lt_irrefl (0:ℝ) (by simpa [u10h_det_self] using hab.2.2.1)
    · exact hcb.2.2.2.2 a hab.1 h1
  · exfalso; linarith [hcb.2.2.1]

/-- A point in the open frontier pieces of two adjacent pairs forces the pairs to coincide. -/
theorem u10h_adj_eq_of_openSegment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u10h_Adj D z V a b)
    (hcd : u10h_Adj D z V c d) (h1 : y ∈ openSegment ℝ a b) (h2 : y ∈ openSegment ℝ c d) :
    a = c ∧ b = d := by
  obtain ⟨β, γ, hβ, hγ, -, hY1⟩ := u10h_openSegment_sub h1 z
  obtain ⟨β', δ, hβ', hδ, -, hY2⟩ := u10h_openSegment_sub h2 z
  have dAB := hab.2.2.1
  have dCD := hcd.2.2.1
  have eAY : det (a - z) (y - z) = γ * det (a - z) (b - z) := by
    rw [hY1, u10h_det_comb_right, u10h_det_self]; ring
  have eBY : det (b - z) (y - z) = -(β * det (a - z) (b - z)) := by
    rw [hY1, u10h_det_comb_right, u10h_det_self, u10h_det_swap' (b - z) (a - z)]; ring
  have eCY : det (c - z) (y - z) = δ * det (c - z) (d - z) := by
    rw [hY2, u10h_det_comb_right, u10h_det_self]; ring
  have eYD : det (y - z) (d - z) = β' * det (c - z) (d - z) := by
    rw [hY2, u10h_det_comb_left, u10h_det_self]; ring
  have eAY' : det (a - z) (y - z) = β' * det (a - z) (c - z) + δ * det (a - z) (d - z) := by
    rw [hY2, u10h_det_comb_right]
  have eBY' : det (b - z) (y - z) = β' * det (b - z) (c - z) + δ * det (b - z) (d - z) := by
    rw [hY2, u10h_det_comb_right]
  have eYD' : det (y - z) (d - z) = β * det (a - z) (d - z) + γ * det (b - z) (d - z) := by
    rw [hY1, u10h_det_comb_left]
  rcases u10h_adj_trichotomy hD hz hV hab hcd.1 with hc | hc | hc | hc
  · -- c = a
    subst hc
    refine ⟨rfl, ?_⟩
    rcases u10h_adj_trichotomy hD hz hV hab hcd.2.1 with hd | hd | hd | hd
    · exfalso; subst hd
      have := hcd.2.2.1; rw [u10h_det_self] at this; exact lt_irrefl _ this
    · exact hd.symm
    · exfalso; linarith [hcd.2.2.1]
    · exfalso
      have hbd : 0 < det (b - z) (d - z) := by rw [u10h_det_swap']; linarith
      have hbseg := u10h_frontier_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 (hV hab.2.1) dAB.le hbd.le
      rcases u10h_mem_segment_cases hbseg with h | h | h
      · subst h; rw [u10h_det_self] at dAB; exact lt_irrefl _ dAB
      · subst h; rw [u10h_det_self] at hbd; exact lt_irrefl _ hbd
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
    have hCA : 0 < det (c - z) (a - z) := by rw [u10h_det_swap']; linarith
    have haseg := u10h_frontier_mem_segment hD hz dCD hcd.2.2.2.1 (hV hab.1) hCA.le hAD.le
    rcases u10h_mem_segment_cases haseg with h | h | h
    · subst h; rw [u10h_det_self] at hCA; exact lt_irrefl _ hCA
    · subst h; rw [u10h_det_self] at hAD; exact lt_irrefl _ hAD
    · exact hcd.2.2.2.2 a hab.1 h
  · -- det (c-z) (b-z) < 0 : `d` lies strictly inside the sector `(a, b)`
    exfalso
    have hBC : 0 < det (b - z) (c - z) := by rw [u10h_det_swap']; linarith
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
    have hDB : 0 < det (d - z) (b - z) := by rw [u10h_det_swap']; linarith
    have hdseg := u10h_frontier_mem_segment hD hz dAB hab.2.2.2.1 (hV hcd.2.1) hAD.le hDB.le
    rcases u10h_mem_segment_cases hdseg with h | h | h
    · subst h; rw [u10h_det_self] at hAD; exact lt_irrefl _ hAD
    · subst h; rw [u10h_det_self] at hDB; exact lt_irrefl _ hDB
    · exact hab.2.2.2.2 d hcd.2.1 h


theorem u10h_range_three (z a b : Plane) : range ![z, a, b] = {z, a, b} := by
  ext p
  simp only [mem_range, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]

/-- The fan faces: one triangle `z a b` per pair with `A a b`. -/
def u10h_fanFaces (z : Plane) (A : Plane → Plane → Prop) : Set Triangle :=
  {T | ∃ a b, A a b ∧ T.v = ![z, a, b]}

theorem u10h_fanTri_mem {z a b : Plane} {A : Plane → Plane → Prop} (h : A a b)
    (hpos : 0 < det (a - z) (b - z)) :
    (⟨![z, a, b], by simpa using hpos⟩ : Triangle) ∈ u10h_fanFaces z A := ⟨a, b, h, rfl⟩

theorem u10h_carrier_of_v {T : Triangle} {z a b : Plane} (h : T.v = ![z, a, b]) :
    T.carrier = convexHull ℝ {z, a, b} := by
  rw [Triangle.carrier, h, u10h_range_three]

theorem u10h_inter_cases {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hV : V ⊆ frontier D) {a b c d y : Plane} (hab : u10h_Adj D z V a b)
    (hcd : u10h_Adj D z V c d) (hy1 : y ∈ segment ℝ a b) (hy2 : y ∈ segment ℝ c d) :
    (a = c ∧ b = d) ∨ (y = a ∧ a = d) ∨ (y = b ∧ b = c) := by
  rcases u10h_mem_segment_cases hy1 with h1 | h1 | h1 <;>
    rcases u10h_mem_segment_cases hy2 with h2 | h2 | h2
  · subst h1; exact Or.inl ⟨h2, u10h_adj_unique_right hD hz hV hab (h2 ▸ hcd)⟩
  · exact Or.inr (Or.inl ⟨h1, h1 ▸ h2⟩)
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 a hab.1)
  · exact Or.inr (Or.inr ⟨h1, h1 ▸ h2⟩)
  · subst h1; exact Or.inl ⟨u10h_adj_unique_left hD hz hV hab (h2 ▸ hcd), h2⟩
  · exact absurd (h1 ▸ h2) (hcd.2.2.2.2 b hab.2.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 c hcd.1)
  · exact absurd (h2 ▸ h1) (hab.2.2.2.2 d hcd.2.1)
  · exact Or.inl (u10h_adj_eq_of_openSegment hD hz hV hab hcd h1 h2)

theorem u10h_fan_subset {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) : convexHull ℝ {z, a, b} ⊆ D := by
  apply convexHull_min _ hD.convex
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact interior_subset hz
  · exact u10h_frontier_subset hD (hseg (left_mem_segment ℝ _ _))
  · exact u10h_frontier_subset hD (hseg (right_mem_segment ℝ _ _))

theorem u10h_frontier_nonempty {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D) :
    (frontier D).Nonempty :=
  ⟨u10h_ray D z (z + (1, 0)), u10h_ray_mem_frontier hD hz (by simp)⟩

theorem u10h_mem_segment_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ∈ D) (hxz : x ≠ z) : x ∈ segment ℝ z (u10h_ray D z x) := by
  have hr0 := u10h_rg_nonneg D z x
  have hr1 := (u10h_rg_le_one_iff hD hz x).mpr hx
  refine ⟨1 - u10h_rg D z x, u10h_rg D z x, by linarith, hr0, by ring, ?_⟩
  have := u10h_ray_spec hD hz hxz
  rw [smul_sub] at this
  rw [sub_smul, one_smul]
  conv_rhs => rw [this]
  abel

/-- The fan from `z` over the adjacent pairs is a straight triangulation of `D`. -/
theorem u10h_fan_triangulation {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {V : Set Plane} (hVfin : V.Finite) (hV : V ⊆ frontier D) {A : Plane → Plane → Prop}
    (hA : ∀ a b, A a b → u10h_Adj D z V a b)
    (hcov : ∀ y ∈ frontier D, ∃ a b, A a b ∧ y ∈ segment ℝ a b) :
    ∃ K : Triangulation D, K.faces = u10h_fanFaces z A := by
  have hface : ∀ T ∈ u10h_fanFaces z A, ∃ a b, u10h_Adj D z V a b ∧ T.v 0 = z ∧ T.v 1 = a ∧
      T.v 2 = b ∧ T.carrier = convexHull ℝ {z, a, b} := by
    rintro T ⟨a, b, hab, hv⟩
    exact ⟨a, b, hA a b hab, by simp [hv], by simp [hv], by simp [hv], u10h_carrier_of_v hv⟩
  refine ⟨⟨u10h_fanFaces z A, ?_, ?_, ?_⟩, rfl⟩
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
      exact u10h_fan_subset hD hz hab.2.2.2.1 hxT
    · intro x hx
      simp only [mem_iUnion, exists_prop]
      by_cases hxz : x = z
      · subst hxz
        obtain ⟨y0, hy0⟩ := u10h_frontier_nonempty hD hz
        obtain ⟨a, b, hab, -⟩ := hcov y0 hy0
        refine ⟨_, u10h_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u10h_carrier_of_v rfl]
        exact subset_convexHull ℝ _ (mem_insert _ _)
      · obtain ⟨a, b, hab, hyab⟩ := hcov _ (u10h_ray_mem_frontier hD hz hxz)
        refine ⟨_, u10h_fanTri_mem hab (hA a b hab).2.2.1, ?_⟩
        rw [u10h_carrier_of_v rfl]
        have hzmem : z ∈ convexHull ℝ {z, a, b} := subset_convexHull ℝ _ (mem_insert _ _)
        have hymem : u10h_ray D z x ∈ convexHull ℝ {z, a, b} :=
          segment_subset_convexHull (by simp) (by simp) hyab
        exact (convex_convexHull ℝ _).segment_subset hzmem hymem (u10h_mem_segment_ray hD hz hx hxz)
  · -- inter
    intro T hT T' hT'
    obtain ⟨a, b, hab, h0, h1, h2, hc⟩ := hface T hT
    obtain ⟨c, d, hcd, h0', h1', h2', hc'⟩ := hface T' hT'
    have hrT : range T.v = {z, a, b} := by
      rw [← u10h_range_three]; congr 1; funext i; fin_cases i <;> simp [h0, h1, h2]
    have hrT' : range T'.v = {z, c, d} := by
      rw [← u10h_range_three]; congr 1; funext i; fin_cases i <;> simp [h0', h1', h2']
    rw [hc, hc', hrT, hrT']
    apply Set.Subset.antisymm
    · rintro x ⟨hx1, hx2⟩
      by_cases hxz : x = z
      · subst hxz
        exact subset_convexHull ℝ _ ⟨mem_insert _ _, mem_insert _ _⟩
      · have hx1' := (u10h_mem_fan_iff hD hz hab.2.2.1 hab.2.2.2.1 x).mp hx1
        have hx2' := (u10h_mem_fan_iff hD hz hcd.2.2.1 hcd.2.2.2.1 x).mp hx2
        have hy1 := u10h_ray_mem_segment hD hz hab.2.2.1 hab.2.2.2.1 hxz hx1'.1 hx1'.2.1
        have hy2 := u10h_ray_mem_segment hD hz hcd.2.2.1 hcd.2.2.2.1 hxz hx2'.1 hx2'.2.1
        have hxseg := u10h_mem_segment_ray hD hz hx1'.2.2 hxz
        rcases u10h_inter_cases hD hz hV hab hcd hy1 hy2 with ⟨rfl, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩
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
noncomputable def u10h_linOfDet (p q p' q' : Plane) : Plane →ₗ[ℝ] Plane where
  toFun v := (det v q / det p q) • p' + (det p v / det p q) • q'
  map_add' v w := by
    rw [u10h_det_add_left, u10h_det_add_right, add_div, add_div, add_smul, add_smul]; abel
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [u10h_det_smul_left', u10h_det_smul_right, mul_div_assoc, mul_div_assoc, mul_smul, mul_smul,
      smul_add]

theorem u10h_linOfDet_apply (p q p' q' v : Plane) :
    u10h_linOfDet p q p' q' v = (det v q / det p q) • p' + (det p v / det p q) • q' := rfl

theorem u10h_linOfDet_left {p q : Plane} (h : det p q ≠ 0) (p' q' : Plane) :
    u10h_linOfDet p q p' q' p = p' := by
  rw [u10h_linOfDet_apply, div_self h, u10h_det_self, zero_div, one_smul, zero_smul, add_zero]

theorem u10h_linOfDet_right {p q : Plane} (h : det p q ≠ 0) (p' q' : Plane) :
    u10h_linOfDet p q p' q' q = q' := by
  rw [u10h_linOfDet_apply, div_self h, u10h_det_self, zero_div, one_smul, zero_smul, zero_add]

/-- The cone extension of a frontier map `β`: `z ↦ z'`, `z + t (y - z) ↦ z' + t (β y - z')` for
`y ∈ frontier D`, `0 ≤ t ≤ 1`. -/
noncomputable def u10h_cone (D : Set Plane) (z z' : Plane) (β : Plane → Plane) (x : Plane) : Plane :=
  z' + u10h_rg D z x • (β (u10h_ray D z x) - z')

theorem u10h_cone_center (D : Set Plane) (z z' : Plane) (β : Plane → Plane) :
    u10h_cone D z z' β z = z' := by
  simp [u10h_cone, u10h_rg_self]

theorem u10h_cone_frontier {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) (β : Plane → Plane) {y : Plane} (hy : y ∈ frontier D) :
    u10h_cone D z z' β y = β y := by
  rw [u10h_cone, u10h_ray_of_frontier hD hz hy, (u10h_rg_eq_one_iff hD hz y).mpr hy, one_smul,
    add_sub_cancel]

/-- The radial coordinate is preserved by the cone map (for `β` into `frontier D'`). -/
theorem u10h_rg_cone {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') {x : Plane} (hxz : x ≠ z) :
    u10h_rg D' z' (u10h_cone D z z' β x) = u10h_rg D z x := by
  rw [u10h_cone, u10h_rg_smul D' z' _ (u10h_rg_nonneg D z x),
    (u10h_rg_eq_one_iff hD' hz' _).mpr (hβ _ (u10h_ray_mem_frontier hD hz hxz)), mul_one]

theorem u10h_cone_ray_formula {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) (β : Plane → Plane) {y : Plane} (hy : y ∈ frontier D) {t : ℝ} (ht : 0 < t) :
    u10h_cone D z z' β (z + t • (y - z)) = z' + t • (β y - z') := by
  have hyz := u10h_frontier_ne hD hz hy
  have hrg : u10h_rg D z (z + t • (y - z)) = t := by
    rw [u10h_rg_smul D z y ht.le, (u10h_rg_eq_one_iff hD hz y).mpr hy, mul_one]
  have hray : u10h_ray D z (z + t • (y - z)) = y := by
    rw [u10h_ray, hrg, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
  rw [u10h_cone, hrg, hray]

theorem u10h_combo_sub {s t : ℝ} (hst : s + t = 1) (a b z : Plane) :
    s • a + t • b - z = s • (a - z) + t • (b - z) := by
  have hz' : z = s • z + t • z := by rw [← add_smul, hst, one_smul]
  calc s • a + t • b - z = s • a + t • b - (s • z + t • z) := by rw [← hz']
    _ = s • (a - z) + t • (b - z) := by rw [smul_sub, smul_sub]; abel

/-- On a fan triangle over a piece where `β` is affine, the cone map is affine. -/
theorem u10h_cone_eq_on_fan {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) {β : Plane → Plane} {a b : Plane} (hab : 0 < det (a - z) (b - z))
    (hseg : segment ℝ a b ⊆ frontier D) (haff : AffineOn β (segment ℝ a b)) {x : Plane}
    (hx : x ∈ convexHull ℝ {z, a, b}) :
    u10h_cone D z z' β x = u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z') (x - z) + z' := by
  by_cases hxz : x = z
  · subst hxz; simp [u10h_cone_center]
  · obtain ⟨M, c, hM⟩ := haff
    have hx' := (u10h_mem_fan_iff hD hz hab hseg x).mp hx
    have hyseg := u10h_ray_mem_segment hD hz hab hseg hxz hx'.1 hx'.2.1
    obtain ⟨s, t, hs, ht, hst, hy⟩ := id hyseg
    have hβy : β (u10h_ray D z x) - z' = s • (β a - z') + t • (β b - z') := by
      rw [hM _ hyseg, hM a (left_mem_segment ℝ a b), hM b (right_mem_segment ℝ a b), ← hy, map_add,
        map_smul, map_smul]
      have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
      have hz' : z' = s • z' + t • z' := by rw [← add_smul, hst, one_smul]
      calc s • M a + t • M b + c - z' = s • M a + t • M b + (s • c + t • c) - (s • z' + t • z') := by
            rw [← hc, ← hz']
        _ = s • (M a + c - z') + t • (M b + c - z') := by
            rw [smul_sub, smul_sub, smul_add, smul_add]; abel
    have hyz : u10h_ray D z x - z = s • (a - z) + t • (b - z) := by
      rw [← hy, u10h_combo_sub hst]
    have hxz' : x - z = u10h_rg D z x • (s • (a - z) + t • (b - z)) := by
      rw [← hyz]
      have := u10h_ray_spec hD hz hxz
      conv_lhs => rw [this]
      rw [add_sub_cancel_left]
    rw [u10h_cone, hβy, hxz', map_smul, map_add, map_smul, map_smul,
      u10h_linOfDet_left hab.ne', u10h_linOfDet_right hab.ne', add_comm]

/-- The cone map is positive PL on the fan triangulation. -/
theorem u10h_cone_isPositivePLOn {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    (z' : Plane) {V : Set Plane} {A : Plane → Plane → Prop} (hA : ∀ a b, A a b → u10h_Adj D z V a b)
    {β : Plane → Plane} (haff : ∀ a b, A a b → AffineOn β (segment ℝ a b))
    (hpos : ∀ a b, A a b → 0 < det (β a - z') (β b - z')) (K : Triangulation D)
    (hK : K.faces = u10h_fanFaces z A) : IsPositivePLOn (u10h_cone D z z' β) K := by
  intro T hT
  rw [hK] at hT
  obtain ⟨a, b, hab, hv⟩ := hT
  have hadj := hA a b hab
  have hc := u10h_carrier_of_v hv
  refine ⟨⟨u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z'),
    z' - u10h_linOfDet (a - z) (b - z) (β a - z') (β b - z') z, ?_⟩, ?_⟩
  · intro x hx
    rw [hc] at hx
    rw [u10h_cone_eq_on_fan hD hz z' hadj.2.2.1 hadj.2.2.2.1 (haff a b hab) hx, map_sub]; abel
  · have h0 : T.v 0 = z := by simp [hv]
    have h1 : T.v 1 = a := by simp [hv]
    have h2 : T.v 2 = b := by simp [hv]
    rw [h0, h1, h2, u10h_cone_center,
      u10h_cone_frontier hD hz z' β (hadj.2.2.2.1 (left_mem_segment ℝ a b)),
      u10h_cone_frontier hD hz z' β (hadj.2.2.2.1 (right_mem_segment ℝ a b))]
    exact hpos a b hab

/-- The cone map is injective on `D`. -/
theorem u10h_cone_injOn {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') (hinj : InjOn β (frontier D)) :
    InjOn (u10h_cone D z z' β) D := by
  have key : ∀ x, x ≠ z → u10h_cone D z z' β x ≠ z' := by
    intro x hx h
    have := u10h_rg_cone hD hD' hz hz' hβ hx
    rw [h, u10h_rg_self] at this
    exact u10h_rg_pos hD hz hx |>.ne this
  intro x₁ hx₁ x₂ hx₂ heq
  by_cases h₁ : x₁ = z
  · subst h₁
    by_contra h₂
    exact key x₂ (Ne.symm h₂) (heq.symm.trans (u10h_cone_center D x₁ z' β))
  by_cases h₂ : x₂ = z
  · subst h₂
    exact absurd (heq.trans (u10h_cone_center D x₂ z' β)) (key x₁ h₁)
  have hr : u10h_rg D z x₁ = u10h_rg D z x₂ := by
    rw [← u10h_rg_cone hD hD' hz hz' hβ h₁, ← u10h_rg_cone hD hD' hz hz' hβ h₂, heq]
  have hrpos := u10h_rg_pos hD hz h₁
  have hβeq : β (u10h_ray D z x₁) = β (u10h_ray D z x₂) := by
    unfold u10h_cone at heq
    rw [hr] at heq
    have := smul_right_injective Plane (hr ▸ hrpos).ne' (add_left_cancel heq)
    exact sub_left_injective this
  have hyeq := hinj (u10h_ray_mem_frontier hD hz h₁) (u10h_ray_mem_frontier hD hz h₂) hβeq
  rw [u10h_ray_spec hD hz h₁, u10h_ray_spec hD hz h₂, hr, hyeq]

/-- The cone map carries `D` onto `D'`. -/
theorem u10h_cone_image {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D') {z z' : Plane}
    (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : ∀ y ∈ frontier D, β y ∈ frontier D') (hsurj : frontier D' ⊆ β '' frontier D) :
    u10h_cone D z z' β '' D = D' := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxz : x = z
    · subst hxz; rw [u10h_cone_center]; exact interior_subset hz'
    · have hr0 := u10h_rg_nonneg D z x
      have hr1 := (u10h_rg_le_one_iff hD hz x).mpr hx
      have hy := u10h_frontier_subset hD' (hβ _ (u10h_ray_mem_frontier hD hz hxz))
      have := hD'.convex (interior_subset hz') hy (sub_nonneg.mpr hr1) hr0 (by ring)
      convert this using 1
      rw [u10h_cone, sub_smul, one_smul, smul_sub]; abel
  · intro x' hx'
    by_cases hx'z : x' = z'
    · exact ⟨z, interior_subset hz, by rw [u10h_cone_center, hx'z]⟩
    · obtain ⟨y, hy, hyβ⟩ := hsurj (u10h_ray_mem_frontier hD' hz' hx'z)
      have hr := u10h_rg_pos hD' hz' hx'z
      have hr1 := (u10h_rg_le_one_iff hD' hz' x').mpr hx'
      refine ⟨z + u10h_rg D' z' x' • (y - z), ?_, ?_⟩
      · rw [← u10h_rg_le_one_iff hD hz, u10h_rg_smul D z y hr.le, (u10h_rg_eq_one_iff hD hz y).mpr hy,
          mul_one]
        exact hr1
      · rw [u10h_cone_ray_formula hD hz z' β hy hr, hyβ]
        exact (u10h_ray_spec hD' hz' hx'z).symm

/-! ### the marks of a finite frontier cover -/

theorem u10h_gap {M : Set ℝ} (hM : M.Finite) (h0 : (0:ℝ) ∈ M) (h1 : (1:ℝ) ∈ M) {θ₀ : ℝ}
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
noncomputable def u10h_marks (S : Finset (Plane × Plane)) : Set Plane :=
  ↑(S.image Prod.fst ∪ S.image Prod.snd)

theorem u10h_marks_finite (S : Finset (Plane × Plane)) : (u10h_marks S).Finite := Finset.finite_toSet _

theorem u10h_marks_left {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.1 ∈ u10h_marks S := by
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inl ⟨p, hp, rfl⟩

theorem u10h_marks_right {S : Finset (Plane × Plane)} {p : Plane × Plane} (hp : p ∈ S) :
    p.2 ∈ u10h_marks S := by
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
  exact Or.inr ⟨p, hp, rfl⟩

theorem u10h_marks_subset_frontier {D : Set Plane} {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) : u10h_marks S ⊆ frontier D := by
  intro c hc
  simp only [u10h_marks, Finset.coe_union, Finset.coe_image, mem_union, mem_image,
    Finset.mem_coe] at hc
  rw [← hS]
  rcases hc with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, left_mem_segment ℝ _ _⟩
  · exact mem_iUnion₂.mpr ⟨p, hp, right_mem_segment ℝ _ _⟩

/-- The adjacent pairs actually used: adjacent marks lying in one segment of `S`. -/
def u10h_A (D : Set Plane) (z : Plane) (S : Finset (Plane × Plane)) (a b : Plane) : Prop :=
  u10h_Adj D z (u10h_marks S) a b ∧ ∃ p ∈ S, segment ℝ a b ⊆ segment ℝ p.1 p.2

theorem u10h_cover_of_segment {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {p : Plane × Plane}
    (hp : p ∈ S) (hne : p.1 ≠ p.2) {y : Plane} (hy : y ∈ segment ℝ p.1 p.2) :
    ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b := by
  have he : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hne.symm
  set f : ℝ → Plane := fun θ => p.1 + θ • (p.2 - p.1) with hf
  have hfinj : Function.Injective f := fun θ₁ θ₂ h => smul_left_injective ℝ he (add_left_cancel h)
  have hsegp : segment ℝ p.1 p.2 = f '' Icc 0 1 := segment_eq_image' ℝ p.1 p.2
  have hsegfr : segment ℝ p.1 p.2 ⊆ frontier D := hS ▸ subset_iUnion₂ (s := fun p _ => segment ℝ p.1 p.2) p hp
  set M : Set ℝ := f ⁻¹' u10h_marks S ∩ Icc 0 1 with hM
  have hMfin : M.Finite := ((u10h_marks_finite S).preimage hfinj.injOn).subset inter_subset_left
  have h0M : (0:ℝ) ∈ M := ⟨by simp [f, u10h_marks_left hp], by simp⟩
  have h1M : (1:ℝ) ∈ M := ⟨by simp [f, u10h_marks_right hp], by simp⟩
  rw [hsegp] at hy
  obtain ⟨θ₀, hθ₀, rfl⟩ := hy
  obtain ⟨θa, haM, θb, hbM, hlt, hle1, hle2, hgap⟩ := u10h_gap hMfin h0M h1M hθ₀
  have haV : f θa ∈ u10h_marks S := haM.1
  have hbV : f θb ∈ u10h_marks S := hbM.1
  have hap : f θa ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θa, haM.2, rfl⟩
  have hbp : f θb ∈ segment ℝ p.1 p.2 := hsegp ▸ ⟨θb, hbM.2, rfl⟩
  have hsub : segment ℝ (f θa) (f θb) ⊆ segment ℝ p.1 p.2 := (convex_segment _ _).segment_subset hap hbp
  have hsegab : segment ℝ (f θa) (f θb) ⊆ frontier D := hsub.trans hsegfr
  have hneab : f θa ≠ f θb := fun h => hlt.ne (hfinj h)
  have hcomb : ∀ lam : ℝ, f θa + lam • (f θb - f θa) = f (θa + lam * (θb - θa)) := by
    intro lam
    simp only [hf]
    ext <;> simp <;> ring
  have hnomark : ∀ c ∈ u10h_marks S, c ∉ openSegment ℝ (f θa) (f θb) := by
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
  have hdet := u10h_det_ne_zero_of_segment hD hz hneab hsegab
  rcases hdet.lt_or_gt with hneg | hpos
  · refine ⟨f θb, f θa, ⟨⟨hbV, haV, by rw [u10h_det_swap']; linarith, by rw [segment_symm]; exact hsegab,
      fun c hc => by rw [openSegment_symm]; exact hnomark c hc⟩, p, hp, by rw [segment_symm]; exact hsub⟩,
      by rw [segment_symm]; exact hyab⟩
  · exact ⟨f θa, f θb, ⟨⟨haV, hbV, hpos, hsegab, hnomark⟩, p, hp, hsub⟩, hyab⟩

/-! ### frontier points are not isolated; a nondegenerate segment through each -/

theorem u10h_ray_continuousAt {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {x : Plane} (hx : x ≠ z) : ContinuousAt (u10h_ray D z) x := by
  have : u10h_ray D z = fun x => z + (u10h_rg D z x)⁻¹ • (x - z) := rfl
  rw [this]
  exact continuousAt_const.add
    ((((u10h_rg_continuous hD hz).continuousAt).inv₀ (u10h_rg_pos hD hz hx).ne').smul
      (continuousAt_id.sub continuousAt_const))

theorem u10h_not_isolated {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {y : Plane} (hy : y ∈ frontier D) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ frontier D, w ≠ y ∧ dist w y < ε := by
  have hyz := u10h_frontier_ne hD hz hy
  have hu : y - z ≠ 0 := sub_ne_zero.mpr hyz
  set v : Plane := (-(y - z).2, (y - z).1) with hv
  have hdet : 0 < det (y - z) v := by
    have : det (y - z) v = (y - z).1 ^ 2 + (y - z).2 ^ 2 := by simp only [det, hv]; ring
    rw [this]
    rcases not_and_or.mp (fun hc : (y - z).1 = 0 ∧ (y - z).2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
      positivity
  set g : ℝ → Plane := fun t => u10h_ray D z (y + t • v) with hg
  have hg0 : g 0 = y := by simp [hg, u10h_ray_of_frontier hD hz hy]
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun t : ℝ => y + t • v) 0 := continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have h2 : ContinuousAt (u10h_ray D z) (y + (0:ℝ) • v) := by
      rw [zero_smul, add_zero]; exact u10h_ray_continuousAt hD hz hyz
    exact ContinuousAt.comp (f := fun t : ℝ => y + t • v) h2 h1
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hgc ε hε
  have hpt : y + (δ / 2) • v ≠ z := by
    intro h
    have : det (y - z) (y + (δ / 2) • v - z) = 0 := by rw [h, sub_self, u10h_det_zero_right]
    rw [add_sub_right_comm, u10h_det_add_right, u10h_det_self, u10h_det_smul_right] at this
    have : 0 < δ / 2 * det (y - z) v := by positivity
    linarith
  refine ⟨g (δ / 2), u10h_ray_mem_frontier hD hz hpt, ?_, ?_⟩
  · intro h
    have h1 : det (y - z) (g (δ / 2) - z) = 0 := by rw [h, u10h_det_self]
    have h2 : g (δ / 2) - z = (u10h_rg D z (y + (δ / 2) • v))⁻¹ • ((δ / 2) • v + (y - z)) := by
      simp only [hg, u10h_ray, add_sub_cancel_left]; congr 1; abel
    rw [h2, u10h_det_smul_right, u10h_det_add_right, u10h_det_smul_right, u10h_det_self, add_zero] at h1
    have hr := u10h_rg_pos hD hz hpt
    have : 0 < (u10h_rg D z (y + (δ / 2) • v))⁻¹ * (δ / 2 * det (y - z) v) := by positivity
    linarith
  · have := hδε (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rwa [hg0] at this

theorem u10h_isClosed_segment (a b : Plane) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image']
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem u10h_exists_nondeg {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ p ∈ S, p.1 ≠ p.2 ∧ y ∈ segment ℝ p.1 p.2 := by
  classical
  by_contra hcon
  have hdeg : ∀ p ∈ S, y ∈ segment ℝ p.1 p.2 → p.1 = p.2 := fun p hp hyp =>
    by_contra fun hne => hcon ⟨p, hp, hne, hyp⟩
  set U : Set Plane := ⋃ p ∈ S.filter (fun p => y ∉ segment ℝ p.1 p.2), segment ℝ p.1 p.2 with hU
  have hUc : IsClosed U := isClosed_biUnion_finset (fun p _ => u10h_isClosed_segment _ _)
  have hyU : y ∉ U := by
    intro h
    rw [hU, mem_iUnion₂] at h
    obtain ⟨p, hp, hyp⟩ := h
    exact (Finset.mem_filter.mp hp).2 hyp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUc.isOpen_compl y hyU
  obtain ⟨w, hw, hwy, hwd⟩ := u10h_not_isolated hD hz hy hε
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

theorem u10h_cover {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {y : Plane}
    (hy : y ∈ frontier D) : ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b := by
  obtain ⟨p, hp, hne, hyp⟩ := u10h_exists_nondeg hD hz hS hy
  exact u10h_cover_of_segment hD hz hS hp hne hyp

theorem u10h_det_neg_right (u v : Plane) : det u (-v) = -det u v := by
  simp only [det, Prod.fst_neg, Prod.snd_neg]; ring

theorem u10h_affine_combo {β : Plane → Plane} {M : Plane →ₗ[ℝ] Plane} {c a b : Plane}
    (hM : ∀ x ∈ segment ℝ a b, β x = M x + c) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    β (s • a + t • b) = s • β a + t • β b := by
  rw [hM _ ⟨s, t, hs, ht, hst, rfl⟩, hM a (left_mem_segment ℝ a b), hM b (right_mem_segment ℝ a b),
    map_add, map_smul, map_smul, smul_add, smul_add]
  have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
  conv_lhs => rw [hc]
  abel

theorem u10h_affine_image_segment {β : Plane → Plane} {a b : Plane} (h : AffineOn β (segment ℝ a b)) :
    β '' segment ℝ a b = segment ℝ (β a) (β b) := by
  obtain ⟨M, c, hM⟩ := h
  ext w
  constructor
  · rintro ⟨x, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, (u10h_affine_combo hM hs ht hst).symm⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, u10h_affine_combo hM hs ht hst⟩

theorem u10h_third_mark {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {S : Finset (Plane × Plane)} (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {a b : Plane}
    (hab : u10h_A D z S a b) : ∃ c ∈ u10h_marks S, c ≠ a ∧ c ≠ b := by
  have hadj := hab.1
  have hV := u10h_marks_subset_frontier hS
  have haz : a - z ≠ 0 := sub_ne_zero.mpr (u10h_frontier_ne hD hz (hV hadj.1))
  have hxz : z - (a - z) ≠ z := by
    intro h; apply haz; have := congrArg (fun w => z - w) h; simpa using this
  set y := u10h_ray D z (z - (a - z)) with hy_def
  have hy : y ∈ frontier D := u10h_ray_mem_frontier hD hz hxz
  have hyz' : y - z = (u10h_rg D z (z - (a - z)))⁻¹ • (-(a - z)) := by
    rw [hy_def, u10h_ray, add_sub_cancel_left]; congr 1; abel
  obtain ⟨c, d, hcd, hycd⟩ := u10h_cover hD hz hS hy
  have hynot : y ∉ segment ℝ a b := by
    rintro ⟨s, t, hs, ht, hst, hy'⟩
    have hyz : y - z = s • (a - z) + t • (b - z) := by rw [← hy', u10h_combo_sub hst]
    have h1 : det (a - z) (y - z) = t * det (a - z) (b - z) := by
      rw [hyz, u10h_det_comb_right, u10h_det_self]; ring
    have h2 : det (a - z) (y - z) = 0 := by
      rw [hyz', u10h_det_smul_right, u10h_det_neg_right, u10h_det_self]; ring
    have ht0 : t = 0 := (mul_eq_zero.mp (h1.symm.trans h2)).resolve_right hadj.2.2.1.ne'
    have hs1 : s = 1 := by linarith
    rw [ht0, hs1, one_smul, zero_smul, add_zero] at hy'
    rw [← hy', smul_neg] at hyz'
    have h3 : (1 + (u10h_rg D z (z - (a - z)))⁻¹) • (a - z) = 0 := by
      rw [add_smul, one_smul]
      nth_rewrite 1 [hyz']
      abel
    rcases smul_eq_zero.mp h3 with h | h
    · have := u10h_rg_pos hD hz hxz
      have : 0 < 1 + (u10h_rg D z (z - (a - z)))⁻¹ := by positivity
      linarith
    · exact haz h
  by_contra hcon
  have hall : ∀ c ∈ u10h_marks S, c = a ∨ c = b := by
    intro c hc
    by_contra h
    exact hcon ⟨c, hc, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  have hsub : segment ℝ c d ⊆ segment ℝ a b := by
    rcases hall c hcd.1.1 with rfl | rfl <;> rcases hall d hcd.1.2.1 with rfl | rfl
    · rw [segment_same]; exact singleton_subset_iff.mpr (left_mem_segment ℝ _ _)
    · exact le_rfl
    · rw [segment_symm]
    · rw [segment_same]; exact singleton_subset_iff.mpr (right_mem_segment ℝ _ _)
  exact hynot (hsub hycd)


theorem u10h_pos_of_preserves {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {S : Finset (Plane × Plane)}
    (hS : (⋃ p ∈ S, segment ℝ p.1 p.2) = frontier D) {β : Plane → Plane}
    (hβmap : ∀ y ∈ frontier D, β y ∈ frontier D') (hinj : InjOn β (frontier D))
    (haffS : ∀ p ∈ S, AffineOn β (segment ℝ p.1 p.2)) (hpos : PreservesCyclicPos D z z' β)
    {a b : Plane} (hab : u10h_A D z S a b) : 0 < det (β a - z') (β b - z') := by
  obtain ⟨hadj, p, hp, hsub⟩ := hab
  have hV := u10h_marks_subset_frontier hS
  have haff : AffineOn β (segment ℝ a b) := by
    obtain ⟨M, c, hM⟩ := haffS p hp
    exact ⟨M, c, fun x hx => hM x (hsub hx)⟩
  have himg := u10h_affine_image_segment haff
  have hseg' : segment ℝ (β a) (β b) ⊆ frontier D' := by
    rw [← himg]; rintro _ ⟨w, hw, rfl⟩; exact hβmap w (hadj.2.2.2.1 hw)
  have hane : a ≠ b := by
    intro h; have := hadj.2.2.1; rw [h, u10h_det_self] at this; exact lt_irrefl _ this
  have hane' : β a ≠ β b := fun h => hane (hinj (hV hadj.1) (hV hadj.2.1) h)
  have hdet' := u10h_det_ne_zero_of_segment hD' hz' hane' hseg'
  rcases hdet'.lt_or_gt with hneg | hpos'
  · exfalso
    obtain ⟨c, hcV, hca, hcb⟩ := u10h_third_mark hD hz hS ⟨hadj, p, hp, hsub⟩
    have hcyc : CyclicPos z a b c := by
      rcases u10h_adj_trichotomy hD hz hV hadj hcV with h | h | h | h
      · exact absurd h hca
      · exact absurd h hcb
      · exact Or.inr (Or.inr ⟨by rw [u10h_det_swap']; linarith, hadj.2.2.1⟩)
      · exact Or.inl ⟨hadj.2.2.1, by rw [u10h_det_swap']; linarith⟩
    have hcyc' := hpos a (hV hadj.1) b (hV hadj.2.1) c (hV hcV) hcyc
    have hba' : 0 < det (β b - z') (β a - z') := by rw [u10h_det_swap']; linarith
    rcases hcyc' with ⟨h1, -⟩ | ⟨h1, h2⟩ | ⟨-, h2⟩
    · linarith
    · have hsegba : segment ℝ (β b) (β a) ⊆ frontier D' := by rw [segment_symm]; exact hseg'
      have hmem := u10h_frontier_mem_segment hD' hz' hba' hsegba (hβmap c (hV hcV)) h1.le h2.le
      rw [segment_symm, ← himg] at hmem
      obtain ⟨w, hw, hwc⟩ := hmem
      have hwc' : w = c := hinj (hadj.2.2.2.1 hw) (hV hcV) hwc
      subst hwc'
      rcases u10h_mem_segment_cases hw with h | h | h
      · exact hca h
      · exact hcb h
      · exact hadj.2.2.2.2 w hcV h
    · linarith
  · exact hpos'

/-- U10 (sm-3:535-537, the fan extension on convex models): a finite positive PL homeomorphism
between the boundaries of two convex discs, preserving the cyclic order around interior points
`z ↦ z'`, extends to a positive PL homeomorphism of the discs (cone from `z` to `z'`). -/
theorem U10_fan_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {z z' : Plane} (hz : z ∈ interior D) (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβ : IsHomeoOnto (frontier D) (frontier D') β) (hpl : IsFinitePLOnFrontier D β)
    (hpos : PreservesCyclicPos D z z' β) :
    ∃ (K : Triangulation D) (F : Plane → Plane), IsPositivePLOn F K ∧ IsHomeoOnto D D' F ∧
      ∀ x ∈ frontier D, F x = β x := by
  obtain ⟨e, he⟩ := hβ
  have hβmap : ∀ y ∈ frontier D, β y ∈ frontier D' := by
    intro y hy; have := (e ⟨y, hy⟩).2; rwa [he] at this
  have hinj : InjOn β (frontier D) := by
    intro y₁ h₁ y₂ h₂ heq
    have : e ⟨y₁, h₁⟩ = e ⟨y₂, h₂⟩ := Subtype.ext (by rw [he, he]; exact heq)
    exact congrArg Subtype.val (e.injective this)
  have hsurj : frontier D' ⊆ β '' frontier D := by
    intro w hw
    refine ⟨e.symm ⟨w, hw⟩, (e.symm ⟨w, hw⟩).2, ?_⟩
    rw [← he]; simp
  obtain ⟨S, hS, haffS⟩ := hpl
  have hV := u10h_marks_subset_frontier hS
  have hA : ∀ a b, u10h_A D z S a b → u10h_Adj D z (u10h_marks S) a b := fun a b h => h.1
  have hcov : ∀ y ∈ frontier D, ∃ a b, u10h_A D z S a b ∧ y ∈ segment ℝ a b :=
    fun y hy => u10h_cover hD hz hS hy
  obtain ⟨K, hK⟩ := u10h_fan_triangulation hD hz (u10h_marks_finite S) hV hA hcov
  have haff : ∀ a b, u10h_A D z S a b → AffineOn β (segment ℝ a b) := by
    rintro a b ⟨-, p, hp, hsub⟩
    obtain ⟨M, c, hM⟩ := haffS p hp
    exact ⟨M, c, fun x hx => hM x (hsub hx)⟩
  have hposdet : ∀ a b, u10h_A D z S a b → 0 < det (β a - z') (β b - z') :=
    fun a b h => u10h_pos_of_preserves hD hD' hz hz' hS hβmap hinj haffS hpos h
  have hPL := u10h_cone_isPositivePLOn hD hz z' hA haff hposdet K hK
  refine ⟨K, u10h_cone D z z' β, hPL, ?_, fun x hx => u10h_cone_frontier hD hz z' β hx⟩
  have := U2_isHomeoOnto_of_isPositivePLOn K hPL (u10h_cone_injOn hD hD' hz hz' hβmap hinj)
  rwa [u10h_cone_image hD hD' hz hz' hβmap hsurj] at this

/-! #### U10 helpers for `U10_boundary_map_of_lift` (circle in the closure, periodicity, the lift) -/

theorem u10h_coe_traversal_mem_circle [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    ((traversal P x : Plane) : Sphere) ∈ sphereCircle P :=
  ⟨traversal P x, by rw [← U4_range_traversal P]; exact mem_range_self x, rfl⟩

/-! ### CyclicPos: rotation, antisymmetry, totality on a convex frontier -/

theorem u10h_cyclicPos_rotate {z a b c : Plane} (h : CyclicPos z a b c) : CyclicPos z b c a := by
  unfold CyclicPos at *; tauto

theorem u10h_cyclicPos_antisymm {z a b c : Plane} (h1 : CyclicPos z a b c) (h2 : CyclicPos z a c b) :
    False := by
  unfold CyclicPos at *
  have e1 := u10h_det_swap' (a - z) (b - z)
  have e2 := u10h_det_swap' (b - z) (c - z)
  have e3 := u10h_det_swap' (c - z) (a - z)
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem u10h_cyclicPos_ne {z a b c : Plane} (h : CyclicPos z a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> unfold CyclicPos at h
  · have := u10h_det_self (a - z); have := u10h_det_swap' (a - z) (c - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u10h_det_self (b - z); have := u10h_det_swap' (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have := u10h_det_self (a - z); have := u10h_det_swap' (a - z) (b - z)
    rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem u10h_eq_of_ray {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p r : Plane} (hp : p ∈ frontier D) (hr : r ∈ frontier D) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : r - z = μ • (p - z)) : r = p := by
  have hr' : r = z + μ • (p - z) := by rw [← h]; abel
  have h1 := (u10h_rg_eq_one_iff hD hz r).mpr hr
  rw [hr', u10h_rg_smul D z p hμ, (u10h_rg_eq_one_iff hD hz p).mpr hp, mul_one] at h1
  rw [hr', h1, one_smul, add_sub_cancel]

theorem u10h_antipodal {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hne : q ≠ p)
    (h0 : det (p - z) (q - z) = 0) : ∃ lam : ℝ, 0 < lam ∧ q - z = -(lam • (p - z)) := by
  obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u10h_frontier_ne hD hz hp)) h0
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · exact absurd (u10h_eq_of_ray hD hz hp hq hμ0 hμ) hne
  · exact ⟨-μ, by linarith, by rw [hμ, neg_smul, neg_neg]⟩

theorem u10h_det_prod_pos {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hqp : q ≠ p)
    (hrp : r ≠ p) (hrq : r ≠ q) (h0 : det (p - z) (q - z) = 0) :
    0 < det (q - z) (r - z) * det (r - z) (p - z) := by
  obtain ⟨lam, hlam, hq'⟩ := u10h_antipodal hD hz hp hq hqp h0
  have e : det (q - z) (r - z) = lam * det (r - z) (p - z) := by
    rw [hq', ← neg_smul, u10h_det_smul_left', u10h_det_swap' (p - z) (r - z)]; ring
  rw [e, mul_assoc]
  have hne : det (r - z) (p - z) ≠ 0 := by
    intro h
    have h' : det (p - z) (r - z) = 0 := by rw [u10h_det_swap']; linarith
    obtain ⟨μ, hμ⟩ := u10h_parallel_of_det_eq_zero (sub_ne_zero.mpr (u10h_frontier_ne hD hz hp)) h'
    rcases le_or_gt 0 μ with hμ0 | hμ0
    · exact hrp (u10h_eq_of_ray hD hz hp hr hμ0 hμ)
    · apply hrq
      refine u10h_eq_of_ray hD hz hq hr (μ := -μ / lam) (div_nonneg (by linarith) hlam.le) ?_
      rw [hμ, hq', smul_neg, smul_smul]
      have : -μ / lam * lam = -μ := div_mul_cancel₀ _ hlam.ne'
      rw [this, neg_smul, neg_neg]
  have : 0 < det (r - z) (p - z) * det (r - z) (p - z) := mul_self_pos.mpr hne
  positivity

theorem u10h_cyclicPos_total {D : Set Plane} (hD : Link.IsDisc D) {z : Plane} (hz : z ∈ interior D)
    {p q r : Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hr : r ∈ frontier D) (hpq : p ≠ q)
    (hqr : q ≠ r) (hpr : p ≠ r) : CyclicPos z p q r ∨ CyclicPos z p r q := by
  have e1 := u10h_det_swap' (q - z) (p - z)
  have e2 := u10h_det_swap' (r - z) (q - z)
  have e3 := u10h_det_swap' (p - z) (r - z)
  unfold CyclicPos
  by_cases hA : det (p - z) (q - z) = 0
  · have := u10h_det_prod_pos hD hz hp hq hr hpq.symm hpr.symm hqr.symm hA
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hB, hC⟩ | ⟨hB, hC⟩
    · exact Or.inl (Or.inr (Or.inl ⟨hB, hC⟩))
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  by_cases hB : det (q - z) (r - z) = 0
  · have := u10h_det_prod_pos hD hz hq hr hp hqr.symm hpq hpr hB
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hC, hA'⟩ | ⟨hC, hA'⟩
    · exact Or.inl (Or.inr (Or.inr ⟨hC, hA'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
  by_cases hC : det (r - z) (p - z) = 0
  · have := u10h_det_prod_pos hD hz hr hp hq hpr hqr hpq.symm hC
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos this with ⟨hA', hB'⟩ | ⟨hA', hB'⟩
    · exact Or.inl (Or.inl ⟨hA', hB'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
  rcases lt_or_gt_of_ne hA with hA | hA <;> rcases lt_or_gt_of_ne hB with hB | hB <;>
    rcases lt_or_gt_of_ne hC with hC | hC <;>
    first
    | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

/-! ### abstract refinement of finite interval covers -/

/-- `g : ℝ → Plane` is affine on `I`. -/
def u10h_AffOn (g : ℝ → Plane) (I : Set ℝ) : Prop := ∃ p u : Plane, ∀ t ∈ I, g t = p + t • u

theorem u10h_AffOn_mono {g : ℝ → Plane} {I J : Set ℝ} (h : u10h_AffOn g I) (hJ : J ⊆ I) :
    u10h_AffOn g J := by
  obtain ⟨p, u, h⟩ := h; exact ⟨p, u, fun t ht => h t (hJ ht)⟩

theorem u10h_gap' {B : Set ℝ} (hB : B.Finite) {lo hi : ℝ} (hlo : lo ∈ B) (hhi : hi ∈ B)
    (hlh : lo < hi) {t : ℝ} (ht : t ∈ Icc lo hi) :
    ∃ b ∈ B, ∃ b' ∈ B, b < b' ∧ b ≤ t ∧ t ≤ b' ∧ ∀ a ∈ B, b < a → a < b' → False := by
  classical
  rcases ht.2.lt_or_eq with hlt | heq
  · set Fa := hB.toFinset.filter (fun θ => θ ≤ t) with hFa
    set Fb := hB.toFinset.filter (fun θ => t < θ) with hFb
    have hane : Fa.Nonempty := ⟨lo, by simp [hFa, hlo, ht.1]⟩
    have hbne : Fb.Nonempty := ⟨hi, by simp [hFb, hhi, hlt]⟩
    have hamem := Finset.max'_mem Fa hane
    have hbmem := Finset.min'_mem Fb hbne
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    simp only [hFb, Finset.mem_filter, Set.Finite.mem_toFinset] at hbmem
    refine ⟨_, hamem.1, _, hbmem.1, by linarith [hamem.2, hbmem.2], hamem.2, hbmem.2.le, ?_⟩
    intro θ hθM hlo' hhi'
    rcases le_or_gt θ t with h | h
    · have hmem : θ ∈ Fa := by simp [hFa, hθM, h]
      exact absurd hlo' (not_lt.mpr (Finset.le_max' Fa θ hmem))
    · have hmem : θ ∈ Fb := by simp [hFb, hθM, h]
      exact absurd hhi' (not_lt.mpr (Finset.min'_le Fb θ hmem))
  · subst heq
    set Fa := hB.toFinset.filter (fun θ => θ < t) with hFa
    have hane : Fa.Nonempty := ⟨lo, by simp [hFa, hlo, hlh]⟩
    have hamem := Finset.max'_mem Fa hane
    simp only [hFa, Finset.mem_filter, Set.Finite.mem_toFinset] at hamem
    refine ⟨_, hamem.1, t, hhi, hamem.2, hamem.2.le, le_rfl, ?_⟩
    intro θ hθM hlo' hhi'
    have hmem : θ ∈ Fa := by simp [hFa, hθM, hhi']
    exact absurd hlo' (not_lt.mpr (Finset.le_max' Fa θ hmem))

/-- Midpoint argument: an interval with no breakpoint strictly inside lies in one covering piece. -/
theorem u10h_subset_piece {B : Set ℝ} {C : Set (ℝ × ℝ)} (hCB : ∀ c ∈ C, c.1 ∈ B ∧ c.2 ∈ B) {lo hi : ℝ}
    (hcov : ∀ t ∈ Icc lo hi, ∃ c ∈ C, t ∈ Icc c.1 c.2) {b b' : ℝ} (hb : lo ≤ b) (hb' : b' ≤ hi)
    (hlt : b < b') (hgap : ∀ a ∈ B, b < a → a < b' → False) : ∃ c ∈ C, Icc b b' ⊆ Icc c.1 c.2 := by
  obtain ⟨c, hc, hm⟩ := hcov ((b + b') / 2) ⟨by linarith, by linarith⟩
  refine ⟨c, hc, Icc_subset_Icc ?_ ?_⟩
  · rcases le_or_gt c.1 b with h | h
    · exact h
    · exact absurd (hgap c.1 (hCB c hc).1 h (by linarith [hm.1])) id
  · rcases le_or_gt b' c.2 with h | h
    · exact h
    · exact absurd (hgap c.2 (hCB c hc).2 (by linarith [hm.2]) h) id

/-- The linear map `w ↦ (⟪w, u⟫ / ⟪u, u⟫) • u''`. -/
noncomputable def u10h_dotLin (u u'' : Plane) : Plane →ₗ[ℝ] Plane where
  toFun w := (planeDot w u / planeDot u u) • u''
  map_add' v w := by
    have : planeDot (v + w) u = planeDot v u + planeDot w u := by
      simp only [planeDot, Prod.fst_add, Prod.snd_add]; ring
    rw [this, add_div, add_smul]
  map_smul' c w := by
    have : planeDot (c • w) u = c * planeDot w u := by
      simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    simp only [RingHom.id_apply]
    rw [this, mul_div_assoc, mul_smul]

theorem u10h_planeDot_self_pos {u : Plane} (hu : u ≠ 0) : 0 < planeDot u u := by
  have : planeDot u u = u.1 ^ 2 + u.2 ^ 2 := by simp only [planeDot]; ring
  rw [this]
  rcases not_and_or.mp (fun hc : u.1 = 0 ∧ u.2 = 0 => hu (Prod.ext hc.1 hc.2)) with h1 | h2 <;>
    positivity

theorem u10h_planeDot_add_smul (p u : Plane) (t : ℝ) :
    planeDot (p + t • u) u = planeDot p u + t * planeDot u u := by
  simp only [planeDot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- A map that is affine in the parameter of an affinely parametrised segment is affine on it. -/
theorem u10h_affineOn_of_param {β : Plane → Plane} {c : ℝ → Plane} {b b' : ℝ} {p u p'' u'' : Plane}
    (hc : ∀ t ∈ Icc b b', c t = p + t • u) (hβ : ∀ t ∈ Icc b b', β (c t) = p'' + t • u'')
    (hbb : b ≤ b') : AffineOn β (c '' Icc b b') := by
  by_cases hu : u = 0
  · refine ⟨0, p'' + b • u'', ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have : c t = c b := by rw [hc t ht, hc b ⟨le_rfl, hbb⟩, hu, smul_zero, smul_zero]
    rw [this, hβ b ⟨le_rfl, hbb⟩, LinearMap.zero_apply, zero_add]
  · have hpos := u10h_planeDot_self_pos hu
    refine ⟨u10h_dotLin u u'', p'' - (planeDot p u / planeDot u u) • u'', ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [hβ t ht]
    have : u10h_dotLin u u'' (c t) = (planeDot p u / planeDot u u) • u'' + t • u'' := by
      change (planeDot (c t) u / planeDot u u) • u'' = _
      rw [hc t ht, u10h_planeDot_add_smul, add_div, mul_div_assoc, div_self hpos.ne', mul_one, add_smul]
    rw [this]; abel

theorem u10h_image_Icc_eq_segment {c : ℝ → Plane} {b b' : ℝ} {p u : Plane}
    (hc : ∀ t ∈ Icc b b', c t = p + t • u) (hbb : b ≤ b') :
    c '' Icc b b' = segment ℝ (c b) (c b') := by
  rw [segment_eq_image']
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases hbb.lt_or_eq with hlt | heq
    · refine ⟨(t - b) / (b' - b), ⟨div_nonneg (by linarith [ht.1]) (by linarith),
        div_le_one_of_le₀ (by linarith [ht.2]) (by linarith)⟩, ?_⟩
      rw [hc t ht, hc b ⟨le_rfl, hbb⟩, hc b' ⟨hbb, le_rfl⟩]
      have hne : b' - b ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    · subst heq
      have : t = b := le_antisymm ht.2 ht.1
      subst this
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨b + θ * (b' - b), ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, ?_⟩
    rw [hc _ ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, hc b ⟨le_rfl, hbb⟩, hc b' ⟨hbb, le_rfl⟩]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; ring

theorem u10h_circle_subset_closure [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) {L : ℝ} (hL : InsideModel L P) : sphereCircle P ⊆ closure (regionOf P s) := by
  obtain ⟨A⟩ := U6_exists_ambientParam hn P hP hL
  have hcl : IsClosed A.T₀.carrier := by
    show IsClosed (convexHull ℝ (range A.T₀.v))
    exact ((Set.finite_range A.T₀.v).isCompact_convexHull ℝ).isClosed
  cases s with
  | inner =>
    show sphereCircle P ⊆ closure (interiorRegion P)
    rw [U7_closure_interiorRegion_eq hn P hP A]
    rintro _ ⟨w, hw, rfl⟩
    rw [← A.boundary] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨A.H v, ⟨v, hcl.frontier_subset hv, rfl⟩, rfl⟩
  | outer =>
    show sphereCircle P ⊆ closure (exteriorRegion P)
    rw [U8_closure_exteriorRegion_eq hn P hP A]
    rintro _ ⟨w, hw, rfl⟩ ⟨_, ⟨v, hv, rfl⟩, hvw⟩
    rw [← A.boundary] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have : v = u := A.H.injective (OnePoint.coe_eq_coe.mp hvw)
    subst this
    exact hu.2 hv

theorem u10h_traversal_add_int_mul [NeZero n] (P : LabelledTuple n) (x : ℝ) (m : ℤ) :
    traversal P (x + m * n) = traversal P x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, traversal_add_nat, ih]
  | pred k ih =>
    push_cast at ih ⊢
    have := traversal_add_nat P (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring] at this
    rw [← this, ih]

theorem u10h_lift_shift_same {n n' : ℕ} {φ : ℝ → ℝ} (h : ∀ x, φ (x + n) = φ x + n') (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, h, ih]; ring
  | pred k ih =>
    push_cast at ih ⊢
    have := h (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring, ih] at this
    linarith

theorem u10h_lift_shift_opp {n n' : ℕ} {φ : ℝ → ℝ} (h : ∀ x, φ (x + n) = φ x - n') (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x - m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show x + ((k : ℝ) + 1) * n = (x + k * n) + n by ring, h, ih]; ring
  | pred k ih =>
    push_cast at ih ⊢
    have := h (x + (-(k : ℝ) - 1) * n)
    rw [show x + (-(k : ℝ) - 1) * n + n = x + -(k : ℝ) * n by ring, ih] at this
    linarith

theorem u10h_isHomeoOnto_injOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : InjOn f S := by
  obtain ⟨e, he⟩ := h
  intro x hx y hy hxy
  have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (by rw [he, he]; exact hxy)
  exact congrArg Subtype.val (e.injective this)

/-- Two parameters give the same point of the parametrised frontier iff they differ by a multiple
of the period. -/
theorem u10h_param_eq_iff [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P) {s : Side}
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hBS : sphereCircle P ⊆ closure (regionOf P s)) (x y : ℝ) :
    f ((traversal P x : Plane) : Sphere) = f ((traversal P y : Plane) : Sphere) ↔
      ∃ m : ℤ, y = x + m * n := by
  constructor
  · intro h
    have h1 := u10h_isHomeoOnto_injOn hf (hBS (u10h_coe_traversal_mem_circle P x))
      (hBS (u10h_coe_traversal_mem_circle P y)) h
    exact hP.traversal_injective hn (OnePoint.coe_eq_coe.mp h1)
  · rintro ⟨m, rfl⟩
    rw [u10h_traversal_add_int_mul]

theorem u10h_reduce {n : ℕ} (hn : 0 < n) (x : ℝ) : ∃ x₀ ∈ Ico (0:ℝ) n, ∃ m : ℤ, x = x₀ + m * n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨x - ⌊x / n⌋ * n, ⟨?_, ?_⟩, ⌊x / n⌋, by ring⟩
  · have := Int.floor_le (x / n)
    have : (⌊x / n⌋ : ℝ) * n ≤ x / n * n := by nlinarith
    rw [div_mul_cancel₀ _ hn'.ne'] at this
    linarith
  · have := Int.lt_floor_add_one (x / n)
    have : x / n * n < ((⌊x / n⌋ : ℝ) + 1) * n := by nlinarith
    rw [div_mul_cancel₀ _ hn'.ne'] at this
    linarith

/-- A positive boundary lift is onto. -/
theorem u10h_lift_surj [NeZero n] {n' : ℕ} [NeZero n'] {P : LabelledTuple n} {s : Side}
    {P' : LabelledTuple n'} {s' : Side} {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    Function.Surjective φ := by
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  intro v
  by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨-, hper⟩ := hφ.same hsame
    obtain ⟨m₁, hm₁⟩ := exists_int_lt ((v - φ 0) / n')
    obtain ⟨m₂, hm₂⟩ := exists_int_gt ((v - φ 0) / n')
    have h1 : φ (m₁ * n) ≤ v := by
      have := u10h_lift_shift_same hper 0 m₁; rw [zero_add] at this; rw [this]
      have : (m₁ : ℝ) * n' < v - φ 0 := by rwa [lt_div_iff₀ hn'] at hm₁
      linarith
    have h2 : v ≤ φ (m₂ * n) := by
      have := u10h_lift_shift_same hper 0 m₂; rw [zero_add] at this; rw [this]
      have : v - φ 0 < (m₂ : ℝ) * n' := by rwa [div_lt_iff₀ hn'] at hm₂
      linarith
    have hm : (m₁ : ℝ) * n ≤ m₂ * n := by
      have : (m₁ : ℝ) < m₂ := by linarith
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc hm hφ.continuous.continuousOn ⟨h1, h2⟩
    exact ⟨x, hx⟩
  · obtain ⟨-, hper⟩ := hφ.opposite hsame
    obtain ⟨m₁, hm₁⟩ := exists_int_lt ((φ 0 - v) / n')
    obtain ⟨m₂, hm₂⟩ := exists_int_gt ((φ 0 - v) / n')
    have h1 : v ≤ φ (m₁ * n) := by
      have := u10h_lift_shift_opp hper 0 m₁; rw [zero_add] at this; rw [this]
      have : (m₁ : ℝ) * n' < φ 0 - v := by rwa [lt_div_iff₀ hn'] at hm₁
      linarith
    have h2 : φ (m₂ * n) ≤ v := by
      have := u10h_lift_shift_opp hper 0 m₂; rw [zero_add] at this; rw [this]
      have : φ 0 - v < (m₂ : ℝ) * n' := by rwa [div_lt_iff₀ hn'] at hm₂
      linarith
    have hm : (m₁ : ℝ) * n ≤ m₂ * n := by
      have : (m₁ : ℝ) < m₂ := by linarith
      nlinarith
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc' hm hφ.continuous.continuousOn ⟨h2, h1⟩
    exact ⟨x, hx⟩

/-- The parameter set of edge piece `[k, k+1]` inside a face `T`. -/
def u10h_J [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) : Set ℝ :=
  {t | t ∈ Icc (k : ℝ) (k + 1) ∧ traversal P t ∈ T.carrier}

theorem u10h_J_ordConnected [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) :
    (u10h_J P k T).OrdConnected := by
  refine ⟨fun t₁ h₁ t₂ h₂ t ht => ⟨⟨by linarith [h₁.1.1, ht.1], by linarith [h₂.1.2, ht.2]⟩, ?_⟩⟩
  have hconv : Convex ℝ T.carrier := convex_convexHull ℝ _
  have e1 := ea_traversal_eq_on_Icc P k h₁.1.1 h₁.1.2
  have e2 := ea_traversal_eq_on_Icc P k h₂.1.1 h₂.1.2
  have e := ea_traversal_eq_on_Icc P k (by linarith [h₁.1.1, ht.1] : (k:ℝ) ≤ t)
    (by linarith [h₂.1.2, ht.2] : t ≤ k + 1)
  rcases (ht.1.trans ht.2).lt_or_eq with hlt | heq
  · have hmem : traversal P t ∈ segment ℝ (traversal P t₁) (traversal P t₂) := by
      rw [segment_eq_image']
      refine ⟨(t - t₁) / (t₂ - t₁), ⟨div_nonneg (by linarith [ht.1]) (by linarith),
        div_le_one_of_le₀ (by linarith [ht.2]) (by linarith)⟩, ?_⟩
      rw [e1, e2, e]
      have hne : t₂ - t₁ ≠ 0 := by linarith
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; field_simp; ring
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; field_simp; ring
    exact hconv.segment_subset h₁.2 h₂.2 hmem
  · have : t = t₁ := le_antisymm (heq ▸ ht.2) ht.1
    rw [this]; exact h₁.2

theorem u10h_J_isCompact [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle) :
    IsCompact (u10h_J P k T) := by
  have hT : IsClosed T.carrier := by
    show IsClosed (convexHull ℝ (range T.v))
    exact ((Set.finite_range T.v).isCompact_convexHull ℝ).isClosed
  exact isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (hT.preimage (continuous_traversal P)))
    (fun t ht => ht.1)

theorem u10h_J_eq_Icc [NeZero n] (P : LabelledTuple n) (k : ℤ) (T : Triangle)
    (hne : (u10h_J P k T).Nonempty) :
    u10h_J P k T = Icc (sInf (u10h_J P k T)) (sSup (u10h_J P k T)) :=
  eq_Icc_of_connected_compact ⟨hne, (u10h_J_ordConnected P k T).isPreconnected⟩ (u10h_J_isCompact P k T)

theorem u10h_modelChart_false (L : ℝ) (x : Plane) : modelChart L false x = (x : Sphere) := rfl

/-- On a piece, `f ∘ ↑ ∘ traversal` is affine in the parameter. -/
theorem u10h_affOn_J [NeZero n] (P : LabelledTuple n) {L : ℝ} {S : Set Sphere} {f : Sphere → Plane}
    {K : Triangulation (chartPart L false S)} (hK : IsPositivePLOn (f ∘ modelChart L false) K)
    (k : ℤ) {T : Triangle} (hT : T ∈ K.faces) :
    u10h_AffOn (fun t => f ((traversal P t : Plane) : Sphere)) (u10h_J P k T) := by
  obtain ⟨M, b₀, hM⟩ := (hK T hT).1
  refine ⟨M (P (k : ZMod n)) - (k : ℝ) • M (edge P (k : ZMod n)) + b₀, M (edge P (k : ZMod n)), ?_⟩
  intro t ht
  have := hM _ ht.2
  simp only [Function.comp, u10h_modelChart_false] at this
  show f ((traversal P t : Plane) : Sphere) = _
  rw [this, ea_traversal_eq_on_Icc P k ht.1.1 ht.1.2, map_add, map_smul]
  simp only [sub_smul]
  abel

theorem u10h_supNorm_combo {x y : Plane} {L a b : ℝ} (hx : supNorm x ≤ L) (hy : supNorm y ≤ L)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : supNorm (a • x + b • y) ≤ L := by
  have h1 : |x.1| ≤ L := le_trans (le_max_left _ _) hx
  have h2 : |x.2| ≤ L := le_trans (le_max_right _ _) hx
  have h3 : |y.1| ≤ L := le_trans (le_max_left _ _) hy
  have h4 : |y.2| ≤ L := le_trans (le_max_right _ _) hy
  unfold supNorm
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  apply max_le
  · calc |a * x.1 + b * y.1| ≤ |a * x.1| + |b * y.1| := abs_add_le _ _
      _ = a * |x.1| + b * |y.1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * L + b * L := by gcongr
      _ = L := by rw [← add_mul, hab, one_mul]
  · calc |a * x.2 + b * y.2| ≤ |a * x.2| + |b * y.2| := abs_add_le _ _
      _ = a * |x.2| + b * |y.2| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * L + b * L := by gcongr
      _ = L := by rw [← add_mul, hab, one_mul]

/-- Every traversal point lies in the plane chart part of the closed region. -/
theorem u10h_traversal_mem_chartPart [NeZero n] (P : LabelledTuple n) {L : ℝ} (hL : InsideModel L P)
    {S : Set Sphere} (hBS : sphereCircle P ⊆ S) (t : ℝ) :
    traversal P t ∈ chartPart L false S := by
  refine ⟨?_, hBS (u10h_coe_traversal_mem_circle P t)⟩
  show supNorm (traversal P t) ≤ L
  have h0 : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have h1 : t ≤ ⌊t⌋ + 1 := (Int.lt_floor_add_one t).le
  rw [ea_traversal_eq_on_Icc P ⌊t⌋ h0 h1, edge]
  have : P (⌊t⌋ : ZMod n) + (t - ⌊t⌋) • (P ((⌊t⌋ : ZMod n) + 1) - P (⌊t⌋ : ZMod n)) =
      (1 - (t - ⌊t⌋)) • P (⌊t⌋ : ZMod n) + (t - ⌊t⌋) • P ((⌊t⌋ : ZMod n) + 1) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [this]
  exact u10h_supNorm_combo (hL _).le (hL _).le (by linarith) (by linarith) (by ring)

/-- The P-side pieces: one parameter interval per edge `k < n` and face `T` meeting it. -/
def u10h_pieceSet [NeZero n] (P : LabelledTuple n) (K : Set Triangle) : Set (ℝ × ℝ) :=
  {c | ∃ k : ℕ, k < n ∧ ∃ T ∈ K, (u10h_J P k T).Nonempty ∧ c = (sInf (u10h_J P k T), sSup (u10h_J P k T))}

theorem u10h_pieceSet_finite [NeZero n] (P : LabelledTuple n) {K : Set Triangle} (hK : K.Finite) :
    (u10h_pieceSet P K).Finite := by
  have : u10h_pieceSet P K ⊆
      (fun q : ℕ × Triangle => (sInf (u10h_J P q.1 q.2), sSup (u10h_J P q.1 q.2))) ''
        ({k | k < n} ×ˢ K) := by
    rintro c ⟨k, hk, T, hT, -, rfl⟩
    exact ⟨(k, T), ⟨hk, hT⟩, rfl⟩
  exact ((Set.finite_lt_nat n).prod hK).image _ |>.subset this

theorem u10h_pieceSet_affOn [NeZero n] (P : LabelledTuple n) {L : ℝ} {S : Set Sphere}
    {f : Sphere → Plane} {K : Triangulation (chartPart L false S)}
    (hK : IsPositivePLOn (f ∘ modelChart L false) K) {c : ℝ × ℝ} (hc : c ∈ u10h_pieceSet P K.faces) :
    u10h_AffOn (fun t => f ((traversal P t : Plane) : Sphere)) (Icc c.1 c.2) := by
  obtain ⟨k, -, T, hT, hne, rfl⟩ := hc
  have := u10h_affOn_J P hK k hT
  rwa [u10h_J_eq_Icc P k T hne] at this

theorem u10h_pieceSet_cover [NeZero n] (P : LabelledTuple n) {L : ℝ} (hL : InsideModel L P)
    {S : Set Sphere} (hBS : sphereCircle P ⊆ S) (K : Triangulation (chartPart L false S)) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) n) : ∃ c ∈ u10h_pieceSet P K.faces, t ∈ Icc c.1 c.2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- choose the edge index
  obtain ⟨k, hk, hkt⟩ : ∃ k : ℕ, k < n ∧ t ∈ Icc (k : ℝ) (k + 1) := by
    rcases ht.2.lt_or_eq with hlt | heq
    · refine ⟨⌊t⌋.toNat, ?_, ?_⟩
      · have h1 : ⌊t⌋ < n := Int.floor_lt.mpr hlt
        have h2 : (0:ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
        omega
      · have h2 : (0:ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
        have : ((⌊t⌋.toNat : ℤ) : ℝ) = (⌊t⌋ : ℝ) := by rw [Int.toNat_of_nonneg h2]
        push_cast at this
        rw [this]
        exact ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩
    · refine ⟨n - 1, by omega, ?_⟩
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this, heq]
      constructor <;> linarith
  have hmem := u10h_traversal_mem_chartPart P hL hBS t
  rw [← K.cover, mem_iUnion₂] at hmem
  obtain ⟨T, hT, hTt⟩ := hmem
  have hJ : t ∈ u10h_J P k T := ⟨by exact_mod_cast hkt, hTt⟩
  refine ⟨(sInf (u10h_J P k T), sSup (u10h_J P k T)), ⟨k, hk, T, hT, ⟨t, hJ⟩, rfl⟩, ?_⟩
  have := u10h_J_eq_Icc P k T ⟨t, hJ⟩
  rw [← this]; exact hJ

/-- The P′-side pieces pulled back through `φ`: parameters `t ∈ [lo, hi]` with `φ t` in the `m`-th
translate of the edge piece `[k', k'+1]` and `traversal P' (φ t)` in the face `T'`. -/
def u10h_J' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) (k' m : ℤ)
    (T' : Triangle) : Set ℝ :=
  Icc lo hi ∩ φ ⁻¹' ((fun u => u - m * n') ⁻¹' u10h_J P' k' T')

theorem u10h_J'_ordConnected {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ}
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) (k' m : ℤ) (T' : Triangle) :
    (u10h_J' P' φ lo hi k' m T').OrdConnected := by
  have hg : Monotone (fun u : ℝ => u - m * n') := fun a b h => sub_le_sub_right h _
  have h1 := (u10h_J_ordConnected P' k' T').preimage_mono hg
  rcases hφ with hφ | hφ
  · exact ordConnected_Icc.inter (h1.preimage_mono hφ)
  · exact ordConnected_Icc.inter (h1.preimage_anti hφ)

theorem u10h_J'_isCompact {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ} (hφ : Continuous φ)
    (lo hi : ℝ) (k' m : ℤ) (T' : Triangle) : IsCompact (u10h_J' P' φ lo hi k' m T') := by
  have hcl : IsClosed ((fun u : ℝ => u - m * n') ⁻¹' u10h_J P' k' T') :=
    (u10h_J_isCompact P' k' T').isClosed.preimage (continuous_id.sub continuous_const)
  exact isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (hcl.preimage hφ)) inter_subset_left

theorem u10h_J'_eq_Icc {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) (k' m : ℤ) (T' : Triangle)
    (hne : (u10h_J' P' φ lo hi k' m T').Nonempty) :
    u10h_J' P' φ lo hi k' m T' = Icc (sInf (u10h_J' P' φ lo hi k' m T')) (sSup (u10h_J' P' φ lo hi k' m T')) :=
  eq_Icc_of_connected_compact ⟨hne, (u10h_J'_ordConnected P' hφ lo hi k' m T').isPreconnected⟩
    (u10h_J'_isCompact P' hφc lo hi k' m T')

/-- On a P′-piece, `f' ∘ ↑ ∘ traversal P' ∘ φ` is affine in `φ t`. -/
theorem u10h_affOn_J' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) {L' : ℝ}
    {S' : Set Sphere} {f' : Sphere → Plane} {K' : Triangulation (chartPart L' false S')}
    (hK' : IsPositivePLOn (f' ∘ modelChart L' false) K') (k' m : ℤ) {T' : Triangle} (hT' : T' ∈ K'.faces) :
    ∃ p'' u'' : Plane, ∀ t ∈ u10h_J' P' φ lo hi k' m T',
      f' ((traversal P' (φ t) : Plane) : Sphere) = p'' + φ t • u'' := by
  obtain ⟨M, b₀, hM⟩ := (hK' T' hT').1
  refine ⟨M (P' (k' : ZMod n')) - ((m : ℝ) * n' + k') • M (edge P' (k' : ZMod n')) + b₀,
    M (edge P' (k' : ZMod n')), ?_⟩
  rintro t ⟨-, ht⟩
  change (φ t - m * n') ∈ Icc (k' : ℝ) (k' + 1) ∧ traversal P' (φ t - m * n') ∈ T'.carrier at ht
  have hper : traversal P' (φ t) = traversal P' (φ t - m * n') := by
    have := u10h_traversal_add_int_mul P' (φ t - m * n') m
    rwa [sub_add_cancel] at this
  have := hM _ ht.2
  simp only [Function.comp, u10h_modelChart_false] at this
  rw [hper, this, ea_traversal_eq_on_Icc P' k' ht.1.1 ht.1.2, map_add, map_smul]
  simp only [sub_smul, add_smul]
  abel

theorem u10h_J'_cover {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ) {L' : ℝ}
    (hL' : InsideModel L' P') {S' : Set Sphere} (hBS' : sphereCircle P' ⊆ S')
    (K' : Triangulation (chartPart L' false S')) {t : ℝ} (ht : t ∈ Icc lo hi) :
    ∃ k' m : ℤ, 0 ≤ k' ∧ k' < n' ∧ ∃ T' ∈ K'.faces, t ∈ u10h_J' P' φ lo hi k' m T' := by
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  obtain ⟨v, hv, m, hvm⟩ := u10h_reduce (Nat.pos_of_ne_zero (NeZero.ne n')) (φ t)
  have hv' : φ t - m * n' = v := by linarith
  refine ⟨⌊v⌋, m, Int.floor_nonneg.mpr hv.1, ?_, ?_⟩
  · have : (⌊v⌋ : ℝ) < n' := by linarith [Int.floor_le v, hv.2]
    exact_mod_cast this
  · have hmem := u10h_traversal_mem_chartPart P' hL' hBS' v
    rw [← K'.cover, mem_iUnion₂] at hmem
    obtain ⟨T', hT', hTv⟩ := hmem
    refine ⟨T', hT', ht, ?_⟩
    change (φ t - m * n') ∈ Icc (⌊v⌋ : ℝ) (⌊v⌋ + 1) ∧ traversal P' (φ t - m * n') ∈ T'.carrier
    rw [hv']
    exact ⟨⟨Int.floor_le v, (Int.lt_floor_add_one v).le⟩, hTv⟩

/-- The P′-side piece set (endpoints of the nonempty pieces, `0 ≤ k' < n'`). -/
def u10h_pieceSet' {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (φ : ℝ → ℝ) (lo hi : ℝ)
    (K' : Set Triangle) : Set (ℝ × ℝ) :=
  {c | ∃ k' m : ℤ, 0 ≤ k' ∧ k' < n' ∧ ∃ T' ∈ K', (u10h_J' P' φ lo hi k' m T').Nonempty ∧
    c = (sInf (u10h_J' P' φ lo hi k' m T'), sSup (u10h_J' P' φ lo hi k' m T'))}

theorem u10h_pieceSet'_finite {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') {φ : ℝ → ℝ}
    (hφ : Monotone φ ∨ Antitone φ) (lo hi : ℝ) {K' : Set Triangle} (hK' : K'.Finite) :
    (u10h_pieceSet' P' φ lo hi K').Finite := by
  have hn' : (0:ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  set A := min (φ lo) (φ hi)
  set B := max (φ lo) (φ hi)
  have hbound : ∀ t ∈ Icc lo hi, A ≤ φ t ∧ φ t ≤ B := by
    intro t ht
    rcases hφ with hφ | hφ
    · exact ⟨le_trans (min_le_left _ _) (hφ ht.1), le_trans (hφ ht.2) (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) (hφ ht.2), le_trans (hφ ht.1) (le_max_left _ _)⟩
  set m₁ : ℤ := ⌈(A - n') / n'⌉
  set m₂ : ℤ := ⌊B / n'⌋
  have hsub : u10h_pieceSet' P' φ lo hi K' ⊆
      (fun q : (ℤ × ℤ) × Triangle => (sInf (u10h_J' P' φ lo hi q.1.1 q.1.2 q.2),
        sSup (u10h_J' P' φ lo hi q.1.1 q.1.2 q.2))) '' ((Ico 0 (n' : ℤ) ×ˢ Icc m₁ m₂) ×ˢ K') := by
    rintro c ⟨k', m, hk0, hk1, T', hT', ⟨t, ht⟩, rfl⟩
    refine ⟨((k', m), T'), ⟨⟨⟨hk0, hk1⟩, ?_, ?_⟩, hT'⟩, rfl⟩
    · obtain ⟨hA, -⟩ := hbound t ht.1
      have h2 : (k' : ℝ) + 1 ≤ n' := by
        have : k' + 1 ≤ (n' : ℤ) := hk1
        exact_mod_cast this
      have h3 : φ t - m * n' ≤ k' + 1 := ht.2.1.2
      apply Int.ceil_le.mpr
      rw [div_le_iff₀ hn']
      linarith
    · obtain ⟨-, hB⟩ := hbound t ht.1
      have h0 : (0:ℝ) ≤ k' := by exact_mod_cast hk0
      have h3 : (k' : ℝ) ≤ φ t - m * n' := ht.2.1.1
      apply Int.le_floor.mpr
      rw [le_div_iff₀ hn']
      linarith
  exact (((Set.finite_Ico _ _).prod (Set.finite_Icc _ _)).prod hK').image _ |>.subset hsub

theorem u10h_frontier_param [NeZero n] {P : LabelledTuple n} {D : Set Plane} {f : Sphere → Plane}
    (hB : f '' sphereCircle P = frontier D) {a : Plane} (ha : a ∈ frontier D) :
    ∃ x ∈ Ico (0:ℝ) n, f ((traversal P x : Plane) : Sphere) = a := by
  rw [← hB] at ha
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := ha
  rw [← U4_range_traversal P] at hw
  obtain ⟨x₁, rfl⟩ := hw
  obtain ⟨x₀, hx₀, m, rfl⟩ := u10h_reduce (Nat.pos_of_ne_zero (NeZero.ne n)) x₁
  exact ⟨x₀, hx₀, by rw [u10h_traversal_add_int_mul]⟩

theorem u10h_param_ne [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Embedded P) {s : Side}
    {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto (closure (regionOf P s)) D f)
    (hBS : sphereCircle P ⊆ closure (regionOf P s)) {u v : ℝ} (huv : u < v) (hvu : v < u + n) :
    f ((traversal P u : Plane) : Sphere) ≠ f ((traversal P v : Plane) : Sphere) := by
  intro h
  obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn hP hf hBS u v).mp h
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : (0:ℝ) < m * n := by linarith
  have h2 : (m:ℝ) * n < 1 * n := by linarith
  have h3 : (0:ℝ) < m := by
    by_contra h
    have : (m:ℝ) * n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hn0.le
    linarith
  have h4 : (m:ℝ) < 1 := lt_of_mul_lt_mul_right h2 hn0.le
  have h5 : (0:ℤ) < m := by exact_mod_cast h3
  have h6 : m < (1:ℤ) := by exact_mod_cast h4
  omega

/-- The two ordered cases of cyclic-order preservation (parameters `x < y < w < x + n`). -/
theorem u10h_pres_ordered [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D') {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) :
    (CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P y : Plane) : Sphere))
        (f ((traversal P w : Plane) : Sphere)) →
      CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ y) : Plane) : Sphere))
        (f' ((traversal P' (φ w) : Plane) : Sphere))) ∧
    (CyclicPos z (f ((traversal P x : Plane) : Sphere)) (f ((traversal P w : Plane) : Sphere))
        (f ((traversal P y : Plane) : Sphere)) →
      CyclicPos z' (f' ((traversal P' (φ x) : Plane) : Sphere)) (f' ((traversal P' (φ w) : Plane) : Sphere))
        (f' ((traversal P' (φ y) : Plane) : Sphere))) := by
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hfr' : ∀ u, f' ((traversal P' u : Plane) : Sphere) ∈ frontier D' := fun u =>
    hB' ▸ mem_image_of_mem f' (u10h_coe_traversal_mem_circle P' u)
  have hiff := U9_traversalPositiveFor_iff_cyclicPos hn P hP s hL hD hf hB hpl hz hxy hyw hwx
  by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨hmono, hper⟩ := hφ.same hsame
    have h1 : φ x < φ y := hmono hxy
    have h2 : φ y < φ w := hmono hyw
    have h3 : φ w < φ x + n' := by have := hmono hwx; rwa [hper] at this
    have hiff' := U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz' h1 h2 h3
    constructor
    · intro hc
      exact hiff'.mp (hsame.mp (hiff.mpr hc))
    · intro hc
      have hnot : ¬ traversalPositiveFor P s := fun ht => u10h_cyclicPos_antisymm (hiff.mp ht) hc
      have hnot' : ¬ CyclicPos z' _ _ _ := fun hc' => hnot (hsame.mpr (hiff'.mpr hc'))
      rcases u10h_cyclicPos_total hD' hz' (hfr' (φ x)) (hfr' (φ y)) (hfr' (φ w))
        (u10h_param_ne hn' hP' hf' hBS' h1 (by linarith)) (u10h_param_ne hn' hP' hf' hBS' h2 (by linarith))
        (u10h_param_ne hn' hP' hf' hBS' (h1.trans h2) h3) with h | h
      · exact absurd h hnot'
      · exact h
  · obtain ⟨hanti, hper⟩ := hφ.opposite hsame
    have h1 : φ y < φ x := hanti hxy
    have h2 : φ w < φ y := hanti hyw
    have h3 : φ x - n' < φ w := by have := hanti hwx; rwa [hper] at this
    have hiff' := U9_traversalPositiveFor_iff_cyclicPos hn' P' hP' s' hL' hD' hf' hB' hpl' hz' h2 h1
      (by linarith)
    have hopp : traversalPositiveFor P s ↔ ¬ traversalPositiveFor P' s' := by tauto
    constructor
    · intro hc
      have hnot' : ¬ CyclicPos z' _ _ _ := fun hc' => (hopp.mp (hiff.mpr hc)) (hiff'.mpr hc')
      rcases u10h_cyclicPos_total hD' hz' (hfr' (φ x)) (hfr' (φ y)) (hfr' (φ w))
        (u10h_param_ne hn' hP' hf' hBS' h1 (by linarith)).symm
        (u10h_param_ne hn' hP' hf' hBS' h2 (by linarith)).symm
        (u10h_param_ne hn' hP' hf' hBS' (h2.trans h1) (by linarith)).symm with h | h
      · exact h
      · exact absurd (u10h_cyclicPos_rotate h) hnot'
    · intro hc
      have hnot : ¬ traversalPositiveFor P s := fun ht => u10h_cyclicPos_antisymm (hiff.mp ht) hc
      have hpos' : traversalPositiveFor P' s' := by tauto
      exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate (hiff'.mp hpos'))

theorem u10h_preservesCyclicPos [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {z z' : Plane} (hz : z ∈ interior D)
    (hz' : z' ∈ interior D') {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    PreservesCyclicPos D z z' β := by
  intro a ha b hb c hc habc
  obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB ha
  obtain ⟨y, hy, rfl⟩ := u10h_frontier_param hB hb
  obtain ⟨w, hw, rfl⟩ := u10h_frontier_param hB hc
  obtain ⟨hab, hbc, hac⟩ := u10h_cyclicPos_ne habc
  have hxy : x ≠ y := fun h => hab (by rw [h])
  have hyw : y ≠ w := fun h => hbc (by rw [h])
  have hxw : x ≠ w := fun h => hac (by rw [h])
  rw [hβc, hβc, hβc]
  have key := fun {x y w : ℝ} (hxy : x < y) (hyw : y < w) (hwx : w < x + n) =>
    u10h_pres_ordered hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hz hz' hxy hyw hwx
  have hn0 : (0:ℝ) ≤ n := by positivity
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hyw with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxw with h3 | h3
  · exact (key h1 h2 (by linarith [hw.2, hx.1])).1 habc
  · exact absurd (h1.trans h2) (not_lt.mpr h3.le)
  · exact (key h3 h2 (by linarith [hy.2, hx.1])).2 habc
  · have := (key h3 h1 (by linarith [hy.2, hw.1])).1 (u10h_cyclicPos_rotate (u10h_cyclicPos_rotate habc))
    exact u10h_cyclicPos_rotate this
  · have := (key h1 h3 (by linarith [hw.2, hy.1])).2 (u10h_cyclicPos_rotate habc)
    exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate this)
  · have := (key h2 h3 (by linarith [hx.2, hy.1])).1 (u10h_cyclicPos_rotate habc)
    exact u10h_cyclicPos_rotate (u10h_cyclicPos_rotate this)
  · exact absurd (h2.trans h1) (not_lt.mpr h3.le)
  · have := (key h2 h1 (by linarith [hx.2, hw.1])).2 (u10h_cyclicPos_rotate (u10h_cyclicPos_rotate habc))
    exact u10h_cyclicPos_rotate this

theorem u10h_continuousOn_of_isHomeoOnto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : ContinuousOn f S := by
  obtain ⟨e, he⟩ := h
  rw [continuousOn_iff_continuous_domRestrict]
  have : S.domRestrict f = fun x => (e x : β) := by funext x; exact (he x).symm
  rw [this]
  exact continuous_subtype_val.comp e.continuous

/-- The boundary map induced by a positive lift is a homeomorphism of the model frontiers. -/
theorem u10h_boundary_homeo [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    IsHomeoOnto (frontier D) (frontier D') β := by
  have hBS := u10h_circle_subset_closure hn P hP s hL
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hfr : ∀ t, f ((traversal P t : Plane) : Sphere) ∈ frontier D := fun t =>
    hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P t)
  have hfr' : ∀ u, f' ((traversal P' u : Plane) : Sphere) ∈ frontier D' := fun u =>
    hB' ▸ mem_image_of_mem f' (u10h_coe_traversal_mem_circle P' u)
  have hc : Continuous fun t => f ((traversal P t : Plane) : Sphere) :=
    (u10h_continuousOn_of_isHomeoOnto hf).comp_continuous
      (OnePoint.continuous_coe.comp (continuous_traversal P))
      (fun t => hBS (u10h_coe_traversal_mem_circle P t))
  have hc' : Continuous fun t => f' ((traversal P' (φ t) : Plane) : Sphere) :=
    (u10h_continuousOn_of_isHomeoOnto hf').comp_continuous
      (OnePoint.continuous_coe.comp ((continuous_traversal P').comp hφ.continuous))
      (fun t => hBS' (u10h_coe_traversal_mem_circle P' (φ t)))
  have hβfr : ∀ w ∈ frontier D, β w ∈ frontier D' := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := u10h_frontier_param hB hw
    rw [hβc]; exact hfr' _
  -- the map on subtypes
  let e₀ : frontier D → frontier D' := fun w => ⟨β w, hβfr w w.2⟩
  have hinj : Function.Injective e₀ := by
    rintro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
    have h' : β w₁ = β w₂ := congrArg Subtype.val h
    obtain ⟨x, -, rfl⟩ := u10h_frontier_param hB hw₁
    obtain ⟨y, -, rfl⟩ := u10h_frontier_param hB hw₂
    rw [hβc, hβc] at h'
    obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn' hP' hf' hBS' (φ x) (φ y)).mp h'
    apply Subtype.ext
    show f _ = f _
    rw [u10h_param_eq_iff hn hP hf hBS]
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · obtain ⟨hmono, hper⟩ := hφ.same hsame
      refine ⟨m, hmono.injective ?_⟩
      rw [u10h_lift_shift_same hper, hm]
    · obtain ⟨hanti, hper⟩ := hφ.opposite hsame
      refine ⟨-m, hanti.injective ?_⟩
      rw [u10h_lift_shift_opp hper, hm]; push_cast; ring
  have hsurj : Function.Surjective e₀ := by
    rintro ⟨w', hw'⟩
    obtain ⟨u, -, rfl⟩ := u10h_frontier_param hB' hw'
    obtain ⟨x, rfl⟩ := u10h_lift_surj hφ u
    exact ⟨⟨_, hfr x⟩, Subtype.ext (hβc x)⟩
  have hcont : Continuous e₀ := by
    rw [continuous_iff_isClosed]
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := isClosed_induced_iff.mp hC
    have hKc : IsCompact ((fun t => f ((traversal P t : Plane) : Sphere)) ''
        ((fun t => f' ((traversal P' (φ t) : Plane) : Sphere)) ⁻¹' C₀ ∩ Icc (0:ℝ) n)) :=
      (isCompact_Icc.inter_left (hC₀.preimage hc')).image hc
    have : e₀ ⁻¹' (Subtype.val ⁻¹' C₀) = Subtype.val ⁻¹' ((fun t => f ((traversal P t : Plane) : Sphere)) ''
        ((fun t => f' ((traversal P' (φ t) : Plane) : Sphere)) ⁻¹' C₀ ∩ Icc (0:ℝ) n)) := by
      ext ⟨w, hw⟩
      simp only [mem_preimage, e₀]
      constructor
      · intro h
        obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB hw
        rw [hβc] at h
        exact ⟨x, ⟨h, hx.1, hx.2.le⟩, rfl⟩
      · rintro ⟨x, ⟨hx, -⟩, hxw⟩
        show β w ∈ C₀
        rw [← hxw, hβc]; exact hx
    rw [this]
    exact hKc.isClosed.preimage continuous_subtype_val
  have : CompactSpace (frontier D) :=
    isCompact_iff_compactSpace.mp (hD.isCompact.of_isClosed_subset isClosed_frontier (u10h_frontier_subset hD))
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective e₀ ⟨hinj, hsurj⟩) hcont, fun w => rfl⟩

theorem u10h_marks_mono {m : ℕ} {a : ℕ → ℝ} (hainc : ∀ j < m, a j < a (j + 1)) :
    ∀ i j, i ≤ j → j ≤ m → a i ≤ a j := by
  intro i j hij hjm
  induction j with
  | zero =>
    have : i = 0 := by omega
    rw [this]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hainc j (by omega)).le
    · have : i = j + 1 := by omega
      rw [this]

theorem u10h_marks_cover {m : ℕ} {a : ℕ → ℝ} (_hainc : ∀ j < m, a j < a (j + 1)) (hm : 1 ≤ m) :
    ∀ t ∈ Icc (a 0) (a m), ∃ j < m, t ∈ Icc (a j) (a (j + 1)) := by
  suffices h : ∀ j, 1 ≤ j → j ≤ m → ∀ t ∈ Icc (a 0) (a j), ∃ i < j, t ∈ Icc (a i) (a (i + 1)) from
    h m hm le_rfl
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ j ih =>
    intro t ht
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; exact ⟨0, by omega, ht⟩
    · rcases le_or_gt t (a j) with h | h
      · obtain ⟨i, hi, hti⟩ := ih hj (by omega) t ⟨ht.1, h⟩
        exact ⟨i, by omega, hti⟩
      · exact ⟨j, by omega, h.le, ht.2⟩

/-- The induced boundary map is finite PL on the frontier of the model. -/
theorem u10h_finitePL [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D : Set Plane}
    {f f' : Sphere → Plane} (hB : f '' sphereCircle P = frontier D)
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) {β : Plane → Plane}
    (hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere)) :
    IsFinitePLOnFrontier D β := by
  classical
  have hBS := u10h_circle_subset_closure hn P hP s hL
  have hBS' := u10h_circle_subset_closure hn' P' hP' s' hL'
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hfr : ∀ t, f ((traversal P t : Plane) : Sphere) ∈ frontier D := fun t =>
    hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P t)
  obtain ⟨K, hK⟩ := hpl false
  obtain ⟨K', hK'⟩ := hpl' false
  obtain ⟨m, a, ha0, ham, hainc, haff⟩ := hfin
  have hmono : Monotone φ ∨ Antitone φ := by
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · exact Or.inl (hφ.same hsame).1.monotone
    · exact Or.inr (hφ.opposite hsame).1.antitone
  have hφc : Continuous φ := hφ.continuous
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; subst h; rw [ha0] at ham; linarith
    · exact h
  set c : ℝ → Plane := fun t => f ((traversal P t : Plane) : Sphere) with hc_def
  -- the three covers of `[0, n]`
  set C₁ := u10h_pieceSet P K.faces with hC₁
  set C₂ : Set (ℝ × ℝ) := (fun j : ℕ => (a j, a (j + 1))) '' {j | j < m} with hC₂
  set C₃ := u10h_pieceSet' P' φ 0 n K'.faces with hC₃
  have hC₁fin : C₁.Finite := u10h_pieceSet_finite P K.finite
  have hC₂fin : C₂.Finite := (Set.finite_lt_nat m).image _
  have hC₃fin : C₃.Finite := u10h_pieceSet'_finite P' hmono 0 n K'.finite
  have hC₁in : ∀ q ∈ C₁, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨k, hk, T, hT, hne, rfl⟩
    have hcpt := u10h_J_isCompact P k T
    have h1 := hcpt.sInf_mem hne
    have h2 := hcpt.sSup_mem hne
    have h1' := h1.1.1
    have h2' := h2.1.2
    have h12 : sInf (u10h_J P k T) ≤ sSup (u10h_J P k T) :=
      csInf_le_csSup hne hcpt.bddBelow hcpt.bddAbove
    push_cast at h1' h2'
    have hk1 : (k:ℝ) + 1 ≤ n := by
      have : (k + 1 : ℕ) ≤ n := hk
      exact_mod_cast this
    exact ⟨(by positivity : (0:ℝ) ≤ k).trans h1', h12, h2'.trans hk1⟩
  have hC₂in : ∀ q ∈ C₂, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨j, hj, rfl⟩
    have hmo := u10h_marks_mono hainc
    refine ⟨?_, (hainc j hj).le, ?_⟩
    · rw [← ha0]; exact hmo 0 j (Nat.zero_le _) hj.le
    · rw [← ham]; exact hmo (j + 1) m hj le_rfl
  have hC₃in : ∀ q ∈ C₃, 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ n := by
    rintro q ⟨k', mm, hk0, hk1, T', hT', hne, rfl⟩
    have hcpt := u10h_J'_isCompact P' hφc 0 n k' mm T'
    have h1 := hcpt.sInf_mem hne
    have h2 := hcpt.sSup_mem hne
    exact ⟨h1.1.1, csInf_le_csSup hne hcpt.bddBelow hcpt.bddAbove, h2.1.2⟩
  have hC₁cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₁, t ∈ Icc q.1 q.2 := fun t ht =>
    u10h_pieceSet_cover P hL hBS K ht
  have hC₂cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₂, t ∈ Icc q.1 q.2 := by
    intro t ht
    obtain ⟨j, hj, htj⟩ := u10h_marks_cover hainc hm1 t (by rw [ha0, ham]; exact ht)
    exact ⟨(a j, a (j + 1)), ⟨j, hj, rfl⟩, htj⟩
  have hC₃cov : ∀ t ∈ Icc (0:ℝ) n, ∃ q ∈ C₃, t ∈ Icc q.1 q.2 := by
    intro t ht
    obtain ⟨k', mm, hk0, hk1, T', hT', htJ⟩ := u10h_J'_cover P' φ 0 n hL' hBS' K' ht
    refine ⟨_, ⟨k', mm, hk0, hk1, T', hT', ⟨t, htJ⟩, rfl⟩, ?_⟩
    have := u10h_J'_eq_Icc P' hφc hmono 0 n k' mm T' ⟨t, htJ⟩
    rw [← this]; exact htJ
  have hC₁aff : ∀ q ∈ C₁, u10h_AffOn c (Icc q.1 q.2) := fun q hq => u10h_pieceSet_affOn P hK hq
  have hC₂aff : ∀ q ∈ C₂, ∃ α δ : ℝ, ∀ t ∈ Icc q.1 q.2, φ t = α * t + δ := by
    rintro q ⟨j, hj, rfl⟩
    exact haff j hj
  have hC₃aff : ∀ q ∈ C₃, ∃ p'' u'' : Plane, ∀ t ∈ Icc q.1 q.2,
      f' ((traversal P' (φ t) : Plane) : Sphere) = p'' + φ t • u'' := by
    rintro q ⟨k', mm, hk0, hk1, T', hT', hne, rfl⟩
    obtain ⟨p'', u'', h⟩ := u10h_affOn_J' P' φ 0 n hK' k' mm hT'
    refine ⟨p'', u'', fun t ht => h t ?_⟩
    rwa [u10h_J'_eq_Icc P' hφc hmono 0 n k' mm T' hne]
  -- the breakpoints
  set B : Set ℝ := ({0, (n:ℝ)} ∪ (Prod.fst '' C₁ ∪ Prod.snd '' C₁)) ∪
    ((Prod.fst '' C₂ ∪ Prod.snd '' C₂) ∪ (Prod.fst '' C₃ ∪ Prod.snd '' C₃)) with hB_def
  have hBfin : B.Finite :=
    ((Set.toFinite _).union ((hC₁fin.image _).union (hC₁fin.image _))).union
      (((hC₂fin.image _).union (hC₂fin.image _)).union ((hC₃fin.image _).union (hC₃fin.image _)))
  have h0B : (0:ℝ) ∈ B := Or.inl (Or.inl (by simp))
  have hnB : (n:ℝ) ∈ B := Or.inl (Or.inl (by simp))
  have hC₁B : ∀ q ∈ C₁, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inl (Or.inr (Or.inl ⟨q, hq, rfl⟩)), Or.inl (Or.inr (Or.inr ⟨q, hq, rfl⟩))⟩
  have hC₂B : ∀ q ∈ C₂, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inr (Or.inl (Or.inl ⟨q, hq, rfl⟩)), Or.inr (Or.inl (Or.inr ⟨q, hq, rfl⟩))⟩
  have hC₃B : ∀ q ∈ C₃, q.1 ∈ B ∧ q.2 ∈ B := fun q hq =>
    ⟨Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨q, hq, rfl⟩))⟩
  have hBin : ∀ b ∈ B, 0 ≤ b ∧ b ≤ n := by
    intro b hb
    rcases hb with (hb | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)) | ((⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩))
    · simp only [mem_insert_iff, mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> constructor <;> linarith
    · obtain ⟨h1, h2, h3⟩ := hC₁in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₁in q hq; exact ⟨h1.trans h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₂in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₂in q hq; exact ⟨h1.trans h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₃in q hq; exact ⟨h1, h2.trans h3⟩
    · obtain ⟨h1, h2, h3⟩ := hC₃in q hq; exact ⟨h1.trans h2, h3⟩
  -- the gap pairs
  set G : Set (ℝ × ℝ) := {g | g.1 ∈ B ∧ g.2 ∈ B ∧ g.1 < g.2 ∧ ∀ a ∈ B, g.1 < a → a < g.2 → False}
    with hG
  have hGfin : G.Finite := (hBfin.prod hBfin).subset (fun g hg => ⟨hg.1, hg.2.1⟩)
  have hgap : ∀ g ∈ G, (∃ p u : Plane, ∀ t ∈ Icc g.1 g.2, c t = p + t • u) ∧
      (∃ p'' u'' : Plane, ∀ t ∈ Icc g.1 g.2, β (c t) = p'' + t • u'') := by
    rintro g ⟨hg1, hg2, hlt, hnone⟩
    have hb0 : 0 ≤ g.1 := (hBin _ hg1).1
    have hbn : g.2 ≤ n := (hBin _ hg2).2
    obtain ⟨q₁, hq₁, hsub₁⟩ := u10h_subset_piece hC₁B hC₁cov hb0 hbn hlt hnone
    obtain ⟨q₂, hq₂, hsub₂⟩ := u10h_subset_piece hC₂B hC₂cov hb0 hbn hlt hnone
    obtain ⟨q₃, hq₃, hsub₃⟩ := u10h_subset_piece hC₃B hC₃cov hb0 hbn hlt hnone
    obtain ⟨p, u, hpu⟩ := hC₁aff q₁ hq₁
    obtain ⟨α, δ, hαδ⟩ := hC₂aff q₂ hq₂
    obtain ⟨p'', u'', hpu''⟩ := hC₃aff q₃ hq₃
    refine ⟨⟨p, u, fun t ht => hpu t (hsub₁ ht)⟩, ⟨p'' + δ • u'', α • u'', ?_⟩⟩
    intro t ht
    show β (f ((traversal P t : Plane) : Sphere)) = _
    rw [hβc, hpu'' t (hsub₃ ht), hαδ t (hsub₂ ht), add_smul, smul_smul, mul_comm t α]
    abel
  -- the segments
  set sF : Finset (Plane × Plane) := (hGfin.image (fun g : ℝ × ℝ => (c g.1, c g.2))).toFinset with hsF
  refine ⟨sF, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      rw [mem_iUnion₂] at hw
      obtain ⟨p, hp, hwp⟩ := hw
      rw [hsF, Set.Finite.mem_toFinset] at hp
      obtain ⟨g, hg, rfl⟩ := hp
      obtain ⟨⟨pp, u, hpu⟩, -⟩ := hgap g hg
      rw [← u10h_image_Icc_eq_segment hpu hg.2.2.1.le] at hwp
      obtain ⟨t, -, rfl⟩ := hwp
      exact hfr t
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := u10h_frontier_param hB hw
      obtain ⟨b, hb, b', hb', hlt, hbx, hxb, hnone⟩ := u10h_gap' hBfin h0B hnB hn0 ⟨hx.1, hx.2.le⟩
      have hgG : (b, b') ∈ G := ⟨hb, hb', hlt, hnone⟩
      rw [mem_iUnion₂]
      refine ⟨(c b, c b'), ?_, ?_⟩
      · rw [hsF, Set.Finite.mem_toFinset]; exact ⟨(b, b'), hgG, rfl⟩
      · obtain ⟨⟨pp, u, hpu⟩, -⟩ := hgap (b, b') hgG
        show f ((traversal P x : Plane) : Sphere) ∈ segment ℝ (c b) (c b')
        rw [← u10h_image_Icc_eq_segment hpu hlt.le]
        exact ⟨x, ⟨hbx, hxb⟩, rfl⟩
  · intro p hp
    rw [hsF, Set.Finite.mem_toFinset] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    obtain ⟨⟨pp, u, hpu⟩, ⟨p'', u'', hβ⟩⟩ := hgap g hg
    show AffineOn β (segment ℝ (c g.1) (c g.2))
    rw [← u10h_image_Icc_eq_segment hpu hg.2.2.1.le]
    exact u10h_affineOn_of_param hpu hβ hg.2.2.1.le

/-- U10 (sm-3:431-433 "finite prescribed positive PL boundary maps" read in the models): a finite PL
positive boundary lift `φ`, conjugated by two positive PL disc parametrisations, is a finite PL
homeomorphism of the model frontiers preserving the cyclic order around suitable interior points. -/
theorem U10_boundary_map_of_lift [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {L L' : ℝ} (hL : InsideModel L P) (hL' : InsideModel L' P') {D D' : Set Plane}
    {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    (hpl : IsPositivePLToPlane L (closure (regionOf P s)) f)
    (hpl' : IsPositivePLToPlane L' (closure (regionOf P' s')) f')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) :
    ∃ (β : Plane → Plane) (z z' : Plane), z ∈ interior D ∧ z' ∈ interior D' ∧
      IsHomeoOnto (frontier D) (frontier D') β ∧ IsFinitePLOnFrontier D β ∧
      PreservesCyclicPos D z z' β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  classical
  obtain ⟨z, hz⟩ := hD.interior_nonempty
  obtain ⟨z', hz'⟩ := hD'.interior_nonempty
  have hBS := u10h_circle_subset_closure hn P hP s hL
  let β : Plane → Plane := fun w =>
    if h : ∃ x : ℝ, f ((traversal P x : Plane) : Sphere) = w then
      f' ((traversal P' (φ h.choose) : Plane) : Sphere) else w
  have hβc : ∀ x, β (f ((traversal P x : Plane) : Sphere)) =
      f' ((traversal P' (φ x) : Plane) : Sphere) := by
    intro x
    have hex : ∃ x' : ℝ, f ((traversal P x' : Plane) : Sphere) = f ((traversal P x : Plane) : Sphere) :=
      ⟨x, rfl⟩
    show (if h : ∃ x' : ℝ, f ((traversal P x' : Plane) : Sphere) = f ((traversal P x : Plane) : Sphere) then
      f' ((traversal P' (φ h.choose) : Plane) : Sphere) else _) = _
    rw [dite_eq_left hex]
    have hspec := hex.choose_spec
    set x₀ := hex.choose with hx₀
    clear_value x₀
    obtain ⟨m, hm⟩ := (u10h_param_eq_iff hn hP hf hBS x₀ x).mp hspec
    rw [hm]
    by_cases hsame : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
    · rw [u10h_lift_shift_same (hφ.same hsame).2, u10h_traversal_add_int_mul]
    · rw [u10h_lift_shift_opp (hφ.opposite hsame).2, sub_eq_add_neg, ← neg_mul, ← Int.cast_neg,
        u10h_traversal_add_int_mul]
  exact ⟨β, z, z', hz, hz',
    u10h_boundary_homeo hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hφ hβc,
    u10h_finitePL hn P hP hn' P' hP' s s' hL hL' hB hpl hpl' hφ hfin hβc,
    u10h_preservesCyclicPos hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hz hz' hβc,
    hβc⟩

/-! #### U10 helpers for `U10_pl_extension` -/

theorem u10h_isHomeoOnto_image {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {S : Set α}
    {S' : Set β} {f : α → β} (h : IsHomeoOnto S S' f) : f '' S = S' := by
  obtain ⟨e, he⟩ := h
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he ⟨x, hx⟩]; exact (e ⟨x, hx⟩).2
  · intro hw
    refine ⟨e.symm ⟨w, hw⟩, (e.symm ⟨w, hw⟩).2, ?_⟩
    rw [← he]; simp

theorem u10h_pl_discs [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (s : Side)
    (L : ℝ) (hL : InsideModel L P) :
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P) := by
  cases s with
  | inner => exact U7_pl_discs_inner hn P hP L hL
  | outer => exact U8_pl_discs_outer hn P hP L hL

/-- U10 (57c, sm-3:431-433 / 535-537): finite positive PL boundary maps extend to positive PL disc
maps `F = Φ'⁻¹ ∘ Fan ∘ Φ`. -/
theorem U10_pl_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (L L' : ℝ) (hL : InsideModel L P) (hL' : InsideModel L' P')
    (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) (hfin : IsFinitePL n φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      IsPositivePLSphereMap L L' (closure (regionOf P s)) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  obtain ⟨D, f, hD, hBS, hf, hB, hpl⟩ := u10h_pl_discs hn P hP s L hL
  obtain ⟨D', f', hD', hBS', hf', hB', hpl'⟩ := u10h_pl_discs hn' P' hP' s' L' hL'
  obtain ⟨β, z, z', hz, hz', hβ, hβpl, hβpos, hβc⟩ :=
    U10_boundary_map_of_lift hn P hP hn' P' hP' s s' hL hL' hD hD' hf hf' hB hB' hpl hpl' hφ hfin
  obtain ⟨K, Fan, hFanK, hFan, hFanβ⟩ := U10_fan_extension hD hD' hz hz' hβ hβpl hβpos
  obtain ⟨g', hg'pl, hg'l, hg'r⟩ :=
    U3_isPositivePLFromPlane_inv (U4_polygonImage_subset_interior_square P' hL').2 hD' hf' hpl'
  have hfS : f '' closure (regionOf P s) = D := u10h_isHomeoOnto_image hf
  have hFanD : Fan '' D = D' := u10h_isHomeoOnto_image hFan
  have hg' : IsHomeoOnto D' (closure (regionOf P' s')) g' := U1_isHomeoOnto_inv hf' hg'l
  refine ⟨g' ∘ (Fan ∘ f), ?_, ?_, ?_⟩
  · exact U1_isHomeoOnto_comp (U1_isHomeoOnto_comp hf hFan) hg'
  · have h1 : IsPositivePLToPlane L (closure (regionOf P s)) (Fan ∘ f) :=
      U3_isPositivePLToPlane_comp_plane K hpl hfS.le hFanK
    have h2 : (Fan ∘ f) '' closure (regionOf P s) ⊆ D' := by rw [image_comp, hfS, hFanD]
    exact U3_isPositivePLSphereMap_comp h1 h2 hg'pl
  · intro x
    have hfx : f ((traversal P x : Plane) : Sphere) ∈ frontier D :=
      hB ▸ mem_image_of_mem f (u10h_coe_traversal_mem_circle P x)
    have hx' : ((traversal P' (φ x) : Plane) : Sphere) ∈ closure (regionOf P' s') :=
      hBS' (u10h_coe_traversal_mem_circle P' (φ x))
    simp only [Function.comp]
    rw [hFanβ _ hfx, hβc x, hg'l _ hx']

/-! ### U11 (lane C convex model, then sequential) — 57d -/

/-- a disc with `0` interior is a neighbourhood of `0`. -/
theorem u11h_mem_nhds_of_interior {D : Set Plane} (h0 : (0 : Plane) ∈ interior D) : D ∈ nhds 0 :=
  mem_interior_iff_mem_nhds.mp h0

theorem u11h_isVonNBounded {D : Set Plane} (hD : Link.IsDisc D) : Bornology.IsVonNBounded ℝ D :=
  hD.2.1.isVonNBounded ℝ

/-- U11 (gauge coordinates): for a convex disc with `0` in its interior, the frontier is the gauge
level `1` and the disc is the sublevel `≤ 1`. -/
theorem U11_frontier_eq_gauge_one {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    frontier D = {x | gauge D x = 1} ∧ D = {x | gauge D x ≤ 1} := by
  have hn : D ∈ nhds (0 : Plane) := u11h_mem_nhds_of_interior h0
  refine ⟨?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq]
    exact (gauge_eq_one_iff_mem_frontier hD.1 hn).symm
  · ext x
    simp only [mem_ofPred_eq]
    rw [gauge_le_one_iff_mem_closure hD.1 hn, hD.2.1.isClosed.closure_eq]
/-- gauge positivity off `0` for a disc with `0` interior. -/
theorem u11h_gauge_pos {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : 0 < gauge D x :=
  (gauge_pos (absorbent_nhds_zero (u11h_mem_nhds_of_interior h0)) (u11h_isVonNBounded hD)).mpr hx

/-- The radial projection onto the frontier: `x ↦ (gauge D x)⁻¹ • x`. -/
noncomputable def u11h_proj (D : Set Plane) (x : Plane) : Plane := (gauge D x)⁻¹ • x

/-- The radial map: `x ↦ gauge D x • b (proj D x)`. -/
noncomputable def u11h_rad (D : Set Plane) (b : Plane → Plane) (x : Plane) : Plane :=
  gauge D x • b (u11h_proj D x)

theorem u11h_gauge_proj {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : gauge D (u11h_proj D x) = 1 := by
  have hp := u11h_gauge_pos hD h0 hx
  unfold u11h_proj
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hp.le), smul_eq_mul, inv_mul_cancel₀ hp.ne']

theorem u11h_proj_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    {x : Plane} (hx : x ≠ 0) : u11h_proj D x ∈ frontier D := by
  rw [(U11_frontier_eq_gauge_one hD h0).1]
  exact u11h_gauge_proj hD h0 hx

theorem u11h_rad_zero (D : Set Plane) (b : Plane → Plane) : u11h_rad D b 0 = 0 := by
  simp [u11h_rad]

theorem u11h_rad_of_mem_frontier {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (b : Plane → Plane) {x : Plane} (hx : x ∈ frontier D) : u11h_rad D b x = b x := by
  have h1 : gauge D x = 1 := by
    rw [(U11_frontier_eq_gauge_one hD h0).1] at hx; exact hx
  simp [u11h_rad, u11h_proj, h1]

theorem u11h_gauge_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) (x : Plane) :
    gauge D' (u11h_rad D b x) = gauge D x := by
  by_cases hx : x = 0
  · subst hx; simp [u11h_rad]
  · have h1 : gauge D' (b (u11h_proj D x)) = 1 := by
      have := hb (u11h_proj_mem_frontier hD h0 hx)
      rw [(U11_frontier_eq_gauge_one hD' h0').1] at this; exact this
    unfold u11h_rad
    rw [gauge_smul_of_nonneg (gauge_nonneg _), smul_eq_mul, h1, mul_one]

theorem u11h_proj_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) {x : Plane} (hx : x ≠ 0) :
    u11h_proj D' (u11h_rad D b x) = b (u11h_proj D x) := by
  have hp := u11h_gauge_pos hD h0 hx
  unfold u11h_proj
  rw [u11h_gauge_rad hD h0 hD' h0' hb x]
  unfold u11h_rad
  rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rfl

theorem u11h_rad_mem {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) {x : Plane} (hx : x ∈ D) : u11h_rad D b x ∈ D' := by
  rw [(U11_frontier_eq_gauge_one hD' h0').2]
  show gauge D' (u11h_rad D b x) ≤ 1
  rw [u11h_gauge_rad hD h0 hD' h0' hb x]
  exact gauge_le_one_of_mem hx

theorem u11h_rad_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') (h0' : (0 : Plane) ∈ interior D') {b b' : Plane → Plane}
    (hb : MapsTo b (frontier D) (frontier D')) (hb' : ∀ u ∈ frontier D, b' (b u) = u) (x : Plane) :
    u11h_rad D' b' (u11h_rad D b x) = x := by
  by_cases hx : x = 0
  · subst hx; simp [u11h_rad]
  · have hp := u11h_gauge_pos hD h0 hx
    have h1 := u11h_gauge_rad hD h0 hD' h0' hb x
    have h2 := u11h_proj_rad hD h0 hD' h0' hb hx
    show gauge D' (u11h_rad D b x) • b' (u11h_proj D' (u11h_rad D b x)) = x
    rw [h1, h2, hb' _ (u11h_proj_mem_frontier hD h0 hx)]
    unfold u11h_proj
    rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

theorem u11h_continuousOn_proj {D : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D) :
    ContinuousOn (u11h_proj D) {x | x ≠ 0} := by
  have hg : Continuous (gauge D) := continuous_gauge hD.1 (u11h_mem_nhds_of_interior h0)
  refine ContinuousOn.smul (hg.continuousOn.inv₀ ?_) continuousOn_id
  intro x hx
  exact (u11h_gauge_pos hD h0 hx).ne'

theorem u11h_continuous_rad {D D' : Set Plane} (hD : Link.IsDisc D) (h0 : (0 : Plane) ∈ interior D)
    (hD' : Link.IsDisc D') {b : Plane → Plane}
    (hb : ContinuousOn b (frontier D)) (hbm : MapsTo b (frontier D) (frontier D')) :
    Continuous (u11h_rad D b) := by
  have hg : Continuous (gauge D) := continuous_gauge hD.1 (u11h_mem_nhds_of_interior h0)
  have hmaps : MapsTo (u11h_proj D) {x | x ≠ 0} (frontier D) := fun x hx =>
    u11h_proj_mem_frontier hD h0 hx
  have hne : ContinuousOn (u11h_rad D b) {x | x ≠ 0} :=
    hg.continuousOn.smul (hb.comp (u11h_continuousOn_proj hD h0) hmaps)
  obtain ⟨M, hM⟩ := hD'.2.1.isBounded.subset_closedBall 0
  have hbound : ∀ x, ‖u11h_rad D b x‖ ≤ gauge D x * M := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [u11h_rad_zero]
    · have hmem : b (u11h_proj D x) ∈ D' :=
        hD'.2.1.isClosed.frontier_subset (hbm (u11h_proj_mem_frontier hD h0 hx))
      have hM' : ‖b (u11h_proj D x)‖ ≤ M := by simpa using hM hmem
      unfold u11h_rad
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gauge_nonneg _)]
      exact mul_le_mul_of_nonneg_left hM' (gauge_nonneg _)
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, u11h_rad_zero]
    refine squeeze_zero_norm hbound ?_
    have : Filter.Tendsto (fun x => gauge D x * M) (nhds 0) (nhds (gauge D 0 * M)) :=
      (hg.tendsto 0).mul_const M
    simpa [gauge_zero] using this
  · exact hne.continuousAt (isOpen_ne.mem_nhds hx)

/-- Translating a disc so that an interior point `c` goes to `0`: the preimage under `x ↦ x + c`. -/
theorem u11h_translate {D : Set Plane} (hD : Link.IsDisc D) {c : Plane} (hc : c ∈ interior D) :
    Link.IsDisc ((fun x => x + c) ⁻¹' D) ∧ (0 : Plane) ∈ interior ((fun x => x + c) ⁻¹' D) ∧
      frontier ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' frontier D := by
  have hint : interior ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' interior D :=
    ((Homeomorph.addRight c).preimage_interior D).symm
  have hfr : frontier ((fun x => x + c) ⁻¹' D) = (fun x => x + c) ⁻¹' frontier D :=
    ((Homeomorph.addRight c).preimage_frontier D).symm
  have h0 : (0 : Plane) ∈ interior ((fun x => x + c) ⁻¹' D) := by
    rw [hint]; show (0 : Plane) + c ∈ interior D; simpa using hc
  refine ⟨⟨hD.1.translate_preimage_left c, ?_, ⟨0, h0⟩⟩, h0, hfr⟩
  exact (Homeomorph.addRight c).isCompact_preimage.mpr hD.2.1

open Classical in
/-- The inverse of a set homeomorphism, as a plane map (junk `0` off the target). -/
noncomputable def u11h_homeoInv {S S' : Set Plane} (e : S ≃ₜ S') (y : Plane) : Plane :=
  if h : y ∈ S' then (e.symm ⟨y, h⟩ : Plane) else 0

theorem u11h_isHomeoOnto_facts {S S' : Set Plane} {β : Plane → Plane}
    (hβ : IsHomeoOnto S S' β) :
    ∃ βi : Plane → Plane, ContinuousOn β S ∧ MapsTo β S S' ∧ ContinuousOn βi S' ∧ MapsTo βi S' S ∧
      (∀ u ∈ S, βi (β u) = u) ∧ (∀ u ∈ S', β (βi u) = u) := by
  obtain ⟨e, he⟩ := hβ
  refine ⟨u11h_homeoInv e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S β = fun z => (e z : Plane) := funext fun z => (he z).symm
    rw [this]; exact continuous_subtype_val.comp e.continuous
  · intro z hz; rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S' (u11h_homeoInv e) = fun y => (e.symm y : Plane) := by
      funext y; simp only [domRestrict, u11h_homeoInv, y.2, ↓reduceDIte]
    rw [this]; exact continuous_subtype_val.comp e.symm.continuous
  · intro y hy; simp only [u11h_homeoInv, hy, ↓reduceDIte]; exact (e.symm ⟨y, hy⟩).2
  · intro u hu
    have h1 : β u ∈ S' := by rw [← he ⟨u, hu⟩]; exact (e ⟨u, hu⟩).2
    simp only [u11h_homeoInv, h1, ↓reduceDIte]
    have : (⟨β u, h1⟩ : S') = e ⟨u, hu⟩ := Subtype.ext (he ⟨u, hu⟩).symm
    rw [this, e.symm_apply_apply]
  · intro u hu
    simp only [u11h_homeoInv, hu, ↓reduceDIte]
    rw [← he (e.symm ⟨u, hu⟩), e.apply_symm_apply]

/-- U11 (sm-3:537-542, the radial / Alexander extension on convex models): a homeomorphism between
the frontiers of two convex discs extends to a homeomorphism of the discs. -/
theorem U11_radial_extension {D D' : Set Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    {β : Plane → Plane} (hβ : IsHomeoOnto (frontier D) (frontier D') β) :
    ∃ F : Plane → Plane, IsHomeoOnto D D' F ∧ ∀ x ∈ frontier D, F x = β x := by
  obtain ⟨c, hc⟩ := hD.2.2
  obtain ⟨c', hc'⟩ := hD'.2.2
  obtain ⟨hA, h0, hfrA⟩ := u11h_translate hD hc
  obtain ⟨hA', h0', hfrA'⟩ := u11h_translate hD' hc'
  obtain ⟨βi, hβc, hβm, hβic, hβim, hβiβ, hββi⟩ := u11h_isHomeoOnto_facts hβ
  set A : Set Plane := (fun x => x + c) ⁻¹' D with hAdef
  set A' : Set Plane := (fun x => x + c') ⁻¹' D' with hA'def
  set b : Plane → Plane := fun y => β (y + c) - c' with hbdef
  set b' : Plane → Plane := fun y => βi (y + c') - c with hb'def
  have hmA : ∀ y, y ∈ frontier A ↔ y + c ∈ frontier D := fun y => by rw [hfrA]; rfl
  have hmA' : ∀ y, y ∈ frontier A' ↔ y + c' ∈ frontier D' := fun y => by rw [hfrA']; rfl
  have hbc : ContinuousOn b (frontier A) := by
    refine ContinuousOn.sub (hβc.comp (continuous_add_const c).continuousOn ?_) continuousOn_const
    intro y hy; exact (hmA y).mp hy
  have hbm : MapsTo b (frontier A) (frontier A') := by
    intro y hy; rw [hmA']; simp only [hbdef, sub_add_cancel]; exact hβm ((hmA y).mp hy)
  have hb'c : ContinuousOn b' (frontier A') := by
    refine ContinuousOn.sub (hβic.comp (continuous_add_const c').continuousOn ?_) continuousOn_const
    intro y hy; exact (hmA' y).mp hy
  have hb'm : MapsTo b' (frontier A') (frontier A) := by
    intro y hy; rw [hmA]; simp only [hb'def, sub_add_cancel]; exact hβim ((hmA' y).mp hy)
  have hb'b : ∀ u ∈ frontier A, b' (b u) = u := by
    intro u hu; simp only [hbdef, hb'def, sub_add_cancel]
    rw [hβiβ _ ((hmA u).mp hu), add_sub_cancel_right]
  have hbb' : ∀ u ∈ frontier A', b (b' u) = u := by
    intro u hu; simp only [hbdef, hb'def, sub_add_cancel]
    rw [hββi _ ((hmA' u).mp hu), add_sub_cancel_right]
  have hcont : Continuous (u11h_rad A b) := u11h_continuous_rad hA h0 hA' hbc hbm
  have hcont' : Continuous (u11h_rad A' b') := u11h_continuous_rad hA' h0' hA hb'c hb'm
  have hmemA : ∀ x, x ∈ D → x - c ∈ A := fun x hx => by
    show x - c + c ∈ D; rwa [sub_add_cancel]
  have hmemA' : ∀ x, x ∈ D' → x - c' ∈ A' := fun x hx => by
    show x - c' + c' ∈ D'; rwa [sub_add_cancel]
  refine ⟨fun x => u11h_rad A b (x - c) + c', ⟨?_, ?_⟩, ?_⟩
  · exact
      { toFun := fun x => ⟨u11h_rad A b (x.1 - c) + c', u11h_rad_mem hA h0 hA' h0' hbm (hmemA _ x.2)⟩
        invFun := fun y => ⟨u11h_rad A' b' (y.1 - c') + c,
          u11h_rad_mem hA' h0' hA h0 hb'm (hmemA' _ y.2)⟩
        left_inv := fun x => by
          apply Subtype.ext
          simp only [add_sub_cancel_right]
          rw [u11h_rad_rad hA h0 hA' h0' hbm hb'b, sub_add_cancel]
        right_inv := fun y => by
          apply Subtype.ext
          simp only [add_sub_cancel_right]
          rw [u11h_rad_rad hA' h0' hA h0 hb'm hbb', sub_add_cancel]
        continuous_toFun := by
          exact ((hcont.comp (continuous_subtype_val.sub continuous_const)).add
            continuous_const).subtype_mk _
        continuous_invFun := by
          exact ((hcont'.comp (continuous_subtype_val.sub continuous_const)).add
            continuous_const).subtype_mk _ }
  · intro z; rfl
  · intro x hx
    have hxA : x - c ∈ frontier A := by rw [hmA, sub_add_cancel]; exact hx
    show u11h_rad A b (x - c) + c' = β x
    rw [u11h_rad_of_mem_frontier hA h0 b hxA]
    simp only [hbdef, sub_add_cancel]
/-- integer periodicity of the traversal. -/
theorem u11h_traversal_add_int (P : LabelledTuple n) (x : ℝ) (m : ℤ) :
    traversal P (x + m * n) = traversal P x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : x + (((k : ℤ) + 1 : ℤ) : ℝ) * n = (x + ((k : ℤ) : ℝ) * n) + n := by push_cast; ring
    rw [this, traversal_add_nat, ih]
  | pred k ih =>
    have : x + ((-(k : ℤ) : ℤ) : ℝ) * n = (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) + n := by
      push_cast; ring
    rw [this, traversal_add_nat] at ih
    exact ih

/-- a lift with `φ (x + n) = φ x + a` satisfies `φ (x + m n) = φ x + m a`. -/
theorem u11h_lift_add_int {φ : ℝ → ℝ} {a : ℝ} (hper : ∀ x, φ (x + n) = φ x + a) (x : ℝ) (m : ℤ) :
    φ (x + m * n) = φ x + m * a := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : x + (((k : ℤ) + 1 : ℤ) : ℝ) * n = (x + ((k : ℤ) : ℝ) * n) + n := by push_cast; ring
    rw [this, hper, ih]; push_cast; ring
  | pred k ih =>
    have h1 : x + ((-(k : ℤ) : ℤ) : ℝ) * n = (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) + n := by
      push_cast; ring
    rw [h1, hper] at ih
    have : φ (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * n) = φ x + ((-(k : ℤ) : ℤ) : ℝ) * a - a := by linarith
    rw [this]; push_cast; ring

/-- surjectivity of a continuous map with `φ (x + n) = φ x + a`, `a > 0` (IVT). -/
theorem u11h_surj_of_period {φ : ℝ → ℝ} (hc : Continuous φ) {a : ℝ} (ha : 0 < a)
    (hper : ∀ x, φ (x + n) = φ x + a) : Function.Surjective φ := by
  intro y
  set m : ℤ := ⌊(y - φ 0) / a⌋ with hm
  have h1 : (m : ℝ) ≤ (y - φ 0) / a := Int.floor_le _
  have h2 : (y - φ 0) / a < m + 1 := Int.lt_floor_add_one _
  have hlo : φ ((m : ℝ) * n) ≤ y := by
    have := u11h_lift_add_int hper 0 m
    rw [zero_add] at this; rw [this]
    have := (le_div_iff₀ ha).mp h1; linarith
  have hhi : y ≤ φ (((m + 1 : ℤ) : ℝ) * n) := by
    have := u11h_lift_add_int hper 0 (m + 1)
    rw [zero_add] at this; rw [this]
    have := (div_lt_iff₀ ha).mp h2; push_cast; linarith
  have hab : (m : ℝ) * n ≤ ((m + 1 : ℤ) : ℝ) * n := by
    push_cast; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hab hc.continuousOn ⟨hlo, hhi⟩
  exact ⟨x, hx⟩

/-- Packaging of a positive boundary lift: a sign `ε = ±1` with `φ (x + n) = φ x + ε n'`,
injectivity and surjectivity. -/
theorem u11h_lift_facts [NeZero n] {n' : ℕ} [NeZero n'] (hn' : 3 ≤ n') (P : LabelledTuple n)
    (P' : LabelledTuple n') (s s' : Side) {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ (∀ x, φ (x + n) = φ x + ε * n') ∧
      Function.Injective φ ∧ Function.Surjective φ := by
  have hn'0 : (0 : ℝ) < n' := by exact_mod_cast (show 0 < n' by omega)
  by_cases h : (traversalPositiveFor P s ↔ traversalPositiveFor P' s')
  · obtain ⟨hmono, hper⟩ := hφ.same h
    refine ⟨1, Or.inl rfl, fun x => by rw [hper, one_mul], hmono.injective, ?_⟩
    exact u11h_surj_of_period hφ.continuous hn'0 hper
  · obtain ⟨hanti, hper⟩ := hφ.opposite h
    refine ⟨-1, Or.inr rfl, fun x => by rw [hper]; ring, hanti.injective, ?_⟩
    have hneg : ∀ x, (fun t => -φ t) (x + n) = (fun t => -φ t) x + n' := fun x => by
      simp only; rw [hper]; ring
    have hs := u11h_surj_of_period hφ.continuous.neg hn'0 hneg
    intro y
    obtain ⟨x, hx⟩ := hs (-y)
    exact ⟨x, by simpa using congrArg Neg.neg hx⟩

/-- the boundary lift respects the traversal identifications. -/
theorem u11h_traversal_congr [NeZero n] {n' : ℕ} (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Embedded P) (P' : LabelledTuple n') {φ : ℝ → ℝ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hper : ∀ x, φ (x + n) = φ x + ε * n') {x y : ℝ} (hxy : traversal P x = traversal P y) :
    traversal P' (φ x) = traversal P' (φ y) := by
  obtain ⟨m, hm⟩ := hP.traversal_injective hn hxy
  rcases hε with rfl | rfl
  · have h1 : φ y = φ x + m * n' := by rw [hm, u11h_lift_add_int hper x m]; ring
    rw [h1, u11h_traversal_add_int]
  · have h1 : φ y = φ x + ((-m : ℤ) : ℝ) * n' := by
      rw [hm, u11h_lift_add_int hper x m]; push_cast; ring
    rw [h1, u11h_traversal_add_int]

/-- and conversely (injectivity of the induced circle map). -/
theorem u11h_traversal_congr_inv [NeZero n] {n' : ℕ} [NeZero n'] (hn' : 3 ≤ n') (P : LabelledTuple n)
    {P' : LabelledTuple n'} (hP' : Embedded P') {φ : ℝ → ℝ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hper : ∀ x, φ (x + n) = φ x + ε * n') (hinj : Function.Injective φ) {x y : ℝ}
    (hxy : traversal P' (φ x) = traversal P' (φ y)) : traversal P x = traversal P y := by
  obtain ⟨m, hm⟩ := hP'.traversal_injective hn' hxy
  rcases hε with rfl | rfl
  · have h1 : φ y = φ (x + m * n) := by rw [u11h_lift_add_int hper x m, hm]; ring
    rw [hinj h1, u11h_traversal_add_int]
  · have h1 : φ y = φ (x + ((-m : ℤ) : ℝ) * n) := by
      rw [u11h_lift_add_int hper x (-m), hm]; push_cast; ring
    rw [hinj h1, u11h_traversal_add_int]

/-- the traversal image is the polygon image. -/
theorem u11h_range_traversal [NeZero n] (P : LabelledTuple n) : range (traversal P) = embeddedPolygonImage P := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine mem_iUnion.mpr ⟨((⌊x⌋ : ℤ) : ZMod n), Int.fract x, Int.fract_nonneg x, (Int.fract_lt_one x).le, rfl⟩
  · intro hz
    obtain ⟨i, t, ht0, ht1, rfl⟩ := mem_iUnion.mp hz
    refine ⟨((i.val : ℕ) : ℝ) + t, ?_⟩
    have := ea_traversal_eq_on_Icc P (i.val : ℤ) (y := ((i.val : ℕ) : ℝ) + t) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [this]
    simp [edgePoint]

/-- every traversal point is reached from `[0, n]`. -/
theorem u11h_exists_reduce [NeZero n] (P : LabelledTuple n) (x : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) n, traversal P t = traversal P x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set m : ℤ := ⌊x / n⌋ with hm
  refine ⟨x + (-m : ℤ) * n, ⟨?_, ?_⟩, u11h_traversal_add_int P x (-m)⟩
  · have := Int.floor_le (x / n)
    have := (le_div_iff₀ hn0).mp this
    push_cast; linarith
  · have := Int.lt_floor_add_one (x / n)
    have := (div_lt_iff₀ hn0).mp this
    push_cast; linarith

/-- continuity, image and injectivity of a set homeomorphism. -/
theorem u11h_isHomeoOnto_cont_inj {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} {S' : Set β} {f : α → β} (hf : IsHomeoOnto S S' f) :
    ContinuousOn f S ∧ MapsTo f S S' ∧ InjOn f S := by
  obtain ⟨e, he⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : domRestrict S f = fun z => (e z : β) := funext fun z => (he z).symm
    rw [this]; exact continuous_subtype_val.comp e.continuous
  · intro z hz; rw [← he ⟨z, hz⟩]; exact (e ⟨z, hz⟩).2
  · intro z hz w hw hzw
    have : e ⟨z, hz⟩ = e ⟨w, hw⟩ := Subtype.ext (by rw [he, he]; exact hzw)
    exact congrArg Subtype.val (e.injective this)

/-- The traversal parametrisation of the frontier through a disc parametrisation `f`:
`q x = f ↑(traversal P x)` is continuous, lands in the frontier, covers it, and identifies exactly
the traversal identifications. -/
theorem u11h_param_facts [NeZero n] (P : LabelledTuple n) {S : Set Sphere}
    (hCS : sphereCircle P ⊆ S) {D : Set Plane} {f : Sphere → Plane} (hf : IsHomeoOnto S D f)
    (hB : f '' sphereCircle P = frontier D) :
    Continuous (fun x : ℝ => f ((traversal P x : Plane) : Sphere)) ∧
      (∀ x : ℝ, f ((traversal P x : Plane) : Sphere) ∈ frontier D) ∧
      (∀ y ∈ frontier D, ∃ x : ℝ, f ((traversal P x : Plane) : Sphere) = y) ∧
      (∀ x y : ℝ, f ((traversal P x : Plane) : Sphere) = f ((traversal P y : Plane) : Sphere) ↔
        traversal P x = traversal P y) := by
  obtain ⟨hfc, -, hfi⟩ := u11h_isHomeoOnto_cont_inj hf
  have hcirc : ∀ x : ℝ, ((traversal P x : Plane) : Sphere) ∈ sphereCircle P := fun x =>
    ⟨traversal P x, (u11h_range_traversal P) ▸ mem_range_self x, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hfc.comp_continuous (continuous_coe.comp (continuous_traversal P)) fun x => hCS (hcirc x)
  · intro x; rw [← hB]; exact ⟨_, hcirc x, rfl⟩
  · intro y hy
    rw [← hB] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← u11h_range_traversal P] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  · intro x y
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have := hfi (hCS (hcirc x)) (hCS (hcirc y)) h
    exact coe_eq_coe.mp this

open Classical Topology in
/-- Abstract form of `U11_boundary_homeo_of_lift`: the closed regions are replaced by any sets
`S ⊇ sphereCircle P`, `S' ⊇ sphereCircle P'`. -/
theorem u11h_boundary_homeo_aux [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {S S' : Set Sphere} (hCS : sphereCircle P ⊆ S) (hCS' : sphereCircle P' ⊆ S')
    {D D' : Set Plane} {f f' : Sphere → Plane} (hD : Link.IsDisc D)
    (hf : IsHomeoOnto S D f) (hf' : IsHomeoOnto S' D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ β : Plane → Plane, IsHomeoOnto (frontier D) (frontier D') β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  obtain ⟨ε, hε, hper, hinj, hsurj⟩ := u11h_lift_facts hn' P P' s s' hφ
  obtain ⟨hqc, hqf, hqs, hqi⟩ := u11h_param_facts P hCS hf hB
  obtain ⟨hqc', hqf', hqs', hqi'⟩ := u11h_param_facts P' hCS' hf' hB'
  set q : ℝ → Plane := fun x => f ((traversal P x : Plane) : Sphere) with hq
  set q' : ℝ → Plane := fun x => f' ((traversal P' x : Plane) : Sphere) with hq'
  -- the induced map on the frontier
  let β₀ : frontier D → frontier D' := fun y => ⟨q' (φ (choose (hqs y.1 y.2))), hqf' _⟩
  have key : ∀ x : ℝ, β₀ ⟨q x, hqf x⟩ = ⟨q' (φ x), hqf' _⟩ := by
    intro x
    apply Subtype.ext
    show q' (φ (choose (hqs (q x) (hqf x)))) = q' (φ x)
    have h1 : q (choose (hqs (q x) (hqf x))) = q x := choose_spec (hqs (q x) (hqf x))
    have h2 := (hqi _ _).mp h1
    show f' _ = f' _
    rw [u11h_traversal_congr hn hP P' hε hper h2]
  -- continuity via the quotient map from `[0, n]`
  have : CompactSpace (Icc (0 : ℝ) n) := isCompact_iff_compactSpace.mp isCompact_Icc
  let Q : Icc (0 : ℝ) n → frontier D := fun t => ⟨q t.1, hqf t.1⟩
  have hQc : Continuous Q := (hqc.comp continuous_subtype_val).subtype_mk _
  have hQs : Function.Surjective Q := by
    intro y
    obtain ⟨x, hx⟩ := hqs y.1 y.2
    obtain ⟨t, ht, htx⟩ := u11h_exists_reduce P x
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    show q t = y.1
    rw [← hx]; show f _ = f _; rw [htx]
  have hQq : IsQuotientMap Q := hQc.isClosedMap.isQuotientMap hQc hQs
  have hβc : Continuous β₀ := by
    rw [hQq.continuous_iff]
    have : β₀ ∘ Q = fun t => ⟨q' (φ t.1), hqf' _⟩ := funext fun t => key t.1
    rw [this]
    exact ((hqc'.comp hφ.continuous).comp continuous_subtype_val).subtype_mk _
  have hβbij : Function.Bijective β₀ := by
    constructor
    · intro y₁ y₂ h
      obtain ⟨x₁, hx₁⟩ := hqs y₁.1 y₁.2
      obtain ⟨x₂, hx₂⟩ := hqs y₂.1 y₂.2
      have e₁ : y₁ = ⟨q x₁, hqf x₁⟩ := Subtype.ext hx₁.symm
      have e₂ : y₂ = ⟨q x₂, hqf x₂⟩ := Subtype.ext hx₂.symm
      rw [e₁, e₂, key, key] at h
      have h3 : q' (φ x₁) = q' (φ x₂) := congrArg Subtype.val h
      have h4 := (hqi' _ _).mp h3
      have h5 := u11h_traversal_congr_inv hn' P hP' hε hper hinj h4
      rw [e₁, e₂]
      exact Subtype.ext ((hqi _ _).mpr h5)
    · intro y'
      obtain ⟨x', hx'⟩ := hqs' y'.1 y'.2
      obtain ⟨x, rfl⟩ := hsurj x'
      exact ⟨⟨q x, hqf x⟩, by rw [key]; exact Subtype.ext hx'⟩
  have : CompactSpace (frontier D) := isCompact_iff_compactSpace.mp
    (hD.2.1.of_isClosed_subset isClosed_frontier hD.2.1.isClosed.frontier_subset)
  let E : frontier D ≃ₜ frontier D' :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective β₀ hβbij) hβc
  refine ⟨fun y => if h : y ∈ frontier D then (β₀ ⟨y, h⟩ : Plane) else 0, ⟨E, ?_⟩, ?_⟩
  · intro z; simp only [z.2, ↓reduceDIte]; rfl
  · intro x
    simp only [hqf x, ↓reduceDIte]
    have := congrArg Subtype.val (key x)
    exact this

/-- 57b for either side (consumes `U7_pl_discs_inner` / `U8_pl_discs_outer`). -/
theorem u11h_pl_disc [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P) (L : ℝ)
    (hL : InsideModel L P) (s : Side) :
    IsPLDiscSphere L (closure (regionOf P s)) (sphereCircle P) := by
  cases s with
  | inner => exact U7_pl_discs_inner hn P hP L hL
  | outer => exact U8_pl_discs_outer hn P hP L hL

/-- The circle lies in the closure of each region (the `B ⊆ S` clause of 57b, via
`U4_exists_insideModel`). -/
theorem u11h_circle_subset_closure [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    (s : Side) : sphereCircle P ⊆ closure (regionOf P s) := by
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨D, f, -, h, -⟩ := u11h_pl_disc hn P hP L hL s
  exact h

/-- U11 (sm-3:433-434 "continuous positive boundary map", FR-TD-10): a positive boundary lift `φ`,
conjugated by two disc parametrisations, is a homeomorphism of the model frontiers. -/
theorem U11_boundary_homeo_of_lift [NeZero n] {n' : ℕ} [NeZero n'] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Embedded P) (hn' : 3 ≤ n') (P' : LabelledTuple n') (hP' : Embedded P') (s s' : Side)
    {D D' : Set Plane} {f f' : Sphere → Plane} (hD : Link.IsDisc D) (hD' : Link.IsDisc D')
    (hf : IsHomeoOnto (closure (regionOf P s)) D f) (hf' : IsHomeoOnto (closure (regionOf P' s')) D' f')
    (hB : f '' sphereCircle P = frontier D) (hB' : f' '' sphereCircle P' = frontier D')
    {φ : ℝ → ℝ} (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ β : Plane → Plane, IsHomeoOnto (frontier D) (frontier D') β ∧
      ∀ x : ℝ, β (f ((traversal P x : Plane) : Sphere)) = f' ((traversal P' (φ x) : Plane) : Sphere) := by
  exact u11h_boundary_homeo_aux hn P hP hn' P' hP' s s' (u11h_circle_subset_closure hn P hP s)
    (u11h_circle_subset_closure hn' P' hP' s') hD hf hf' hB hB' hφ

/-- U11 (57d, sm-3:433-434 / 537-542): a continuous positive boundary map extends to a topological
disc map `F = Φ'⁻¹ ∘ A ∘ Φ` (the positivity hypothesis is kept as printed and unused, FR-TD-5). -/
theorem U11_top_extension [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Embedded P)
    {n' : ℕ} [NeZero n'] (P' : LabelledTuple n') (hn' : 3 ≤ n') (hP' : Embedded P')
    (s s' : Side) (φ : ℝ → ℝ) (hφ : IsPositiveBoundaryLift P s P' s' φ) :
    ∃ F : Sphere → Sphere,
      IsHomeoOnto (closure (regionOf P s)) (closure (regionOf P' s')) F ∧
      ∀ x : ℝ, F ((traversal P x : Plane) : Sphere) = ((traversal P' (φ x) : Plane) : Sphere) := by
  classical
  obtain ⟨L, -, hL⟩ := U4_exists_insideModel P
  obtain ⟨L', -, hL'⟩ := U4_exists_insideModel P'
  obtain ⟨D, f, hD, -, hf, hB, -⟩ := u11h_pl_disc hn P hP L hL s
  obtain ⟨D', f', hD', hCS', hf', hB', -⟩ := u11h_pl_disc hn' P' hP' L' hL' s'
  obtain ⟨β, hβ, hβφ⟩ := U11_boundary_homeo_of_lift hn P hP hn' P' hP' s s' hD hD' hf hf' hB hB' hφ
  obtain ⟨A, hA, hAβ⟩ := U11_radial_extension hD hD' hβ
  obtain ⟨e, he⟩ := hf
  obtain ⟨e', he'⟩ := hf'
  obtain ⟨eA, heA⟩ := hA
  let finv' : Plane → Sphere := fun y => if h : y ∈ D' then (e'.symm ⟨y, h⟩ : Sphere) else ∞
  refine ⟨fun z => finv' (A (f z)), ⟨e.trans (eA.trans e'.symm), ?_⟩, ?_⟩
  · intro z
    show (e'.symm (eA (e z)) : Sphere) = finv' (A (f z))
    have h1 : (eA (e z) : Plane) = A (f z) := by rw [heA, he]
    have h2 : A (f z) ∈ D' := h1 ▸ (eA (e z)).2
    simp only [finv', h2, ↓reduceDIte]
    have h3 : (⟨A (f z), h2⟩ : D') = eA (e z) := Subtype.ext h1.symm
    rw [h3]
  · intro x
    have hz : ((traversal P x : Plane) : Sphere) ∈ sphereCircle P :=
      ⟨_, (u11h_range_traversal P) ▸ mem_range_self x, rfl⟩
    have hfz : f ((traversal P x : Plane) : Sphere) ∈ frontier D := hB ▸ ⟨_, hz, rfl⟩
    show finv' (A (f _)) = _
    rw [hAβ _ hfz, hβφ x]
    have hz' : ((traversal P' (φ x) : Plane) : Sphere) ∈ closure (regionOf P' s') :=
      hCS' ⟨_, (u11h_range_traversal P') ▸ mem_range_self (φ x), rfl⟩
    have hmem : f' ((traversal P' (φ x) : Plane) : Sphere) ∈ D' := by
      rw [← he' ⟨_, hz'⟩]; exact (e' ⟨_, hz'⟩).2
    simp only [finv', hmem, ↓reduceDIte]
    have : (⟨f' ((traversal P' (φ x) : Plane) : Sphere), hmem⟩ : D') = e' ⟨_, hz'⟩ :=
      Subtype.ext (he' ⟨_, hz'⟩).symm
    rw [this, e'.symm_apply_apply]

end SM
