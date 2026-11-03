import Gemini.SimpleComponentFusedTelescope

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.Gemini

open DirectGLSSW DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients
open Equiv PermutationOrbits

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Part 1: The Algebraic Half-Open Ray-Crossing Function `rayPhi` -/

def rayPhi (u v : PlanarPoint ℝ) : ℤ :=
  if u.2 ≤ 0 ∧ 0 < v.2 ∧ 0 < planarDet u v then 1
  else if v.2 ≤ 0 ∧ 0 < u.2 ∧ planarDet u v < 0 then -1
  else 0

theorem rayPhi_of_le_le (u v : PlanarPoint ℝ) (hu : u.2 ≤ 0) (hv : v.2 ≤ 0) :
    rayPhi u v = 0 := by
  unfold rayPhi
  have h1 : ¬ (u.2 ≤ 0 ∧ 0 < v.2 ∧ 0 < planarDet u v) := fun h => not_lt_of_ge hv h.2.1
  have h2 : ¬ (v.2 ≤ 0 ∧ 0 < u.2 ∧ planarDet u v < 0) := fun h => not_lt_of_ge hu h.2.1
  rw [if_neg h1, if_neg h2]

theorem rayPhi_of_gt_gt (u v : PlanarPoint ℝ) (hu : 0 < u.2) (hv : 0 < v.2) :
    rayPhi u v = 0 := by
  unfold rayPhi
  have h1 : ¬ (u.2 ≤ 0 ∧ 0 < v.2 ∧ 0 < planarDet u v) := fun h => not_le_of_gt hu h.1
  have h2 : ¬ (v.2 ≤ 0 ∧ 0 < u.2 ∧ planarDet u v < 0) := fun h => not_le_of_gt hv h.1
  rw [if_neg h1, if_neg h2]

theorem rayPhi_of_le_gt (u v : PlanarPoint ℝ) (hu : u.2 ≤ 0) (hv : 0 < v.2) :
    rayPhi u v = if 0 < planarDet u v then 1 else 0 := by
  unfold rayPhi
  have h2 : ¬ (v.2 ≤ 0 ∧ 0 < u.2 ∧ planarDet u v < 0) := fun h => not_le_of_gt hv h.1
  rw [if_neg h2]
  by_cases hd : 0 < planarDet u v <;> simp [hu, hv, hd]

theorem rayPhi_of_gt_le (u v : PlanarPoint ℝ) (hu : 0 < u.2) (hv : v.2 ≤ 0) :
    rayPhi u v = if planarDet u v < 0 then -1 else 0 := by
  unfold rayPhi
  have h1 : ¬ (u.2 ≤ 0 ∧ 0 < v.2 ∧ 0 < planarDet u v) := fun h => not_le_of_gt hu h.1
  rw [if_neg h1]
  by_cases hd : planarDet u v < 0 <;> simp [hu, hv, hd]

theorem rayPhi_swap (u v : PlanarPoint ℝ) :
    rayPhi v u = -rayPhi u v := by
  by_cases hu : u.2 ≤ 0 <;> by_cases hv : v.2 ≤ 0
  · rw [rayPhi_of_le_le v u hv hu, rayPhi_of_le_le u v hu hv, neg_zero]
  · have hv' : 0 < v.2 := not_le.mp hv
    rw [rayPhi_of_gt_le v u hv' hu, rayPhi_of_le_gt u v hu hv', planarDet_swap v u]
    split_ifs <;> linarith
  · have hu' : 0 < u.2 := not_le.mp hu
    rw [rayPhi_of_le_gt v u hv hu', rayPhi_of_gt_le u v hu' hv, planarDet_swap v u]
    split_ifs <;> linarith
  · rw [rayPhi_of_gt_gt v u (not_le.mp hv) (not_le.mp hu),
        rayPhi_of_gt_gt u v (not_le.mp hu) (not_le.mp hv), neg_zero]

theorem rayPhi_self (u : PlanarPoint ℝ) :
    rayPhi u u = 0 := by
  have h := rayPhi_swap u u
  omega

theorem planarDet_affinePoint_right (u w : PlanarPoint ℝ) (t : ℝ) :
    planarDet u (affinePoint u w t) = t * planarDet u w := by
  dsimp [planarDet, affinePoint]
  ring

theorem planarDet_affinePoint_left (u w : PlanarPoint ℝ) (t : ℝ) :
    planarDet (affinePoint u w t) w = (1 - t) * planarDet u w := by
  dsimp [planarDet, affinePoint]
  ring

theorem affinePoint_snd (u w : PlanarPoint ℝ) (t : ℝ) :
    (affinePoint u w t).2 = (1 - t) * u.2 + t * w.2 := by
  dsimp [affinePoint]
  ring

theorem rayPhi_collinear_add (u w : PlanarPoint ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    rayPhi u (affinePoint u w t) + rayPhi (affinePoint u w t) w = rayPhi u w := by
  let m := affinePoint u w t
  have h1t : 0 < 1 - t := by linarith
  have hm2 : m.2 = (1 - t) * u.2 + t * w.2 := affinePoint_snd u w t
  have hdet_um : planarDet u m = t * planarDet u w := planarDet_affinePoint_right u w t
  have hdet_mw : planarDet m w = (1 - t) * planarDet u w := planarDet_affinePoint_left u w t
  have hum_pos : 0 < planarDet u m ↔ 0 < planarDet u w := by
    rw [hdet_um]
    exact mul_pos_iff_of_pos_left ht0
  have hum_neg : planarDet u m < 0 ↔ planarDet u w < 0 := by
    rw [hdet_um]
    constructor <;> intro h <;> nlinarith
  have hmw_pos : 0 < planarDet m w ↔ 0 < planarDet u w := by
    rw [hdet_mw]
    exact mul_pos_iff_of_pos_left h1t
  have hmw_neg : planarDet m w < 0 ↔ planarDet u w < 0 := by
    rw [hdet_mw]
    constructor <;> intro h <;> nlinarith
  change rayPhi u m + rayPhi m w = rayPhi u w
  by_cases hu : u.2 ≤ 0 <;> by_cases hw : w.2 ≤ 0 <;> by_cases hm : m.2 ≤ 0
  · rw [rayPhi_of_le_le u m hu hm, rayPhi_of_le_le m w hm hw, rayPhi_of_le_le u w hu hw]; ring
  · exfalso; nlinarith
  · have hw' : 0 < w.2 := not_le.mp hw
    rw [rayPhi_of_le_le u m hu hm, rayPhi_of_le_gt m w hm hw', rayPhi_of_le_gt u w hu hw']
    simp only [hmw_pos]
    ring
  · have hw' : 0 < w.2 := not_le.mp hw
    have hm' : 0 < m.2 := not_le.mp hm
    rw [rayPhi_of_le_gt u m hu hm', rayPhi_of_gt_gt m w hm' hw', rayPhi_of_le_gt u w hu hw']
    simp only [hum_pos]
    ring
  · have hu' : 0 < u.2 := not_le.mp hu
    rw [rayPhi_of_gt_le u m hu' hm, rayPhi_of_le_le m w hm hw, rayPhi_of_gt_le u w hu' hw]
    simp only [hum_neg]
    ring
  · have hu' : 0 < u.2 := not_le.mp hu
    have hm' : 0 < m.2 := not_le.mp hm
    rw [rayPhi_of_gt_gt u m hu' hm', rayPhi_of_gt_le m w hm' hw, rayPhi_of_gt_le u w hu' hw]
    simp only [hmw_neg]
    ring
  · exfalso; nlinarith
  · have hu' : 0 < u.2 := not_le.mp hu
    have hw' : 0 < w.2 := not_le.mp hw
    have hm' : 0 < m.2 := not_le.mp hm
    rw [rayPhi_of_gt_gt u m hu' hm', rayPhi_of_gt_gt m w hm' hw', rayPhi_of_gt_gt u w hu' hw']
    ring

/-! ### Part 2: The Triangle Functional `triPhi` and Cramer's Rule -/

def triPhi (u v w : PlanarPoint ℝ) : ℤ :=
  rayPhi u v + rayPhi v w + rayPhi w u

theorem triPhi_rotate (u v w : PlanarPoint ℝ) :
    triPhi v w u = triPhi u v w := by
  unfold triPhi
  ring

theorem cramer_origin_fst (u v w : PlanarPoint ℝ) :
    planarDet v w * u.1 + planarDet w u * v.1 + planarDet u v * w.1 = 0 := by
  dsimp [planarDet]
  ring

theorem cramer_origin_snd (u v w : PlanarPoint ℝ) :
    planarDet v w * u.2 + planarDet w u * v.2 + planarDet u v * w.2 = 0 := by
  dsimp [planarDet]
  ring

theorem triPhi_all_le_zero (u v w : PlanarPoint ℝ)
    (hu : u.2 ≤ 0) (hv : v.2 ≤ 0) (hw : w.2 ≤ 0) :
    triPhi u v w = 0 := by
  unfold triPhi
  rw [rayPhi_of_le_le u v hu hv, rayPhi_of_le_le v w hv hw, rayPhi_of_le_le w u hw hu]
  ring

theorem triPhi_all_gt_zero (u v w : PlanarPoint ℝ)
    (hu : 0 < u.2) (hv : 0 < v.2) (hw : 0 < w.2) :
    triPhi u v w = 0 := by
  unfold triPhi
  rw [rayPhi_of_gt_gt u v hu hv, rayPhi_of_gt_gt v w hv hw, rayPhi_of_gt_gt w u hw hu]
  ring

theorem triPhi_one_le_two_gt (u v w : PlanarPoint ℝ)
    (hu : u.2 ≤ 0) (hv : 0 < v.2) (hw : 0 < w.2) :
    triPhi u v w =
      (if 0 < planarDet u v then 1 else 0) - (if planarDet w u < 0 then 1 else 0) := by
  unfold triPhi
  rw [rayPhi_of_le_gt u v hu hv, rayPhi_of_gt_gt v w hv hw, rayPhi_of_gt_le w u hw hu]
  split_ifs <;> ring

theorem triPhi_one_gt_two_le (u v w : PlanarPoint ℝ)
    (hu : 0 < u.2) (hv : v.2 ≤ 0) (hw : w.2 ≤ 0) :
    triPhi u v w =
      (if 0 < planarDet w u then 1 else 0) - (if planarDet u v < 0 then 1 else 0) := by
  unfold triPhi
  rw [rayPhi_of_gt_le u v hu hv, rayPhi_of_le_le v w hv hw, rayPhi_of_le_gt w u hw hu]
  split_ifs <;> ring

theorem triPhi_of_pos (u v w : PlanarPoint ℝ)
    (ha : 0 < planarDet v w) (hb : 0 < planarDet w u) (hc : 0 < planarDet u v) :
    triPhi u v w = 1 := by
  have hcr := cramer_origin_snd u v w
  by_cases hu : u.2 ≤ 0 <;> by_cases hv : v.2 ≤ 0 <;> by_cases hw : w.2 ≤ 0
  · have hu0 : u.2 = 0 := by nlinarith
    have hv0 : v.2 = 0 := by nlinarith
    have hc0 : planarDet u v = 0 := by
      dsimp [planarDet]
      rw [hu0, hv0]
      ring
    linarith
  · rw [← triPhi_rotate u v w, ← triPhi_rotate v w u]
    rw [triPhi_one_gt_two_le w u v (not_le.mp hw) hu hv]
    split_ifs <;> linarith
  · rw [← triPhi_rotate u v w]
    rw [triPhi_one_gt_two_le v w u (not_le.mp hv) hw hu]
    split_ifs <;> linarith
  · rw [triPhi_one_le_two_gt u v w hu (not_le.mp hv) (not_le.mp hw)]
    split_ifs <;> linarith
  · rw [triPhi_one_gt_two_le u v w (not_le.mp hu) hv hw]
    split_ifs <;> linarith
  · rw [← triPhi_rotate u v w]
    rw [triPhi_one_le_two_gt v w u hv (not_le.mp hw) (not_le.mp hu)]
    split_ifs <;> linarith
  · rw [← triPhi_rotate u v w, ← triPhi_rotate v w u]
    rw [triPhi_one_le_two_gt w u v hw (not_le.mp hu) (not_le.mp hv)]
    split_ifs <;> linarith
  · exfalso
    have hu' : 0 < u.2 := not_le.mp hu
    have hv' : 0 < v.2 := not_le.mp hv
    have hw' : 0 < w.2 := not_le.mp hw
    nlinarith

theorem triPhi_of_neg (u v w : PlanarPoint ℝ)
    (ha : planarDet v w < 0) (hb : planarDet w u < 0) (hc : planarDet u v < 0) :
    triPhi u v w = -1 := by
  have hcr := cramer_origin_snd u v w
  by_cases hu : u.2 ≤ 0 <;> by_cases hv : v.2 ≤ 0 <;> by_cases hw : w.2 ≤ 0
  · have hu0 : u.2 = 0 := by nlinarith
    have hv0 : v.2 = 0 := by nlinarith
    have hc0 : planarDet u v = 0 := by
      dsimp [planarDet]
      rw [hu0, hv0]
      ring
    linarith
  · rw [← triPhi_rotate u v w, ← triPhi_rotate v w u]
    rw [triPhi_one_gt_two_le w u v (not_le.mp hw) hu hv]
    split_ifs <;> linarith
  · rw [← triPhi_rotate u v w]
    rw [triPhi_one_gt_two_le v w u (not_le.mp hv) hw hu]
    split_ifs <;> linarith
  · rw [triPhi_one_le_two_gt u v w hu (not_le.mp hv) (not_le.mp hw)]
    split_ifs <;> linarith
  · rw [triPhi_one_gt_two_le u v w (not_le.mp hu) hv hw]
    split_ifs <;> linarith
  · rw [← triPhi_rotate u v w]
    rw [triPhi_one_le_two_gt v w u hv (not_le.mp hw) (not_le.mp hu)]
    split_ifs <;> linarith
  · rw [← triPhi_rotate u v w, ← triPhi_rotate v w u]
    rw [triPhi_one_le_two_gt w u v hw (not_le.mp hu) (not_le.mp hv)]
    split_ifs <;> linarith
  · exfalso
    have hu' : 0 < u.2 := not_le.mp hu
    have hv' : 0 < v.2 := not_le.mp hv
    have hw' : 0 < w.2 := not_le.mp hw
    nlinarith

private theorem triPhi_ne_zero_one_le_two_gt_aux (u v w : PlanarPoint ℝ)
    (hu : u.2 ≤ 0) (hv : 0 < v.2) (hw : 0 < w.2) (hne : triPhi u v w ≠ 0) :
    (0 ≤ planarDet v w ∧ 0 ≤ planarDet w u ∧ 0 ≤ planarDet u v ∧
      0 < planarDet v w + planarDet w u + planarDet u v) ∨
    (planarDet v w ≤ 0 ∧ planarDet w u ≤ 0 ∧ planarDet u v ≤ 0 ∧
      planarDet v w + planarDet w u + planarDet u v < 0) := by
  have hcr := cramer_origin_snd u v w
  rw [triPhi_one_le_two_gt u v w hu hv hw] at hne
  by_cases hc : 0 < planarDet u v <;> by_cases hb : planarDet w u < 0
  · simp [hc, hb] at hne
  · left
    have hb' : 0 ≤ planarDet w u := not_lt.mp hb
    have hau : planarDet v w * u.2 < 0 := by nlinarith
    have ha : 0 < planarDet v w := by nlinarith
    exact ⟨le_of_lt ha, hb', le_of_lt hc, by linarith⟩
  · right
    have hc' : planarDet u v ≤ 0 := not_lt.mp hc
    have hau : 0 < planarDet v w * u.2 := by nlinarith
    have ha : planarDet v w < 0 := by nlinarith
    exact ⟨le_of_lt ha, le_of_lt hb, hc', by linarith⟩
  · simp [hc, hb] at hne

private theorem triPhi_ne_zero_one_gt_two_le_aux (u v w : PlanarPoint ℝ)
    (hu : 0 < u.2) (hv : v.2 ≤ 0) (hw : w.2 ≤ 0) (hne : triPhi u v w ≠ 0) :
    (0 ≤ planarDet v w ∧ 0 ≤ planarDet w u ∧ 0 ≤ planarDet u v ∧
      0 < planarDet v w + planarDet w u + planarDet u v) ∨
    (planarDet v w ≤ 0 ∧ planarDet w u ≤ 0 ∧ planarDet u v ≤ 0 ∧
      planarDet v w + planarDet w u + planarDet u v < 0) := by
  have hcr := cramer_origin_snd u v w
  rw [triPhi_one_gt_two_le u v w hu hv hw] at hne
  by_cases hb : 0 < planarDet w u <;> by_cases hc : planarDet u v < 0
  · simp [hb, hc] at hne
  · left
    have hc' : 0 ≤ planarDet u v := not_lt.mp hc
    have hau : 0 ≤ planarDet v w * u.2 := by nlinarith
    have ha : 0 ≤ planarDet v w := nonneg_of_mul_nonneg_left hau hu
    exact ⟨ha, le_of_lt hb, hc', by linarith⟩
  · right
    have hb' : planarDet w u ≤ 0 := not_lt.mp hb
    have hau : planarDet v w * u.2 ≤ 0 := by nlinarith
    have ha : planarDet v w ≤ 0 := nonpos_of_mul_nonpos_left hau hu
    exact ⟨ha, hb', le_of_lt hc, by linarith⟩
  · simp [hb, hc] at hne

theorem triPhi_ne_zero_imp_same_sign (u v w : PlanarPoint ℝ)
    (hne : triPhi u v w ≠ 0) :
    (0 ≤ planarDet v w ∧ 0 ≤ planarDet w u ∧ 0 ≤ planarDet u v ∧
      0 < planarDet v w + planarDet w u + planarDet u v) ∨
    (planarDet v w ≤ 0 ∧ planarDet w u ≤ 0 ∧ planarDet u v ≤ 0 ∧
      planarDet v w + planarDet w u + planarDet u v < 0) := by
  by_cases hu : u.2 ≤ 0 <;> by_cases hv : v.2 ≤ 0 <;> by_cases hw : w.2 ≤ 0
  · exact False.elim (hne (triPhi_all_le_zero u v w hu hv hw))
  · have hne' : triPhi w u v ≠ 0 := by
      rwa [triPhi_rotate v w u, triPhi_rotate u v w]
    rcases triPhi_ne_zero_one_gt_two_le_aux w u v (not_le.mp hw) hu hv hne' with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h2, h3, h1, by linarith⟩
    · exact Or.inr ⟨h2, h3, h1, by linarith⟩
  · have hne' : triPhi v w u ≠ 0 := by
      rwa [triPhi_rotate u v w]
    rcases triPhi_ne_zero_one_gt_two_le_aux v w u (not_le.mp hv) hw hu hne' with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h3, h1, h2, by linarith⟩
    · exact Or.inr ⟨h3, h1, h2, by linarith⟩
  · exact triPhi_ne_zero_one_le_two_gt_aux u v w hu (not_le.mp hv) (not_le.mp hw) hne
  · exact triPhi_ne_zero_one_gt_two_le_aux u v w (not_le.mp hu) hv hw hne
  · have hne' : triPhi v w u ≠ 0 := by
      rwa [triPhi_rotate u v w]
    rcases triPhi_ne_zero_one_le_two_gt_aux v w u hv (not_le.mp hw) (not_le.mp hu) hne' with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h3, h1, h2, by linarith⟩
    · exact Or.inr ⟨h3, h1, h2, by linarith⟩
  · have hne' : triPhi w u v ≠ 0 := by
      rwa [triPhi_rotate v w u, triPhi_rotate u v w]
    rcases triPhi_ne_zero_one_le_two_gt_aux w u v hw (not_le.mp hu) (not_le.mp hv) hne' with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h2, h3, h1, by linarith⟩
    · exact Or.inr ⟨h2, h3, h1, by linarith⟩
  · exact False.elim (hne (triPhi_all_gt_zero u v w (not_le.mp hu) (not_le.mp hv) (not_le.mp hw)))

theorem triPhi_of_mixed (u v w : PlanarPoint ℝ)
    (h1 : ¬ (0 ≤ planarDet v w ∧ 0 ≤ planarDet w u ∧ 0 ≤ planarDet u v))
    (h2 : ¬ (planarDet v w ≤ 0 ∧ planarDet w u ≤ 0 ∧ planarDet u v ≤ 0)) :
    triPhi u v w = 0 := by
  by_contra hne
  rcases triPhi_ne_zero_imp_same_sign u v w hne with ⟨ha, hb, hc, _⟩ | ⟨ha, hb, hc, _⟩
  · exact h1 ⟨ha, hb, hc⟩
  · exact h2 ⟨ha, hb, hc⟩

theorem triPhi_ne_zero_imp_convex_origin (u v w : PlanarPoint ℝ)
    (hne : triPhi u v w ≠ 0) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      α • u + β • v + γ • w = 0 := by
  let a := planarDet v w
  let b := planarDet w u
  let c := planarDet u v
  let S := a + b + c
  have h1 := cramer_origin_fst u v w
  have h2 := cramer_origin_snd u v w
  rcases triPhi_ne_zero_imp_same_sign u v w hne with ⟨ha, hb, hc, hS⟩ | ⟨ha, hb, hc, hS⟩
  · have hSnz : S ≠ 0 := ne_of_gt hS
    refine ⟨a / S, b / S, c / S, div_nonneg ha (le_of_lt hS),
      div_nonneg hb (le_of_lt hS), div_nonneg hc (le_of_lt hS), ?_, ?_⟩
    · calc
        a / S + b / S + c / S = S / S := by dsimp [S]; ring
        _ = 1 := div_self hSnz
    · ext
      · change (a / S) * u.1 + (b / S) * v.1 + (c / S) * w.1 = 0
        calc
          (a / S) * u.1 + (b / S) * v.1 + (c / S) * w.1 =
              (a * u.1 + b * v.1 + c * w.1) / S := by ring
          _ = 0 := by rw [h1, zero_div]
      · change (a / S) * u.2 + (b / S) * v.2 + (c / S) * w.2 = 0
        calc
          (a / S) * u.2 + (b / S) * v.2 + (c / S) * w.2 =
              (a * u.2 + b * v.2 + c * w.2) / S := by ring
          _ = 0 := by rw [h2, zero_div]
  · have hSneg : 0 < -S := neg_pos.mpr hS
    refine ⟨(-a) / (-S), (-b) / (-S), (-c) / (-S),
      div_nonneg (neg_nonneg.mpr ha) (le_of_lt hSneg),
      div_nonneg (neg_nonneg.mpr hb) (le_of_lt hSneg),
      div_nonneg (neg_nonneg.mpr hc) (le_of_lt hSneg), ?_, ?_⟩
    · calc
        (-a) / (-S) + (-b) / (-S) + (-c) / (-S) = (-S) / (-S) := by dsimp [S]; ring
        _ = 1 := div_self (ne_of_gt hSneg)
    · ext
      · change ((-a) / (-S)) * u.1 + ((-b) / (-S)) * v.1 + ((-c) / (-S)) * w.1 = 0
        calc
          ((-a) / (-S)) * u.1 + ((-b) / (-S)) * v.1 + ((-c) / (-S)) * w.1 =
              -(a * u.1 + b * v.1 + c * w.1) / (-S) := by ring
          _ = 0 := by rw [h1, neg_zero, zero_div]
      · change ((-a) / (-S)) * u.2 + ((-b) / (-S)) * v.2 + ((-c) / (-S)) * w.2 = 0
        calc
          ((-a) / (-S)) * u.2 + ((-b) / (-S)) * v.2 + ((-c) / (-S)) * w.2 =
              -(a * u.2 + b * v.2 + c * w.2) / (-S) := by ring
          _ = 0 := by rw [h2, neg_zero, zero_div]

/-! ### Part 3: The Parallelogram Functional `paraPsi` and Core Lemmas A & B -/

def paraPsi (a0 a1 b0 b1 : PlanarPoint ℝ) : ℤ :=
  rayPhi (a0 - b0) (a1 - b0) + rayPhi (a1 - b0) (a1 - b1) -
    rayPhi (a0 - b1) (a1 - b1) - rayPhi (a0 - b0) (a0 - b1)

theorem paraPsi_eq_triPhi_add (a0 a1 b0 b1 : PlanarPoint ℝ) :
    paraPsi a0 a1 b0 b1 =
      triPhi (a0 - b0) (a1 - b0) (a1 - b1) +
        triPhi (a0 - b0) (a1 - b1) (a0 - b1) := by
  unfold paraPsi triPhi
  rw [rayPhi_swap (a1 - b1) (a0 - b0),
      rayPhi_swap (a1 - b1) (a0 - b1),
      rayPhi_swap (a0 - b1) (a0 - b0)]
  ring

theorem affinePoint_sub_const (a0 a1 b : PlanarPoint ℝ) (s : ℝ) :
    affinePoint a0 a1 s - b = affinePoint (a0 - b) (a1 - b) s := by
  ext <;> dsimp [affinePoint] <;> ring

theorem const_sub_affinePoint (a b0 b1 : PlanarPoint ℝ) (t : ℝ) :
    a - affinePoint b0 b1 t = affinePoint (a - b0) (a - b1) t := by
  ext <;> dsimp [affinePoint] <;> ring

theorem paraPsi_collinear_left (a0 a1 b0 b1 : PlanarPoint ℝ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    paraPsi a0 (affinePoint a0 a1 s) b0 b1 +
      paraPsi (affinePoint a0 a1 s) a1 b0 b1 = paraPsi a0 a1 b0 b1 := by
  unfold paraPsi
  have h0 : rayPhi (a0 - b0) (affinePoint a0 a1 s - b0) +
      rayPhi (affinePoint a0 a1 s - b0) (a1 - b0) = rayPhi (a0 - b0) (a1 - b0) := by
    rw [affinePoint_sub_const]
    exact rayPhi_collinear_add (a0 - b0) (a1 - b0) s hs0 hs1
  have h1 : rayPhi (a0 - b1) (affinePoint a0 a1 s - b1) +
      rayPhi (affinePoint a0 a1 s - b1) (a1 - b1) = rayPhi (a0 - b1) (a1 - b1) := by
    rw [affinePoint_sub_const]
    exact rayPhi_collinear_add (a0 - b1) (a1 - b1) s hs0 hs1
  linarith

theorem paraPsi_collinear_right (a0 a1 b0 b1 : PlanarPoint ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    paraPsi a0 a1 b0 (affinePoint b0 b1 t) +
      paraPsi a0 a1 (affinePoint b0 b1 t) b1 = paraPsi a0 a1 b0 b1 := by
  unfold paraPsi
  have h0 : rayPhi (a0 - b0) (a0 - affinePoint b0 b1 t) +
      rayPhi (a0 - affinePoint b0 b1 t) (a0 - b1) = rayPhi (a0 - b0) (a0 - b1) := by
    rw [const_sub_affinePoint]
    exact rayPhi_collinear_add (a0 - b0) (a0 - b1) t ht0 ht1
  have h1 : rayPhi (a1 - b0) (a1 - affinePoint b0 b1 t) +
      rayPhi (a1 - affinePoint b0 b1 t) (a1 - b1) = rayPhi (a1 - b0) (a1 - b1) := by
    rw [const_sub_affinePoint]
    exact rayPhi_collinear_add (a1 - b0) (a1 - b1) t ht0 ht1
  linarith

/-- Core Lemma A: Disjoint closed segments have `paraPsi = 0`. -/
theorem paraPsi_eq_zero_of_disjoint (a0 a1 b0 b1 : PlanarPoint ℝ)
    (hdisj : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      affinePoint a0 a1 s ≠ affinePoint b0 b1 t) :
    paraPsi a0 a1 b0 b1 = 0 := by
  rw [paraPsi_eq_triPhi_add]
  have h1 : triPhi (a0 - b0) (a1 - b0) (a1 - b1) = 0 := by
    by_contra hne
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hzero⟩ :=
      triPhi_ne_zero_imp_convex_origin (a0 - b0) (a1 - b0) (a1 - b1) hne
    have hx : α * (a0.1 - b0.1) + β * (a1.1 - b0.1) + γ * (a1.1 - b1.1) = 0 :=
      congrArg Prod.fst hzero
    have hy : α * (a0.2 - b0.2) + β * (a1.2 - b0.2) + γ * (a1.2 - b1.2) = 0 :=
      congrArg Prod.snd hzero
    have hα_eq : α = 1 - (β + γ) := by linarith
    have hpt : affinePoint a0 a1 (β + γ) = affinePoint b0 b1 γ := by
      rw [hα_eq] at hx hy
      ext <;> dsimp [affinePoint] <;> linarith
    exact hdisj (β + γ) γ (by linarith) (by linarith) hγ (by linarith) hpt
  have h2 : triPhi (a0 - b0) (a1 - b1) (a0 - b1) = 0 := by
    by_contra hne
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hzero⟩ :=
      triPhi_ne_zero_imp_convex_origin (a0 - b0) (a1 - b1) (a0 - b1) hne
    have hx : α * (a0.1 - b0.1) + β * (a1.1 - b1.1) + γ * (a0.1 - b1.1) = 0 :=
      congrArg Prod.fst hzero
    have hy : α * (a0.2 - b0.2) + β * (a1.2 - b1.2) + γ * (a0.2 - b1.2) = 0 :=
      congrArg Prod.snd hzero
    have hα_eq : α = 1 - (β + γ) := by linarith
    have hpt : affinePoint a0 a1 β = affinePoint b0 b1 (β + γ) := by
      rw [hα_eq] at hx hy
      ext <;> dsimp [affinePoint] <;> linarith
    exact hdisj β (β + γ) hβ (by linarith) (by linarith) (by linarith) hpt
  rw [h1, h2, add_zero]

private theorem paraPsi_interior_dets (a0 a1 b0 b1 : PlanarPoint ℝ) (s t : ℝ)
    (hpt : affinePoint a0 a1 s = affinePoint b0 b1 t) :
    let D := planarDet (a1 - a0) (b1 - b0)
    planarDet (a1 - b0) (a1 - b1) = -(1 - s) * D ∧
    planarDet (a1 - b1) (a0 - b0) = -(s - t) * D ∧
    planarDet (a0 - b0) (a1 - b0) = -t * D ∧
    planarDet (a1 - b1) (a0 - b1) = -(1 - t) * D ∧
    planarDet (a0 - b1) (a0 - b0) = -s * D ∧
    planarDet (a0 - b0) (a1 - b1) = -(t - s) * D := by
  intro D
  have hx : a0.1 - b0.1 = t * (b1.1 - b0.1) - s * (a1.1 - a0.1) := by
    have h := congrArg Prod.fst hpt
    dsimp [affinePoint] at h
    linarith
  have hy : a0.2 - b0.2 = t * (b1.2 - b0.2) - s * (a1.2 - a0.2) := by
    have h := congrArg Prod.snd hpt
    dsimp [affinePoint] at h
    linarith
  have hv10_x : a1.1 - b0.1 = (a0.1 - b0.1) + (a1.1 - a0.1) := by ring
  have hv10_y : a1.2 - b0.2 = (a0.2 - b0.2) + (a1.2 - a0.2) := by ring
  have hv01_x : a0.1 - b1.1 = (a0.1 - b0.1) - (b1.1 - b0.1) := by ring
  have hv01_y : a0.2 - b1.2 = (a0.2 - b0.2) - (b1.2 - b0.2) := by ring
  have hv11_x : a1.1 - b1.1 = (a0.1 - b0.1) + (a1.1 - a0.1) - (b1.1 - b0.1) := by ring
  have hv11_y : a1.2 - b1.2 = (a0.2 - b0.2) + (a1.2 - a0.2) - (b1.2 - b0.2) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (dsimp [D, planarDet];
     try rw [hv10_x]; try rw [hv10_y];
     try rw [hv01_x]; try rw [hv01_y];
     try rw [hv11_x]; try rw [hv11_y];
     try rw [hx]; try rw [hy];
     ring)

private theorem paraPsi_eq_of_interior_intersection_ne (a0 a1 b0 b1 : PlanarPoint ℝ)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hst : s ≠ t)
    (hpt : affinePoint a0 a1 s = affinePoint b0 b1 t)
    (hD : planarDet (a1 - a0) (b1 - b0) ≠ 0) :
    paraPsi a0 a1 b0 b1 =
      if 0 < planarDet (a1 - a0) (b1 - b0) then -1 else 1 := by
  obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩ := paraPsi_interior_dets a0 a1 b0 b1 s t hpt
  rw [paraPsi_eq_triPhi_add]
  let D := planarDet (a1 - a0) (b1 - b0)
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have ht1_zero : triPhi (a0 - b0) (a1 - b0) (a1 - b1) = 0 := by
      apply triPhi_of_mixed
      · rintro ⟨ha, hb, hc⟩
        rw [hd1] at ha; rw [hd2] at hb; rw [hd3] at hc
        rcases lt_or_gt_of_ne hD with hDn | hDp
        · nlinarith
        · nlinarith
      · rintro ⟨ha, hb, hc⟩
        rw [hd1] at ha; rw [hd2] at hb; rw [hd3] at hc
        rcases lt_or_gt_of_ne hD with hDn | hDp
        · nlinarith
        · nlinarith
    rw [ht1_zero, zero_add]
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · rw [if_neg (not_lt_of_gt hDn)]
      apply triPhi_of_pos
      · rw [hd4]; nlinarith
      · rw [hd5]; nlinarith
      · rw [hd6]; nlinarith
    · rw [if_pos hDp]
      apply triPhi_of_neg
      · rw [hd4]; nlinarith
      · rw [hd5]; nlinarith
      · rw [hd6]; nlinarith
  · have ht2_zero : triPhi (a0 - b0) (a1 - b1) (a0 - b1) = 0 := by
      apply triPhi_of_mixed
      · rintro ⟨ha, hb, hc⟩
        rw [hd4] at ha; rw [hd5] at hb; rw [hd6] at hc
        rcases lt_or_gt_of_ne hD with hDn | hDp
        · nlinarith
        · nlinarith
      · rintro ⟨ha, hb, hc⟩
        rw [hd4] at ha; rw [hd5] at hb; rw [hd6] at hc
        rcases lt_or_gt_of_ne hD with hDn | hDp
        · nlinarith
        · nlinarith
    rw [ht2_zero, add_zero]
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · rw [if_neg (not_lt_of_gt hDn)]
      apply triPhi_of_pos
      · rw [hd1]; nlinarith
      · rw [hd2]; nlinarith
      · rw [hd3]; nlinarith
    · rw [if_pos hDp]
      apply triPhi_of_neg
      · rw [hd1]; nlinarith
      · rw [hd2]; nlinarith
      · rw [hd3]; nlinarith

/-- Core Lemma B: Transverse interior-crossing segments have `paraPsi = -sign(D)`. -/
theorem paraPsi_eq_of_interior_intersection (a0 a1 b0 b1 : PlanarPoint ℝ)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hpt : affinePoint a0 a1 s = affinePoint b0 b1 t)
    (hD : planarDet (a1 - a0) (b1 - b0) ≠ 0) :
    paraPsi a0 a1 b0 b1 =
      if 0 < planarDet (a1 - a0) (b1 - b0) then -1 else 1 := by
  by_cases hst : s = t
  · subst t
    let m := affinePoint a0 a1 (s / 2)
    have hs2_pos : 0 < s / 2 := by linarith
    have hs2_lt1 : s / 2 < 1 := by linarith
    have hsplit := paraPsi_collinear_left a0 a1 b0 b1 (s / 2) hs2_pos hs2_lt1
    have hleft_zero : paraPsi a0 m b0 b1 = 0 := by
      apply paraPsi_eq_zero_of_disjoint
      intro u v hu0 hu1 hv0 hv1 huv
      have haff : affinePoint a0 m u = affinePoint a0 a1 ((s / 2) * u) := by
        ext <;> dsimp [m, affinePoint] <;> ring
      rw [haff] at huv
      have huniq := affinePoint_intersection_parameters_unique a0 a1 b0 b1
        ((s / 2) * u) v s s hD huv hpt
      have hle : (s / 2) * u ≤ s / 2 := by nlinarith
      linarith [huniq.1]
    let s' := s / (2 - s)
    have h2s_pos : 0 < 2 - s := by linarith
    have hs'_pos : 0 < s' := div_pos hs0 h2s_pos
    have hs'_lt1 : s' < 1 := (div_lt_one h2s_pos).mpr (by linarith)
    have hs'_lt_s : s' < s := by
      dsimp [s']
      rw [div_lt_iff₀ h2s_pos]
      nlinarith
    have hm_pt : affinePoint m a1 s' = affinePoint a0 a1 s := by
      have h2s_ne : 2 - s ≠ 0 := ne_of_gt h2s_pos
      ext <;> dsimp [m, s', affinePoint] <;> field_simp [h2s_ne] <;> ring
    have hdet_m : planarDet (a1 - m) (b1 - b0) =
        (1 - s / 2) * planarDet (a1 - a0) (b1 - b0) := by
      dsimp [m, affinePoint, planarDet]
      ring
    have h1s2_pos : 0 < 1 - s / 2 := by linarith
    have hDm : planarDet (a1 - m) (b1 - b0) ≠ 0 := by
      rw [hdet_m]
      exact mul_ne_zero (ne_of_gt h1s2_pos) hD
    have hright := paraPsi_eq_of_interior_intersection_ne m a1 b0 b1
      s' s hs'_pos hs'_lt1 hs0 hs1 (ne_of_lt hs'_lt_s) (hm_pt.trans hpt) hDm
    have hsign_eq : (0 < planarDet (a1 - m) (b1 - b0)) ↔
        (0 < planarDet (a1 - a0) (b1 - b0)) := by
      rw [hdet_m]
      exact mul_pos_iff_of_pos_left h1s2_pos
    simp only [hsign_eq] at hright
    rw [← hsplit, hleft_zero, zero_add, hright]
  · exact paraPsi_eq_of_interior_intersection_ne a0 a1 b0 b1 s t hs0 hs1 ht0 ht1 hst hpt hD

/-! ### Part 4: Bilinear Telescope of `paraPsi` on `PLLinkDiagram` Components -/

def arcStartPoint (D : PLLinkDiagram) (e : Fin D.nArc) : PlanarPoint ℝ :=
  D.vertexPoint (D.arcSource e)

def arcEndPoint (D : PLLinkDiagram) (e : Fin D.nArc) : PlanarPoint ℝ :=
  D.vertexPoint (D.arcTarget e)

theorem arcEndPoint_eq_arcStartPoint_continuation (D : PLLinkDiagram) (e : Fin D.nArc) :
    arcEndPoint D e = arcStartPoint D (D.continuation e) :=
  congrArg D.vertexPoint (D.continuation_incidence e)

def componentArcFinset (D : PLLinkDiagram) (C : diagramComponent D) : Finset (Fin D.nArc) :=
  Finset.univ.filter (fun e => (componentOf D.continuation e : diagramComponent D) = C)

theorem mem_componentArcFinset_iff (D : PLLinkDiagram) (C : diagramComponent D) (e : Fin D.nArc) :
    e ∈ componentArcFinset D C ↔ (componentOf D.continuation e : diagramComponent D) = C := by
  simp [componentArcFinset]

theorem continuation_mem_componentArcFinset_iff (D : PLLinkDiagram) (C : diagramComponent D)
    (e : Fin D.nArc) :
    D.continuation e ∈ componentArcFinset D C ↔ e ∈ componentArcFinset D C := by
  simp only [mem_componentArcFinset_iff]
  have h : componentOf D.continuation (D.continuation e) = componentOf D.continuation e :=
    componentOf_apply D.continuation e
  rw [h]

theorem sum_componentArcFinset_continuation_sub (D : PLLinkDiagram) (C : diagramComponent D)
    (g : PlanarPoint ℝ → ℤ) :
    (∑ e ∈ componentArcFinset D C, (g (arcStartPoint D e) - g (arcEndPoint D e))) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  symm
  refine Finset.sum_bij (fun e _ => D.continuation e) ?_ ?_ ?_ ?_
  · intro e he
    exact (continuation_mem_componentArcFinset_iff D C e).mpr he
  · intro e1 _ e2 _ h
    exact D.continuation.injective h
  · intro b hb
    refine ⟨D.continuation.symm b, ?_, D.continuation.apply_symm_apply b⟩
    have hb' : D.continuation (D.continuation.symm b) ∈ componentArcFinset D C := by
      simpa using hb
    exact (continuation_mem_componentArcFinset_iff D C (D.continuation.symm b)).mp hb'
  · intro e _
    exact congrArg g (arcEndPoint_eq_arcStartPoint_continuation D e)

theorem sum_paraPsi_component_left_eq_zero (D : PLLinkDiagram)
    (A B : diagramComponent D) :
    (∑ e ∈ componentArcFinset D A, ∑ f ∈ componentArcFinset D B,
      paraPsi (arcStartPoint D e) (arcEndPoint D e)
        (arcStartPoint D f) (arcEndPoint D f)) = 0 := by
  have hsplit_inner : ∀ e : Fin D.nArc,
      (∑ f ∈ componentArcFinset D B,
        paraPsi (arcStartPoint D e) (arcEndPoint D e) (arcStartPoint D f) (arcEndPoint D f)) =
      (∑ f ∈ componentArcFinset D B,
        (rayPhi (arcStartPoint D e - arcStartPoint D f) (arcEndPoint D e - arcStartPoint D f) -
          rayPhi (arcStartPoint D e - arcEndPoint D f) (arcEndPoint D e - arcEndPoint D f))) -
      (∑ f ∈ componentArcFinset D B,
        (rayPhi (arcStartPoint D e - arcStartPoint D f) (arcStartPoint D e - arcEndPoint D f) -
          rayPhi (arcEndPoint D e - arcStartPoint D f) (arcEndPoint D e - arcEndPoint D f))) := by
    intro e
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f _
    unfold paraPsi
    ring
  simp_rw [hsplit_inner]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ e ∈ componentArcFinset D A, ∑ f ∈ componentArcFinset D B,
      (rayPhi (arcStartPoint D e - arcStartPoint D f) (arcEndPoint D e - arcStartPoint D f) -
        rayPhi (arcStartPoint D e - arcEndPoint D f) (arcEndPoint D e - arcEndPoint D f))) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact sum_componentArcFinset_continuation_sub D B
      (fun q => rayPhi (arcStartPoint D e - q) (arcEndPoint D e - q))
  have h2 : (∑ e ∈ componentArcFinset D A, ∑ f ∈ componentArcFinset D B,
      (rayPhi (arcStartPoint D e - arcStartPoint D f) (arcStartPoint D e - arcEndPoint D f) -
        rayPhi (arcEndPoint D e - arcStartPoint D f) (arcEndPoint D e - arcEndPoint D f))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro f _
    exact sum_componentArcFinset_continuation_sub D A
      (fun p => rayPhi (p - arcStartPoint D f) (p - arcEndPoint D f))
  rw [h1, h2, sub_self]

/-! ### Part 5: Disjointness and 4-Arc Grouping on `PLLinkDiagram` -/

theorem arc_segments_meeting_endpoints (D : PLLinkDiagram)
    (e f : Fin D.nArc) (hef : e ≠ f) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (heq : affinePoint (arcStartPoint D e) (arcEndPoint D e) s =
      affinePoint (arcStartPoint D f) (arcEndPoint D f) t) :
    (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
  have interior_ne {a b : Fin D.nArc} (hab : a ≠ b) (u v : ℝ)
      (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
      affinePoint (arcStartPoint D a) (arcEndPoint D a) u ≠
        affinePoint (arcStartPoint D b) (arcEndPoint D b) v := by
    intro h
    by_cases hv_zero : v = 0
    · subst hv_zero
      rw [affinePoint_zero] at h
      exact D.vertices_avoid_arc_interiors (D.arcSource b) a u hu0 hu1 h.symm
    · by_cases hv_one : v = 1
      · subst hv_one
        rw [affinePoint_one] at h
        exact D.vertices_avoid_arc_interiors (D.arcTarget b) a u hu0 hu1 h.symm
      · exact D.arc_interiors_disjoint a b hab u v hu0 hu1
          (lt_of_le_of_ne hv0 (Ne.symm hv_zero))
          (lt_of_le_of_ne hv1 hv_one) h
  have hs_end : s = 0 ∨ s = 1 := by
    by_contra hs_int
    push_neg at hs_int
    exact interior_ne hef s t
      (lt_of_le_of_ne hs0 (Ne.symm hs_int.1))
      (lt_of_le_of_ne hs1 hs_int.2) ht0 ht1 heq
  have ht_end : t = 0 ∨ t = 1 := by
    by_contra ht_int
    push_neg at ht_int
    exact interior_ne hef.symm t s
      (lt_of_le_of_ne ht0 (Ne.symm ht_int.1))
      (lt_of_le_of_ne ht1 ht_int.2) hs0 hs1 heq.symm
  exact ⟨hs_end, ht_end⟩

theorem arc_segments_intersect_shared_vertex (D : PLLinkDiagram)
    (e f : Fin D.nArc) (hef : e ≠ f) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (heq : affinePoint (arcStartPoint D e) (arcEndPoint D e) s =
      affinePoint (arcStartPoint D f) (arcEndPoint D f) t) :
    ∃ v : Fin D.nVertex,
      (D.arcSource e = v ∨ D.arcTarget e = v) ∧
      (D.arcSource f = v ∨ D.arcTarget f = v) := by
  obtain ⟨hs, ht⟩ := arc_segments_meeting_endpoints D e f hef s t hs0 hs1 ht0 ht1 heq
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rw [affinePoint_zero, affinePoint_zero] at heq
    exact ⟨D.arcSource e, Or.inl rfl, Or.inl (D.vertexPoint_injective heq.symm)⟩
  · rw [affinePoint_zero, affinePoint_one] at heq
    exact ⟨D.arcSource e, Or.inl rfl, Or.inr (D.vertexPoint_injective heq.symm)⟩
  · rw [affinePoint_one, affinePoint_zero] at heq
    exact ⟨D.arcTarget e, Or.inr rfl, Or.inl (D.vertexPoint_injective heq.symm)⟩
  · rw [affinePoint_one, affinePoint_one] at heq
    exact ⟨D.arcTarget e, Or.inr rfl, Or.inr (D.vertexPoint_injective heq.symm)⟩

theorem regular_vertex_incoming_unique' (D : PLLinkDiagram) (v : Fin D.nVertex)
    (hregular : ∀ c, D.crossingVertex c ≠ v) (e f : Fin D.nArc)
    (he : D.arcTarget e = v) (hf : D.arcTarget f = v) : e = f := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (D.regular_degree_one v hregular).1
  have hem : e ∈ incomingArcs D.arcTarget v := by simp [incomingArcs, he]
  have hfm : f ∈ incomingArcs D.arcTarget v := by simp [incomingArcs, hf]
  rw [ha, Finset.mem_singleton] at hem hfm
  exact hem.trans hfm.symm

theorem regular_vertex_incident_same_component' (D : PLLinkDiagram)
    (v : Fin D.nVertex) (hregular : ∀ c, D.crossingVertex c ≠ v)
    (e f : Fin D.nArc)
    (he : D.arcSource e = v ∨ D.arcTarget e = v)
    (hf : D.arcSource f = v ∨ D.arcTarget f = v) :
    componentOf D.continuation e = componentOf D.continuation f := by
  have incoming_rep (a : Fin D.nArc)
      (ha : D.arcSource a = v ∨ D.arcTarget a = v) :
      ∃ b : Fin D.nArc, D.arcTarget b = v ∧
        componentOf D.continuation b = componentOf D.continuation a := by
    rcases ha with ha | ha
    · refine ⟨D.continuation.symm a, ?_, ?_⟩
      · simpa only [Equiv.apply_symm_apply] using
          (D.continuation_incidence (D.continuation.symm a)).trans
            (by simpa only [Equiv.apply_symm_apply] using ha)
      · have hp := componentOf_apply D.continuation (D.continuation.symm a)
        simpa only [Equiv.apply_symm_apply] using hp.symm
    · exact ⟨a, ha, rfl⟩
  obtain ⟨a, ha, hea⟩ := incoming_rep e he
  obtain ⟨b, hb, hfb⟩ := incoming_rep f hf
  have hab := regular_vertex_incoming_unique' D v hregular a b ha hb
  exact hea.symm.trans ((congrArg (componentOf D.continuation) hab).trans hfb)

theorem distinct_arcs_not_same_endpoints (D : PLLinkDiagram)
    (e f : Fin D.nArc) (hef : e ≠ f)
    (v1 v2 : Fin D.nVertex) (hv12 : v1 ≠ v2)
    (he1 : D.arcSource e = v1 ∨ D.arcTarget e = v1)
    (he2 : D.arcSource e = v2 ∨ D.arcTarget e = v2)
    (hf1 : D.arcSource f = v1 ∨ D.arcTarget f = v1)
    (hf2 : D.arcSource f = v2 ∨ D.arcTarget f = v2) : False := by
  have he_ends : (D.arcSource e = v1 ∧ D.arcTarget e = v2) ∨
      (D.arcSource e = v2 ∧ D.arcTarget e = v1) := by
    rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2
    · exact False.elim (hv12 (h1.symm.trans h2))
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact False.elim (hv12 (h1.symm.trans h2))
  have hf_ends : (D.arcSource f = v1 ∧ D.arcTarget f = v2) ∨
      (D.arcSource f = v2 ∧ D.arcTarget f = v1) := by
    rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2
    · exact False.elim (hv12 (h1.symm.trans h2))
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact False.elim (hv12 (h1.symm.trans h2))
  have hmid : affinePoint (arcStartPoint D e) (arcEndPoint D e) (1 / 2) =
      affinePoint (arcStartPoint D f) (arcEndPoint D f) (1 / 2) := by
    rcases he_ends with ⟨hes, het⟩ | ⟨hes, het⟩ <;>
      rcases hf_ends with ⟨hfs, hft⟩ | ⟨hfs, hft⟩ <;>
      (ext <;> dsimp [arcStartPoint, arcEndPoint, affinePoint] <;>
        rw [hes, het, hfs, hft] <;> ring)
  exact D.arc_interiors_disjoint e f hef (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmid

/-- For a crossing `c`, the 4-element Finset of arc pairs `(e, f)` where `e` is on the
`firstVisitedBranch T c` strand and `f` is on the `otherBranch (firstVisitedBranch T c)` strand. -/
def crossingQuadruple {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) : Finset (Fin D.nArc × Fin D.nArc) :=
  let jA := firstVisitedBranch T c
  let jB := otherBranch jA
  let e_in := D.incoming c jA
  let e_out := D.continuation e_in
  let f_in := D.incoming c jB
  let f_out := D.continuation f_in
  ({e_in, e_out} : Finset (Fin D.nArc)) ×ˢ ({f_in, f_out} : Finset (Fin D.nArc))

theorem incoming_ne_continuation_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing) (j : Fin 2) :
    D.incoming c j ≠ D.continuation (D.incoming c j) := by
  rw [D.continuation_crossing c j]
  exact (D.four_ports_distinct c).2.2 j (D.through c j)

theorem mem_crossingQuadruple_endpoints {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) {p : Fin D.nArc × Fin D.nArc}
    (hp : p ∈ crossingQuadruple T c) :
    (D.arcSource p.1 = D.crossingVertex c ∨ D.arcTarget p.1 = D.crossingVertex c) ∧
    (D.arcSource p.2 = D.crossingVertex c ∨ D.arcTarget p.2 = D.crossingVertex c) := by
  simp only [crossingQuadruple, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with ⟨he | he, hf | hf⟩
  · refine ⟨Or.inr (he ▸ D.incoming_target c _), Or.inr (hf ▸ D.incoming_target c _)⟩
  · refine ⟨Or.inr (he ▸ D.incoming_target c _), Or.inl ?_⟩
    rw [hf, D.continuation_crossing]
    exact D.outgoing_source c _
  · refine ⟨Or.inl ?_, Or.inr (hf ▸ D.incoming_target c _)⟩
    rw [he, D.continuation_crossing]
    exact D.outgoing_source c _
  · refine ⟨Or.inl ?_, Or.inl ?_⟩
    · rw [he, D.continuation_crossing]; exact D.outgoing_source c _
    · rw [hf, D.continuation_crossing]; exact D.outgoing_source c _

theorem crossingQuadruple_subset_components {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    crossingQuadruple T c ⊆
      componentArcFinset D (T.componentIndex.symm r) ×ˢ
        componentArcFinset D (T.componentIndex.symm ⟨r.val + 1, hr⟩) := by
  intro p hp
  simp only [crossingQuadruple, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hp
  simp only [Finset.mem_product, mem_componentArcFinset_iff]
  have hA : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      T.componentIndex.symm r := by
    apply T.componentIndex.injective
    rw [affected_branch_A_componentIndex T r c hc, T.componentIndex.apply_symm_apply]
  have hB : componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c))) =
      T.componentIndex.symm ⟨r.val + 1, hr⟩ :=
    affected_branch_B_componentOf T r hr c hc
  constructor
  · rcases hp.1 with h | h
    · rw [h]; exact hA
    · rw [h, componentOf_apply]; exact hA
  · rcases hp.2 with h | h
    · rw [h]; exact hB
    · rw [h, componentOf_apply]; exact hB

theorem crossingQuadruple_disjoint {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    {c1 c2 : Fin D.nCrossing}
    (hc1 : adjacentSwapAffectedCrossing T r c1)
    (h12 : c1 ≠ c2) :
    Disjoint (crossingQuadruple T c1) (crossingQuadruple T c2) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have hsub := crossingQuadruple_subset_components T r hr c1 hc1 hp1
  simp only [Finset.mem_product, mem_componentArcFinset_iff] at hsub
  have hef : p.1 ≠ p.2 := by
    intro hEq
    have hcomp : (T.componentIndex.symm r : diagramComponent D) =
        T.componentIndex.symm ⟨r.val + 1, hr⟩ := by
      rw [← hsub.1, ← hsub.2, hEq]
    have hidx := congrArg (fun C => (T.componentIndex C).val) hcomp
    simp only [Equiv.apply_symm_apply] at hidx
    omega
  have hv12 : D.crossingVertex c1 ≠ D.crossingVertex c2 :=
    fun h => h12 (D.crossingVertex_injective h)
  obtain ⟨he1, hf1⟩ := mem_crossingQuadruple_endpoints T c1 hp1
  obtain ⟨he2, hf2⟩ := mem_crossingQuadruple_endpoints T c2 hp2
  exact distinct_arcs_not_same_endpoints D p.1 p.2 hef
    (D.crossingVertex c1) (D.crossingVertex c2) hv12 he1 he2 hf1 hf2

theorem incident_crossing_mem_affected_and_quadruple
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (e f : Fin D.nArc)
    (heA : (componentOf D.continuation e : diagramComponent D) = T.componentIndex.symm r)
    (hfB : (componentOf D.continuation f : diagramComponent D) =
      T.componentIndex.symm ⟨r.val + 1, hr⟩)
    (he_inc : D.arcSource e = D.crossingVertex c ∨ D.arcTarget e = D.crossingVertex c)
    (hf_inc : D.arcSource f = D.crossingVertex c ∨ D.arcTarget f = D.crossingVertex c) :
    adjacentSwapAffectedCrossing T r c ∧ (e, f) ∈ crossingQuadruple T c := by
  have h_port_comp : ∀ b : Fin D.nArc,
      (b = D.incoming c 0 ∨ b = D.incoming c 1 ∨ b = D.outgoing c 0 ∨ b = D.outgoing c 1) →
      ∃ j : Fin 2, (b = D.incoming c j ∨ b = D.continuation (D.incoming c j)) ∧
        componentOf D.continuation b = componentOf D.continuation (D.incoming c j) := by
    rintro b (rfl | rfl | rfl | rfl)
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨1, Or.inl rfl, rfl⟩
    · refine ⟨(D.through c).symm 0, Or.inr ?_, ?_⟩
      · rw [D.continuation_crossing, Equiv.apply_symm_apply]
      · have h := componentOf_apply D.continuation (D.incoming c ((D.through c).symm 0))
        rw [D.continuation_crossing, Equiv.apply_symm_apply] at h
        exact h
    · refine ⟨(D.through c).symm 1, Or.inr ?_, ?_⟩
      · rw [D.continuation_crossing, Equiv.apply_symm_apply]
      · have h := componentOf_apply D.continuation (D.incoming c ((D.through c).symm 1))
        rw [D.continuation_crossing, Equiv.apply_symm_apply] at h
        exact h
  obtain ⟨je, hje_mem, hje_comp⟩ := h_port_comp e ((D.crossing_incidence_complete c e).mp he_inc)
  obtain ⟨jf, hjf_mem, hjf_comp⟩ := h_port_comp f ((D.crossing_incidence_complete c f).mp hf_inc)
  have hje_A : (componentOf D.continuation (D.incoming c je) : diagramComponent D) =
      T.componentIndex.symm r := hje_comp.symm.trans heA
  have hjf_B : (componentOf D.continuation (D.incoming c jf) : diagramComponent D) =
      T.componentIndex.symm ⟨r.val + 1, hr⟩ := hjf_comp.symm.trans hfB
  have hje_ne_jf : je ≠ jf := by
    intro hEq
    subst hEq
    have hcomp := hje_A.symm.trans hjf_B
    have hidx := congrArg (fun C => (T.componentIndex C).val) hcomp
    simp only [Equiv.apply_symm_apply] at hidx
    omega
  have hc_aff : adjacentSwapAffectedCrossing T r c := by
    have hje01 : je = 0 ∨ je = 1 := by fin_cases je <;> simp
    have hjf01 : jf = 0 ∨ jf = 1 := by fin_cases jf <;> simp
    rcases hje01 with rfl | rfl <;> rcases hjf01 with rfl | rfl
    · exact False.elim (hje_ne_jf rfl)
    · left
      refine ⟨?_, ?_⟩
      · change T.componentIndex (componentOf D.continuation (D.incoming c 0)) = r
        rw [hje_A, T.componentIndex.apply_symm_apply]
      · change (T.componentIndex (componentOf D.continuation (D.incoming c 1))).val = r.val + 1
        rw [hjf_B, T.componentIndex.apply_symm_apply]
    · right
      refine ⟨?_, ?_⟩
      · change (T.componentIndex (componentOf D.continuation (D.incoming c 0))).val = r.val + 1
        rw [hjf_B, T.componentIndex.apply_symm_apply]
      · change T.componentIndex (componentOf D.continuation (D.incoming c 1)) = r
        rw [hje_A, T.componentIndex.apply_symm_apply]
    · exact False.elim (hje_ne_jf rfl)
  have hje_eq_fb : je = firstVisitedBranch T c := by
    by_contra hne
    have hje_other : je = otherBranch (firstVisitedBranch T c) :=
      eq_otherBranch_of_ne je (firstVisitedBranch T c) hne
    have hB_idx := affected_branch_B_componentIndex_val T r c hc_aff
    rw [← hje_other, hje_A, T.componentIndex.apply_symm_apply] at hB_idx
    omega
  have hjf_eq_other : jf = otherBranch (firstVisitedBranch T c) := by
    have h := eq_otherBranch_of_ne jf je hje_ne_jf.symm
    rwa [hje_eq_fb] at h
  refine ⟨hc_aff, ?_⟩
  simp only [crossingQuadruple, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  rw [← hjf_eq_other, ← hje_eq_fb]
  exact ⟨hje_mem, hjf_mem⟩

theorem paraPsi_eq_zero_of_not_in_quadruples
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    {p : Fin D.nArc × Fin D.nArc}
    (hpAB : p ∈ componentArcFinset D (T.componentIndex.symm r) ×ˢ
      componentArcFinset D (T.componentIndex.symm ⟨r.val + 1, hr⟩))
    (hp_not : p ∉ (Finset.univ.filter (adjacentSwapAffectedCrossing T r)).biUnion
      (crossingQuadruple T)) :
    paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
      (arcStartPoint D p.2) (arcEndPoint D p.2) = 0 := by
  simp only [Finset.mem_product, mem_componentArcFinset_iff] at hpAB
  apply paraPsi_eq_zero_of_disjoint
  intro s t hs0 hs1 ht0 ht1 heq
  have hef : p.1 ≠ p.2 := by
    intro hEq
    have hcomp := hpAB.1.symm.trans (hEq ▸ hpAB.2)
    have hidx := congrArg (fun C => (T.componentIndex C).val) hcomp
    simp only [Equiv.apply_symm_apply] at hidx
    omega
  obtain ⟨v, he_v, hf_v⟩ := arc_segments_intersect_shared_vertex D p.1 p.2 hef s t hs0 hs1 ht0 ht1 heq
  by_cases hc : ∃ c : Fin D.nCrossing, D.crossingVertex c = v
  · obtain ⟨c, rfl⟩ := hc
    obtain ⟨hc_aff, hp_mem⟩ := incident_crossing_mem_affected_and_quadruple T r hr
      c p.1 p.2 hpAB.1 hpAB.2 he_v hf_v
    apply hp_not
    rw [Finset.mem_biUnion]
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc_aff⟩, hp_mem⟩
  · push_neg at hc
    have hsame := regular_vertex_incident_same_component' D v hc p.1 p.2 he_v hf_v
    have hcomp : (T.componentIndex.symm r : diagramComponent D) =
        T.componentIndex.symm ⟨r.val + 1, hr⟩ :=
      hpAB.1.symm.trans (hsame.trans hpAB.2)
    have hidx := congrArg (fun C => (T.componentIndex C).val) hcomp
    simp only [Equiv.apply_symm_apply] at hidx
    omega

/-! ### Part 6: Evaluating the 4-Arc Crossing Sum at Each Mixed Crossing -/

def crossingSignInt (D : PLLinkDiagram) (c : Fin D.nCrossing) : ℤ :=
  match crossingSign D c with
  | .pos => -1
  | .neg => 1

theorem through_collinear_affinePoint (D : PLLinkDiagram) (c : Fin D.nCrossing) (j : Fin 2) :
    let e_in := D.incoming c j
    let e_out := D.continuation e_in
    let p_minus := arcStartPoint D e_in
    let v_c := D.vertexPoint (D.crossingVertex c)
    let p_plus := arcEndPoint D e_out
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      v_c = affinePoint p_minus p_plus s ∧
      ∃ μ : ℝ, 0 < μ ∧ p_plus - p_minus = μ • strandTangent D c j := by
  intro e_in e_out p_minus v_c p_plus
  obtain ⟨scale, hscale_pos, hcol⟩ := D.through_tangents_positive_collinear c j
  have hp_plus : p_plus = D.vertexPoint (D.arcTarget (D.outgoing c (D.through c j))) := by
    dsimp [p_plus, arcEndPoint, e_out, e_in]
    rw [D.continuation_crossing c j]
  have hcol' : v_c - p_minus = scale • (p_plus - v_c) := by
    rw [hp_plus]
    exact hcol
  let s := scale / (1 + scale)
  have h1s_pos : 0 < 1 + scale := by linarith
  have h1s_ne : 1 + scale ≠ 0 := ne_of_gt h1s_pos
  have hs0 : 0 < s := div_pos hscale_pos h1s_pos
  have hs1 : s < 1 := (div_lt_one h1s_pos).mpr (by linarith)
  have hx := congrArg Prod.fst hcol'
  have hy := congrArg Prod.snd hcol'
  dsimp at hx hy
  refine ⟨s, hs0, hs1, ?_, (1 + scale) / scale, div_pos h1s_pos hscale_pos, ?_⟩
  · ext <;> dsimp [s, affinePoint] <;> field_simp [h1s_ne] <;> linarith
  · have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
    change p_plus - p_minus = ((1 + scale) / scale) • (v_c - p_minus)
    ext <;> dsimp <;> field_simp [hscale_ne] <;> linarith

theorem sum_crossingQuadruple_eq_crossingSignInt
    {D : PLLinkDiagram} (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (_r : Fin (diagramComponentCount D)) (_hr : _r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (_hc : adjacentSwapAffectedCrossing T _r c) :
    (∑ p ∈ crossingQuadruple T c,
      paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
        (arcStartPoint D p.2) (arcEndPoint D p.2)) =
      crossingSignInt D c := by
  let jA := firstVisitedBranch T c
  let jB := otherBranch jA
  let e_in := D.incoming c jA
  let e_out := D.continuation e_in
  let f_in := D.incoming c jB
  let f_out := D.continuation f_in
  have he_ne : e_in ≠ e_out := incoming_ne_continuation_incoming D c jA
  have hf_ne : f_in ≠ f_out := incoming_ne_continuation_incoming D c jB
  change (∑ p ∈ ({e_in, e_out} : Finset (Fin D.nArc)) ×ˢ ({f_in, f_out} : Finset (Fin D.nArc)),
    paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
      (arcStartPoint D p.2) (arcEndPoint D p.2)) =
    crossingSignInt D c
  rw [Finset.sum_product, Finset.sum_pair he_ne, Finset.sum_pair hf_ne, Finset.sum_pair hf_ne]
  let p_minus := arcStartPoint D e_in
  let v_c := D.vertexPoint (D.crossingVertex c)
  let p_plus := arcEndPoint D e_out
  let q_minus := arcStartPoint D f_in
  let q_plus := arcEndPoint D f_out
  have he_in_end : arcEndPoint D e_in = v_c :=
    congrArg D.vertexPoint (D.incoming_target c jA)
  have he_out_start : arcStartPoint D e_out = v_c :=
    (arcEndPoint_eq_arcStartPoint_continuation D e_in).symm.trans he_in_end
  have hf_in_end : arcEndPoint D f_in = v_c :=
    congrArg D.vertexPoint (D.incoming_target c jB)
  have hf_out_start : arcStartPoint D f_out = v_c :=
    (arcEndPoint_eq_arcStartPoint_continuation D f_in).symm.trans hf_in_end
  change (paraPsi p_minus (arcEndPoint D e_in) q_minus (arcEndPoint D f_in) +
      paraPsi p_minus (arcEndPoint D e_in) (arcStartPoint D f_out) q_plus) +
    (paraPsi (arcStartPoint D e_out) p_plus q_minus (arcEndPoint D f_in) +
      paraPsi (arcStartPoint D e_out) p_plus (arcStartPoint D f_out) q_plus) =
    crossingSignInt D c
  rw [he_in_end, he_out_start, hf_in_end, hf_out_start]
  obtain ⟨sA, hsA0, hsA1, hv_A, μA, hμA_pos, htanA⟩ := through_collinear_affinePoint D c jA
  obtain ⟨tB, htB0, htB1, hv_B, μB, hμB_pos, htanB⟩ := through_collinear_affinePoint D c jB
  have hv_A_symm : affinePoint p_minus p_plus sA = v_c := hv_A.symm
  have hv_B_symm : affinePoint q_minus q_plus tB = v_c := hv_B.symm
  have hcol_B1 : paraPsi p_minus v_c q_minus v_c + paraPsi p_minus v_c v_c q_plus =
      paraPsi p_minus v_c q_minus q_plus := by
    simpa only [hv_B_symm] using
      paraPsi_collinear_right p_minus v_c q_minus q_plus tB htB0 htB1
  have hcol_B2 : paraPsi v_c p_plus q_minus v_c + paraPsi v_c p_plus v_c q_plus =
      paraPsi v_c p_plus q_minus q_plus := by
    simpa only [hv_B_symm] using
      paraPsi_collinear_right v_c p_plus q_minus q_plus tB htB0 htB1
  have hcol_A : paraPsi p_minus v_c q_minus q_plus + paraPsi v_c p_plus q_minus q_plus =
      paraPsi p_minus p_plus q_minus q_plus := by
    simpa only [hv_A_symm] using
      paraPsi_collinear_left p_minus p_plus q_minus q_plus sA hsA0 hsA1
  rw [hcol_B1, hcol_B2, hcol_A]
  have hover : D.overBranch c = jA :=
    ((badCrossings_eq_empty_iff_firstVisited_over T).mp hT c).symm
  have hdet_scale : planarDet (p_plus - p_minus) (q_plus - q_minus) =
      (μA * μB) * crossingDet D c := by
    unfold crossingDet
    rw [hover, htanA, htanB]
    dsimp [planarDet, jB]
    ring
  have hμAB_pos : 0 < μA * μB := mul_pos hμA_pos hμB_pos
  have hdet_nz : planarDet (p_plus - p_minus) (q_plus - q_minus) ≠ 0 := by
    rw [hdet_scale]
    exact mul_ne_zero (ne_of_gt hμAB_pos) (selectedDet_ne_zero D c)
  rw [paraPsi_eq_of_interior_intersection p_minus p_plus q_minus q_plus
    sA tB hsA0 hsA1 htB0 htB1 (hv_A.symm.trans hv_B) hdet_nz]
  have hsign_iff : 0 < planarDet (p_plus - p_minus) (q_plus - q_minus) ↔
      0 < crossingDet D c := by
    rw [hdet_scale]
    exact mul_pos_iff_of_pos_left hμAB_pos
  simp only [hsign_iff]
  unfold crossingSignInt crossingSign nonzeroScalarSign
  by_cases hneg : crossingDet D c < 0
  · have hn : ¬ 0 < crossingDet D c := not_lt_of_gt hneg
    simp [hneg, hn]
  · have hp : 0 < crossingDet D c :=
      lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm (selectedDet_ne_zero D c))
    simp [hneg, hp]

theorem sum_crossingSignInt_affected_eq_zero
    {D : PLLinkDiagram} (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) :
    (∑ c ∈ Finset.univ.filter (adjacentSwapAffectedCrossing T r),
      crossingSignInt D c) = 0 := by
  let A := T.componentIndex.symm r
  let B := T.componentIndex.symm ⟨r.val + 1, hr⟩
  let M := Finset.univ.filter (adjacentSwapAffectedCrossing T r)
  let U := M.biUnion (crossingQuadruple T)
  have hU_sub : U ⊆ componentArcFinset D A ×ˢ componentArcFinset D B := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨c, hcM, hpc⟩ := hp
    have hc_aff : adjacentSwapAffectedCrossing T r c := (Finset.mem_filter.mp hcM).2
    exact crossingQuadruple_subset_components T r hr c hc_aff hpc
  have htotal : (∑ p ∈ componentArcFinset D A ×ˢ componentArcFinset D B,
      paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
        (arcStartPoint D p.2) (arcEndPoint D p.2)) = 0 := by
    rw [Finset.sum_product]
    exact sum_paraPsi_component_left_eq_zero D A B
  have hsum_U : (∑ p ∈ U,
      paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
        (arcStartPoint D p.2) (arcEndPoint D p.2)) = 0 := by
    rw [← htotal]
    apply Finset.sum_subset hU_sub
    intro p hpAB hp_not
    exact paraPsi_eq_zero_of_not_in_quadruples T r hr hpAB hp_not
  have hbiUnion : (∑ p ∈ U,
      paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
        (arcStartPoint D p.2) (arcEndPoint D p.2)) =
      ∑ c ∈ M, ∑ p ∈ crossingQuadruple T c,
        paraPsi (arcStartPoint D p.1) (arcEndPoint D p.1)
          (arcStartPoint D p.2) (arcEndPoint D p.2) := by
    apply Finset.sum_biUnion
    intro c1 hc1 c2 _ h12
    exact crossingQuadruple_disjoint T r hr (Finset.mem_filter.mp hc1).2 h12
  rw [hbiUnion] at hsum_U
  rw [← hsum_U]
  apply Finset.sum_congr rfl
  intro c hcM
  exact (sum_crossingQuadruple_eq_crossingSignInt T hT r hr c (Finset.mem_filter.mp hcM).2).symm

/-! ### Part 7: Converting Zero Signed Intersection Sum to Unit Product -/

def aSquareUnit : HOMFLYCoeffˣ where
  val := aMonomial * aMonomial
  inv := aInvMonomial * aInvMonomial
  val_inv := by
    calc
      (aMonomial * aMonomial) * (aInvMonomial * aInvMonomial) =
          (aMonomial * aInvMonomial) * (aMonomial * aInvMonomial) := by ring
      _ = 1 := by rw [aMonomial_mul_aInvMonomial]; ring
  inv_val := by
    calc
      (aInvMonomial * aInvMonomial) * (aMonomial * aMonomial) =
          (aMonomial * aInvMonomial) * (aMonomial * aInvMonomial) := by ring
      _ = 1 := by rw [aMonomial_mul_aInvMonomial]; ring

theorem pivotSwitchFactor_eq_aSquareUnit_zpow (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    pivotSwitchFactor D c = ((aSquareUnit ^ (crossingSignInt D c) : HOMFLYCoeffˣ) : HOMFLYCoeff) := by
  unfold pivotSwitchFactor crossingSignInt
  cases crossingSign D c with
  | pos =>
      dsimp
      rw [zpow_neg_one]
      rfl
  | neg =>
      dsimp
      rw [zpow_one]
      rfl

theorem prod_aSquareUnit_zpow {α : Type*} (S : Finset α) (f : α → ℤ) :
    (∏ x ∈ S, ((aSquareUnit ^ (f x) : HOMFLYCoeffˣ) : HOMFLYCoeff)) =
      ((aSquareUnit ^ (∑ x ∈ S, f x) : HOMFLYCoeffˣ) : HOMFLYCoeff) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, Units.val_mul, ih]

theorem prod_pivotSwitchFactor_affected_eq_one
    {D : PLLinkDiagram} (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) :
    (∏ c ∈ Finset.univ.filter (adjacentSwapAffectedCrossing T r),
      pivotSwitchFactor D c) = 1 := by
  have hcongr : (∏ c ∈ Finset.univ.filter (adjacentSwapAffectedCrossing T r),
      pivotSwitchFactor D c) =
      ∏ c ∈ Finset.univ.filter (adjacentSwapAffectedCrossing T r),
        ((aSquareUnit ^ (crossingSignInt D c) : HOMFLYCoeffˣ) : HOMFLYCoeff) := by
    apply Finset.prod_congr rfl
    intro c _
    exact pivotSwitchFactor_eq_aSquareUnit_zpow D c
  rw [hcongr, prod_aSquareUnit_zpow,
    sum_crossingSignInt_affected_eq_zero T hT r hr, zpow_zero, Units.val_one]

theorem descending_adjacentSwap_unconditional {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) :
    descendingLaurentEvaluator D
      (reindexTraversalComponents T (adjacentComponentSwap r hr)) =
        descendingUnlinkValue D :=
  descending_adjacentSwap_of_prod_eq_one outer D hD T hT r hr
    (fun _hA => prod_pivotSwitchFactor_affected_eq_one T hT r hr)

end

end DirectGLSSW.HOMFLY.Gemini
