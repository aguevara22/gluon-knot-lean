import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.SpinorVertices
import Mathlib.Algebra.Module.Prod

set_option autoImplicit false

namespace DirectGLSSW.EndpointEventGeometry
open DirectGLSSW

def moveEndpoint (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    (t : ℝ) (a : ℕ) : PlanarPoint ℝ :=
  if a = 0 then q 0 + t • v else q a

theorem moveEndpoint_farDet (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (t : ℝ) :
    polygonHDet (moveEndpoint q v t) 0 k j =
      polygonHDet q 0 k j + t * planarDet (q k - q j) v := by
  have hj : j ≠ 0 := by omega
  simp [polygonHDet, moveEndpoint, ne_of_gt hk, hj, planarDet]
  ring

private theorem moveEndpoint_nonzero_start (q : ℕ → PlanarPoint ℝ)
    (v : PlanarPoint ℝ) {a b c : ℕ} (ha : a ≠ 0)
    (hab : a < b) (hbc : b < c) (t : ℝ) :
    polygonHDet (moveEndpoint q v t) a b c = polygonHDet q a b c := by
  have hb : b ≠ 0 := by omega
  have hc : c ≠ 0 := by omega
  simp [polygonHDet, moveEndpoint, ha, hb, hc]

private theorem scalarSignValue_congr_of_neg_iff {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hneg : x < 0 ↔ y < 0) :
    scalarSignValue x = scalarSignValue y := by
  simp only [scalarSignValue, hx, hy, if_false]
  exact if_congr hneg rfl rfl

private theorem exists_unchanged_triple_radius
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (hd : polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      polygonHDet (moveEndpoint q v ε) a b c ≠ 0 ∧
      polygonHDet (moveEndpoint q v (-ε)) a b c ≠ 0 ∧
      polygonSignArray (moveEndpoint q v ε) a b c = polygonSignArray q a b c ∧
      polygonSignArray (moveEndpoint q v (-ε)) a b c = polygonSignArray q a b c := by
  by_cases ha : a = 0
  · subst a
    let d := polygonHDet q 0 b c
    let s := planarDet (q b - q c) v
    obtain ⟨ρp, hρp, hp⟩ := ShortEdgeSignStability.exists_affine_sign_radius d s hd
    obtain ⟨ρm, hρm, hm⟩ := ShortEdgeSignStability.exists_affine_sign_radius d (-s) hd
    refine ⟨min ρp ρm, lt_min hρp hρm, ?_⟩
    intro ε hε hερ
    have hplus := hp ε hε (lt_of_lt_of_le hερ (min_le_left _ _))
    have hminus := hm ε hε (lt_of_lt_of_le hερ (min_le_right _ _))
    have heqp : polygonHDet (moveEndpoint q v ε) 0 b c = d + ε * s :=
      moveEndpoint_farDet q v hab hbc ε
    have heqm : polygonHDet (moveEndpoint q v (-ε)) 0 b c = d + ε * (-s) := by
      rw [moveEndpoint_farDet q v hab hbc]
      dsimp [d, s]
      ring
    refine ⟨by rw [heqp]; exact hplus.1, by rw [heqm]; exact hminus.1, ?_, ?_⟩
    · change scalarSignValue _ = scalarSignValue d
      rw [heqp]
      exact scalarSignValue_congr_of_neg_iff hplus.1 hd hplus.2
    · change scalarSignValue _ = scalarSignValue d
      rw [heqm]
      exact scalarSignValue_congr_of_neg_iff hminus.1 hd hminus.2
  · refine ⟨1, by norm_num, ?_⟩
    intro ε _ _
    have hp := moveEndpoint_nonzero_start q v ha hab hbc ε
    have hm := moveEndpoint_nonzero_start q v ha hab hbc (-ε)
    exact ⟨by rwa [hp], by rwa [hm], by simp [polygonSignArray, hp],
      by simp [polygonSignArray, hm]⟩

private theorem target_sign_jump (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j)
    (hzero : polygonHDet q 0 k j = 0)
    (htransverse : planarDet (q k - q j) v ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    polygonHDet (moveEndpoint q v ε) 0 k j ≠ 0 ∧
    polygonHDet (moveEndpoint q v (-ε)) 0 k j ≠ 0 ∧
    polygonSignArray (moveEndpoint q v ε) 0 k j -
        polygonSignArray (moveEndpoint q v (-ε)) 0 k j =
      2 * scalarSignValue (planarDet (q k - q j) v) := by
  let s := planarDet (q k - q j) v
  have hp : polygonHDet (moveEndpoint q v ε) 0 k j = ε * s := by
    rw [moveEndpoint_farDet q v hk hkj, hzero, zero_add]
  have hm : polygonHDet (moveEndpoint q v (-ε)) 0 k j = -(ε * s) := by
    rw [moveEndpoint_farDet q v hk hkj, hzero, zero_add, neg_mul]
  have hnon : ε * s ≠ 0 := mul_ne_zero (ne_of_gt hε) htransverse
  refine ⟨by rwa [hp], by rw [hm]; exact neg_ne_zero.mpr hnon, ?_⟩
  change scalarSignValue _ - scalarSignValue _ = 2 * scalarSignValue s
  rw [hp, hm]
  by_cases hs : s < 0
  · have hprod : ε * s < 0 := mul_neg_of_pos_of_neg hε hs
    have hnprod : 0 < -(ε * s) := neg_pos.mpr hprod
    norm_num [scalarSignValue, hs, ne_of_lt hs, hprod, hnon,
      not_lt_of_gt hnprod, neg_ne_zero.mpr hnon]
  · have hspos : 0 < s := lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm htransverse)
    have hprod : 0 < ε * s := mul_pos hε hspos
    have hnprod : -(ε * s) < 0 := neg_neg_of_pos hprod
    norm_num [scalarSignValue, hs, ne_of_gt hspos, not_lt_of_gt hprod, hnon,
      hnprod, neg_ne_zero.mpr hnon]

theorem exists_endpoint_event_radius
    (q : ℕ → PlanarPoint ℝ) (v : PlanarPoint ℝ) (N : ℕ)
    {k j : ℕ} (hk : 0 < k) (hkj : k < j) (hjN : j ≤ N)
    (hzero : polygonHDet q 0 k j = 0)
    (htransverse : planarDet (q k - q j) v ≠ 0)
    (hisolated : ∀ a b c, a < b → b < c → c ≤ N →
      (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) → polygonHDet q a b c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint q v (-ε)) N ∧
      (∀ a b c, a < b → b < c → c ≤ N →
        (a ≠ 0 ∨ b ≠ k ∨ c ≠ j) →
        polygonSignArray (moveEndpoint q v ε) a b c = polygonSignArray q a b c ∧
        polygonSignArray (moveEndpoint q v (-ε)) a b c = polygonSignArray q a b c) ∧
      polygonSignArray (moveEndpoint q v ε) 0 k j -
          polygonSignArray (moveEndpoint q v (-ε)) 0 k j =
        2 * scalarSignValue (planarDet (q k - q j) v) := by
  classical
  let triples := Finset.range (N + 1) ×ˢ (Finset.range (N + 1) ×ˢ Finset.range (N + 1))
  let P : (ℕ × ℕ × ℕ) → ℝ → Prop := fun t ε =>
    t.1 < t.2.1 → t.2.1 < t.2.2 → t.2.2 ≤ N →
      (t.1 ≠ 0 ∨ t.2.1 ≠ k ∨ t.2.2 ≠ j) →
      polygonHDet (moveEndpoint q v ε) t.1 t.2.1 t.2.2 ≠ 0 ∧
      polygonHDet (moveEndpoint q v (-ε)) t.1 t.2.1 t.2.2 ≠ 0 ∧
      polygonSignArray (moveEndpoint q v ε) t.1 t.2.1 t.2.2 =
        polygonSignArray q t.1 t.2.1 t.2.2 ∧
      polygonSignArray (moveEndpoint q v (-ε)) t.1 t.2.1 t.2.2 =
        polygonSignArray q t.1 t.2.1 t.2.2
  have hlocal : ∀ t, t ∈ triples → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ε < ρ → P t ε := by
    intro t _
    by_cases hh : t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 ≤ N ∧
        (t.1 ≠ 0 ∨ t.2.1 ≠ k ∨ t.2.2 ≠ j)
    · obtain ⟨ρ, hρ, hgood⟩ := exists_unchanged_triple_radius q v hh.1 hh.2.1
        (hisolated _ _ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)
      exact ⟨ρ, hρ, fun ε hε hερ _ _ _ _ => hgood ε hε hερ⟩
    · exact ⟨1, by norm_num, fun ε _ _ hab hbc hc he => False.elim (hh ⟨hab,hbc,hc,he⟩)⟩
  obtain ⟨ρ, hρ, hgood⟩ := ShortEdgeSignStability.exists_finset_common_radius triples P hlocal
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε hερ
  have htarget := target_sign_jump q v hk hkj hzero htransverse hε
  have hrest (a b c : ℕ) (hab : a < b) (hbc : b < c) (hc : c ≤ N)
      (he : a ≠ 0 ∨ b ≠ k ∨ c ≠ j) := by
    have hmem : (a,b,c) ∈ triples := by
      simp only [triples, Finset.mem_product, Finset.mem_range]
      omega
    exact hgood ε hε hερ (a,b,c) hmem hab hbc hc he
  have hall : ∀ a b c, a < b → b < c → c ≤ N →
      polygonHDet (moveEndpoint q v ε) a b c ≠ 0 ∧
      polygonHDet (moveEndpoint q v (-ε)) a b c ≠ 0 := by
    intro a b c hab hbc hc
    by_cases he : a ≠ 0 ∨ b ≠ k ∨ c ≠ j
    · exact ⟨(hrest a b c hab hbc hc he).1, (hrest a b c hab hbc hc he).2.1⟩
    · have ha : a = 0 := by tauto
      have hb : b = k := by tauto
      have hc' : c = j := by tauto
      subst a b c
      exact ⟨htarget.1, htarget.2.1⟩
  exact ⟨fun a b c hab hbc hc => (hall a b c hab hbc hc).1,
    (fun a b c hab hbc hc => (hall a b c hab hbc hc).2),
    (fun a b c hab hbc hc he => (hrest a b c hab hbc hc he).2.2), htarget.2.2⟩








end DirectGLSSW.EndpointEventGeometry
