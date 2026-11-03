import ActiveArcCursorWallGeometry
import ActiveArcBeforeFirstDaughters
import TailSecantSeparation
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open Cursor RetainedWords OpenCarrier EndpointEventGeometry
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
include hR

theorem first_interior_ne_anchor (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (i : Fin (n+2)) (hi : i≠0) : affinePoint (q 0) (q 1) t≠q i := by
  intro he
  by_cases hi1 : i=1
  · subst i
    have ht : t=1 := edge_parameter_unique q hR 0 t 1 (by simpa only [affinePoint_one] using he)
    linarith
  · apply hR.anchor_avoid 0 i hi hi1
    exact ⟨t,ht0,ht1,he.symm⟩

/-- The regular moving cursor cannot meet a later closed physical edge; the
endpoint cases use original anchor avoidance on the first-edge interior. -/
theorem positive_cursor_not_later_closed_edge (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (hM : Regular (moveStart q t)) (e : Fin (n+1)) (he : e≠0)
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) :
    affinePoint (q 0) (q 1) t≠affinePoint (q e.castSucc) (q e.succ) u := by
  by_cases hu : u=0
  · rw [hu,affinePoint_zero]
    exact first_interior_ne_anchor q hR t ht0 ht1 e.castSucc (castSucc_ne_zero he)
  by_cases hu' : u=1
  · rw [hu',affinePoint_one]
    exact first_interior_ne_anchor q hR t ht0 ht1 e.succ (Fin.succ_ne_zero _)
  intro hh
  have hp : edgeInterior q e (affinePoint (q 0) (q 1) t) :=
    ⟨u,lt_of_le_of_ne hu0 (Ne.symm hu),lt_of_le_of_ne hu1 hu',hh⟩
  have hpm := (edgeInterior_unchanged q t e he _).mpr hp
  rw [←moveStart_zero q t] at hpm
  exact hM.anchor_avoid e 0 (Ne.symm (castSucc_ne_zero he)) (Ne.symm (Fin.succ_ne_zero _)) hpm

/-- Actual no-first-crossing geometry supplies the full closed-side separation
needed by compact parallel perturbation; endpoint genericity is only used at
cursor parameter zero, where Regular permits coinciding remote anchors. -/
theorem before_first_cursor_closed_side_avoidance
    (c : Crossing q) (hc : FirstCrossing q c) (b : ℝ) (hb0 : 0≤b) (hbc : b<leftParameter q c)
    (U : Support q hR)
    (hcore : ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1)) :
    let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
    ∀ t : ℝ, 0≤t → t≤b → ∀ r : ℕ, 0<r → r<openCount q hR U.val-1 →
      ∀ u : ℝ, 0≤u → u≤1 → W 0+t • (q 1-q 0)≠affinePoint (W r) (W (r+1)) u := by
  dsimp only
  let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
  intro t ht0 htb r hr0 hrN u hu0 hu1
  have hn := open_count_ge_two q hR U.val
  have ht1 : t<1 := lt_trans (lt_of_le_of_lt htb hbc) (leftParameter_spec q c).2.1
  have hW0 : W 0=q 0 := by dsimp only [W]; rw [openCurrent_word q hR U 0 (by omega),openVertex_zero]
  have hp : W 0+t • (q 1-q 0)=affinePoint (q 0) (q 1) t := by rw [hW0];rfl
  by_cases ht : t=0
  · subst t
    simp only [zero_smul,add_zero]
    by_cases hu : u=0
    · rw [hu,affinePoint_zero]
      intro he
      apply hcore 0 r (r+1) hr0 (by omega) (by omega)
      change planarDet (W r-W (r+1)) (W 0-W (r+1))=0
      change W 0=W r at he
      rw [he]
      simp [planarDet] <;> ring
    by_cases hu' : u=1
    · rw [hu',affinePoint_one]
      intro he
      apply hcore 0 r (r+1) hr0 (by omega) (by omega)
      change planarDet (W r-W (r+1)) (W 0-W (r+1))=0
      change W 0=W (r+1) at he
      rw [he,sub_self]
      simp [planarDet] <;> ring
    exact open_word_cursor_not_side q hR U r hrN u (lt_of_le_of_ne hu0 (Ne.symm hu)) (lt_of_le_of_ne hu1 hu')
  · have htp : 0<t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let e := openSideCarrier q hR U.val ⟨r,hrN⟩
    have he : e≠0 := by
      intro hh
      have heq : openSideCarrier q hR U.val ⟨r,hrN⟩ =
          openSideCarrier q hR U.val ⟨0,by omega⟩ := hh.trans (openSideCarrier_zero q hR U.val).symm
      have hi : (⟨r,hrN⟩ : Fin (openCount q hR U.val-1))=⟨0,by omega⟩ := openSideCarrier_injective q hR U.val U.property heq
      have hv : r=0 := congrArg Fin.val hi
      omega
    obtain ⟨a,d,ha,had,hd,hpa,hpd⟩ := openSideCarrier_physical q hR U.val ⟨r,hrN⟩
    have hs0 : 0≤a+(d-a)*u := by nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt had)) hu0]
    have hs1 : a+(d-a)*u≤1 := by nlinarith [mul_le_mul_of_nonneg_left hu1 (sub_nonneg.mpr (le_of_lt had))]
    rw [hp,openCurrent_word q hR U r (by omega),openCurrent_word q hR U (r+1) (by omega)]
    dsimp only [OpenVertex]
    rw [hpa,hpd]
    have hnest : affinePoint (affinePoint (q e.castSucc) (q e.succ) a)
        (affinePoint (q e.castSucc) (q e.succ) d) u = affinePoint (q e.castSucc) (q e.succ) (a+(d-a)*u) := by
      ext <;> dsimp [affinePoint] <;> ring
    rw [hnest]
    exact positive_cursor_not_later_closed_edge q hR t htp ht1
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 (lt_of_le_of_lt htb hbc)) e he _ hs0 hs1

end DirectGLSSW.ActiveArc.Primitive
