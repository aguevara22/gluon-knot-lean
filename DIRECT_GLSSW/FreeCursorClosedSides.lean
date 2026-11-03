import ActualCursorClosedSides
import ActiveArcFirstEdgeFreeMotion
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open Cursor RetainedWords OpenCarrier EndpointEventGeometry
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
include hR
/-- Actual no-first-crossing geometry supplies the full closed-side separation
needed by compact parallel perturbation; endpoint genericity is only used at
cursor parameter zero, where Regular permits coinciding remote anchors. -/
theorem firstEdgeFree_closed_side_avoidance
    (hfree : ∀ c : Crossing q, c.val.1≠0) (b : ℝ) (hb0 : 0≤b) (hb1 : b<1)
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
  have ht1 : t<1 := lt_of_le_of_lt htb hb1
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
      (firstEdgeFree_regular_moveStart q hR hfree t ht0 ht1) e he _ hs0 hs1

end DirectGLSSW.ActiveArc.Primitive
