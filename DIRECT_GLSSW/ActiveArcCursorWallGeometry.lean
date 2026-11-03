import ActiveArcOpenFirstSide
import ActiveArcOpenSideGeometry
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open RetainedWords OpenCarrier
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
include hR

/-- The actual start never lies in the interior of any physical edge. -/
theorem start_not_physical_edgeInterior (e : Fin (n+1)) : ¬edgeInterior q e (q 0) := by
  intro hh
  by_cases he : e=0
  · subst e
    obtain ⟨s,hs0,hs1,hp⟩ := hh
    have hz : affinePoint (q (0 : Fin (n+1)).castSucc) (q (0 : Fin (n+1)).succ) s =
      affinePoint (q (0 : Fin (n+1)).castSucc) (q (0 : Fin (n+1)).succ) 0 := by
      simpa only [affinePoint_zero] using hp.symm
    have heq := edge_parameter_unique q hR 0 s 0 hz
    exact (ne_of_gt hs0) heq
  · apply hR.anchor_avoid e 0 _ _ hh
    · intro hh
      apply he
      apply Fin.ext
      have hv := congrArg Fin.val hh
      simpa using hv.symm
    · intro hh
      have hv := congrArg Fin.val hh
      simp at hv

/-- The first actual retained side is parallel to cursor motion and nonzero. -/
theorem open_word_first_direction (U : Support q hR) :
    let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
    planarDet (W 1-W 0) (q 1-q 0)=0 ∧ W 1≠W 0 := by
  dsimp only
  have hn := open_count_ge_two q hR U.val
  rw [openCurrent_word q hR U 1 (by omega),openCurrent_word q hR U 0 (by omega),openVertex_zero]
  obtain ⟨s,hs0,hs1,hp⟩ := openVertex_one_firstEdge q hR U
  rw [hp]
  constructor
  · simp only [planarDet,affinePoint,Prod.fst_sub,Prod.snd_sub]
    ring
  · intro he
    have heq : s=0 := edge_parameter_unique q hR 0 s 0 (by simpa only [affinePoint_zero] using he)
    exact (ne_of_gt hs0) heq

/-- Actual retained sides lie inside physical edges, so the cursor is not in
the interior of any of them. No auxiliary determinant assertion is used. -/
theorem open_word_cursor_not_side (U : Support q hR) (r : ℕ)
    (hr : r<openCount q hR U.val-1) (u : ℝ) (hu0 : 0<u) (hu1 : u<1) :
    let W := rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)
    W 0≠affinePoint (W r) (W (r+1)) u := by
  dsimp only
  have hn := open_count_ge_two q hR U.val
  rw [openCurrent_word q hR U 0 (by omega),openVertex_zero,
    openCurrent_word q hR U r (by omega),openCurrent_word q hR U (r+1) (by omega)]
  obtain ⟨a,b,ha,hab,hb,hpa,hpb⟩ := openSideCarrier_physical q hR U.val ⟨r,hr⟩
  intro he
  dsimp only [OpenVertex] at he
  rw [hpa,hpb] at he
  let v := a+(b-a)*u
  have hv0 : 0<v := by dsimp [v];nlinarith [mul_pos (sub_pos.mpr hab) hu0]
  have hv1 : v<1 := by
    have hm := mul_lt_mul_of_pos_left hu1 (sub_pos.mpr hab)
    dsimp [v]
    nlinarith
  apply start_not_physical_edgeInterior q hR (openSideCarrier q hR U.val ⟨r,hr⟩)
  refine ⟨v,hv0,hv1,?_⟩
  rw [he]
  ext <;> simp only [affinePoint,v] <;> ring

end DirectGLSSW.ActiveArc.Primitive
