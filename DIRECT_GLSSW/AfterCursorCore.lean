import ActualCursorConstancy
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open Cursor RetainedWords EndpointEventGeometry

/-- Transfer the original-word endpoint domain to every actual surviving
support by the proved physical retained-word and support equivalences. -/
theorem after_first_all_support_core {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (t : ℝ) (hct : leftParameter q c<t) (htb : t<afterBound q c)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
      (openCount q hR U.val-1)) :
    let ht0 : 0≤t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    ∀ V : Support (moveStart q t) hM, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex _ _ V) (openLast _ _ V.val))
      (openCount (moveStart q t) hM V.val-1) := by
  intro ht0 hM V
  let E := Surviving.afterFirstSupportEquiv q hR c hc t hct htb
  let U := E V
  have hv : V.val=Surviving.movingSelection q t ht0
      (lt_of_lt_of_le htb (afterBound_le_one q c)) U.val.val := by
    have he := congrArg Subtype.val (E.symm_apply_apply V)
    exact he.symm.trans (Surviving.afterFirstSupportEquiv_symm_val q hR c hc t hct htb U)
  have hw := Surviving.after_first_open_word q hR c hc t hct htb U.val.val U.property
  change List.ofFn (vertex (moveStart q t) hM
    (Surviving.movingSelection q t ht0 (lt_of_lt_of_le htb (afterBound_le_one q c)) U.val.val)
    (start (moveStart q t))) = _ at hw
  rw [← hv] at hw
  have hn := open_count_ge_two q hR U.val.val
  have hp := ofFn_replace_head (OpenVertex q hR U.val) (OpenVertex (moveStart q t) hM V)
    (affinePoint (q 0) (q 1) t) (by change 0<openCount q hR U.val.val;omega) hw
  have hcount : openCount (moveStart q t) hM V.val=openCount q hR U.val.val := hp.1
  have hpoint (i : ℕ) (hi : i<openCount (moveStart q t) hM V.val) :
      rootedPolygonWord (OpenVertex (moveStart q t) hM V) (openLast (moveStart q t) hM V.val) i =
      moveEndpoint (rootedPolygonWord (OpenVertex q hR U.val) (openLast q hR U.val.val)) (q 1-q 0) t i := by
    have hj : i<openCount q hR U.val.val := by rwa [hcount] at hi
    rw [openCurrent_word _ _ _ i hi,hp.2 i hi hj]
    by_cases hz : i=0
    · subst i
      simp only [moveEndpoint,if_pos rfl]
      rw [openCurrent_word q hR U.val 0 (by omega),openVertex_zero]
      ext <;> dsimp [affinePoint] <;> ring
    · simp only [moveEndpoint,if_neg hz]
      exact (openCurrent_word q hR U.val i hj).symm
  intro i j k hij hjk hk
  have hk' : k<openCount (moveStart q t) hM V.val := by
    have := open_count_ge_two (moveStart q t) hM V.val;omega
  have hj' : j<openCount (moveStart q t) hM V.val := by omega
  have hi' : i<openCount (moveStart q t) hM V.val := by omega
  have H := hcore U.val i j k hij hjk (by rwa [← hcount])
  simpa only [polygonHDet,hpoint i hi',hpoint j hj',hpoint k hk'] using H
end DirectGLSSW.ActiveArc.Primitive
