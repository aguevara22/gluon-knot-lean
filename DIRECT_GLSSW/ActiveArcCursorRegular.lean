import ActiveArcCursorGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- The actual first tangent shrinks by 1-t; later tangents stay unchanged. -/
def tangentScale (t : ℝ) (e : Fin (n+1)) : ℝ := if e=0 then 1-t else 1

theorem tangentScale_pos (t : ℝ) (ht : t<1) (e : Fin (n+1)) : 0<tangentScale (n:=n) t e := by
  unfold tangentScale;split_ifs <;> linarith

theorem tangent_moveStart (t : ℝ) (e : Fin (n+1)) :
    moveStart q t e.succ-moveStart q t e.castSucc=
      tangentScale t e • (q e.succ-q e.castSucc) := by
  by_cases he : e=0
  · subst e;simpa [tangentScale] using first_tangent q t
  · rw [moveStart_succ,moveStart_eq q t e.castSucc (castSucc_ne_zero he)]
    simp [tangentScale,he]

theorem det_tangent_moveStart (t : ℝ) (e f : Fin (n+1)) :
    planarDet (moveStart q t e.succ-moveStart q t e.castSucc)
      (moveStart q t f.succ-moveStart q t f.castSucc)=
      (tangentScale t e*tangentScale t f)*planarDet (q e.succ-q e.castSucc) (q f.succ-q f.castSucc) := by
  rw [tangent_moveStart,tangent_moveStart]
  change (tangentScale t e*(q e.succ-q e.castSucc).1)*(tangentScale t f*(q f.succ-q f.castSucc).2)-
    (tangentScale t e*(q e.succ-q e.castSucc).2)*(tangentScale t f*(q f.succ-q f.castSucc).1)=_
  unfold planarDet
  ring

/-- Removing only the actual finite crossing parameters gives Regular open chambers.
This does not assert auxiliary genericity of all smoothed closed daughters. -/
theorem regular_moveStart (hR : Regular q) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1)
    (ht : t∉criticalParameters q) : Regular (moveStart q t) := by
  constructor
  · intro e
    rw [tangent_moveStart]
    intro hz
    apply hR.edge_nonzero e
    have hs : tangentScale t e≠0 := ne_of_gt (tangentScale_pos t ht1 e)
    apply Prod.ext
    · have hx := congrArg Prod.fst hz
      change tangentScale t e*(q e.succ-q e.castSucc).1=0 at hx
      exact (mul_eq_zero.mp hx).resolve_left hs
    · have hx := congrArg Prod.snd hz
      change tangentScale t e*(q e.succ-q e.castSucc).2=0 at hx
      exact (mul_eq_zero.mp hx).resolve_left hs
  · intro e f hef x he hf
    rw [det_tangent_moveStart]
    apply mul_ne_zero
    · exact mul_ne_zero (ne_of_gt (tangentScale_pos t ht1 e)) (ne_of_gt (tangentScale_pos t ht1 f))
    · exact hR.transverse e f hef x (edgeInterior_subset q t ht0 ht1 e x he)
        (edgeInterior_subset q t ht0 ht1 f x hf)
  · intro e f g x hef hfg hge h
    exact hR.noTriple e f g x hef hfg hge
      ⟨edgeInterior_subset q t ht0 ht1 e x h.1,
       edgeInterior_subset q t ht0 ht1 f x h.2.1,
       edgeInterior_subset q t ht0 ht1 g x h.2.2⟩
  · intro e i hil hir hi
    by_cases hi0 : i=0
    · subst i
      have he : e≠0 := by intro he;subst e;exact hil rfl
      rw [moveStart_zero] at hi
      have hx := (edgeInterior_unchanged q t e he _).mp hi
      by_cases htzero : t=0
      · rw [htzero,affinePoint_zero] at hx
        exact hR.anchor_avoid e 0 hil hir hx
      · exact ht ((endpoint_on_later_iff q hR t (lt_of_le_of_ne ht0 (Ne.symm htzero)) ht1).mp ⟨e,he,hx⟩)
    · rw [moveStart_eq q t i hi0] at hi
      exact hR.anchor_avoid e i hil hir (edgeInterior_subset q t ht0 ht1 e (q i) hi)

/-- The full-word regularity boundary is exactly the genuine crossing-time set. -/
theorem regular_moveStart_iff (hR : Regular q) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) :
    Regular (moveStart q t) ↔ t∉criticalParameters q :=
  ⟨fun h ht => not_regular_at_critical q t ht h,regular_moveStart q hR t ht0 ht1⟩

end DirectGLSSW.ActiveArc.Cursor
