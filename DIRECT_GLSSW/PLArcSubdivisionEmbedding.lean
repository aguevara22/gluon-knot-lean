import PLArcSubdivisionGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
attribute [local instance] Classical.propDecidable
variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ) (ht0 : 0<t) (ht1 : t<1)

/-- Parametrization of each actual new physical arc from the fixed endpoints. -/
def arcPoint (a : Fin (D.nArc+1)) (s : ℝ) : PlanarPoint ℝ :=
  affinePoint (vertexPoint D e t (arcSource D a)) (vertexPoint D e t (arcTarget D e a)) s

theorem arcPoint_old (a : Fin D.nArc) (s : ℝ) :
    arcPoint D e t a.castSucc s =
      if a=e then affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (t*s)
      else affinePoint (D.vertexPoint (D.arcSource a)) (D.vertexPoint (D.arcTarget a)) s := by
  by_cases h : a=e
  · subst a;simp [arcPoint,first_affine]
  · simp only [arcPoint,arcSource_old,arcTarget_old,if_neg h,vertexPoint_old]

theorem arcPoint_new (s : ℝ) :
    arcPoint D e t (Fin.last D.nArc) s =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (t+(1-t)*s) := by
  simp only [arcPoint,arcSource_new,arcTarget_new,vertexPoint_new,vertexPoint_old,second_affine]

include ht0 ht1 in
theorem vertexPoint_injective : Function.Injective (vertexPoint D e t) := by
  intro v
  refine Fin.lastCases ?_ (fun v=>?_) v
  · intro w
    refine Fin.lastCases ?_ (fun w=>?_) w
    · intro _;rfl
    · intro h
      exact False.elim (old_vertex_ne_point D e t ht0 ht1 w (by simpa only [vertexPoint_new,vertexPoint_old] using h.symm))
  · intro w
    refine Fin.lastCases ?_ (fun w=>?_) w
    · intro h
      exact False.elim (old_vertex_ne_point D e t ht0 ht1 v (by simpa only [vertexPoint_new,vertexPoint_old] using h))
    · intro h
      exact congrArg Fin.castSucc (D.vertexPoint_injective (by simpa only [vertexPoint_old] using h))

theorem arc_endpoints_distinct (a : Fin (D.nArc+1)) : arcSource D a ≠ arcTarget D e a := by
  refine Fin.lastCases ?_ (fun a=>?_) a
  · rw [arcSource_new,arcTarget_new]
    intro h
    have hv:=congrArg Fin.val h
    have hb:=(D.arcTarget e).isLt
    change D.nVertex = (D.arcTarget e).val at hv
    omega
  · by_cases h : a=e
    · simp [arcSource_old,arcTarget_old,h]
    · simpa only [arcSource_old,arcTarget_old,if_neg h,ne_eq,Fin.castSucc_inj] using D.arc_endpoints_distinct a

include ht0 ht1 in
/-- Both fresh half interiors are disjoint from every other original arc. -/
theorem arc_interiors_disjoint : ∀ a b : Fin (D.nArc+1), a≠b → ∀ s u : ℝ,
    0<s → s<1 → 0<u → u<1 → arcPoint D e t a s ≠ arcPoint D e t b u := by
  intro a
  refine Fin.lastCases ?_ (fun a=>?_) a
  · intro b
    refine Fin.lastCases ?_ (fun b=>?_) b
    · intro h;exact False.elim (h rfl)
    · intro _ s u hs0 hs1 hu0 hu1
      rw [arcPoint_new,arcPoint_old]
      by_cases hb : b=e
      · rw [if_pos hb]
        intro h
        exact halves_interiors_disjoint D e t ht0 ht1 u s hu0 hu1 hs0 hs1
          (by simpa only [first_affine,second_affine] using h.symm)
      · rw [if_neg hb]
        have hs:=second_parameter_bounds t ht0 ht1 s hs0 hs1
        exact D.arc_interiors_disjoint e b (Ne.symm hb) _ _ hs.1 hs.2.2 hu0 hu1
  · intro b
    refine Fin.lastCases ?_ (fun b=>?_) b
    · intro _ s u hs0 hs1 hu0 hu1
      rw [arcPoint_old,arcPoint_new]
      by_cases ha : a=e
      · rw [if_pos ha]
        intro h
        exact halves_interiors_disjoint D e t ht0 ht1 s u hs0 hs1 hu0 hu1
          (by simpa only [first_affine,second_affine] using h)
      · rw [if_neg ha]
        have hu:=second_parameter_bounds t ht0 ht1 u hu0 hu1
        exact D.arc_interiors_disjoint a e ha _ _ hs0 hs1 hu.1 hu.2.2
    · intro hab s u hs0 hs1 hu0 hu1
      have hab' : a≠b := fun h=>hab (congrArg Fin.castSucc h)
      rw [arcPoint_old,arcPoint_old]
      by_cases ha : a=e
      · have hb : b≠e := fun h=>hab' (ha.trans h.symm)
        rw [if_pos ha,if_neg hb]
        have hs:=first_parameter_bounds t ht0 ht1 s hs0 hs1
        exact D.arc_interiors_disjoint e b (Ne.symm hb) _ _ hs.1 hs.2.2 hu0 hu1
      · rw [if_neg ha]
        by_cases hb : b=e
        · rw [if_pos hb]
          have hu:=first_parameter_bounds t ht0 ht1 u hu0 hu1
          exact D.arc_interiors_disjoint a e ha _ _ hs0 hs1 hu.1 hu.2.2
        · rw [if_neg hb]
          exact D.arc_interiors_disjoint a b hab' _ _ hs0 hs1 hu0 hu1
end DirectGLSSW.HOMFLY.ArcSubdivision
