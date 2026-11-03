import FiniteSecantRetainedRectangles

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

-- SOURCE-PREPARED, UNCOMPILED. No incidence certificate is a premise.
theorem secantAxisAdjacent_left_unique {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b d : ℝ)
    (hb : secantAxisAdjacent T C a b) (hd : secantAxisAdjacent T C a d) : b=d := by
  rcases lt_trichotomy b d with h | h | h
  · exact False.elim (hd.2.2.2 b hb.2.1 hb.2.2.1 h)
  · exact h
  · exact False.elim (hb.2.2.2 d hd.2.1 hd.2.2.1 h)

theorem secantAxisAdjacent_right_unique {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a c b : ℝ)
    (ha : secantAxisAdjacent T C a b) (hc : secantAxisAdjacent T C c b) : a=c := by
  rcases lt_trichotomy a c with h | h | h
  · exact False.elim (ha.2.2.2 c hc.1 h hc.2.2.1)
  · exact h
  · exact False.elim (hc.2.2.2 a ha.1 h ha.2.2.1)

abbrev RetainedRectangleIndex {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :=
  ↥(secantRetainedRectangles T C)
abbrev RetainedRectangleSide {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :=
  RetainedRectangleIndex T C × Fin 4

def rectangleSideStart {D : PLLinkDiagram} {T : BasedTraversal D} {C : diagramComponent D}
    (e : RetainedRectangleSide T C) : ℝ × ℝ :=
  if e.2=0 then (e.1.val.1.1,e.1.val.2.1)
  else if e.2=1 then (e.1.val.1.2,e.1.val.2.1)
  else if e.2=2 then (e.1.val.1.2,e.1.val.2.2)
  else (e.1.val.1.1,e.1.val.2.2)

def rectangleSideFinish {D : PLLinkDiagram} {T : BasedTraversal D} {C : diagramComponent D}
    (e : RetainedRectangleSide T C) : ℝ × ℝ :=
  if e.2=0 then (e.1.val.1.2,e.1.val.2.1)
  else if e.2=1 then (e.1.val.1.2,e.1.val.2.2)
  else if e.2=2 then (e.1.val.1.1,e.1.val.2.2)
  else (e.1.val.1.1,e.1.val.2.1)

theorem retainedRectangle_axis_cells {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (r : RetainedRectangleIndex T C) :
    secantAxisAdjacent T C r.val.1.1 r.val.1.2 ∧
      secantAxisAdjacent T C r.val.2.1 r.val.2.2 := by
  have hc := Finset.mem_product.mp (Finset.mem_filter.mp r.property).1
  exact ⟨(Finset.mem_filter.mp hc.1).2,(Finset.mem_filter.mp hc.2).2⟩

theorem rectangleSide_endpoints_distinct {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) :
    rectangleSideStart e ≠ rectangleSideFinish e := by
  have hc := retainedRectangle_axis_cells e.1
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  rcases e with ⟨r,k⟩
  fin_cases k <;> simp [rectangleSideStart,rectangleSideFinish] at hx hy <;>
    linarith [hc.1.2.2.1,hc.2.2.2.1]

/-- Directed parameter-side uniqueness, derived from actual adjacent cells. -/
theorem rectangleSide_key_injective {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} : Function.Injective
      (fun e : RetainedRectangleSide T C => (rectangleSideStart e,rectangleSideFinish e)) := by
  intro ⟨r,i⟩ ⟨q,j⟩ he
  have hr := retainedRectangle_axis_cells r
  have hq := retainedRectangle_axis_cells q
  have hstart := congrArg Prod.fst he
  have hfinish := congrArg Prod.snd he
  have hsx := congrArg Prod.fst hstart
  have hsy := congrArg Prod.snd hstart
  have hfx := congrArg Prod.fst hfinish
  have hfy := congrArg Prod.snd hfinish
  fin_cases i <;> fin_cases j <;>
    simp [rectangleSideStart,rectangleSideFinish] at hsx hsy hfx hfy
  all_goals try (exfalso; linarith [hr.1.2.2.1,hr.2.2.2.1,hq.1.2.2.1,hq.2.2.2.1])
  · have hv := secantAxisAdjacent_left_unique T C r.val.2.1 r.val.2.2 q.val.2.2
      hr.2 (by simpa only [hsy] using hq.2)
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (Prod.ext hsx hfx) (Prod.ext hsy hv)
    · rfl
  · have ha := secantAxisAdjacent_right_unique T C r.val.1.1 q.val.1.1 r.val.1.2
      hr.1 (by simpa only [hsx] using hq.1)
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (Prod.ext ha hsx) (Prod.ext hsy hfy)
    · rfl
  · have hu := secantAxisAdjacent_right_unique T C r.val.2.1 q.val.2.1 r.val.2.2
      hr.2 (by simpa only [hsy] using hq.2)
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (Prod.ext hfx hsx) (Prod.ext hu hsy)
    · rfl
  · have hb := secantAxisAdjacent_left_unique T C r.val.1.1 r.val.1.2 q.val.1.2
      hr.1 (by simpa only [hsx] using hq.1)
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (Prod.ext hsx hb) (Prod.ext hfy hsy)
    · rfl

def rectangleReverseRelation {D : PLLinkDiagram} {T : BasedTraversal D} {C : diagramComponent D}
    (e f : RetainedRectangleSide T C) : Prop :=
  rectangleSideStart f = rectangleSideFinish e ∧ rectangleSideFinish f = rectangleSideStart e

theorem rectangleReverseRelation_symm {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} {e f : RetainedRectangleSide T C}
    (h : rectangleReverseRelation e f) : rectangleReverseRelation f e := ⟨h.2.symm,h.1.symm⟩

theorem rectangleReverseRelation_unique {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} {e f g : RetainedRectangleSide T C}
    (hf : rectangleReverseRelation e f) (hg : rectangleReverseRelation e g) : f=g :=
  rectangleSide_key_injective (Prod.ext (hf.1.trans hg.1.symm) (hf.2.trans hg.2.symm))

/-- Actual retained-neighbor pairing. A side is fixed exactly when its
reverse directed parameter side is absent from this literal finite region. -/
def rectangleSideReverse {D : PLLinkDiagram} {T : BasedTraversal D} {C : diagramComponent D}
    (e : RetainedRectangleSide T C) : RetainedRectangleSide T C :=
  if h : ∃ f, rectangleReverseRelation e f then Classical.choose h else e

theorem rectangleSideReverse_of_exists {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C)
    (h : ∃ f, rectangleReverseRelation e f) :
    rectangleReverseRelation e (rectangleSideReverse e) := by
  unfold rectangleSideReverse
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem rectangleSideReverse_involutive {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} : Function.Involutive
      (rectangleSideReverse : RetainedRectangleSide T C → RetainedRectangleSide T C) := by
  intro e
  by_cases h : ∃ f, rectangleReverseRelation e f
  · have he := rectangleSideReverse_of_exists e h
    have hr := rectangleSideReverse_of_exists (rectangleSideReverse e)
      ⟨e,rectangleReverseRelation_symm he⟩
    exact rectangleReverseRelation_unique hr (rectangleReverseRelation_symm he)
  · simp [rectangleSideReverse,h]

theorem rectangleSideReverse_nonfixed_endpoints {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C)
    (hne : rectangleSideReverse e ≠ e) :
    rectangleReverseRelation e (rectangleSideReverse e) := by
  apply rectangleSideReverse_of_exists
  by_contra h
  exact hne (by simp [rectangleSideReverse,h])

theorem rectangleSideReverse_fixed_iff {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) :
    rectangleSideReverse e = e ↔ ¬∃ f, rectangleReverseRelation e f := by
  constructor
  · intro he h
    have hr := rectangleSideReverse_of_exists e h
    rw [he] at hr
    exact rectangleSide_endpoints_distinct e hr.1
  · intro h
    simp [rectangleSideReverse,h]

end
end DirectGLSSW.HOMFLY.PrincipalTurning




