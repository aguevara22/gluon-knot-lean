import HOMFLYComponentPLPath

/-! Source-only draft. Exact local geometry of the given drawing; no planar
reduction, Jordan separation, or Reidemeister assertion is assumed here. -/

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
noncomputable section

theorem diagramArcPath_interior_ne_other (D : PLLinkDiagram)
    (e f : Fin D.nArc) (hef : e ≠ f) (s t : unitInterval)
    (hs0 : 0 < s.val) (hs1 : s.val < 1) :
    diagramArcPath D e s ≠ diagramArcPath D f t := by
  intro heq
  by_cases ht0 : t.val = 0
  · have ht : t = 0 := Subtype.ext ht0
    subst t
    have hvertex : D.vertexPoint (D.arcSource f) =
        affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) s.val := by
      exact (diagramArcPath D f).source.symm.trans heq.symm
    exact D.vertices_avoid_arc_interiors (D.arcSource f) e s.val hs0 hs1 hvertex
  · by_cases ht1 : t.val = 1
    · have ht : t = 1 := Subtype.ext ht1
      subst t
      have hvertex : D.vertexPoint (D.arcTarget f) =
          affinePoint (D.vertexPoint (D.arcSource e))
            (D.vertexPoint (D.arcTarget e)) s.val := by
        exact (diagramArcPath D f).target.symm.trans heq.symm
      exact D.vertices_avoid_arc_interiors (D.arcTarget f) e s.val hs0 hs1 hvertex
    · exact D.arc_interiors_disjoint e f hef s.val t.val hs0 hs1
        (lt_of_le_of_ne t.property.1 (Ne.symm ht0))
        (lt_of_le_of_ne t.property.2 ht1) heq

theorem diagramArcPath_meeting_endpoints (D : PLLinkDiagram)
    (e f : Fin D.nArc) (hef : e ≠ f) (s t : unitInterval)
    (heq : diagramArcPath D e s = diagramArcPath D f t) :
    (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
  have endpoint {a b : Fin D.nArc} (hab : a ≠ b) (u v : unitInterval)
      (h : diagramArcPath D a u = diagramArcPath D b v) : u = 0 ∨ u = 1 := by
    by_cases hu0 : u.val = 0
    · exact Or.inl (Subtype.ext hu0)
    · by_cases hu1 : u.val = 1
      · exact Or.inr (Subtype.ext hu1)
      · exact False.elim (diagramArcPath_interior_ne_other D a b hab u v
          (lt_of_le_of_ne u.property.1 (Ne.symm hu0))
          (lt_of_le_of_ne u.property.2 hu1) h)
  exact ⟨endpoint hef s t heq, endpoint (Ne.symm hef) t s heq.symm⟩

theorem diagramArcPath_intersection_iff (D : PLLinkDiagram)
    (e f : Fin D.nArc) (hef : e ≠ f) (z : PlanarPoint ℝ) :
    z ∈ Set.range (diagramArcPath D e) ∧ z ∈ Set.range (diagramArcPath D f) ↔
      ∃ v : Fin D.nVertex, z = D.vertexPoint v ∧
        (D.arcSource e = v ∨ D.arcTarget e = v) ∧
        (D.arcSource f = v ∨ D.arcTarget f = v) := by
  constructor
  · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
    obtain ⟨he,hf⟩ := diagramArcPath_meeting_endpoints D e f hef s t (hs.trans ht.symm)
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · refine ⟨D.arcSource e, hs.symm.trans (diagramArcPath D e).source,
        Or.inl rfl, Or.inl ?_⟩
      exact D.vertexPoint_injective
        ((diagramArcPath D f).source.symm.trans (ht.trans
          (hs.symm.trans (diagramArcPath D e).source)))
    · refine ⟨D.arcSource e, hs.symm.trans (diagramArcPath D e).source,
        Or.inl rfl, Or.inr ?_⟩
      exact D.vertexPoint_injective
        ((diagramArcPath D f).target.symm.trans (ht.trans
          (hs.symm.trans (diagramArcPath D e).source)))
    · refine ⟨D.arcTarget e, hs.symm.trans (diagramArcPath D e).target,
        Or.inr rfl, Or.inl ?_⟩
      exact D.vertexPoint_injective
        ((diagramArcPath D f).source.symm.trans (ht.trans
          (hs.symm.trans (diagramArcPath D e).target)))
    · refine ⟨D.arcTarget e, hs.symm.trans (diagramArcPath D e).target,
        Or.inr rfl, Or.inr ?_⟩
      exact D.vertexPoint_injective
        ((diagramArcPath D f).target.symm.trans (ht.trans
          (hs.symm.trans (diagramArcPath D e).target)))
  · rintro ⟨v,rfl,he,hf⟩
    constructor
    · rcases he with he | he
      · exact ⟨0, (diagramArcPath D e).source.trans (congrArg D.vertexPoint he)⟩
      · exact ⟨1, (diagramArcPath D e).target.trans (congrArg D.vertexPoint he)⟩
    · rcases hf with hf | hf
      · exact ⟨0, (diagramArcPath D f).source.trans (congrArg D.vertexPoint hf)⟩
      · exact ⟨1, (diagramArcPath D f).target.trans (congrArg D.vertexPoint hf)⟩

theorem regular_vertex_incoming_unique (D : PLLinkDiagram) (v : Fin D.nVertex)
    (hregular : ∀ c, D.crossingVertex c ≠ v) (e f : Fin D.nArc)
    (he : D.arcTarget e = v) (hf : D.arcTarget f = v) : e = f := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (D.regular_degree_one v hregular).1
  have hem : e ∈ incomingArcs D.arcTarget v := by simp [incomingArcs, he]
  have hfm : f ∈ incomingArcs D.arcTarget v := by simp [incomingArcs, hf]
  rw [ha, Finset.mem_singleton] at hem hfm
  exact hem.trans hfm.symm

theorem regular_vertex_incident_same_component (D : PLLinkDiagram)
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
    · exact ⟨a,ha,rfl⟩
  obtain ⟨a,ha,hea⟩ := incoming_rep e he
  obtain ⟨b,hb,hfb⟩ := incoming_rep f hf
  have hab := regular_vertex_incoming_unique D v hregular a b ha hb
  exact hea.symm.trans ((congrArg (componentOf D.continuation) hab).trans hfb)

theorem different_component_loops_meet_at_crossing (D : PLLinkDiagram)
    (e f : Fin D.nArc)
    (hef : componentOf D.continuation e ≠ componentOf D.continuation f)
    (z : PlanarPoint ℝ)
    (he : z ∈ Set.range (componentPLLoop D e))
    (hf : z ∈ Set.range (componentPLLoop D f)) :
    ∃ c : Fin D.nCrossing, z = D.vertexPoint (D.crossingVertex c) := by
  classical
  obtain ⟨a,ha,hza⟩ := (componentPLLoop_trace D e z).1 he
  obtain ⟨b,hb,hzb⟩ := (componentPLLoop_trace D f z).1 hf
  have hab : a ≠ b := by
    intro h
    exact hef (ha.symm.trans ((congrArg (componentOf D.continuation) h).trans hb))
  obtain ⟨v,hz,hav,hbv⟩ := (diagramArcPath_intersection_iff D a b hab z).1 ⟨hza,hzb⟩
  by_cases hc : ∃ c, D.crossingVertex c = v
  · obtain ⟨c,hc⟩ := hc
    exact ⟨c,hz.trans (congrArg D.vertexPoint hc.symm)⟩
  · have hregular : ∀ c, D.crossingVertex c ≠ v := by
      simpa only [not_exists] using hc
    have hp := regular_vertex_incident_same_component D v hregular a b hav hbv
    exact False.elim (hef (ha.symm.trans (hp.trans hb)))

end
end DirectGLSSW.HOMFLY







