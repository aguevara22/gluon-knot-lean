import IncidentRetainedEndpoints
import CrossingIncidentRays
import RegularVertexCellLabels

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate4 complete: at any actual vertex, the only corner/incident
retained contacts are its own two cut endpoints. Actual degree/port fields
supply the case split; no intersection certificate is assumed. -/
theorem roundedCorner_incident_retained_iff (D : PLLinkDiagram) (e f : Fin D.nArc)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (hf : D.arcSource f = D.arcTarget e ∨ D.arcTarget f = D.arcTarget e) :
    Complex.equivRealProd (roundedCorner D e δ.val s) = retainedArcPoint D f δ t ↔
      (f = e ∧ s = 0 ∧ t = 1) ∨ (f = D.continuation e ∧ s = 1 ∧ t = 0) := by
  classical
  constructor
  · intro heq
    by_cases hcross : ∃ c : Fin D.nCrossing, D.crossingVertex c = D.arcTarget e
    · obtain ⟨c,hc⟩ := hcross
      obtain ⟨i,hi⟩ := crossing_incoming_arc_label D c e hc.symm
      subst e
      have hfCross : D.arcSource f = D.crossingVertex c ∨ D.arcTarget f = D.crossingVertex c := by
        simpa only [D.incoming_target] using hf
      obtain ⟨j,hj⟩ := crossing_incident_arc_label D c f hfCross
      rcases hj with hj | hj
      · subst f
        by_cases hij : i = j
        · subst j
          have h := (roundedCorner_retained_incoming_iff D (D.incoming c i) δ s t hs ht).mp heq
          exact Or.inl ⟨rfl,h.1,h.2⟩
        · exact False.elim (roundedCorner_ne_other_retained_incoming D c i j hij δ s t ht heq)
      · subst f
        by_cases hij : i = j
        · subst j
          have h := (roundedCorner_retained_outgoing_iff D (D.incoming c i) δ s t hs ht).mp heq
          exact Or.inr ⟨rfl,h.1,h.2⟩
        · exact False.elim (roundedCorner_ne_other_retained_outgoing D c i j hij δ s t ht heq)
    · have hnoncross : ∀ c, D.crossingVertex c ≠ D.arcTarget e := by
        simpa only [not_exists] using hcross
      rcases hf with hf | hf
      · have hlabel : f = D.continuation e := regular_vertex_outgoing_unique D (D.arcTarget e)
          hnoncross f (D.continuation e) hf (D.continuation_incidence e).symm
        subst f
        have h := (roundedCorner_retained_outgoing_iff D e δ s t hs ht).mp heq
        exact Or.inr ⟨rfl,h.1,h.2⟩
      · have hlabel : f = e := regular_vertex_incoming_unique D (D.arcTarget e)
          hnoncross f e hf rfl
        subst f
        have h := (roundedCorner_retained_incoming_iff D e δ s t hs ht).mp heq
        exact Or.inl ⟨rfl,h.1,h.2⟩
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩)
    · exact roundedCorner_incoming_cut D _ δ
    · exact roundedCorner_outgoing_cut D _ δ

end DirectGLSSW.HOMFLY.PrincipalTurning

