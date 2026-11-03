import SmoothedRestrictionCrossingCompleteness
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

theorem MarkedParentStep.crossingOrigin_complete {s t : MarkedParentState}
    (step : MarkedParentStep s t) (d : Fin s.1.nCrossing)
    (hports : ∀ i : Fin 2, ∃ e : Fin t.1.nArc,
      step.arcOrigin e = some (s.1.incoming d i)) :
    ∃ e : Fin t.1.nCrossing, step.crossingOrigin e = d := by
  cases step with
  | switched S c hc hgood => exact ⟨d,rfl⟩
  | @smoothed D T S c hc hgood R =>
    exact smoothedRestrictionCrossingOrigin_complete D c (S.connected _ _) R d hports

/-- A historical crossing with both incoming arcs still present must itself
still be present. Deleted or demoted crossings cannot silently remain in the
resulting two-port interval. -/
theorem MarkedParentTrace.crossingOrigin_complete {s t : MarkedParentState}
    (h : MarkedParentTrace s t) :
    ∀ d : Fin s.1.nCrossing,
      (∀ i : Fin 2, ∃ e : Fin t.1.nArc, h.arcOrigin e = some (s.1.incoming d i)) →
      ∃ e : Fin t.1.nCrossing, h.crossingOrigin e = d := by
  induction h with
  | nil s => intro d hports; exact ⟨d,rfl⟩
  | @cons s m t step tail ih =>
    intro d hports
    have hmid : ∀ i : Fin 2, ∃ a : Fin m.1.nArc,
        step.arcOrigin a = some (s.1.incoming d i) ∧
        ∃ e : Fin t.1.nArc, tail.arcOrigin e = some a := by
      intro i
      obtain ⟨e,he⟩ := hports i
      cases hh : tail.arcOrigin e with
      | none => simp [MarkedParentTrace.arcOrigin,hh] at he
      | some a =>
        refine ⟨a,?_,e,hh⟩
        simpa only [MarkedParentTrace.arcOrigin,hh,Option.some_bind] using he
    obtain ⟨dm,hdm⟩ := step.crossingOrigin_complete d (by
      intro i
      obtain ⟨a,ha,_⟩ := hmid i
      exact ⟨a,ha⟩)
    have htail : ∀ i : Fin 2, ∃ e : Fin t.1.nArc,
        tail.arcOrigin e = some (m.1.incoming dm i) := by
      intro i
      obtain ⟨a,ha,e,he⟩ := hmid i
      have hi := step.crossingOrigin_incoming dm i
      rw [hdm] at hi
      have hae := step.arcOrigin_some_injective a (m.1.incoming dm i) _ ha hi
      exact ⟨e,hae ▸ he⟩
    obtain ⟨e,he⟩ := ih dm htail
    refine ⟨e,?_⟩
    change step.crossingOrigin (tail.crossingOrigin e) = d
    rw [he,hdm]

end DirectGLSSW.HOMFLY
