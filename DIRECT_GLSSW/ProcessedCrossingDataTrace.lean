import ProcessedCrossingDataStep
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
namespace MarkedParentTrace

/-- A retained crossing's marked incoming port remains the same marked port
under the actual forward mark embedding, by partial-origin injectivity. -/
theorem crossingOrigin_incoming_marked {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (d : Fin t.1.nCrossing) (i : Fin 2)
    (hi : s.1.incoming (h.crossingOrigin d) i ∈ s.2.2.marks) :
    t.1.incoming d i ∈ t.2.2.marks := by
  let x : StateMarks s := ⟨s.1.incoming (h.crossingOrigin d) i,hi⟩
  have heq : t.1.incoming d i=(h.markEmbedding x).val :=
    h.arcOrigin_some_injective _ _ x.val (h.crossingOrigin_incoming d i)
      (h.arcOrigin_markEmbedding x)
  rw [heq]
  exact (h.markEmbedding x).property

theorem crossingOrigin_over_or_marked {s t : MarkedParentState}
    (h : MarkedParentTrace s t) : ∀ d : Fin t.1.nCrossing,
    t.1.overBranch d = s.1.overBranch (h.crossingOrigin d) ∨
      ∃ i : Fin 2, t.1.incoming d i ∈ t.2.2.marks := by
  induction h with
  | nil s => intro d; exact Or.inl rfl
  | cons step tail ih =>
    intro d
    rcases ih d with heq | hm
    · rcases step.crossingOrigin_over_or_marked (tail.crossingOrigin d) with hs | ⟨i,hi⟩
      · exact Or.inl (heq.trans hs)
      · exact Or.inr ⟨i,tail.crossingOrigin_incoming_marked d i hi⟩
    · exact Or.inr hm

theorem crossingOrigin_sign_or_marked {s t : MarkedParentState}
    (h : MarkedParentTrace s t) : ∀ d : Fin t.1.nCrossing,
    crossingSign t.1 d = crossingSign s.1 (h.crossingOrigin d) ∨
      ∃ i : Fin 2, t.1.incoming d i ∈ t.2.2.marks := by
  induction h with
  | nil s => intro d; exact Or.inl rfl
  | cons step tail ih =>
    intro d
    rcases ih d with heq | hm
    · rcases step.crossingOrigin_sign_or_marked (tail.crossingOrigin d) with hs | ⟨i,hi⟩
      · exact Or.inl (heq.trans hs)
      · exact Or.inr ⟨i,tail.crossingOrigin_incoming_marked d i hi⟩
    · exact Or.inr hm
end MarkedParentTrace
end DirectGLSSW.HOMFLY
