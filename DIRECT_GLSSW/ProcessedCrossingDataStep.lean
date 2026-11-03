import ProcessedChildCrossingInterval
import ComponentRestrictionSigns
import DirectGLSSW.HOMFLY.HOMFLYSwitchChoiceFacts
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
namespace MarkedParentStep

theorem crossingOrigin_over_or_marked {s t : MarkedParentState}
    (step : MarkedParentStep s t) (d : Fin t.1.nCrossing) :
    t.1.overBranch d = s.1.overBranch (step.crossingOrigin d) ∨
      ∃ i : Fin 2, t.1.incoming d i ∈ t.2.2.marks := by
  cases step with
  | @switched D T S c hc hgood =>
    by_cases hd : d=c
    · subst d
      exact Or.inr ⟨firstVisitedBranch T c,Finset.mem_insert_self _ _⟩
    · left
      exact Function.update_of_ne hd _ _
  | @smoothed D T S c hc hgood R =>
    exact Or.inl (R.overBranch_eq d)

theorem crossingOrigin_sign_or_marked {s t : MarkedParentState}
    (step : MarkedParentStep s t) (d : Fin t.1.nCrossing) :
    crossingSign t.1 d = crossingSign s.1 (step.crossingOrigin d) ∨
      ∃ i : Fin 2, t.1.incoming d i ∈ t.2.2.marks := by
  cases step with
  | @switched D T S c hc hgood =>
    by_cases hd : d=c
    · subst d
      exact Or.inr ⟨firstVisitedBranch T c,Finset.mem_insert_self _ _⟩
    · exact Or.inl (crossingSign_switchCrossing_of_ne D c d hd)
  | @smoothed D T S c hc hgood R =>
    left
    let old := (smoothCrossingEquiv D c).symm (R.crossingEquiv d).val
    have he : smoothCrossingEquiv D c old = (R.crossingEquiv d).val :=
      (smoothCrossingEquiv D c).apply_symm_apply _
    rw [R.crossingSign_eq,←he,crossingSign_smoothRetained]
    rfl
end MarkedParentStep
end DirectGLSSW.HOMFLY
