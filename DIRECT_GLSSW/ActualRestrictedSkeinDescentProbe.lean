import ActualRestrictedSkeinDescent
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ActualRestrictedSkeinDescentProbe
open LowestRowContract PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- The same actual first-bad decision admits the switched branch and every
supplied extracted component; both decreases are derived. -/
theorem actual_first_bad_all_components (D : PLLinkDiagram) (T : BasedTraversal D)
    (hbad : (badCrossings T).Nonempty) :
    ∃ c : Fin D.nCrossing,
      (Prod.Lex (· < ·) (· < ·)
        (actualRestrictedSkeinComplexity ⟨switchCrossing D c,switchTraversal T c⟩)
        (actualRestrictedSkeinComplexity ⟨D,T⟩)) ∧
      ∀ (C : Component (smoothCrossing D c).continuation)
        (R : ComponentRestriction (smoothCrossing D c) C) (U : BasedTraversal R.diagram),
        R.diagram.nCrossing < D.nCrossing ∧
        Prod.Lex (· < ·) (· < ·)
          (actualRestrictedSkeinComplexity ⟨R.diagram,U⟩)
          (actualRestrictedSkeinComplexity ⟨D,T⟩) := by
  obtain ⟨c,hc,_⟩ := exists_firstBad_goodPrefix D T hbad
  exact ⟨c,(ActualRestrictedSkeinStep.switched D T c hc).decreases,
    fun C R U => ⟨R.nCrossing_lt_before_smoothing D c C,
      (ActualRestrictedSkeinStep.smoothed D T c C R U).decreases⟩⟩

end DirectGLSSW.HOMFLY.ActualRestrictedSkeinDescentProbe
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.ActualRestrictedSkeinState
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.ActualRestrictedSkeinStep
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.actualRestrictedSkeinComplexity
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.ActualRestrictedSkeinStep.decreases
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.actualRestrictedSkeinStep_wellFounded
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.no_infinite_actualRestrictedSkeinSteps
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.MarkedParentStep.toActualRestrictedSkeinStep
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.ActualRestrictedSkeinDescentProbe.actual_first_bad_all_components
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.ActualRestrictedSkeinStep.switched
set_option pp.all true in
#check @DirectGLSSW.HOMFLY.ActualRestrictedSkeinStep.smoothed
