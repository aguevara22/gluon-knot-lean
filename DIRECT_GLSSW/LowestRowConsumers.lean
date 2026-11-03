import GeminiLowest.Solution
import FramedKnotSkein
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract
open DirectGLSSW PermutationOrbits Coefficients PrincipalTurning
open scoped BigOperators

 theorem componentRowProduct_independent (D : PLLinkDiagram)
    (R S : ∀ C : diagramComponent D, ComponentRestriction D C) :
    componentRowProduct Gemini.candidateEvaluator D R =
      componentRowProduct Gemini.candidateEvaluator D S := by
  classical
  unfold componentRowProduct
  apply Finset.prod_congr rfl
  intro C _
  rw [_root_.GeminiLowest.component_evaluator_independent D C (R C) (S C)]

theorem lowest_row_for_restrictions (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (R : ∀ C : diagramComponent D, ComponentRestriction D C) :
    ∃ Λ : ℤ, 2 * Λ = mixedWrithe D ∧
      zRow (Gemini.candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
        aPower (-2 * Λ) * (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) *
          componentRowProduct Gemini.candidateEvaluator D R := by
  obtain ⟨S, linking, Λ, hconn, hpair, hsum, hmix, hfloor, hrow⟩ :=
    _root_.GeminiLowest.lowest_row_package D hD
  refine ⟨Λ, hmix, ?_⟩
  rw [componentRowProduct_independent D S R] at hrow
  exact hrow

theorem mixed_weighted_lowest_row (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (R : ∀ C : diagramComponent D, ComponentRestriction D C) :
    aPower (mixedWrithe D) *
      zRow (Gemini.candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
        (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) *
          componentRowProduct Gemini.candidateEvaluator D R := by
  obtain ⟨Λ, hmix, hrow⟩ := lowest_row_for_restrictions D hD R
  rw [hrow]
  have hneg : -2 * Λ = -(mixedWrithe D) := by omega
  rw [hneg, ← mul_assoc, ← mul_assoc, _root_.GeminiLowest.aPower_mul_neg, one_mul]

theorem mixed_weighted_lowest_row_switch (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (c : Fin D.nCrossing) (hc : IsMixed D c) :
    aPower (mixedWrithe (switchCrossing D c)) *
      zRow (Gemini.candidateEvaluator (switchCrossing D c) hD)
        (1 - (diagramComponentCount (switchCrossing D c) : ℤ)) =
    aPower (mixedWrithe D) *
      zRow (Gemini.candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) := by
  rw [mixed_weighted_lowest_row (switchCrossing D c) hD
    (_root_.GeminiLowest.canonicalComponentRestriction (switchCrossing D c)),
    mixed_weighted_lowest_row D hD (_root_.GeminiLowest.canonicalComponentRestriction D),
    _root_.GeminiLowest.componentRowProduct_switchCrossing_of_mixed D c hc]
  rfl

theorem lowest_row_of_no_mixed_crossing (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (hno : ∀ c : Fin D.nCrossing, ¬ IsMixed D c)
    (R : ∀ C : diagramComponent D, ComponentRestriction D C) :
    zRow (Gemini.candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
      (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) *
        componentRowProduct Gemini.candidateEvaluator D R := by
  have hm := _root_.GeminiLowest.mixedWrithe_eq_zero_of_no_mixed_bad
    (chooseBasedTraversal D) (fun c hm _ => hno c hm)
  have h := mixed_weighted_lowest_row D hD R
  simpa only [hm, _root_.GeminiLowest.aPower_zero, one_mul] using h

theorem actual_initial_history_framed_knot_row_unconditional
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (t : MarkedParentState)
    (htrace : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (ht : 0 < t.1.nArc) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ∀ C : diagramComponent (smoothCrossing t.1 c),
      ComponentRestriction (smoothCrossing t.1 c) C)
 :
    DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator t.1 ht
        (componentOf t.1.continuation ⟨0, ht⟩) =
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (switchCrossing t.1 c) ht
        (componentOf (switchCrossing t.1 c).continuation ⟨0, ht⟩) +
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl false))).diagram
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl false))).nonempty
        (componentOf
          (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl false))).diagram.continuation
          ⟨0, (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl false))).nonempty⟩) *
      DirectGLSSW.HOMFLY.framedKnotRow Gemini.candidateEvaluator
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl true))).diagram
        (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
          (firstVisitedBranch t.2.1 c) (Sum.inl true))).nonempty
        (componentOf
          (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl true))).diagram.continuation
          ⟨0, (R (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
            (firstVisitedBranch t.2.1 c) (Sum.inl true))).nonempty⟩) := by
  have hsm : 0 < (smoothCrossing t.1 c).nArc := by
    change 0 < t.1.nArc + 2
    omega
  obtain ⟨Λ, hLambda, hfactor⟩ := lowest_row_for_restrictions
    (smoothCrossing t.1 c) hsm R
  exact actual_initial_history_framed_knot_row D T hconn hpos t htrace ht c hc
    R Λ hfactor hLambda

end DirectGLSSW.HOMFLY.LowestRowContract
