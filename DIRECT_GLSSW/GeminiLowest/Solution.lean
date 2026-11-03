import GeminiLowest.LayeredSublinkFactorization

set_option autoImplicit false
noncomputable section

namespace GeminiLowest

open DirectGLSSW
open DirectGLSSW.PermutationOrbits
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.LowestRowContract
open scoped BigOperators

attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  PermutationOrbits.componentFintype D.continuation

/-! ### Part 1: Mixed-Crossing Lowest-Row Skein Step -/

theorem candidateEvaluator_pivot_expansion (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (c : Fin D.nCrossing) :
    candidateEvaluator D hD =
      pivotSwitchFactor D c * candidateEvaluator (switchCrossing D c) hD +
        pivotSmoothFactor D c *
          candidateEvaluator (smoothCrossing D c) (by change 0 < D.nArc + 2; omega) := by
  let T := chooseBasedTraversal D
  have hstep := descendingEvaluator_eq_any_pivot
    (all_lowerCrossingEvaluatorSkeinIH D.nCrossing) D rfl T c
  rw [descendingEvaluatorPivotBranch] at hstep
  rw [candidateEvaluator_eq_traversal all_lowerCrossingEvaluatorSkeinIH D hD T]
  rw [candidateEvaluator_eq_traversal all_lowerCrossingEvaluatorSkeinIH (switchCrossing D c) hD
    (switchTraversal T c)]
  rw [candidateEvaluator_eq_traversal all_lowerCrossingEvaluatorSkeinIH (smoothCrossing D c)
    (by change 0 < D.nArc + 2; omega) (smoothChildBasedTraversal D c)]
  exact hstep

theorem pivotSwitchFactor_eq_aPower (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    pivotSwitchFactor D c = aPower (-2 * writheSign D c) := by
  unfold pivotSwitchFactor writheSign
  cases crossingSign D c
  · change aMonomial * aMonomial = aPower (-2 * -1)
    rw [← aPower_one, ← aPower_add]
    rfl
  · change aInvMonomial * aInvMonomial = aPower (-2 * 1)
    rw [← aPower_neg_one, ← aPower_add]
    rfl

theorem zRow_pivotSmoothFactor_mul_of_mixed (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hc : IsMixed D c) :
    zRow (pivotSmoothFactor D c *
      candidateEvaluator (smoothCrossing D c) (by change 0 < D.nArc + 2; omega))
      (1 - (diagramComponentCount D : ℤ)) = 0 := by
  let D₀ := smoothCrossing D c
  have hD₀ : 0 < D₀.nArc := by change 0 < D.nArc + 2; omega
  have hjoin : diagramComponentCount D₀ + 1 = diagramComponentCount D :=
    smooth_componentCount_join D c (fun hsc => hc (Quotient.sound hsc))
  have hfloor₀ : zFloor (candidateEvaluator D₀ hD₀) (1 - (diagramComponentCount D₀ : ℤ)) :=
    lowest_z_floor D₀ hD₀
  have hlt : (1 - (diagramComponentCount D : ℤ)) - 1 <
      (1 - (diagramComponentCount D₀ : ℤ)) := by omega
  have hz_zero : zRow (zMonomial * candidateEvaluator D₀ hD₀)
      (1 - (diagramComponentCount D : ℤ)) = 0 := by
    rw [zRow_zMonomial_mul]
    exact zRow_eq_zero_of_lt_zFloor hfloor₀ hlt
  unfold pivotSmoothFactor
  cases crossingSign D c
  · change zRow (-(aMonomial * zMonomial) * candidateEvaluator D₀ hD₀)
      (1 - (diagramComponentCount D : ℤ)) = 0
    have hneg : -(aMonomial * zMonomial) * candidateEvaluator D₀ hD₀ =
        -(aMonomial * (zMonomial * candidateEvaluator D₀ hD₀)) := by ring
    rw [hneg, zRow_neg, zRow_aMonomial_mul, hz_zero, mul_zero, neg_zero]
  · change zRow ((aInvMonomial * zMonomial) * candidateEvaluator D₀ hD₀)
      (1 - (diagramComponentCount D : ℤ)) = 0
    rw [mul_assoc, zRow_aInvMonomial_mul, hz_zero, mul_zero]

theorem zRow_switchCrossing_of_mixed (D : PLLinkDiagram) (hD : 0 < D.nArc)
    (c : Fin D.nCrossing) (hc : IsMixed D c) :
    zRow (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
      aPower (-2 * writheSign D c) *
        zRow (candidateEvaluator (switchCrossing D c) hD)
          (1 - (diagramComponentCount D : ℤ)) := by
  conv_lhs => rw [candidateEvaluator_pivot_expansion D hD c]
  rw [zRow_add, zRow_pivotSmoothFactor_mul_of_mixed D c hc, add_zero]
  rw [pivotSwitchFactor_eq_aPower D c, zRow_aPower_mul]

/-! ### Part 2: Invariance of `componentRowProduct` under Mixed Crossing Switch -/

theorem singletonOldCrossing_ne_of_mixed (D : PLLinkDiagram) (C : diagramComponent D)
    (c : Fin D.nCrossing) (hc : IsMixed D c)
    (d : Fin (restrictSublink D (singletonSublink D C)).nCrossing) :
    sublinkOldCrossing D (singletonSublink D C) d ≠ c := by
  intro heq
  have hout := (sublinkCrossingEquiv D (singletonSublink D C) d).property
  have hin := (outgoing_mem_sublink_iff_incoming D (singletonSublink D C)
    (sublinkOldCrossing D (singletonSublink D C) d)).mp hout
  rw [heq] at hin
  have h0 : componentOf D.continuation (D.incoming c 0) = C := hin 0
  have h1 : componentOf D.continuation (D.incoming c 1) = C := hin 1
  exact hc (h0.trans h1.symm)

def singletonSwitchRestrictionSignedIso (D : PLLinkDiagram) (C : diagramComponent D)
    (c : Fin D.nCrossing) (hc : IsMixed D c) :
    SignedDiagramIso
      (canonicalComponentRestriction (switchCrossing D c) C).diagram
      (canonicalComponentRestriction D C).diagram where
  arcEquiv := Equiv.refl _
  crossingEquiv := Equiv.refl _
  incoming_map _ _ := rfl
  outgoing_map _ _ := rfl
  continuation_map _ := rfl
  through_map _ := rfl
  overBranch_map d := by
    have hdc := singletonOldCrossing_ne_of_mixed D C c hc d
    change (switchCrossing D c).overBranch
      (sublinkOldCrossing D (singletonSublink D C) d) =
      D.overBranch (sublinkOldCrossing D (singletonSublink D C) d)
    simp [switchCrossing, hdc]
  crossingSign_map d := by
    have hdc := singletonOldCrossing_ne_of_mixed D C c hc d
    change crossingSign (restrictSublink (switchCrossing D c)
        (switchSublink D (singletonSublink D C) c)) d =
      crossingSign (restrictSublink D (singletonSublink D C)) d
    rw [sublink_crossing_sign_preserved (switchCrossing D c)
      (switchSublink D (singletonSublink D C) c) d, sublinkOldCrossing_switchSublink]
    calc
      crossingSign (switchCrossing D c) (sublinkOldCrossing D (singletonSublink D C) d) =
          crossingSign D (sublinkOldCrossing D (singletonSublink D C) d) :=
        crossingSign_switchCrossing_of_ne D c
          (sublinkOldCrossing D (singletonSublink D C) d) hdc
      _ = crossingSign (restrictSublink D (singletonSublink D C)) d :=
        (sublink_crossing_sign_preserved D (singletonSublink D C) d).symm

theorem componentRowProduct_switchCrossing_of_mixed (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (hc : IsMixed D c) :
    componentRowProduct candidateEvaluator (switchCrossing D c)
      (canonicalComponentRestriction (switchCrossing D c)) =
    componentRowProduct candidateEvaluator D (canonicalComponentRestriction D) := by
  unfold componentRowProduct
  apply Finset.prod_congr rfl
  intro C _
  congr 1
  exact candidateEvaluator_signedDiagramIso all_lowerCrossingEvaluatorSkeinIH
    (canonicalComponentRestriction (switchCrossing D c) C).diagram
    (canonicalComponentRestriction D C).diagram
    (canonicalComponentRestriction (switchCrossing D c) C).nonempty
    (canonicalComponentRestriction D C).nonempty
    (singletonSwitchRestrictionSignedIso D C c hc)

/-! ### Part 3: Complete Lowest-Row Formula and `lowest_row_package` -/

theorem lowest_row_formula_aux :
    ∀ k : ℕ, ∀ (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D),
      (badCrossings T).card = k →
        zRow (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
          aPower (-mixedWrithe D) *
            (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) *
            componentRowProduct candidateEvaluator D (canonicalComponentRestriction D) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro D hD T hk
    by_cases hmix : ∃ c ∈ badCrossings T, IsMixed D c
    · obtain ⟨c, hc_bad, hc_mix⟩ := hmix
      have hlt : (badCrossings (switchTraversal T c)).card < k := by
        have hd := badCrossings_switch_card T c hc_bad
        omega
      have hsw := ih _ hlt (switchCrossing D c) hD (switchTraversal T c) rfl
      have hrow := zRow_switchCrossing_of_mixed D hD c hc_mix
      have hcomp_cnt : diagramComponentCount (switchCrossing D c) = diagramComponentCount D := rfl
      rw [hcomp_cnt] at hsw
      rw [hrow, hsw]
      rw [componentRowProduct_switchCrossing_of_mixed D c hc_mix]
      have hmw : -mixedWrithe D =
          (-2 * writheSign D c) + (-mixedWrithe (switchCrossing D c)) := by
        have := mixedWrithe_switchCrossing_of_mixed D c hc_mix
        omega
      rw [hmw, aPower_add]
      ring
    · push_neg at hmix
      have hmw0 : mixedWrithe D = 0 :=
        mixedWrithe_eq_zero_of_no_mixed_bad T (fun c hmc hbad =>
          hmix c (by simpa [badCrossings] using hbad) hmc)
      rw [hmw0, neg_zero, aPower_zero, one_mul]
      exact zRow_candidateEvaluator_of_no_mixed_bad D hD T hmix

theorem lowest_row_formula (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    zRow (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
      aPower (-mixedWrithe D) *
        (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) *
        componentRowProduct candidateEvaluator D (canonicalComponentRestriction D) :=
  lowest_row_formula_aux _ D hD (chooseBasedTraversal D) rfl

theorem lowest_row_package :
    ∀ (D : PLLinkDiagram) (hD : 0 < D.nArc),
      ∃ (R : ∀ C : diagramComponent D, ComponentRestriction D C)
        (linking : diagramComponent D → diagramComponent D → ℤ)
        (Λ : ℤ),
        (∀ C, diagramComponentCount (R C).diagram = 1) ∧
        (∀ C E, 2 * linking C E = pairWrithe D C E) ∧
        2 * Λ = totalOrderedPairSum D linking ∧
        2 * Λ = mixedWrithe D ∧
        zFloor (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) ∧
        zRow (candidateEvaluator D hD) (1 - (diagramComponentCount D : ℤ)) =
          aPower (-2 * Λ) * (aMonomial - aInvMonomial) ^ (diagramComponentCount D - 1) *
            componentRowProduct candidateEvaluator D R := by
  intro D hD
  refine ⟨canonicalComponentRestriction D, linking D, totalLinking D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C
    exact componentRestriction_componentCount_eq_one (canonicalComponentRestriction D C)
  · intro C E
    exact two_mul_linking_eq_pairWrithe D C E
  · exact two_mul_totalLinking_eq_totalOrderedPairSum D
  · exact two_mul_totalLinking_eq_mixedWrithe D
  · exact lowest_z_floor D hD
  · have hΛ : -2 * totalLinking D = -mixedWrithe D := by
      have := two_mul_totalLinking_eq_mixedWrithe D
      omega
    rw [hΛ]
    exact lowest_row_formula D hD

end GeminiLowest
