import ActiveArcGammaM
import ActiveArcTerminal
import DirectGLSSW.OpenMarkedCurrent

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW ActiveArc Nonalternation PermutationOrbits RetainedWords
attribute [local instance] Classical.propDecidable

/-- The actual retained open word has exactly its two endpoint corners. -/
theorem singleEdge_openCount_two (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q)
    (S : Support q hR) : RetainedWords.openCount q hR S.val=2 := by
  classical
  let e : RetainedWords.Corner q hR S.val (start q) ≃
      RetainedWords.Coord q hR S.val (start q) := {
    toFun := Subtype.val
    invFun := fun i => ⟨i,ActiveArc.singleEdge_all_retained q S.val
      (RetainedWords.eventAt q hR S.val (start q) i)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Fintype.card (RetainedWords.Corner q hR S.val (start q))=
      Fintype.card (RetainedWords.Coord q hR S.val (start q)) :=
    Fintype.card_congr e
  calc
    RetainedWords.openCount q hR S.val =
        Fintype.card (Fibre (incoming q hR.noTriple S.val)
          (openComponent q hR.noTriple S.val)) := by
      simpa [RetainedWords.openCount,RetainedWords.Coord,openComponent] using hcard
    _=2 := ActiveArc.singleEdge_openOrbit_card q hR.noTriple S.val

/-- The true source open-current term reduces to an adjacent one-edge interval. -/
theorem singleEdge_openCurrent_one (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q)
    (S : Support q hR) : openCurrent q hR S=1 := by
  unfold openCurrent
  rw [singleEdge_openCount_two q hR S]
  norm_num
  exact OpenMarkedCurrent.entry_adjacent_eq_one _ 0

def singleEdgeSupportEquiv (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q) :
    Support q hR ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨∅,by simp [Nonalternation.Nonalternating]⟩
  left_inv S := by
    apply Subtype.ext
    exact (ActiveArc.singleEdge_support_empty q S.val).symm
  right_inv _ := rfl

theorem singleEdge_closedFactors_empty (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q)
    (S : Support q hR) :
    Finset.univ.erase (openComponent q hR.noTriple S.val)=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro C hC
  have hcne := (Finset.mem_erase.mp hC).1
  exact hcne (ActiveArc.singleEdge_component_eq_open q hR.noTriple S.val C)

theorem singleEdge_GammaM_one (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q)
    (hAux : ClosedAuxiliary q hR) : GammaM q hR hAux=1 := by
  classical
  unfold GammaM
  calc
    (∑ S : Support q hR, (-1 : ℚ)^S.val.card *
        (openCurrent q hR S * ∏ C ∈ Finset.univ.erase
          (openComponent q hR.noTriple S.val), closedWeight q hR hAux S C)) =
      ∑ _ : Unit, (1 : ℚ) := by
        apply Fintype.sum_equiv (singleEdgeSupportEquiv q hR)
        intro S
        have hS : S.val=∅ := ActiveArc.singleEdge_support_empty q S.val
        have hcard : S.val.card=0 := by
          simp [hS]
        have hcur := singleEdge_openCurrent_one q hR S
        have hindex := singleEdge_closedFactors_empty q hR S
        have hprod : ∏ C ∈ Finset.univ.erase (openComponent q hR.noTriple S.val),
            closedWeight q hR hAux S C=1 := by
          simp [hindex]
        rw [hcard,hcur,hprod]
        norm_num
    _ = 1 := by simp

/-- There are no actual closed components, so the source auxiliary condition is vacuous. -/
def singleEdge_closedAuxiliary (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q) :
    ClosedAuxiliary q hR := by
  intro S C hc
  letI : IsEmpty {C : Components q hR S // C≠openComponent q hR.noTriple S.val} :=
    ActiveArc.singleEdgeClosedComponentsEmpty q hR.noTriple S.val
  exact False.elim (this.false ⟨C,hc⟩)

theorem singleEdge_GammaM_one_vacuous (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q) :
    GammaM q hR (singleEdge_closedAuxiliary q hR)=1 :=
  singleEdge_GammaM_one q hR (singleEdge_closedAuxiliary q hR)

theorem singleEdge_terminal_parity (q : Fin 2 → PlanarPoint ℝ) (hR : Regular q)
    (hAux : ClosedAuxiliary q hR) :
    (-1 : ℚ)^(List.ofFn q).length * GammaM q hR hAux=1 := by
  rw [singleEdge_GammaM_one q hR hAux]
  simp

theorem singleEdge_terminal_parity_vacuous (q : Fin 2 → PlanarPoint ℝ)
    (hR : Regular q) :
    (-1 : ℚ)^(List.ofFn q).length * GammaM q hR (singleEdge_closedAuxiliary q hR)=1 := by
  rw [singleEdge_GammaM_one_vacuous q hR]
  simp

end DirectGLSSW.ActiveArc.Primitive
