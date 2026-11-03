import FramingWritheRelations
import ComponentRestrictionSigns
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open LowestRowContract PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  componentFintype D.continuation

 theorem diagramWrithe_restriction {D : PLLinkDiagram} {C : diagramComponent D}
    (R : ComponentRestriction D C) :
    diagramWrithe R.diagram = ∑ c : Fin D.nCrossing,
      if ∀ i : Fin 2, componentOf D.continuation (D.incoming c i) = C
      then writheSign D c else 0 := by
  let E : Fin R.diagram.nCrossing ≃
      {c : Fin D.nCrossing // ∀ i : Fin 2,
        componentOf D.continuation (D.incoming c i) = C} := R.crossingEquiv
  have he : (∑ c : Fin R.diagram.nCrossing, writheSign R.diagram c) =
      ∑ c : {c : Fin D.nCrossing // ∀ i : Fin 2,
        componentOf D.continuation (D.incoming c i) = C}, writheSign D c.val := by
    apply Fintype.sum_equiv E
    intro c
    change writheSign R.diagram c = writheSign D (R.crossingEquiv c).val
    unfold writheSign
    rw [R.crossingSign_eq]
  have hs : (∑ c ∈ Finset.univ.filter (fun c : Fin D.nCrossing =>
      ∀ i : Fin 2, componentOf D.continuation (D.incoming c i) = C), writheSign D c) =
      ∑ c : {c : Fin D.nCrossing // ∀ i : Fin 2,
        componentOf D.continuation (D.incoming c i) = C}, writheSign D c.val := by
    apply Finset.sum_subtype
    intro c
    simp
  calc
    diagramWrithe R.diagram = _ := he
    _ = ∑ c ∈ Finset.univ.filter (fun c : Fin D.nCrossing =>
          ∀ i : Fin 2, componentOf D.continuation (D.incoming c i) = C),
        writheSign D c := hs.symm
    _ = _ := Finset.sum_filter _ _

theorem crossing_self_component_indicator (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    (∑ C : diagramComponent D,
      if ∀ i : Fin 2, componentOf D.continuation (D.incoming c i) = C
      then writheSign D c else 0) =
      if IsMixed D c then 0 else writheSign D c := by
  have hi (C : diagramComponent D) :
      (∀ i : Fin 2, componentOf D.continuation (D.incoming c i) = C) ↔
      componentOf D.continuation (D.incoming c 0) = C ∧
      componentOf D.continuation (D.incoming c 1) = C := by
    constructor
    · intro h; exact ⟨h 0,h 1⟩
    · rintro ⟨h0,h1⟩ i; fin_cases i <;> assumption
  simp only [hi,IsMixed]
  by_cases h : componentOf D.continuation (D.incoming c 0) =
      componentOf D.continuation (D.incoming c 1)
  · simp [← h,eq_comm]
  · rw [if_pos h]
    apply Finset.sum_eq_zero
    intro C _
    exact if_neg (by rintro ⟨h0,h1⟩; exact h (h0.trans h1.symm))

theorem diagramWrithe_component_partition (D : PLLinkDiagram)
    (R : ∀ C : diagramComponent D, ComponentRestriction D C) :
    diagramWrithe D =
      (∑ C : diagramComponent D, diagramWrithe (R C).diagram) + mixedWrithe D := by
  have hs : (∑ C : diagramComponent D, diagramWrithe (R C).diagram) =
      ∑ c : Fin D.nCrossing, if IsMixed D c then 0 else writheSign D c := by
    simp_rw [diagramWrithe_restriction]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => crossing_self_component_indicator D c)
  rw [hs]
  unfold diagramWrithe mixedWrithe
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : IsMixed D c <;> simp [h]




end DirectGLSSW.HOMFLY
