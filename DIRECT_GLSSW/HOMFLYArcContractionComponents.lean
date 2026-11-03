import HOMFLYArcContraction
import DirectGLSSW.PermutationInsertionWords
import DirectGLSSW.OrbitNormalization
import DirectGLSSW.HOMFLY.BasedTraversal

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SignedArcContraction
variable {D E : PLLinkDiagram} (R : SignedArcContraction D E)

theorem map_deleted : R.arcMap R.deleted = R.arcMap R.retained :=
  (R.arcMap_fibers _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem map_injective_surviving : Function.Injective
    (fun e : {e : Fin D.nArc // e ≠ R.deleted} => R.arcMap e.val) := by
  intro e f h
  apply Subtype.ext
  rcases (R.arcMap_fibers _ _).mp h with h | h | h
  · exact h
  · exact False.elim (e.property h.1)
  · exact False.elim (f.property h.2)

/-- The actual quotient map is bijective after removing just the deleted label. -/
def survivingArcEquiv : {e : Fin D.nArc // e ≠ R.deleted} ≃ Fin E.nArc :=
  Equiv.ofBijective (fun e => R.arcMap e.val) ⟨R.map_injective_surviving, by
    intro y
    obtain ⟨e, he⟩ := R.arcMap_surjective y
    by_cases hd : e = R.deleted
    · subst e
      exact ⟨⟨R.retained, R.distinct.symm⟩, R.map_deleted.symm.trans he⟩
    · exact ⟨⟨e, hd⟩, he⟩⟩

theorem survivingArcEquiv_apply (e : {e : Fin D.nArc // e ≠ R.deleted}) :
    R.survivingArcEquiv e = R.arcMap e.val := rfl

theorem lift_map (e : Fin E.nArc) :
    R.arcMap (R.survivingArcEquiv.symm e).val = e :=
  R.survivingArcEquiv.apply_symm_apply e

theorem lift_retained :
    (R.survivingArcEquiv.symm (R.arcMap R.retained)).val = R.retained := by
  have h : R.survivingArcEquiv.symm (R.arcMap R.retained) =
      (⟨R.retained, R.distinct.symm⟩ : {e : Fin D.nArc // e ≠ R.deleted}) :=
    R.survivingArcEquiv.symm_apply_apply ⟨R.retained, R.distinct.symm⟩
  exact congrArg Subtype.val h

theorem insert_extra : D.continuation R.deleted =
    (R.survivingArcEquiv.symm (R.arcMap R.retained)).val :=
  R.successor.trans R.lift_retained.symm

theorem insert_step (e : Fin E.nArc) :
    D.continuation (R.survivingArcEquiv.symm e).val =
      if E.continuation e = R.arcMap R.retained then R.deleted
      else (R.survivingArcEquiv.symm (E.continuation e)).val := by
  have hn : D.continuation (R.survivingArcEquiv.symm e).val ≠ R.retained := by
    intro h
    exact (R.survivingArcEquiv.symm e).property
      (D.continuation.injective (h.trans R.successor.symm))
  have hm := R.continuation_map _ (R.survivingArcEquiv.symm e).property
  rw [R.lift_map] at hm
  by_cases h : E.continuation e = R.arcMap R.retained
  · rw [if_pos h]
    rcases (R.arcMap_fibers _ _).mp (hm.trans h) with he | he | he
    · exact False.elim (hn he)
    · exact he.1
    · exact False.elim (hn he.1)
  · rw [if_neg h]
    have hd : D.continuation (R.survivingArcEquiv.symm e).val ≠ R.deleted := by
      intro hd
      apply h
      exact hm.symm.trans ((congrArg R.arcMap hd).trans R.map_deleted)
    have he : (⟨D.continuation (R.survivingArcEquiv.symm e).val, hd⟩ :
        {e : Fin D.nArc // e ≠ R.deleted}) = R.survivingArcEquiv.symm (E.continuation e) :=
      R.map_injective_surviving (hm.trans (R.lift_map (E.continuation e)).symm)
    exact congrArg Subtype.val he

def insertedComponentEquiv : diagramComponent E ≃ diagramComponent D :=
  PermutationInsertion.insertedComponentEquiv E.continuation D.continuation
    (R.arcMap R.retained) R.deleted R.survivingArcEquiv.symm R.insert_extra
    (fun e => by
      have h := R.insert_step e
      by_cases he : E.continuation e = R.arcMap R.retained <;> simpa [he] using h)

def componentEquiv : diagramComponent D ≃ diagramComponent E :=
  R.insertedComponentEquiv.symm

theorem componentEquiv_map (e : Fin D.nArc) :
    R.componentEquiv (componentOf D.continuation e) =
      componentOf E.continuation (R.arcMap e) := by
  apply (Equiv.symm_apply_eq R.insertedComponentEquiv).mpr
  symm
  by_cases hd : e = R.deleted
  · subst e
    rw [R.map_deleted]
    exact PermutationInsertion.insertedComponentEquiv_extra _ _ _ _ _ _ _
  · have hl : (R.survivingArcEquiv.symm (R.arcMap e)).val = e := by
      have h := R.survivingArcEquiv.symm_apply_apply ⟨e, hd⟩
      exact congrArg Subtype.val h
    change componentOf D.continuation (R.survivingArcEquiv.symm (R.arcMap e)).val = _
    rw [hl]

include R in
theorem componentCount_eq : diagramComponentCount D = diagramComponentCount E := by
  letI : Fintype (diagramComponent D) := componentFintype D.continuation
  letI : Fintype (diagramComponent E) := componentFintype E.continuation
  exact Fintype.card_congr R.componentEquiv

/-- Retains the original component order and the quotient of each original root. -/
def transportTraversal (T : BasedTraversal D) : BasedTraversal E where
  componentIndex := (R.componentEquiv.symm.trans T.componentIndex).trans
    (finCongr R.componentCount_eq)
  baseArc C := ⟨R.arcMap (T.baseArc (R.componentEquiv.symm C)).val, by
    rw [← R.componentEquiv_map, (T.baseArc _).property, Equiv.apply_symm_apply]⟩

theorem transportTraversal_componentIndex (T : BasedTraversal D) (C : diagramComponent D) :
    ((R.transportTraversal T).componentIndex (R.componentEquiv C)).val =
      (T.componentIndex C).val := by
  simp only [transportTraversal, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem transportTraversal_baseArc (T : BasedTraversal D) (C : diagramComponent D) :
    ((R.transportTraversal T).baseArc (R.componentEquiv C)).val = R.arcMap (T.baseArc C).val := by
  change R.arcMap (T.baseArc (R.componentEquiv.symm (R.componentEquiv C))).val = _
  rw [Equiv.symm_apply_apply]

end SignedArcContraction
end
end DirectGLSSW.HOMFLY







