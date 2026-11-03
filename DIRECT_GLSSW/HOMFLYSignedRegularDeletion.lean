import HOMFLYEmptyTriangleTarget
import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

/-- A one-arc regular deletion in the signed finite data of two actual valid
PL diagrams. No coordinate relation, isotopy or evaluator equality is assumed. -/
structure SignedRegularDeletion (D E : PLLinkDiagram) where
  deleted : Fin D.nArc
  retained : Fin D.nArc
  distinct : deleted ≠ retained
  successor : D.continuation deleted = retained
  arcMap : Fin D.nArc → Fin E.nArc
  arcMap_surjective : Function.Surjective arcMap
  arcMap_fibers : ∀ e f, arcMap e = arcMap f ↔
    e = f ∨ (e = deleted ∧ f = retained) ∨ (e = retained ∧ f = deleted)
  crossingEquiv : Fin D.nCrossing ≃ Fin E.nCrossing
  selected_not_ports : ∀ c i,
    D.incoming c i ≠ deleted ∧ D.incoming c i ≠ retained ∧
    D.outgoing c i ≠ deleted ∧ D.outgoing c i ≠ retained
  incoming_map : ∀ c i, arcMap (D.incoming c i) = E.incoming (crossingEquiv c) i
  outgoing_map : ∀ c i, arcMap (D.outgoing c i) = E.outgoing (crossingEquiv c) i
  continuation_map : ∀ e, e ≠ deleted → arcMap (D.continuation e) = E.continuation (arcMap e)
  through_map : ∀ c, D.through c = E.through (crossingEquiv c)
  overBranch_map : ∀ c, D.overBranch c = E.overBranch (crossingEquiv c)
  crossingSign_map : ∀ c, crossingSign D c = crossingSign E (crossingEquiv c)

namespace EmptyTriangleSite
variable {D : PLLinkDiagram}

def signedRegularDeletion (S : EmptyTriangleSite D) : SignedRegularDeletion D S.contractDiagram where
  deleted := S.left
  retained := S.right
  distinct := S.distinct
  successor := S.consecutive
  arcMap := S.contractArcMap
  arcMap_surjective := S.contractWitness.arcMap_surjective
  arcMap_fibers := S.contractWitness.arcMap_fibers
  crossingEquiv := Equiv.refl _
  selected_not_ports c i := ⟨S.incoming_ne_left c i, S.incoming_ne_right c i,
    S.outgoing_ne_left c i, S.outgoing_ne_right c i⟩
  incoming_map c i := (S.contractWitness.incoming_map c i).symm
  outgoing_map c i := (S.contractWitness.outgoing_map c i).symm
  continuation_map := S.contractWitness.continuation_map
  through_map c := rfl
  overBranch_map c := rfl
  crossingSign_map c := (S.contract_crossingSign c).symm

end EmptyTriangleSite
namespace SignedRegularDeletion
variable {D E : PLLinkDiagram} (R : SignedRegularDeletion D E)

theorem incoming_reflect (c : Fin D.nCrossing) (i : Fin 2) (e : Fin D.nArc) :
    R.arcMap e = E.incoming (R.crossingEquiv c) i ↔ e = D.incoming c i := by
  rw [← R.incoming_map, R.arcMap_fibers]
  constructor
  · rintro (h | ⟨_, h⟩ | ⟨_, h⟩)
    · exact h
    · exact False.elim ((R.selected_not_ports c i).2.1 h)
    · exact False.elim ((R.selected_not_ports c i).1 h)
  · exact Or.inl

theorem outgoing_reflect (c : Fin D.nCrossing) (i : Fin 2) (e : Fin D.nArc) :
    R.arcMap e = E.outgoing (R.crossingEquiv c) i ↔ e = D.outgoing c i := by
  rw [← R.outgoing_map, R.arcMap_fibers]
  constructor
  · rintro (h | ⟨_, h⟩ | ⟨_, h⟩)
    · exact h
    · exact False.elim ((R.selected_not_ports c i).2.2.2 h)
    · exact False.elim ((R.selected_not_ports c i).2.2.1 h)
  · exact Or.inl

/-- Actual crossing switch retains the one-arc deletion relation. -/
def switch (c : Fin D.nCrossing) :
    SignedRegularDeletion (switchCrossing D c) (switchCrossing E (R.crossingEquiv c)) where
  deleted := R.deleted
  retained := R.retained
  distinct := R.distinct
  successor := R.successor
  arcMap := R.arcMap
  arcMap_surjective := R.arcMap_surjective
  arcMap_fibers := R.arcMap_fibers
  crossingEquiv := R.crossingEquiv
  selected_not_ports := R.selected_not_ports
  incoming_map := R.incoming_map
  outgoing_map := R.outgoing_map
  continuation_map := R.continuation_map
  through_map := R.through_map
  overBranch_map := by
    intro d
    by_cases hd : d = c
    · subst d
      simp only [switchCrossing, Function.update_self]
      exact congrArg otherBranch (R.overBranch_map c)
    · simp only [switchCrossing, Function.update_of_ne hd,
        Function.update_of_ne (fun he => hd (R.crossingEquiv.injective he))]
      exact R.overBranch_map d
  crossingSign_map := by
    intro d
    by_cases hd : d = c
    · subst d
      calc
        crossingSign (switchCrossing D c) c = (crossingSign D c).reverse :=
          crossingSign_switchCrossing D c
        _ = (crossingSign E (R.crossingEquiv c)).reverse :=
          congrArg Sign.reverse (R.crossingSign_map c)
        _ = crossingSign (switchCrossing E (R.crossingEquiv c)) (R.crossingEquiv c) :=
          (crossingSign_switchCrossing E (R.crossingEquiv c)).symm
    · rw [crossingSign_switchCrossing_of_ne D c d hd, R.crossingSign_map]
      exact (crossingSign_switchCrossing_of_ne E (R.crossingEquiv c)
        (R.crossingEquiv d) (fun h => hd (R.crossingEquiv.injective h))).symm

end SignedRegularDeletion
end
end DirectGLSSW.HOMFLY





