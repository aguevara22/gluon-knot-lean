import HOMFLYSignedRegularDeletion

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

/-- A one-arc contraction certificate. Only the deleted arc is forbidden at
incoming ports; retained and outgoing ports are unrestricted. -/
structure SignedArcContraction (D E : PLLinkDiagram) where
  deleted : Fin D.nArc
  retained : Fin D.nArc
  distinct : deleted ≠ retained
  successor : D.continuation deleted = retained
  arcMap : Fin D.nArc → Fin E.nArc
  arcMap_surjective : Function.Surjective arcMap
  arcMap_fibers : ∀ e f, arcMap e = arcMap f ↔
    e = f ∨ (e = deleted ∧ f = retained) ∨ (e = retained ∧ f = deleted)
  crossingEquiv : Fin D.nCrossing ≃ Fin E.nCrossing
  deleted_not_incoming : ∀ c i, D.incoming c i ≠ deleted
  incoming_map : ∀ c i, arcMap (D.incoming c i) = E.incoming (crossingEquiv c) i
  outgoing_map : ∀ c i, arcMap (D.outgoing c i) = E.outgoing (crossingEquiv c) i
  continuation_map : ∀ e, e ≠ deleted → arcMap (D.continuation e) = E.continuation (arcMap e)
  through_map : ∀ c, D.through c = E.through (crossingEquiv c)
  overBranch_map : ∀ c, D.overBranch c = E.overBranch (crossingEquiv c)
  crossingSign_map : ∀ c, crossingSign D c = crossingSign E (crossingEquiv c)

def ofSignedRegularDeletion {D E : PLLinkDiagram}
    (R : SignedRegularDeletion D E) : SignedArcContraction D E where
  deleted := R.deleted
  retained := R.retained
  distinct := R.distinct
  successor := R.successor
  arcMap := R.arcMap
  arcMap_surjective := R.arcMap_surjective
  arcMap_fibers := R.arcMap_fibers
  crossingEquiv := R.crossingEquiv
  deleted_not_incoming c i := (R.selected_not_ports c i).1
  incoming_map := R.incoming_map
  outgoing_map := R.outgoing_map
  continuation_map := R.continuation_map
  through_map := R.through_map
  overBranch_map := R.overBranch_map
  crossingSign_map := R.crossingSign_map

namespace SignedArcContraction
variable {D E : PLLinkDiagram} (R : SignedArcContraction D E)

theorem incoming_reflect (c : Fin D.nCrossing) (i : Fin 2)
    (e : Fin D.nArc) (he : e ≠ R.deleted) :
    R.arcMap e = E.incoming (R.crossingEquiv c) i ↔ e = D.incoming c i := by
  rw [← R.incoming_map, R.arcMap_fibers]
  constructor
  · rintro (h | h | h)
    · exact h
    · exact False.elim (he h.1)
    · exact False.elim (R.deleted_not_incoming c i h.2)
  · exact Or.inl

/-- Crossing switch preserves the incoming-only contraction certificate. -/
def switch (c : Fin D.nCrossing) :
    SignedArcContraction (switchCrossing D c) (switchCrossing E (R.crossingEquiv c)) where
  deleted := R.deleted
  retained := R.retained
  distinct := R.distinct
  successor := R.successor
  arcMap := R.arcMap
  arcMap_surjective := R.arcMap_surjective
  arcMap_fibers := R.arcMap_fibers
  crossingEquiv := R.crossingEquiv
  deleted_not_incoming := by
    intro d i
    by_cases hd : d = c
    · subst d
      simpa [switchCrossing] using R.deleted_not_incoming c i
    · simpa [switchCrossing, hd] using R.deleted_not_incoming d i
  incoming_map := by
    intro d i
    by_cases hd : d = c
    · subst d
      simpa [switchCrossing] using R.incoming_map c i
    · simpa [switchCrossing, hd] using R.incoming_map d i
  outgoing_map := by
    intro d i
    by_cases hd : d = c
    · subst d
      simpa [switchCrossing] using R.outgoing_map c i
    · simpa [switchCrossing, hd] using R.outgoing_map d i
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

end SignedArcContraction
end
end DirectGLSSW.HOMFLY




