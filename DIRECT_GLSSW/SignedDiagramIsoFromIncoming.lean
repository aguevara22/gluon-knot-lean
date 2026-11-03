import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SignedDiagramIso

/-- Outgoing ports are determined by incoming ports, continuation and the through pairing. -/
theorem outgoing_map_of_incoming {D E : PLLinkDiagram}
    (f : Fin D.nArc → Fin E.nArc) (g : Fin D.nCrossing → Fin E.nCrossing)
    (hin : ∀ c i, f (D.incoming c i) = E.incoming (g c) i)
    (hcont : ∀ e, f (D.continuation e) = E.continuation (f e))
    (hthrough : ∀ c, D.through c = E.through (g c))
    (c : Fin D.nCrossing) (i : Fin 2) :
    f (D.outgoing c i) = E.outgoing (g c) i := by
  have hd : D.continuation (D.incoming c ((D.through c).symm i)) =
      D.outgoing c i := by
    rw [D.continuation_crossing, Equiv.apply_symm_apply]
  rw [← hd, hcont, hin, E.continuation_crossing, ← hthrough,
    Equiv.apply_symm_apply]

/-- Assemble the existing signed isomorphism once arc conjugacy and crossing
fields have been constructed. Outgoing correspondence is derived, not supplied. -/
def ofIncoming {D E : PLLinkDiagram}
    (f : Fin D.nArc ≃ Fin E.nArc) (g : Fin D.nCrossing ≃ Fin E.nCrossing)
    (hin : ∀ c i, f (D.incoming c i) = E.incoming (g c) i)
    (hcont : ∀ e, f (D.continuation e) = E.continuation (f e))
    (hthrough : ∀ c, D.through c = E.through (g c))
    (hover : ∀ c, D.overBranch c = E.overBranch (g c))
    (hsign : ∀ c, crossingSign D c = crossingSign E (g c)) :
    SignedDiagramIso D E where
  arcEquiv := f
  crossingEquiv := g
  incoming_map := hin
  outgoing_map := outgoing_map_of_incoming f g hin hcont hthrough
  continuation_map := hcont
  through_map := hthrough
  overBranch_map := hover
  crossingSign_map := hsign

end DirectGLSSW.HOMFLY.SignedDiagramIso
