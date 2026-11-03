import DirectGLSSW.HOMFLY.HOMFLYSignedIsoTraversal
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
/-- Signed actual port correspondence permitting a separate local relabelling at each crossing. -/
structure BranchSignedDiagramIso (D E : PLLinkDiagram) where
  arcEquiv : Fin D.nArc ≃ Fin E.nArc
  crossingEquiv : Fin D.nCrossing ≃ Fin E.nCrossing
  branchEquiv : Fin D.nCrossing → Equiv.Perm (Fin 2)
  incoming_map : ∀ c i, arcEquiv (D.incoming c i) = E.incoming (crossingEquiv c) (branchEquiv c i)
  outgoing_map : ∀ c i, arcEquiv (D.outgoing c i) = E.outgoing (crossingEquiv c) (branchEquiv c i)
  continuation_map : ∀ e, arcEquiv (D.continuation e) = E.continuation (arcEquiv e)
  through_map : ∀ c i, branchEquiv c (D.through c i) = E.through (crossingEquiv c) (branchEquiv c i)
  overBranch_map : ∀ c, branchEquiv c (D.overBranch c) = E.overBranch (crossingEquiv c)
  crossingSign_map : ∀ c, crossingSign D c = crossingSign E (crossingEquiv c)
namespace BranchSignedDiagramIso
/-- Every permutation of two branches commutes with the other-branch involution. -/
theorem branch_other (b : Equiv.Perm (Fin 2)) (i : Fin 2) : b (otherBranch i)=otherBranch (b i) := by
  have hn : b 0 ≠ b 1 := b.injective.ne (by decide)
  generalize h0 : b 0 = j0 at *
  generalize h1 : b 1 = j1 at *
  fin_cases i <;> fin_cases j0 <;> fin_cases j1 <;> simp_all [otherBranch_zero,otherBranch_one]

def switch {D E : PLLinkDiagram} (I : BranchSignedDiagramIso D E) (c : Fin D.nCrossing) :
    BranchSignedDiagramIso (switchCrossing D c) (switchCrossing E (I.crossingEquiv c)) where
  arcEquiv := I.arcEquiv
  crossingEquiv := I.crossingEquiv
  branchEquiv := I.branchEquiv
  incoming_map := I.incoming_map
  outgoing_map := I.outgoing_map
  continuation_map := I.continuation_map
  through_map := I.through_map
  overBranch_map := by
    intro d
    by_cases hd : d=c
    · subst d
      simp only [switchCrossing,Function.update_self]
      rw [branch_other,I.overBranch_map]
    · change I.branchEquiv d (Function.update D.overBranch c (otherBranch (D.overBranch c)) d) =
        Function.update E.overBranch (I.crossingEquiv c) (otherBranch (E.overBranch (I.crossingEquiv c))) (I.crossingEquiv d)
      rw [Function.update_of_ne hd,Function.update_of_ne (fun he=>hd (I.crossingEquiv.injective he)),I.overBranch_map]
  crossingSign_map := by
    intro d
    by_cases hd : d=c
    · subst d
      exact (crossingSign_switchCrossing D c).trans ((congrArg Sign.reverse (I.crossingSign_map c)).trans (crossingSign_switchCrossing E (I.crossingEquiv c)).symm)
    · exact (crossingSign_switchCrossing_of_ne D c d hd).trans ((I.crossingSign_map d).trans (crossingSign_switchCrossing_of_ne E (I.crossingEquiv c) (I.crossingEquiv d) (fun he=>hd (I.crossingEquiv.injective he))).symm)
end BranchSignedDiagramIso
end DirectGLSSW.HOMFLY
