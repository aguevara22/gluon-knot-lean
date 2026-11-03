import LowestRowContract.Contract
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
open DirectGLSSW.PermutationOrbits
variable {D : PLLinkDiagram} {C : diagramComponent D} (R : ComponentRestriction D C)

theorem arcEquiv_pow (n : ℕ) (x : Fin R.diagram.nArc) :
    (R.arcEquiv ((R.diagram.continuation ^ n) x)).val =
      (D.continuation ^ n) (R.arcEquiv x).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply, R.continuation_eq, ih]

theorem continuation_sameCycle (x y : Fin R.diagram.nArc) :
    R.diagram.continuation.SameCycle x y := by
  have h : D.continuation.SameCycle (R.arcEquiv x).val (R.arcEquiv y).val :=
    (componentOf_eq_iff _ _ _).mp ((R.arcEquiv x).property.trans (R.arcEquiv y).property.symm)
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hxy : (R.diagram.continuation ^ n) x = y :=
    R.arcEquiv.injective (Subtype.ext ((R.arcEquiv_pow n x).trans hn))
  rw [← hxy]
  simpa using (Equiv.Perm.SameCycle.refl R.diagram.continuation x)

theorem diagramComponentCount_eq_one : diagramComponentCount R.diagram = 1 := by
  letI : Nonempty (Fin R.diagram.nArc) := ⟨⟨0, R.nonempty⟩⟩
  apply componentCount_eq_one
  refine ⟨R.diagram.continuation.bijOn (fun _ => Iff.rfl), ?_⟩
  intro x _ y _
  exact R.continuation_sameCycle x y
end DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
