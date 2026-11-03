import SourcePLWindingIndex
import UniformPLComponent

set_option autoImplicit false
noncomputable section
open DirectGLSSW

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The literal finite word of source vertices visited by the actual
continuation orbit of one component, based at its selected arc. -/
def actualComponentWord {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    Fin (componentArcLength D (T.baseArc C).val) → ℂ :=
  fun i => Complex.equivRealProd.symm
    (D.vertexPoint (D.arcSource
      ((D.continuation ^ i.val) (T.baseArc C).val)))

theorem actualComponentWord_eq_literal {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D)
    (i : Fin (componentArcLength D (T.baseArc C).val)) :
    actualComponentWord T C i = Complex.equivRealProd.symm
      (D.vertexPoint (D.arcSource
        ((D.continuation ^ i.val) (T.baseArc C).val))) := rfl

theorem actualComponentWord_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    actualComponentWord T C ⟨0, componentArcLength_pos D (T.baseArc C).val⟩ =
      Complex.equivRealProd.symm
        (D.vertexPoint (D.arcSource (T.baseArc C).val)) := by
  simp [actualComponentWord]

theorem actualComponentWord_successor {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D)
    (i : Fin (componentArcLength D (T.baseArc C).val)) :
    actualComponentWord T C
      (cyclicSuccessorPerm (componentArcLength D (T.baseArc C).val) i) =
      Complex.equivRealProd.symm
        (D.vertexPoint (D.arcTarget
          ((D.continuation ^ i.val) (T.baseArc C).val))) := by
  let e := (T.baseArc C).val
  let m := componentArcLength D e
  have hm : 0 < m := componentArcLength_pos D e
  have hinc (a : Fin D.nArc) : D.arcSource (D.continuation a) = D.arcTarget a :=
    (D.continuation_incidence a).symm
  by_cases hi : i.val + 1 < m
  · have hs : (cyclicSuccessorPerm m i).val = i.val + 1 := by
      simp only [cyclicSuccessorPerm_apply, cyclicSuccessor, cyclicVertexIndex]
      exact Nat.mod_eq_of_lt hi
    change Complex.equivRealProd.symm
      (D.vertexPoint (D.arcSource ((D.continuation ^ (cyclicSuccessorPerm m i).val) e))) =
      Complex.equivRealProd.symm
        (D.vertexPoint (D.arcTarget ((D.continuation ^ i.val) e)))
    rw [hs]
    rw [pow_succ', Equiv.Perm.mul_apply, hinc]
  · have hs : (cyclicSuccessorPerm m i).val = 0 := by
      have heq : i.val + 1 = m := by
        have := i.isLt
        dsimp [m, e] at hi ⊢
        omega
      simp only [cyclicSuccessorPerm_apply, cyclicSuccessor, cyclicVertexIndex]
      rw [heq, Nat.mod_self]
    have heq : i.val + 1 = m := by
      have := i.isLt
      dsimp [m, e] at hi ⊢
      omega
    have hcl : (D.continuation ^ (i.val + 1)) e = e := by
      rw [heq]
      exact continuation_pow_componentArcLength D e
    rw [pow_succ', Equiv.Perm.mul_apply] at hcl
    have hv : D.vertexPoint (D.arcSource e) =
        D.vertexPoint (D.arcTarget ((D.continuation ^ i.val) e)) := by
      calc
        D.vertexPoint (D.arcSource e) =
            D.vertexPoint (D.arcSource (D.continuation ((D.continuation ^ i.val) e))) :=
          congrArg (fun a : Fin D.nArc => D.vertexPoint (D.arcSource a)) hcl.symm
        _ = _ := congrArg D.vertexPoint (hinc _)
    change Complex.equivRealProd.symm
      (D.vertexPoint (D.arcSource ((D.continuation ^ (cyclicSuccessorPerm m i).val) e))) =
      Complex.equivRealProd.symm
        (D.vertexPoint (D.arcTarget ((D.continuation ^ i.val) e)))
    rw [hs, pow_zero, Equiv.Perm.one_apply]
    exact congrArg Complex.equivRealProd.symm hv

/-- Every literal cyclic edge of the finite word is the corresponding
unrounded affine cell of the actual continuation parametrization. -/
theorem actualComponentWord_edge_cell {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D)
    (i : Fin (componentArcLength D (T.baseArc C).val))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Complex.equivRealProd.symm
      (PrincipalTurning.uniformPLCurve D (T.baseArc C).val ((i.val : ℝ) + t)) =
      actualComponentWord T C i + (t : ℂ) *
        (actualComponentWord T C
          (cyclicSuccessorPerm (componentArcLength D (T.baseArc C).val) i) -
          actualComponentWord T C i) := by
  have hc := PrincipalTurning.uniformPLCurve_arc_cell D (T.baseArc C).val
    (i.val : ℤ) t ht
  have htime : ((i.val : ℤ) : ℝ) + t = (i.val : ℝ) + t := by norm_cast
  rw [htime] at hc
  rw [hc, actualComponentWord_successor]
  simp only [actualComponentWord]
  apply Complex.ext
  · simp [Complex.equivRealProd_symm_apply, affinePoint]
  · simp [Complex.equivRealProd_symm_apply, affinePoint]

/-- The selected basepoint shift identifies the same actual affine cell in
the based parametrization, without inserting a new vertex. -/
theorem actualComponentWord_based_edge_cell {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D)
    (i : Fin (componentArcLength D (T.baseArc C).val))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Complex.equivRealProd.symm
      (PrincipalTurning.basedUniformPLCurve T C ((i.val : ℝ) + t - 1/2)) =
      actualComponentWord T C i + (t : ℂ) *
        (actualComponentWord T C
          (cyclicSuccessorPerm (componentArcLength D (T.baseArc C).val) i) -
          actualComponentWord T C i) := by
  have htime : ((i.val : ℝ) + t - 1/2) + 1/2 = (i.val : ℝ) + t := by ring
  simpa only [PrincipalTurning.basedUniformPLCurve, htime] using
    actualComponentWord_edge_cell T C i t ht

/-- Distinct labels in the literal component word name distinct diagram
arcs, even if their plane vertices coincide at crossings. -/
theorem actualComponentWord_arc_injective {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    Function.Injective (fun i : Fin (componentArcLength D (T.baseArc C).val) =>
      (D.continuation ^ i.val) (T.baseArc C).val) := by
  intro i j hij
  apply (PermutationOrbits.orbitEnumeration D.continuation (T.baseArc C).val).injective
  apply Subtype.ext
  simpa only [PermutationOrbits.orbitEnumeration_apply_val] using hij

end DirectGLSSW.HOMFLY.PLWinding




