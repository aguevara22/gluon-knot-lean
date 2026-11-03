import ContinuousRoundedTangent
import ComponentTurning

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open scoped BigOperators
open DirectGLSSW.PermutationOrbits

/-- Discrete unwrapped turn along the actual continuation orbit, defined in
both directions by literal addition/subtraction of each actual corner turn. -/
noncomputable def orbitTurningPrimitive (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℤ) : ℝ :=
  Int.inductionOn' (C := fun _ => ℝ) k 0 0
    (fun j _ a => a + turn D ((D.continuation ^ j) e))
    (fun j _ a => a - turn D ((D.continuation ^ (j - 1)) e))

theorem orbitTurningPrimitive_zero (D : PLLinkDiagram) (e : Fin D.nArc) :
    orbitTurningPrimitive D e 0 = 0 := by
  unfold orbitTurningPrimitive
  rw [Int.inductionOn'_self]

theorem orbitTurningPrimitive_pred (D : PLLinkDiagram) (e : Fin D.nArc)
    (k : ℤ) (hk : k ≤ 0) :
    orbitTurningPrimitive D e (k - 1) =
      orbitTurningPrimitive D e k - turn D ((D.continuation ^ (k - 1)) e) := by
  unfold orbitTurningPrimitive
  rw [Int.inductionOn'_sub_one hk]

theorem orbitTurningPrimitive_succ (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℤ) :
    orbitTurningPrimitive D e (k + 1) =
      orbitTurningPrimitive D e k + turn D ((D.continuation ^ k) e) := by
  by_cases hk : 0 ≤ k
  · unfold orbitTurningPrimitive
    rw [Int.inductionOn'_add_one hk]
  · have h := orbitTurningPrimitive_pred D e (k + 1) (by omega)
    simp only [add_sub_cancel_right] at h
    linarith

theorem orbitTurningPrimitive_nat (D : PLLinkDiagram) (e : Fin D.nArc) (n : ℕ) :
    orbitTurningPrimitive D e n =
      ∑ j ∈ Finset.range n, turn D ((D.continuation ^ j) e) := by
  induction n with
  | zero => simp [orbitTurningPrimitive_zero]
  | succ n ih =>
    rw [Nat.cast_succ, orbitTurningPrimitive_succ, ih, Finset.sum_range_succ]
    simp only [zpow_natCast]

theorem orbitTurningPrimitive_component_period (D : PLLinkDiagram) (e : Fin D.nArc) :
    orbitTurningPrimitive D e (componentArcLength D e) =
      componentTotalTurn D (componentOf D.continuation e) := by
  rw [orbitTurningPrimitive_nat]
  unfold componentTotalTurn componentArcLength
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (orbitEnumeration D.continuation e) _ _
    (fun i => by simp only [orbitEnumeration_apply_val])

end DirectGLSSW.HOMFLY.PrincipalTurning



