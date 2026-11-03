import DirectGLSSW.DaughterTurns
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
namespace DirectGLSSW.SharpDaughterTurning
open DaughterFirstReturn
open scoped BigOperators
noncomputable section
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)

abbrev CornerIndex := Fin (Fintype.card (CornerCoord q hq.g2 S root))

def sideComplex (i : CornerIndex q hq S root) : ℂ :=
  ⟨(daughterSideVector q hq.g2 S root i).1,
   (daughterSideVector q hq.g2 S root i).2⟩

def cornerTurn (_hroot : retainedCorner q S root)
    (i : CornerIndex q hq S root) : ℝ :=
  Complex.arg (sideComplex q hq S root i /
    sideComplex q hq S root
      ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹ i))

def cornerTotalTurn (hroot : retainedCorner q S root) : ℝ :=
  ∑ i : CornerIndex q hq S root, cornerTurn q hq S root hroot i

theorem sideComplex_ne_zero (hroot : retainedCorner q S root)
    (i : CornerIndex q hq S root) : sideComplex q hq S root i ≠ 0 := by
  intro hz
  apply daughterSide_ne_zero q hq.g2 S hq.size_ge_three hq.g1 root hroot i
  apply Prod.ext
  · exact congrArg Complex.re hz
  · exact congrArg Complex.im hz

theorem cornerTurn_mem_open_semicircle (hroot : retainedCorner q S root)
    (i : CornerIndex q hq S root) :
    -Real.pi < cornerTurn q hq S root hroot i ∧
      cornerTurn q hq S root hroot i < Real.pi := by
  let prev := ((cyclicSuccessorPerm
    (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹ i)
  have hdet := DaughterTurns.daughterTurn_ne_zero q hq.g2 S
    hq.size_ge_three hq.g1 root hroot i
  have him : (sideComplex q hq S root i / sideComplex q hq S root prev).im ≠ 0 := by
    rw [Complex.div_im, ← sub_div]
    apply div_ne_zero
    · change
        ((daughterSideVector q hq.g2 S root i).2 *
          (daughterSideVector q hq.g2 S root prev).1 -
        (daughterSideVector q hq.g2 S root i).1 *
          (daughterSideVector q hq.g2 S root prev).2) ≠ 0
      change
        ((daughterSideVector q hq.g2 S root prev).1 *
          (daughterSideVector q hq.g2 S root i).2 -
        (daughterSideVector q hq.g2 S root prev).2 *
          (daughterSideVector q hq.g2 S root i).1) ≠ 0 at hdet
      rw [mul_comm (daughterSideVector q hq.g2 S root i).2
          (daughterSideVector q hq.g2 S root prev).1,
        mul_comm (daughterSideVector q hq.g2 S root i).1
          (daughterSideVector q hq.g2 S root prev).2]
      exact hdet
    · exact mt Complex.normSq_eq_zero.mp (sideComplex_ne_zero q hq S root hroot prev)
  have hpi : Complex.arg (sideComplex q hq S root i /
      sideComplex q hq S root prev) ≠ Real.pi := by
    intro hp
    exact him (Complex.arg_eq_pi_iff.mp hp).2
  exact ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _) hpi⟩

theorem cornerTotalTurn_coe_angle_zero (hroot : retainedCorner q S root) :
    (cornerTotalTurn q hq S root hroot : Real.Angle) = 0 := by
  change Real.Angle.coeHom (∑ i : CornerIndex q hq S root,
    cornerTurn q hq S root hroot i) = 0
  rw [map_sum]
  simp only [Real.Angle.coe_coeHom, cornerTurn,
    Complex.arg_div_coe_angle (sideComplex_ne_zero q hq S root hroot _)
      (sideComplex_ne_zero q hq S root hroot _)]
  rw [Finset.sum_sub_distrib]
  have hsum :
      (∑ i : CornerIndex q hq S root,
        ((sideComplex q hq S root
          ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹ i)).arg : Real.Angle)) =
      ∑ i : CornerIndex q hq S root, ((sideComplex q hq S root i).arg : Real.Angle) :=
    Fintype.sum_equiv ((cyclicSuccessorPerm
      (Fintype.card (CornerCoord q hq.g2 S root)))⁻¹) _ _ (fun _ => rfl)
  rw [hsum, sub_self]

theorem existsUnique_cornerTurnInteger (hroot : retainedCorner q S root) :
    ∃! r : ℤ, cornerTotalTurn q hq S root hroot = (r : ℝ) * (2 * Real.pi) := by
  obtain ⟨r, hr⟩ := Real.Angle.coe_eq_zero_iff.mp
    (cornerTotalTurn_coe_angle_zero q hq S root hroot)
  refine ⟨r, ?_, ?_⟩
  · simpa only [zsmul_eq_mul] using hr.symm
  · intro s hs
    have hr' : cornerTotalTurn q hq S root hroot = (r : ℝ) * (2 * Real.pi) := by
      simpa only [zsmul_eq_mul] using hr.symm
    have hcast : (s : ℝ) = (r : ℝ) :=
      mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
        (hs.symm.trans hr')
    exact_mod_cast hcast
end
end DirectGLSSW.SharpDaughterTurning


