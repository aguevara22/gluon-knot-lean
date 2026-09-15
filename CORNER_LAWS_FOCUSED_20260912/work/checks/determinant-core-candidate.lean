import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Next-chain prototype only, outside the audited project inventory.
This proves the actual four-variable determinant; it does not yet identify
the geometric Δ/T coordinate polynomials or accept the original source lemma. -/

namespace SM.TransportPolynomialCandidate

noncomputable def determinantCore : MvPolynomial (Bool ⊕ Bool) ℝ :=
  MvPolynomial.X (.inl false) * MvPolynomial.X (.inr false) -
    MvPolynomial.X (.inl true) * MvPolynomial.X (.inr true)

noncomputable def determinantCoefficients : Bool →₀ ℝ :=
  Finsupp.single false 1 + Finsupp.single true (-1)

theorem determinantCore_bilinear :
    determinantCore = MvPolynomial.sumSMulXSMulY determinantCoefficients := by
  rw [determinantCoefficients, map_add]
  simp only [determinantCore, MvPolynomial.sumSMulXSMulY,
    Finsupp.linearCombination_apply, Finsupp.sum_single_index,
    zero_smul, one_smul, neg_one_smul, sub_eq_add_neg]

theorem determinantCore_irreducible : Irreducible determinantCore := by
  rw [determinantCore_bilinear]
  apply MvPolynomial.irreducible_sumSMulXSMulY
  · refine ⟨false, ?_, true, ?_, by decide⟩ <;>
      simp [determinantCoefficients, Finsupp.mem_support_iff]
  · intro r hr
    have h1 : r ∣ (1 : ℝ) := by
      simpa [determinantCoefficients] using hr false
    exact isUnit_of_dvd_one h1

#print axioms determinantCore_irreducible

end SM.TransportPolynomialCandidate
