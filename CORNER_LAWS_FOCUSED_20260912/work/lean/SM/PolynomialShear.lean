import Mathlib.Algebra.MvPolynomial.Equiv

/-! An explicit invertible change of polynomial coordinates. Selected variables
are replaced by their difference from an unselected parent variable. The inverse
adds that same parent. All variables, including unused ones, stay in the ring. -/

namespace SM

open MvPolynomial

noncomputable section

variable {σ R : Type*} [CommRing R]

def polynomialShearSub (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if selected i then X i - X (parent i) else X i

def polynomialShearAdd (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if selected i then X i + X (parent i) else X i

@[simp] theorem polynomialShearSub_X (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) (i : σ) :
    polynomialShearSub (R := R) selected parent (X i) =
      if selected i then X i - X (parent i) else X i := aeval_X _ _

@[simp] theorem polynomialShearAdd_X (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) (i : σ) :
    polynomialShearAdd (R := R) selected parent (X i) =
      if selected i then X i + X (parent i) else X i := aeval_X _ _

theorem polynomialShearSub_comp_add (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) (hparent : ∀ i, selected i → ¬ selected (parent i)) :
    (polynomialShearSub (R := R) selected parent).comp
      (polynomialShearAdd selected parent) = AlgHom.id R (MvPolynomial σ R) := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : selected i
  · simp [hi, hparent i hi]
  · simp [hi]

theorem polynomialShearAdd_comp_sub (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) (hparent : ∀ i, selected i → ¬ selected (parent i)) :
    (polynomialShearAdd (R := R) selected parent).comp
      (polynomialShearSub selected parent) = AlgHom.id R (MvPolynomial σ R) := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : selected i
  · simp [hi, hparent i hi]
  · simp [hi]

def polynomialShear (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) (hparent : ∀ i, selected i → ¬ selected (parent i)) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (polynomialShearSub selected parent)
    (polynomialShearAdd selected parent)
    (polynomialShearSub_comp_add selected parent hparent)
    (polynomialShearAdd_comp_sub selected parent hparent)

@[simp] theorem polynomialShear_X (selected : σ → Prop) [DecidablePred selected]
    (parent : σ → σ) (hparent : ∀ i, selected i → ¬ selected (parent i)) (i : σ) :
    polynomialShear (R := R) selected parent hparent (X i) =
      if selected i then X i - X (parent i) else X i := aeval_X _ _

end

end SM
