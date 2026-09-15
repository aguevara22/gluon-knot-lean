import SM.CoordinateAffinity

/-! Actual vertex supports of coordinate polynomials. Nonzero-dividend degree
arguments and changes at one scalar coordinate detect genuine dependence. -/

namespace SM

open MvPolynomial

theorem polynomial_vars_subset_of_dvd {σ : Type*} {p q : MvPolynomial σ ℝ}
    (hq : q ≠ 0) (h : p ∣ q) : p.vars ⊆ q.vars := by
  intro i hi
  by_contra hiq
  have hp : 0 < p.degreeOf i := Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi)
  have hlt : q.degreeOf i < p.degreeOf i := by
    rw [polynomial_degree_zero hiq]
    exact hp
  exact polynomial_not_dvd_of_degree_lt hq hlt h

theorem polynomial_vars_eq_of_associated {σ : Type*} {p q : MvPolynomial σ ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : Associated p q) : p.vars = q.vars :=
  Finset.Subset.antisymm (polynomial_vars_subset_of_dvd hq h.dvd)
    (polynomial_vars_subset_of_dvd hp h.dvd')

theorem polynomial_variable_of_eval_ne {σ : Type*} (p : MvPolynomial σ ℝ)
    (i : σ) (ρ τ : σ → ℝ) (hagree : ∀ j, j ≠ i → ρ j = τ j)
    (hne : eval ρ p ≠ eval τ p) : i ∈ p.vars := by
  by_contra hi
  apply hne
  change eval₂Hom (RingHom.id ℝ) ρ p = eval₂Hom (RingHom.id ℝ) τ p
  refine eval₂Hom_congr' rfl (fun j hj _ => hagree j ?_) rfl
  intro hji
  subst j
  exact hi hj

noncomputable section

variable {n : ℕ}

def polynomialVertexSupport (p : CoordinatePolynomial n) : Finset (ZMod n) :=
  p.vars.image Prod.fst

theorem mem_polynomialVertexSupport_iff (p : CoordinatePolynomial n) (v : ZMod n) :
    v ∈ polynomialVertexSupport p ↔ ∃ c : Fin 2, (v, c) ∈ p.vars := by
  classical
  constructor
  · intro h
    obtain ⟨⟨w, c⟩, hc, he⟩ := Finset.mem_image.mp h
    dsimp at he
    subst w
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact Finset.mem_image.mpr ⟨(v, c), hc, rfl⟩

theorem polynomialVertexSupport_eq_of_associated {p q : CoordinatePolynomial n}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : Associated p q) :
    polynomialVertexSupport p = polynomialVertexSupport q := by
  unfold polynomialVertexSupport
  rw [polynomial_vars_eq_of_associated hp hq h]

end

end SM
