import OriginalCarrierTransitivity
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open Filter Topology

theorem polynomial_nonzero_punctured (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → p.eval t ≠ 0 := by
  let bad : Finset ℝ := p.roots.toFinset.erase 0
  have hn : (↑bad : Set ℝ)ᶜ ∈ 𝓝 (0:ℝ) := by
    apply bad.finite_toSet.isClosed.isOpen_compl.mem_nhds
    simp [bad]
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,?_⟩
  intro t ht htd hz
  have hm : t ∈ bad := by
    simp only [bad,Finset.mem_erase,Multiset.mem_toFinset]
    exact ⟨ne_of_gt ht,(Polynomial.mem_roots hp).2 hz⟩
  have hb : t ∈ Metric.ball (0:ℝ) δ := by
    simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos ht] using htd
  exact (hball hb) hm

theorem exists_affine_univariate {σ : Type*} (P : MvPolynomial σ ℝ)
    (a b : σ → ℝ) : ∃ p : Polynomial ℝ, ∀ t : ℝ,
      p.eval t = MvPolynomial.eval (fun i => a i+t*b i) P := by
  refine ⟨MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i)+Polynomial.X*Polynomial.C (b i)) P,?_⟩
  intro t
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp only [MvPolynomial.eval₂_add,Polynomial.eval_add,MvPolynomial.eval_add,hP,hQ]
  | mul_X P i hP => simp only [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,MvPolynomial.eval_mul,MvPolynomial.eval_X,hP]

theorem affine_inventory_punctured {σ : Type*} (P : MvPolynomial σ ℝ)
    (a b : σ → ℝ) (t₀ : ℝ)
    (hw : MvPolynomial.eval (fun i => a i+t₀*b i) P ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      MvPolynomial.eval (fun i => a i+t*b i) P ≠ 0 := by
  obtain ⟨p,he⟩ := exists_affine_univariate P a b
  have hp : p ≠ 0 := by
    intro hz
    apply hw
    rw [← he t₀,hz,Polynomial.eval_zero]
  obtain ⟨δ,hδ,hpδ⟩ := polynomial_nonzero_punctured p hp
  exact ⟨δ,hδ,fun t ht htd => by rw [← he t]; exact hpδ t ht htd⟩

end DirectGLSSW.CyclicCarrierClearing



