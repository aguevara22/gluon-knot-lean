import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial
import CarrierDensity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceAuxiliaryCoefficient
open MvPolynomial Set Filter Topology

/-- A nonzero coefficient of an iterated polynomial remains nonzero after any
base specialization outside that coefficient's zero set. -/
theorem exists_base_coefficient {α β : Type*}
    (P : MvPolynomial β (MvPolynomial α ℝ)) (hP : P ≠ 0) :
    ∃ d : β →₀ ℕ, ∃ c : MvPolynomial α ℝ,
      c ≠ 0 ∧ c = MvPolynomial.coeff d P ∧
      ∀ x : α → ℝ, MvPolynomial.eval x c ≠ 0 →
        MvPolynomial.map (MvPolynomial.eval x) P ≠ 0 := by
  obtain ⟨d,hd⟩ := MvPolynomial.exists_coeff_ne_zero hP
  refine ⟨d,MvPolynomial.coeff d P,hd,rfl,?_⟩
  intro x hc hzero
  have hz := congrArg (MvPolynomial.coeff d) hzero
  apply hc
  simpa [MvPolynomial.coeff_map] using hz

/-- A nonzero real multivariate polynomial has a dense open nonzero locus.
The proof uses a polynomial along each affine line to one nonzero witness. -/
theorem mvpoly_nonzero_dense_open {β : Type*}
    (P : MvPolynomial β ℝ) (hP : P ≠ 0) :
    Dense {x : β → ℝ | MvPolynomial.eval x P ≠ 0} ∧
      IsOpen {x : β → ℝ | MvPolynomial.eval x P ≠ 0} := by
  have hopen : IsOpen {x : β → ℝ | MvPolynomial.eval x P ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval P) continuous_const
  refine ⟨?_,hopen⟩
  rw [dense_iff_inter_open]
  intro U hU hUn
  obtain ⟨x,hx⟩ := hUn
  have hy : ∃ y : β → ℝ, MvPolynomial.eval y P ≠ 0 := by
    by_contra hn
    apply hP
    apply MvPolynomial.funext
    intro y
    have hz : MvPolynomial.eval y P = 0 := by
      by_contra h
      exact hn ⟨y,h⟩
    simpa using hz
  obtain ⟨y,hy⟩ := hy
  let path : ℝ → β → ℝ := fun t i => x i + t * (y i - x i)
  let p : Polynomial ℝ := MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i - x i)) P
  have hp_eval (t : ℝ) : p.eval t = MvPolynomial.eval (path t) P := by
    dsimp [p]
    rw [MvPolynomial.polynomial_eval_eval₂]
    have hcomp : ((Polynomial.evalRingHom t).comp Polynomial.C) = RingHom.id ℝ := by
      ext r
      simp
    rw [hcomp, MvPolynomial.eval₂_id]
    have hf : (fun i => Polynomial.eval t
        (Polynomial.C (x i) + Polynomial.X * Polynomial.C (y i - x i))) = path t := by
      funext i
      simp [path]
    rw [hf]
  have hp : p ≠ 0 := by
    intro h
    have h1 := hp_eval 1
    simp [h] at h1
    have hpath : path 1 = y := by funext i; simp [path]
    rw [hpath] at h1
    exact hy h1.symm
  have hpath : Continuous path := by
    apply continuous_pi
    intro i
    dsimp [path]
    fun_prop
  have hpre : IsOpen (path ⁻¹' U) := hU.preimage hpath
  have hprene : (path ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [path] using hx
  obtain ⟨t,htU,htp⟩ :=
    (CarrierDensity.polynomial_nonzero_dense hp).inter_open_nonempty
      (path ⁻¹' U) hpre hprene
  refine ⟨path t,htU,?_⟩
  change MvPolynomial.eval (path t) P ≠ 0
  rw [← hp_eval t]
  exact htp

/-- Reorder literal base-plus-auxiliary coordinates and select one actual
auxiliary coefficient. Outside its base hypersurface, the auxiliary fiber has
a dense open nonzero locus. -/
theorem exists_base_coefficient_for_sum {α β : Type*}
    (P : MvPolynomial (α ⊕ β) ℝ) (hP : P ≠ 0) :
    ∃ c : MvPolynomial α ℝ, c ≠ 0 ∧
      ∀ x : α → ℝ, MvPolynomial.eval x c ≠ 0 →
        let fiber : MvPolynomial β ℝ := MvPolynomial.map (MvPolynomial.eval x)
          ((MvPolynomial.sumRingEquiv ℝ β α)
            ((MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)) P))
        fiber ≠ 0 ∧
          Dense {y : β → ℝ | MvPolynomial.eval y fiber ≠ 0} ∧
          IsOpen {y : β → ℝ | MvPolynomial.eval y fiber ≠ 0} := by
  let Q : MvPolynomial β (MvPolynomial α ℝ) :=
    (MvPolynomial.sumRingEquiv ℝ β α)
      ((MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)) P)
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hP
    apply (MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)).injective
    apply (MvPolynomial.sumRingEquiv ℝ β α).injective
    simpa [Q] using hzero
  obtain ⟨d,c,hc,hcd,hfiber⟩ := exists_base_coefficient Q hQ
  refine ⟨c,hc,?_⟩
  intro x hcx
  have hnonzero := hfiber x hcx
  have hdense := mvpoly_nonzero_dense_open (MvPolynomial.map (MvPolynomial.eval x) Q) hnonzero
  simpa only [Q] using ⟨hnonzero, hdense.1, hdense.2⟩

/-- Every nonempty open auxiliary window meets a nonzero fiber. -/
theorem exists_aux_in_open_window {α β : Type*}
    (P : MvPolynomial (α ⊕ β) ℝ) (hP : P ≠ 0) :
    ∃ c : MvPolynomial α ℝ, c ≠ 0 ∧
      ∀ x : α → ℝ, MvPolynomial.eval x c ≠ 0 →
        ∀ U : Set (β → ℝ), IsOpen U → U.Nonempty →
          ∃ y ∈ U, MvPolynomial.eval y
            (MvPolynomial.map (MvPolynomial.eval x)
              ((MvPolynomial.sumRingEquiv ℝ β α)
                ((MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)) P))) ≠ 0 := by
  obtain ⟨c,hc,h⟩ := exists_base_coefficient_for_sum P hP
  refine ⟨c,hc,?_⟩
  intro x hcx U hU hUn
  exact (h x hcx).2.1.inter_open_nonempty U hU hUn

/-- One proper base hypersurface controls a finite family of nonzero
base-plus-auxiliary polynomials, with a simultaneous auxiliary witness in
every nonempty open window. -/
theorem exists_base_coefficient_finite_family {ι α β : Type*}
    (s : Finset ι) (P : ι → MvPolynomial (α ⊕ β) ℝ)
    (hP : ∀ i ∈ s, P i ≠ 0) :
    ∃ c : MvPolynomial α ℝ, c ≠ 0 ∧
      ∀ x : α → ℝ, MvPolynomial.eval x c ≠ 0 →
        ∀ U : Set (β → ℝ), IsOpen U → U.Nonempty →
          ∃ y ∈ U, ∀ i ∈ s,
            MvPolynomial.eval y
              (MvPolynomial.map (MvPolynomial.eval x)
                ((MvPolynomial.sumRingEquiv ℝ β α)
                  ((MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)) (P i)))) ≠ 0 := by
  let PP : MvPolynomial (α ⊕ β) ℝ := ∏ i ∈ s, P i
  have hPP : PP ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr hP
  obtain ⟨c,hc,hwindow⟩ := exists_aux_in_open_window PP hPP
  refine ⟨c,hc,?_⟩
  intro x hcx U hU hUn
  obtain ⟨y,hyU,hyPP⟩ := hwindow x hcx U hU hUn
  refine ⟨y,hyU,?_⟩
  have hprod : (∏ i ∈ s, MvPolynomial.eval y
      (MvPolynomial.map (MvPolynomial.eval x)
        ((MvPolynomial.sumRingEquiv ℝ β α)
          ((MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)) (P i))))) ≠ 0 := by
    simpa [PP, map_prod] using hyPP
  exact Finset.prod_ne_zero_iff.mp hprod

/-- The iterated fiber is exactly the original polynomial evaluated at
the original base coordinates and the chosen auxiliary coordinates. -/
theorem eval_fiber_eq_original {α β : Type*}
    (P : MvPolynomial (α ⊕ β) ℝ) (x : α → ℝ) (y : β → ℝ) :
    MvPolynomial.eval y
      (MvPolynomial.map (MvPolynomial.eval x)
        ((MvPolynomial.sumRingEquiv ℝ β α)
          ((MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)) P))) =
      MvPolynomial.eval (Sum.elim x y) P := by
  let L : MvPolynomial (α ⊕ β) ℝ →+* ℝ :=
    (MvPolynomial.eval y).comp
      ((MvPolynomial.map (MvPolynomial.eval x)).comp
        ((MvPolynomial.sumRingEquiv ℝ β α).toRingHom.comp
          (MvPolynomial.renameEquiv ℝ (Equiv.sumComm α β)).toRingHom))
  let R : MvPolynomial (α ⊕ β) ℝ →+* ℝ :=
    MvPolynomial.eval (Sum.elim x y)
  have hLR : L = R := by
    apply MvPolynomial.ringHom_ext'
    · ext a
      simp [L, R, MvPolynomial.sumRingEquiv]
    · intro i
      cases i with
      | inl a => simp [L, R, MvPolynomial.sumRingEquiv]
      | inr b => simp [L, R, MvPolynomial.sumRingEquiv]
  exact DFunLike.congr_fun hLR P

/-- The coefficient exclusion guarantees a literal joint-coordinate point
in every nonempty auxiliary window. -/
theorem exists_aux_original_in_open_window {α β : Type*}
    (P : MvPolynomial (α ⊕ β) ℝ) (hP : P ≠ 0) :
    ∃ c : MvPolynomial α ℝ, c ≠ 0 ∧
      ∀ x : α → ℝ, MvPolynomial.eval x c ≠ 0 →
        ∀ U : Set (β → ℝ), IsOpen U → U.Nonempty →
          ∃ y ∈ U, MvPolynomial.eval (Sum.elim x y) P ≠ 0 := by
  obtain ⟨c,hc,h⟩ := exists_aux_in_open_window P hP
  refine ⟨c,hc,?_⟩
  intro x hcx U hU hUn
  obtain ⟨y,hyU,hy⟩ := h x hcx U hU hUn
  exact ⟨y,hyU,(eval_fiber_eq_original P x y) ▸ hy⟩








end DirectGLSSW.SourceAuxiliaryCoefficient
