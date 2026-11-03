import CyclicCarrierClearing

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart CarrierNumeratorPath CarrierDensity Set
open scoped BigOperators

def outerCycleNumerator {R : Type*} [CommRing R] {m n : ℕ}
    (L : Fin n → (R × R) × R) (f : Fin m → Fin n) (l : Fin 4 → Fin m) : R :=
  OriginalOuterProperness.outerNumerator (clearedPoints
    (fun i => L (f ((cyclicSuccessorPerm m)⁻¹ (l i)))) (fun i => L (f (l i))))

theorem outerCycleNumerator_eq {m n : ℕ} (L : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 4 → Fin m)
    (hd : ∀ i, lineDenominator (L (f ((cyclicSuccessorPerm m)⁻¹ i))) (L (f i)) ≠ 0) :
    outerCycleNumerator L f l =
      (∏ i, lineDenominator (L (f ((cyclicSuccessorPerm m)⁻¹ (l i)))) (L (f (l i))))^2 *
      OriginalOuterProperness.outerNumerator ((reconstructPolygon (L ∘ f)) ∘ l) := by
  exact outer_cleared _ _ (fun i => hd (l i))

theorem exists_outerCycle_nonzero {m n : ℕ} (q : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (f : Fin m → Fin n) (hf : Function.Injective f)
    (l : Fin 4 → Fin m) (hl : Function.Injective l) :
    ∃ L : Fin n → CarrierLine, outerCycleNumerator L f l ≠ 0 := by
  obtain ⟨L, hd, h4, h6⟩ := exists_cycle_witness q hq f hf
  refine ⟨L, ?_⟩
  rw [outerCycleNumerator_eq L f l hd]
  exact mul_ne_zero (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hd (l i)))) (h4 l hl)

def outerCyclePolynomial {m n : ℕ} (L M : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 4 → Fin m) : Polynomial ℝ :=
  outerCycleNumerator (fun i => carrierPolynomial (L i) (M i)) f l

theorem outerCyclePolynomial_eval {m n : ℕ} (L M : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 4 → Fin m) (t : ℝ) :
    (outerCyclePolynomial L M f l).eval t =
      outerCycleNumerator (fun i => carrierPath (L i) (M i) t) f l := by
  simp [outerCyclePolynomial, outerCycleNumerator, OriginalOuterProperness.outerNumerator,
    clearedPoints, slotNum, slotDen, planarDet, carrierPolynomial, scalarPolynomial,
    carrierPath, scalarPath, Polynomial.eval_prod]

theorem outerCycle_dense_open {m n : ℕ} (q : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (f : Fin m → Fin n) (hf : Function.Injective f)
    (l : Fin 4 → Fin m) (hl : Function.Injective l) :
    Dense {L : Fin n → CarrierLine | outerCycleNumerator L f l ≠ 0} ∧
    IsOpen {L : Fin n → CarrierLine | outerCycleNumerator L f l ≠ 0} := by
  have hcont : Continuous (fun L : Fin n → CarrierLine => outerCycleNumerator L f l) := by
    unfold outerCycleNumerator OriginalOuterProperness.outerNumerator clearedPoints slotNum slotDen planarDet
    fun_prop
  refine ⟨?_, isOpen_ne_fun hcont continuous_const⟩
  obtain ⟨M, hM⟩ := exists_outerCycle_nonzero q hq f hf l hl
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨L, hL⟩ := hUne
  let path : ℝ → (Fin n → CarrierLine) := fun t i => carrierPath (L i) (M i) t
  have hc : Continuous path := by unfold path carrierPath scalarPath; fun_prop
  have hp : outerCyclePolynomial L M f l ≠ 0 := by
    intro hz
    have he := outerCyclePolynomial_eval L M f l 1
    rw [hz, Polynomial.eval_zero] at he
    apply hM
    simpa [carrierPath, scalarPath] using he.symm
  have hpre : IsOpen (path ⁻¹' U) := hU.preimage hc
  have hprene : (path ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [path, carrierPath, scalarPath] using hL
  obtain ⟨t, htU, ht⟩ := (polynomial_nonzero_dense hp).inter_open_nonempty _ hpre hprene
  refine ⟨path t, htU, ?_⟩
  simpa only [outerCyclePolynomial_eval, path] using ht

def secantCycleNumerator {R : Type*} [CommRing R] {m n : ℕ}
    (L : Fin n → (R × R) × R) (f : Fin m → Fin n) (l : Fin 6 → Fin m) : R :=
  OriginalSecantProperness.secantNumerator (clearedPoints
    (fun i => L (f ((cyclicSuccessorPerm m)⁻¹ (l i)))) (fun i => L (f (l i))))

theorem secantCycleNumerator_eq {m n : ℕ} (L : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 6 → Fin m)
    (hd : ∀ i, lineDenominator (L (f ((cyclicSuccessorPerm m)⁻¹ i))) (L (f i)) ≠ 0) :
    secantCycleNumerator L f l =
      (∏ i, lineDenominator (L (f ((cyclicSuccessorPerm m)⁻¹ (l i)))) (L (f (l i))))^4 *
      OriginalSecantProperness.secantNumerator ((reconstructPolygon (L ∘ f)) ∘ l) := by
  exact secant_cleared _ _ (fun i => hd (l i))

theorem exists_secantCycle_nonzero {m n : ℕ} (q : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (f : Fin m → Fin n) (hf : Function.Injective f)
    (l : Fin 6 → Fin m) (hl : Function.Injective l) :
    ∃ L : Fin n → CarrierLine, secantCycleNumerator L f l ≠ 0 := by
  obtain ⟨L, hd, h4, h6⟩ := exists_cycle_witness q hq f hf
  refine ⟨L, ?_⟩
  rw [secantCycleNumerator_eq L f l hd]
  exact mul_ne_zero (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hd (l i)))) (h6 l hl)

def secantCyclePolynomial {m n : ℕ} (L M : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 6 → Fin m) : Polynomial ℝ :=
  secantCycleNumerator (fun i => carrierPolynomial (L i) (M i)) f l

theorem secantCyclePolynomial_eval {m n : ℕ} (L M : Fin n → CarrierLine)
    (f : Fin m → Fin n) (l : Fin 6 → Fin m) (t : ℝ) :
    (secantCyclePolynomial L M f l).eval t =
      secantCycleNumerator (fun i => carrierPath (L i) (M i) t) f l := by
  simp [secantCyclePolynomial, secantCycleNumerator, OriginalSecantProperness.secantNumerator,
    clearedPoints, slotNum, slotDen, planarDet, carrierPolynomial, scalarPolynomial,
    carrierPath, scalarPath, Polynomial.eval_prod]

theorem secantCycle_dense_open {m n : ℕ} (q : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (f : Fin m → Fin n) (hf : Function.Injective f)
    (l : Fin 6 → Fin m) (hl : Function.Injective l) :
    Dense {L : Fin n → CarrierLine | secantCycleNumerator L f l ≠ 0} ∧
    IsOpen {L : Fin n → CarrierLine | secantCycleNumerator L f l ≠ 0} := by
  have hcont : Continuous (fun L : Fin n → CarrierLine => secantCycleNumerator L f l) := by
    unfold secantCycleNumerator OriginalSecantProperness.secantNumerator clearedPoints slotNum slotDen planarDet
    fun_prop
  refine ⟨?_, isOpen_ne_fun hcont continuous_const⟩
  obtain ⟨M, hM⟩ := exists_secantCycle_nonzero q hq f hf l hl
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨L, hL⟩ := hUne
  let path : ℝ → (Fin n → CarrierLine) := fun t i => carrierPath (L i) (M i) t
  have hc : Continuous path := by unfold path carrierPath scalarPath; fun_prop
  have hp : secantCyclePolynomial L M f l ≠ 0 := by
    intro hz
    have he := secantCyclePolynomial_eval L M f l 1
    rw [hz, Polynomial.eval_zero] at he
    apply hM
    simpa [carrierPath, scalarPath] using he.symm
  have hpre : IsOpen (path ⁻¹' U) := hU.preimage hc
  have hprene : (path ⁻¹' U).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [path, carrierPath, scalarPath] using hL
  obtain ⟨t, htU, ht⟩ := (polynomial_nonzero_dense hp).inter_open_nonempty _ hpre hprene
  refine ⟨path t, htU, ?_⟩
  simpa only [secantCyclePolynomial_eval, path] using ht

end DirectGLSSW.CyclicCarrierClearing









