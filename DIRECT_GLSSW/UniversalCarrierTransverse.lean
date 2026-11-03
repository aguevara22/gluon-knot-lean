import UniversalCarrierLocus
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart CarrierNumeratorPath CarrierDensity Set

def PairTransverse {α : Type*} (L : α → CarrierLine) : Prop :=
  ∀ a b : α, a≠b → lineDenominator (L a) (L b)≠0

theorem pair_denominator_dense {α : Type*} [DecidableEq α]
    (a b : α) (hab : a≠b) :
    Dense {L : α → CarrierLine | lineDenominator (L a) (L b)≠0} := by
  classical
  let M : α → CarrierLine := fun x => if x=a then ((1,0),0) else ((0,1),0)
  have hM : lineDenominator (M a) (M b)≠0 := by
    simp [M,hab,Ne.symm hab,lineDenominator,planarDet]
  rw [dense_iff_inter_open]
  intro U hU hUn
  obtain ⟨L,hL⟩ := hUn
  let path : ℝ → (α → CarrierLine) := fun t x => carrierPath (L x) (M x) t
  have hpath : Continuous path := continuous_pi (fun x => continuous_carrierPath (L x) (M x))
  let p := polynomialDenominator (carrierPolynomial (L a) (M a)) (carrierPolynomial (L b) (M b))
  have he (t : ℝ) : p.eval t=lineDenominator (path t a) (path t b) := by
    simp [p,path,polynomialDenominator,carrierPolynomial,scalarPolynomial,
      carrierPath,scalarPath,lineDenominator,planarDet]
  have he1 : p.eval 1=lineDenominator (M a) (M b) := by
    rw [he]
    simp [path,carrierPath,scalarPath]
  have hp : p≠0 := by
    intro hz
    apply hM
    rw [←he1,hz,Polynomial.eval_zero]
  have hpre : IsOpen (path ⁻¹' U) := hU.preimage hpath
  have hprene : (path ⁻¹' U).Nonempty := by
    refine ⟨0,?_⟩
    simpa [path,carrierPath,scalarPath] using hL
  obtain ⟨t,htU,htp⟩ := (polynomial_nonzero_dense hp).inter_open_nonempty
    (path ⁻¹' U) hpre hprene
  refine ⟨path t,htU,?_⟩
  change p.eval t≠0 at htp
  change lineDenominator (path t a) (path t b)≠0
  rw [←he]
  exact htp

theorem pair_denominator_isOpen {α : Type*} (a b : α) :
    IsOpen {L : α → CarrierLine | lineDenominator (L a) (L b)≠0} := by
  apply isOpen_ne_fun _ continuous_const
  unfold lineDenominator planarDet
  fun_prop

theorem pairTransverse_dense_open {α : Type*} [Fintype α] [DecidableEq α] :
    Dense {L : α → CarrierLine | PairTransverse L} ∧
      IsOpen {L : α → CarrierLine | PairTransverse L} := by
  classical
  let I := {x : α×α // x.1≠x.2}
  let A := fun x : I => {L : α → CarrierLine | lineDenominator (L x.val.1) (L x.val.2)≠0}
  have hD : ∀ x : I, Dense (A x) := fun x => pair_denominator_dense _ _ x.property
  have hO : ∀ x : I, IsOpen (A x) := fun _ => pair_denominator_isOpen _ _
  have hAll := CarrierFamilyDensity.finite_family_dense_open A hD hO
  have heq : (⋂ x,A x)={L : α → CarrierLine | PairTransverse L} := by
    ext L
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    constructor
    · intro h a b hab
      exact h ⟨(a,b),hab⟩
    · intro h x
      exact h _ _ x.property
  simpa only [heq] using hAll

theorem universal_transverse_dense_open {α : Type*} [Fintype α] [DecidableEq α] :
    Dense {L : α → CarrierLine | UniversalLocus L ∧ PairTransverse L} ∧
      IsOpen {L : α → CarrierLine | UniversalLocus L ∧ PairTransverse L} := by
  have hu := universalLocus_dense_open (α:=α)
  have ht := pairTransverse_dense_open (α:=α)
  exact ⟨hu.1.inter_of_isOpen_left ht.1 hu.2,hu.2.inter ht.2⟩

theorem pairTransverse_comap {α β : Type*} (L : β → CarrierLine)
    (hL : PairTransverse L) (f : α → β) (hf : Function.Injective f) :
    PairTransverse (L ∘ f) := by
  intro a b hab
  exact hL _ _ (fun h => hab (hf h))
end DirectGLSSW.UniversalCarrierDomain


