import CarrierTriplePairProperness
import CarrierFamilyDensity
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart CarrierTriplePairProperness

/-- Pure carrier-label exclusions: three distinct two-element pairs with no
carrier common to all three. No geometric conclusion is part of this predicate. -/
def ProperPairs {α : Type*} [DecidableEq α] (p q r : α × α) : Prop :=
  p.1≠p.2 ∧ q.1≠q.2 ∧ r.1≠r.2 ∧
  ({p.1,p.2} : Finset α)≠{q.1,q.2} ∧
  ({q.1,q.2} : Finset α)≠{r.1,r.2} ∧
  ({p.1,p.2} : Finset α)≠{r.1,r.2} ∧
  ¬∃ x : α, x∈({p.1,p.2} : Finset α) ∧ x∈({q.1,q.2} : Finset α) ∧ x∈({r.1,r.2} : Finset α)

/-- The finite locus excluding every non-forced intersection collinearity,
independent of a particular cursor, crossing, or smoothing support. -/
def UniversalLocus {α : Type*} [DecidableEq α] (L : α → CarrierLine) : Prop :=
  ∀ p q r : α × α, ProperPairs p q r →
    carrierTripleNumerator (L p.1) (L p.2) (L q.1) (L q.2) (L r.1) (L r.2)≠0

/-- One dense open carrier locus works for every proper label triple. -/
theorem universalLocus_dense_open {α : Type*} [Fintype α] [DecidableEq α] :
    Dense {L : α → CarrierLine | UniversalLocus L} ∧
      IsOpen {L : α → CarrierLine | UniversalLocus L} := by
  classical
  let I := {x : (α×α)×(α×α)×(α×α) // ProperPairs x.1 x.2.1 x.2.2}
  let A := fun x : I => {L : α → CarrierLine |
    carrierTripleNumerator (L x.val.1.1) (L x.val.1.2)
      (L x.val.2.1.1) (L x.val.2.1.2) (L x.val.2.2.1) (L x.val.2.2.2)≠0}
  have hD : ∀ x : I, Dense (A x) := by
    intro x
    rcases x.property with ⟨hp,hq,hr,hpq,hqr,hpr,hno⟩
    exact triple_pairs_numerator_nonzero_dense _ _ _ _ _ _ hp hq hr hpq hqr hpr hno
  have hO : ∀ x : I, IsOpen (A x) := by
    intro x
    exact CarrierDensity.isOpen_assignmentNumerator_ne_zero _ _ _ _ _ _
  have hAll := CarrierFamilyDensity.finite_family_dense_open A hD hO
  have heq : (⋂ x,A x)={L : α → CarrierLine | UniversalLocus L} := by
    ext L
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    constructor
    · intro h p q r hpqr
      exact h ⟨(p,q,r),hpqr⟩
    · intro h x
      exact h x.val.1 x.val.2.1 x.val.2.2 x.property
  simpa only [heq] using hAll

private theorem pair_reflect {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (a b c d : α)
    (he : ({f a,f b} : Finset β)={f c,f d}) : ({a,b} : Finset α)={c,d} := by
  ext x
  have hh := congrArg (fun S : Finset β => f x∈S) he
  simpa only [Finset.mem_insert,Finset.mem_singleton,hf.eq_iff] using Iff.of_eq hh

theorem properPairs_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (p q r : α×α)
    (h : ProperPairs p q r) : ProperPairs (p.map f f) (q.map f f) (r.map f f) := by
  rcases h with ⟨hp,hq,hr,hpq,hqr,hpr,hno⟩
  refine ⟨fun h => hp (hf h),fun h => hq (hf h),fun h => hr (hf h),
    fun h => hpq (pair_reflect f hf _ _ _ _ h),
    fun h => hqr (pair_reflect f hf _ _ _ _ h),
    fun h => hpr (pair_reflect f hf _ _ _ _ h),?_⟩
  rintro ⟨x,hx,hy,hz⟩
  have hx' : x=f p.1 ∨ x=f p.2 := by simpa only [Prod.map,Finset.mem_insert,Finset.mem_singleton] using hx
  rcases hx' with rfl | rfl
  · apply hno
    exact ⟨p.1,by simp,by simpa only [Prod.map,Finset.mem_insert,Finset.mem_singleton,hf.eq_iff] using hy,
      by simpa only [Prod.map,Finset.mem_insert,Finset.mem_singleton,hf.eq_iff] using hz⟩
  · apply hno
    exact ⟨p.2,by simp,by simpa only [Prod.map,Finset.mem_insert,Finset.mem_singleton,hf.eq_iff] using hy,
      by simpa only [Prod.map,Finset.mem_insert,Finset.mem_singleton,hf.eq_iff] using hz⟩

/-- Restriction to any injectively relabelled physical carrier family. -/
theorem universalLocus_comap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (L : β → CarrierLine) (hL : UniversalLocus L)
    (f : α → β) (hf : Function.Injective f) : UniversalLocus (L ∘ f) := by
  intro p q r h
  exact hL _ _ _ (properPairs_map f hf p q r h)
end DirectGLSSW.UniversalCarrierDomain


