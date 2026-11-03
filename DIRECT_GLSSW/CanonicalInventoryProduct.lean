import CanonicalInventoryPolynomials

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain MvPolynomial
open scoped BigOperators

/-- One literal finite product represents precisely the stated stronger inventory.
This is not a definition of the complete source auxiliary domain. -/
theorem exists_canonical_inventory_polynomial (n : ℕ) :
    ∃ P : MvPolynomial (JointCoordinates n) ℝ, ∀ x,
      eval x P ≠ 0 ↔
        PairTransverse (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) ∧
        UniversalLocus (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) ∧
        allCycleSecantExclusions (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) := by
  classical
  let I2 := {p : Fin (n+1) × Fin (n+1) // p.1 ≠ p.2}
  let I3 := {p : (Fin (n+1) × Fin (n+1)) × (Fin (n+1) × Fin (n+1)) ×
    (Fin (n+1) × Fin (n+1)) // ProperPairs p.1 p.2.1 p.2.2}
  let C := fun m : Fin (n+2) => {f : Fin m.val → Fin (n+1) // Function.Injective f ∧
    ∃ q : Fin m.val → PlanarPoint ℝ, CyclicGeneric q}
  let I4 := Σ m : Fin (n+2), C m × {l : Fin 4 → Fin m.val // Function.Injective l}
  let I6 := Σ m : Fin (n+2), C m × {l : Fin 6 → Fin m.val // Function.Injective l}
  have e2 (p : I2) := exists_joint_denominator_polynomial p.val.1 p.val.2
  have e3 (p : I3) := exists_joint_triple_polynomial
    p.val.1.1 p.val.1.2 p.val.2.1.1 p.val.2.1.2 p.val.2.2.1 p.val.2.2.2
  have e4 (p : I4) := exists_joint_outer_polynomial p.2.1.val p.2.2.val
  have e6 (p : I6) := exists_joint_secant_polynomial p.2.1.val p.2.2.val
  choose P2 h2 using e2
  choose P3 h3 using e3
  choose P4 h4 using e4
  choose P6 h6 using e6
  let P := (∏ p : I2, P2 p) * ((∏ p : I3, P3 p) * ((∏ p : I4, P4 p) * (∏ p : I6, P6 p)))
  refine ⟨P,?_⟩
  intro x
  let L := canonicalAugmentedCarrier (jointVertices x) (jointLine x)
  have he : eval x P ≠ 0 ↔
      (∀ p : I2, lineDenominator (L p.val.1) (L p.val.2) ≠ 0) ∧
      (∀ p : I3, carrierTripleNumerator (L p.val.1.1) (L p.val.1.2)
        (L p.val.2.1.1) (L p.val.2.1.2) (L p.val.2.2.1) (L p.val.2.2.2) ≠ 0) ∧
      (∀ p : I4, outerCycleNumerator L p.2.1.val p.2.2.val ≠ 0) ∧
      (∀ p : I6, secantCycleNumerator L p.2.1.val p.2.2.val ≠ 0) := by
    simp only [P,map_mul,map_prod,mul_ne_zero_iff,Finset.prod_ne_zero_iff,
      Finset.mem_univ,true_implies,h2,h3,h4,h6,L]
  rw [he]
  change _ ↔ PairTransverse L ∧ UniversalLocus L ∧ allCycleSecantExclusions L
  constructor
  · rintro ⟨hT,hU,hO,hS⟩
    refine ⟨fun a b hab => hT ⟨(a,b),hab⟩,fun p q r h => hU ⟨(p,q,r),h⟩,?_⟩
    intro m hm f hf hq
    have hmi : m < n+2 := by omega
    constructor
    · intro l hl
      exact hO ⟨⟨m,hmi⟩,⟨⟨f,hf,hq⟩,⟨l,hl⟩⟩⟩
    · intro l hl
      exact hS ⟨⟨m,hmi⟩,⟨⟨f,hf,hq⟩,⟨l,hl⟩⟩⟩
  · rintro ⟨hT,hU,hC⟩
    refine ⟨fun p => hT _ _ p.property,fun p => hU _ _ _ p.property,?_,?_⟩
    · intro p
      exact (hC p.1.val (by have := p.1.isLt; omega) p.2.1.val p.2.1.property.1
        p.2.1.property.2).1 p.2.2.val p.2.2.property
    · intro p
      exact (hC p.1.val (by have := p.1.isLt; omega) p.2.1.val p.2.1.property.1
        p.2.1.property.2).2 p.2.2.val p.2.2.property

end DirectGLSSW.CyclicCarrierClearing

