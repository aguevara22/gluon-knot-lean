import CanonicalInventoryProduct

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain MvPolynomial Set Filter Topology

/-- Properness is obtained from actual polygon/line reconstruction in the same
original vertex coordinates, not from density under an extraction map. -/
theorem exists_proper_canonical_inventory_polynomial {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ P : MvPolynomial (JointCoordinates n) ℝ, P ≠ 0 ∧ ∀ x,
      eval x P ≠ 0 ↔
        PairTransverse (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) ∧
        UniversalLocus (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) ∧
        allCycleSecantExclusions (canonicalAugmentedCarrier (jointVertices x) (jointLine x)) := by
  obtain ⟨P,hP⟩ := exists_canonical_inventory_polynomial n
  obtain ⟨r,K,_,hr,hAux,hSec,hU,hT,hC⟩ :=
    exists_canonical_augmented_realization q hq 0 Set.univ Filter.univ_mem
  let x : JointCoordinates n → ℝ := Sum.elim
    (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2)
    (fun i => if i = 0 then K.1.1 else if i = 1 then K.1.2 else K.2)
  have hv : jointVertices x = r := by
    funext i
    simp [jointVertices,x]
  have hl : jointLine x = K := by simp [jointLine,x]
  have hx : eval x P ≠ 0 := (hP x).mpr (by simpa only [hv,hl] using And.intro hT (And.intro hU hC))
  refine ⟨P,?_,hP⟩
  intro hz
  exact hx (by rw [hz,map_zero])

/-- A proper ORIGINAL-coordinate polynomial guarantees the entire explicit
augmented carrier inventory in every nonempty open auxiliary-coordinate window.
This still names only the stated inventory, not an unreviewed source domain. -/
theorem exists_original_coefficient_for_all_auxiliary_windows {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ c : MvPolynomial (Fin n × Fin 2) ℝ, c ≠ 0 ∧
      Dense {x | eval x c ≠ 0} ∧ IsOpen {x | eval x c ≠ 0} ∧
      ∀ x : (Fin n × Fin 2) → ℝ, eval x c ≠ 0 →
        ∀ U : Set (Fin 3 → ℝ), IsOpen U → U.Nonempty → ∃ y ∈ U,
          PairTransverse (canonicalAugmentedCarrier (jointVertices (Sum.elim x y)) (jointLine (Sum.elim x y))) ∧
          UniversalLocus (canonicalAugmentedCarrier (jointVertices (Sum.elim x y)) (jointLine (Sum.elim x y))) ∧
          allCycleSecantExclusions (canonicalAugmentedCarrier (jointVertices (Sum.elim x y)) (jointLine (Sum.elim x y))) := by
  obtain ⟨P,hP,hiff⟩ := exists_proper_canonical_inventory_polynomial q hq
  obtain ⟨c,hc,hwin⟩ := SourceAuxiliaryCoefficient.exists_aux_original_in_open_window P hP
  have hdo := SourceAuxiliaryCoefficient.mvpoly_nonzero_dense_open c hc
  refine ⟨c,hc,hdo.1,hdo.2,?_⟩
  intro x hx U hU hUn
  obtain ⟨y,hy,hxy⟩ := hwin x hx U hU hUn
  exact ⟨y,hy,(hiff (Sum.elim x y)).mp hxy⟩

end DirectGLSSW.CyclicCarrierClearing


