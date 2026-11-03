import SpectatorDaughterWords

set_option autoImplicit false
namespace DirectGLSSW.DaughterWordLocality
open DaughterFirstReturn GeometricSmoothingWeights PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem region_of_same_component {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (R : α → Prop) (x : α) (hx : R x)
    (hR : ∀ y, R y → R (p y)) (y : α)
    (hy : componentOf p y = componentOf p x) : R y := by
  have hpow : ∀ k : ℕ, R ((p^k) x) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => simpa only [pow_succ', Equiv.Perm.mul_apply] using hR _ ih
  obtain ⟨k,hk⟩ := ((componentOf_eq_iff p x y).mp hy.symm).exists_nat_pow_eq
  rw [← hk]
  exact hpow k

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S U : Finset (PolygonCrossing P)) (root : PolygonEvent P)

theorem daughterPointList_eq_of_agree_on_component
    (hperm : ∀ y, componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root →
      smoothingDartPermutation P hP.g2 U y = smoothingDartPermutation P hP.g2 S y)
    (hret : ∀ y, componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root →
      (retainedCorner P U y ↔ retainedCorner P S y)) :
    daughterPointList P hP.g2 U root = daughterPointList P hP.g2 S root := by
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    SpectatorDaughterWords.orbitWord_eq_of_agree_on_component _ _ root hperm]
  apply congrArg (List.map (polygonEventPoint P))
  apply List.filter_congr
  intro y hy
  have hc : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root :=
    ((componentOf_eq_iff _ _ _).mpr ((mem_orbitWord_iff _ _ _).mp hy)).symm
  simp only [hret y hc]

theorem daughterPointList_eq_on_region (R : PolygonEvent P → Prop)
    (hr : R root)
    (hR : ∀ y, R y → R (smoothingDartPermutation P hP.g2 S y))
    (hperm : ∀ y, R y → smoothingDartPermutation P hP.g2 U y =
      smoothingDartPermutation P hP.g2 S y)
    (hret : ∀ y, R y → (retainedCorner P U y ↔ retainedCorner P S y)) :
    daughterPointList P hP.g2 U root = daughterPointList P hP.g2 S root := by
  apply daughterPointList_eq_of_agree_on_component P hP S U root
  · intro y hy
    exact hperm y (region_of_same_component _ R root hr hR y hy)
  · intro y hy
    exact hret y (region_of_same_component _ R root hr hR y hy)

theorem rooted_amplitude_eq_on_region
    (hAux : auxiliaryGenericity P hP)
    (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S)
    (hU : PolygonNonalternation.polygonNonalternating P hP.g2 U)
    (R : PolygonEvent P → Prop) (hr : R root)
    (hR : ∀ y, R y → R (smoothingDartPermutation P hP.g2 S y))
    (hperm : ∀ y, R y → smoothingDartPermutation P hP.g2 U y =
      smoothingDartPermutation P hP.g2 S y)
    (hret : ∀ y, R y → (retainedCorner P U y ↔ retainedCorner P S y)) :
    polygonAmplitude (daughterVertex P hP.g2 U root) (hAux U hU root) =
    polygonAmplitude (daughterVertex P hP.g2 S root) (hAux S hS root) := by
  apply TruncationPointListAdapter.polygonAmplitude_eq_of_pointList_eq
  exact daughterPointList_eq_on_region P hP S U root R hr hR hperm hret

theorem componentAmplitude_eq_on_region (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity P hP)
    (hS : PolygonNonalternation.polygonNonalternating P hP.g2 S)
    (hU : PolygonNonalternation.polygonNonalternating P hP.g2 U)
    (R : PolygonEvent P → Prop) (hr : R root)
    (hR : ∀ y, R y → R (smoothingDartPermutation P hP.g2 S y))
    (hperm : ∀ y, R y → smoothingDartPermutation P hP.g2 U y =
      smoothingDartPermutation P hP.g2 S y)
    (hret : ∀ y, R y → (retainedCorner P U y ↔ retainedCorner P S y)) :
    componentAmplitude P hP U hAux hU
      (componentOf (smoothingDartPermutation P hP.g2 U) root) =
    componentAmplitude P hP S hAux hS
      (componentOf (smoothingDartPermutation P hP.g2 S) root) := by
  rw [TruncationComponentWeights.componentAmplitude_eq_at_root hRI P hP U hAux hU _ root rfl,
    TruncationComponentWeights.componentAmplitude_eq_at_root hRI P hP S hAux hS _ root rfl]
  exact rooted_amplitude_eq_on_region P hP S U root hAux hS hU R hr hR hperm hret






end
end DirectGLSSW.DaughterWordLocality
