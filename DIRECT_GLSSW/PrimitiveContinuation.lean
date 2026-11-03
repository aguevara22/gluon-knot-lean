import SourcePrimitiveExtension

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PrimitiveContinuation
open Filter Topology

theorem existsUnique_continuation (hRI : GLSSWRootIndependence) (n : ℕ) :
    ∃! Γ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ,
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
        ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r), Γ r hr = Γ q hq) ∧
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (hAux : GeometricSmoothingWeights.auxiliaryGenericity q hq),
        Γ q hq = GeometricSmoothingWeights.separatingSmoothingSum q hq hAux) :=
  SourcePrimitiveExtension.existsUnique_fullPrimitive_extension hRI n

noncomputable def fullPrimitive (hRI : GLSSWRootIndependence) (n : ℕ) :
    (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ :=
  Classical.choose (existsUnique_continuation hRI n)

theorem fullPrimitive_characterization (hRI : GLSSWRootIndependence) (n : ℕ) :
    (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
      ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r),
        fullPrimitive hRI n r hr = fullPrimitive hRI n q hq) ∧
    (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
      (hAux : GeometricSmoothingWeights.auxiliaryGenericity q hq),
      fullPrimitive hRI n q hq =
        GeometricSmoothingWeights.separatingSmoothingSum q hq hAux) ∧
    (∀ Γ : (q : Fin n → PlanarPoint ℝ) → CyclicGeneric q → ℚ,
      ((∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
        ∀ᶠ r in 𝓝 q, ∀ (hr : CyclicGeneric r), Γ r hr = Γ q hq) ∧
      (∀ (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
        (hAux : GeometricSmoothingWeights.auxiliaryGenericity q hq),
        Γ q hq = GeometricSmoothingWeights.separatingSmoothingSum q hq hAux)) →
      Γ = fullPrimitive hRI n) := by
  have h := Classical.choose_spec (existsUnique_continuation hRI n)
  exact ⟨h.1.1, h.1.2, h.2⟩

end DirectGLSSW.PrimitiveContinuation
