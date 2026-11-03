import OpenCurrentTurnProjector

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.OpenCurrentFiniteFamily

open OpenFirstEdgeGeometry OpenCurrentTurnProjector ShortEdgeSignStability
open scoped BigOperators

/-- A common positive radius for a finite family of actual open words, followed
by the literal weighted sum of their short-first current identities. This is
finite-family infrastructure; it does not identify a physical smoothing sum. -/
theorem exists_weighted_short_first {ι : Type*} [Fintype ι]
    (q : ι → ℕ → PlanarPoint ℝ) (N : ι → ℕ)
    (hN : ∀ i, 1 < N i) (hcore : ∀ i, CoreHGeneric (q i) (N i))
    (w : ι → ℚ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (∀ i, CoreHGeneric (approach (q i) ε) (N i)) ∧
      (∑ i, w i * OpenMarkedCurrent.entry
          (polygonSignArray (approach (q i) ε)) 0 (N i)) =
        ∑ i, w i * (((1 + polygonSignArray (q i) 0 1 2) / 2) - 1) *
          OpenMarkedCurrent.entry (polygonSignArray (q i)) 1 (N i) := by
  classical
  let P : ι → ℝ → Prop := fun i ε =>
    CoreHGeneric (approach (q i) ε) (N i) ∧
      OpenMarkedCurrent.entry (polygonSignArray (approach (q i) ε)) 0 (N i) =
        (((1 + polygonSignArray (q i) 0 1 2) / 2) - 1) *
          OpenMarkedCurrent.entry (polygonSignArray (q i)) 1 (N i)
  have hlocal : ∀ i, i ∈ (Finset.univ : Finset ι) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → P i ε := by
    intro i _
    obtain ⟨δ, hδ, _, hgood⟩ := exists_short_first_currents (q i) (N i) (hcore i)
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ
    have h := hgood ε hε hεδ
    exact ⟨h.1, (h.2 (N i) (hN i) le_rfl).2⟩
  obtain ⟨δ, hδ, hgood⟩ := exists_finset_common_radius Finset.univ P hlocal
  refine ⟨min δ 1, lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro ε hε hεδ
  have hsmall : ε < δ := lt_of_lt_of_le hεδ (min_le_left _ _)
  refine ⟨?_, ?_⟩
  · intro i
    exact (hgood ε hε hsmall i (Finset.mem_univ i)).1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [(hgood ε hε hsmall i hi).2]
    exact (mul_assoc _ _ _).symm

end DirectGLSSW.OpenCurrentFiniteFamily
