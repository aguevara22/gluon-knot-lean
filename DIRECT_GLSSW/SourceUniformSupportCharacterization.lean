import UniformSupportPredicate

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceUniformSupportCharacterization
open GeometricSmoothingWeights PermutationOrbits PolygonNonalternation
open DaughterFirstReturn PolygonUniformity UniformDaughterSupportLocality UniformSupportReconstruction
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

theorem uniform_support_iff (S : Finset (PolygonCrossing q)) :
    uniformDaughterSupport q hq S ↔ polygonNonalternating q hq.g2 S ∧
      ∀ A : Component (smoothingDartPermutation q hq.g2 S),
        PolygonUniform (componentPolygon q hq S A) :=
  uniformDaughterSupport_iff_componentPolygon q hq S

theorem separating_uniform_support_iff (S : SeparatingSupport q hq) :
    uniformDaughterSupport q hq S.val ↔
      ∀ A : Component (smoothingDartPermutation q hq.g2 S.val),
        PolygonUniform (componentPolygon q hq S.val A) := by
  rw [uniform_support_iff]
  exact and_iff_right S.property

/-- The two universal sign conditions remain a disjunction for each component. -/
theorem literal_all_left_or_all_right (S : SeparatingSupport q hq) :
    uniformDaughterSupport q hq S.val ↔
      ∀ A : Component (smoothingDartPermutation q hq.g2 S.val),
        (∀ i, 0 < turnDet (componentPolygon q hq S.val A) i) ∨
        (∀ i, turnDet (componentPolygon q hq S.val A) i < 0) :=
  separating_uniform_support_iff q hq S

theorem retained_root_independent (S : Finset (PolygonCrossing q))
    (r s : PolygonEvent q) (hr : retainedCorner q S r) (hs : retainedCorner q S s)
    (hc : componentOf (smoothingDartPermutation q hq.g2 S) r =
      componentOf (smoothingDartPermutation q hq.g2 S) s) :
    PolygonUniform (daughterVertex q hq.g2 S r) ↔
      PolygonUniform (daughterVertex q hq.g2 S s) :=
  daughterUniform_iff_of_same_component q hq S r s hr hs hc

/-- Empty support leaves exactly the original cyclic traversal and its anchor turns. -/
theorem empty_uniform_support_iff :
    uniformDaughterSupport q hq ∅ ↔ PolygonUniform q := by
  have hsame (x y : PolygonEvent q) :
      componentOf (smoothingDartPermutation q hq.g2 ∅) x =
        componentOf (smoothingDartPermutation q hq.g2 ∅) y := by
    rw [smoothingDartPermutation_empty]
    exact (componentOf_eq_iff _ x y).mpr
      ((polygonEventSuccessor_isCycleOn q hq.g2).2 (Set.mem_univ x) (Set.mem_univ y))
  constructor
  · rintro ⟨_,hu⟩
    let z : PolygonEvent q := Sum.inl ⟨0,by have := hq.size_ge_three; omega⟩
    obtain ⟨r,hr,_,hu⟩ := hu (componentOf (smoothingDartPermutation q hq.g2 ∅) z)
    rcases (daughterUniform_iff_carrier q hq ∅ r hr).mp hu with hpos | hneg
    · left
      intro i
      exact hpos (Sum.inl i) trivial (hsame _ _)
    · right
      intro i
      exact hneg (Sum.inl i) trivial (hsame _ _)
  · intro hu
    refine ⟨?_, ?_⟩
    · intro c hc
      exact False.elim (Finset.not_mem_empty c hc)
    · intro A
      let r := componentRoot q hq ∅ A
      have hr : retainedCorner q ∅ r := componentRoot_retainedCorner q hq ∅ A
      refine ⟨r,hr,componentRoot_sameComponent q hq ∅ A,?_⟩
      apply (daughterUniform_iff_carrier q hq ∅ r hr).mpr
      rcases hu with hpos | hneg
      · left
        intro x hx _
        cases x with
        | inl i => exact hpos i
        | inr v => exact False.elim (Finset.not_mem_empty v.1 hx)
      · right
        intro x hx _
        cases x with
        | inl i => exact hneg i
        | inr v => exact False.elim (Finset.not_mem_empty v.1 hx)

/-- The existing state-sum carrier equivalence preserves the literal support. -/
theorem state_sum_carrier_support
    (S : {S : SeparatingSupport q hq //
      ∀ A : Component (smoothingDartPermutation q hq.g2 S.val),
        PolygonUniform (componentPolygon q hq S.val A)}) :
    (uniformSupportEquiv q hq S).val = S.val.val := rfl

end DirectGLSSW.SourceUniformSupportCharacterization






