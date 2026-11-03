import DirectGLSSW.PolygonSignExtensionality
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace DirectGLSSW

private theorem scalarSignValue_eq_of_continuous_ne_zero
    {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    (f : α → ℝ) (hf : Continuous f) (hne : ∀ t, f t ≠ 0) (x y : α) :
    scalarSignValue (f x) = scalarSignValue (f y) := by
  by_cases hxneg : f x < 0
  · by_cases hyneg : f y < 0
    · simp [scalarSignValue, hne x, hne y, hxneg, hyneg]
    · have hypos : 0 < f y :=
        lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm (hne y))
      obtain ⟨t, hft⟩ := intermediate_value_univ₂ (a := x) (b := y) hf
        continuous_const (le_of_lt hxneg) (le_of_lt hypos)
      exact False.elim (hne t hft)
  · have hxpos : 0 < f x :=
      lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm (hne x))
    by_cases hyneg : f y < 0
    · obtain ⟨t, hft⟩ := intermediate_value_univ₂ (a := y) (b := x) hf
        continuous_const (le_of_lt hyneg) (le_of_lt hxpos)
      exact False.elim (hne t hft)
    · have hypos : 0 < f y :=
        lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm (hne y))
      simp [scalarSignValue, hne x, hne y, hxneg, hyneg]

/-- The GLSSW parent amplitude is constant on every continuous preconnected
family of actual G1/G2 polygons. G1 keeps every oriented triple determinant
nonzero, so its sign cannot change on the preconnected parameter space. -/
theorem polygonAmplitude_eq_of_continuous_cyclicGeneric_preconnected
    {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    {n : ℕ} (q : α → Fin n → PlanarPoint ℝ)
    (hqcont : Continuous q) (hq : ∀ t, CyclicGeneric (q t)) (x y : α) :
    polygonAmplitude (q x) (hq x) = polygonAmplitude (q y) (hq y) := by
  apply polygonAmplitude_eq_of_oriented_triple_signs
  intro a b c hab hbc hac
  let f : α → ℝ := fun t =>
    planarDet (q t b - q t c) (q t a - q t c)
  have hpoint (i : Fin n) : Continuous (fun t => q t i) :=
    (continuous_apply i).comp hqcont
  have hleft : Continuous (fun t => q t b - q t c) := (hpoint b).sub (hpoint c)
  have hright : Continuous (fun t => q t a - q t c) := (hpoint a).sub (hpoint c)
  have hf : Continuous f := by
    dsimp [f, planarDet]
    exact (hleft.fst.mul hright.snd).sub (hleft.snd.mul hright.fst)
  have hne (t : α) : f t ≠ 0 := by
    exact (hq t).g1 a b c hab hbc hac
  have hsign := scalarSignValue_eq_of_continuous_ne_zero f hf hne x y
  simpa [f] using hsign

/-- Path form of `polygonAmplitude_eq_of_continuous_cyclicGeneric_preconnected`. -/
theorem polygonAmplitude_eq_of_continuous_cyclicGeneric_path
    {n : ℕ} (q : Set.Icc (0 : ℝ) 1 → Fin n → PlanarPoint ℝ)
    (hqcont : Continuous q) (hq : ∀ t, CyclicGeneric (q t)) :
    polygonAmplitude (q ⟨0, by norm_num, by norm_num⟩)
        (hq ⟨0, by norm_num, by norm_num⟩) =
      polygonAmplitude (q ⟨1, by norm_num, by norm_num⟩)
        (hq ⟨1, by norm_num, by norm_num⟩) := by
  letI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace (isPreconnected_Icc : IsPreconnected (Set.Icc (0 : ℝ) 1))
  exact polygonAmplitude_eq_of_continuous_cyclicGeneric_preconnected
    q hqcont hq ⟨0, by norm_num, by norm_num⟩ ⟨1, by norm_num, by norm_num⟩


end DirectGLSSW
