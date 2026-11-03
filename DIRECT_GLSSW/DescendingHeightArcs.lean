import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.DescendingSpatial

/-- The literal strictly decreasing height separates all parameters. -/
theorem height_arc_injective (γ : unitInterval → ℂ) (H : ℝ) :
    Function.Injective (fun t : unitInterval => (γ t, H + 1 - t.val)) := by
  intro s t h
  apply Subtype.ext
  have hh := congrArg Prod.snd h
  dsimp at hh
  linarith

theorem height_arc_continuous (γ : C(unitInterval, ℂ)) (H : ℝ) :
    Continuous (fun t : unitInterval => (γ t, H + 1 - t.val)) := by
  fun_prop

/-- At equal height the two parameters agree. Only their common endpoints
remain when the planar paths avoid each other in the open interval. -/
theorem height_arcs_intersection (γ β : C(unitInterval, ℂ)) (H : ℝ)
    (hzero : γ 0 = β 0) (hone : γ 1 = β 1)
    (havoid : ∀ t : unitInterval, 0 < t.val → t.val < 1 → γ t ≠ β t) :
    Set.range (fun t : unitInterval => (γ t, H + 1 - t.val)) ∩
      Set.range (fun t : unitInterval => (β t, H + 1 - t.val)) =
        {(γ 0, H + 1), (γ 1, H)} := by
  ext z
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    have hst : t = s := by
      apply Subtype.ext
      have hh := congrArg Prod.snd ht
      dsimp at hh
      linarith
    subst t
    have heq : γ s = β s := (congrArg Prod.fst ht).symm
    by_cases hs0 : s.val = 0
    · have hs : s = 0 := Subtype.ext hs0
      subst s
      simp
    · by_cases hs1 : s.val = 1
      · have hs : s = 1 := Subtype.ext hs1
        subst s
        simp
      · exact False.elim (havoid s (lt_of_le_of_ne s.property.1 (Ne.symm hs0))
          (lt_of_le_of_ne s.property.2 hs1) heq)
  · intro hz
    rcases (Set.mem_insert_iff.mp hz) with hz | hz
    · subst z
      constructor
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp [hzero]⟩
    · have hz' := Set.mem_singleton_iff.mp hz
      subst z
      constructor
      · exact ⟨1, by simp⟩
      · exact ⟨1, by simp [hone]⟩

end DirectGLSSW.DescendingSpatial




