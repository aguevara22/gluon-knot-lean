import ActiveArcUnselectedFirstSide
import ActiveArcSupportRefinementContract

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords

/-- The unselected first crossing lies in the strict interior of the FIRST
literal retained open side. No closing side is introduced. -/
theorem unselected_first_crossing_mem_first_side
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      crossingPoint q c = affinePoint
        (OpenVertex q hR U
          ⟨0,lt_of_lt_of_le (by decide : 0 < 2) (open_count_ge_two q hR U.val)⟩)
        (OpenVertex q hR U
          ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (open_count_ge_two q hR U.val)⟩) t := by
  obtain ⟨s,hcs,hs1,hpoint⟩ := openVertex_one_after_unselected_first q hR c hc U hu
  have hc0 := (leftParameter_spec q c).1
  have hs0 : 0 < s := lt_trans hc0 hcs
  refine ⟨leftParameter q c / s,div_pos hc0 hs0,(div_lt_one hs0).mpr hcs,?_⟩
  rw [openVertex_zero,hpoint]
  have hcp := (leftParameter_spec q c).2.2
  rw [hc.1] at hcp
  rw [hcp]
  ext <;> simp only [affinePoint] <;> field_simp <;> ring

end DirectGLSSW.ActiveArc.Primitive

namespace DirectGLSSW.ActiveArc.Split
open DirectGLSSW Cursor RetainedWords Primitive

/-- An incompatible selected chord excludes the crossing point from EVERY
later literal open side. Combined with the first-side interior theorem, this
rules out the actual-edge term in the endpoint-event trichotomy. -/
theorem incompatible_first_crossing_not_later_side
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val)
    (hbad : ∃ d ∈ U.val, ¬ Compatible (a:=n) (b:=0) q hR c d)
    (j : Fin (openCount q hR U.val)) (hj0 : 0 < j.val)
    (hj : j.val + 1 < openCount q hR U.val)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    crossingPoint q c ≠ affinePoint (OpenVertex q hR U j)
      (OpenVertex q hR U ⟨j.val+1,hj⟩) t := by
  obtain ⟨s,hs0,hs1,hfirst⟩ := unselected_first_crossing_mem_first_side q hR c hc U hu
  obtain ⟨d,hd,halt⟩ := hbad
  have halt' : ¬ Compatible (a:=n) (b:=0) q hR d c :=
    fun h => halt ((compatible_symm (a:=n) (b:=0) q hR c d).mpr h)
  let i : Fin (openCount q hR U.val) :=
    ⟨0,lt_of_lt_of_le (by decide : 0 < 2) (open_count_ge_two q hR U.val)⟩
  have hi : i.val + 1 < openCount q hR U.val := by
    have hh := open_count_ge_two q hR U.val
    dsimp [i]
    omega
  have hij : i ≠ j := by
    intro he
    have hh := congrArg Fin.val he
    dsimp [i] at hh
    omega
  intro hsecond
  exact no_open_selfCrossing_of_alternating q hR U.val U.property c d hu hd halt'
    i j hij hi hj s t hs0 hs1 ht0 ht1 ⟨hfirst,hsecond⟩

end DirectGLSSW.ActiveArc.Split
