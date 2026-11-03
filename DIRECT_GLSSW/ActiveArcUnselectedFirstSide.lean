import ActiveArcOpenFirstSide
import ActiveArcRetainedCrossingLocality
import ActiveArcFirstCrossing

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Primitive
open DirectGLSSW Cursor RetainedWords

/-- The first unselected physical crossing is strictly before the next retained
open vertex. The strictness comes from the support exclusion, not a supplied
first-side bound. This is the geometric input to the incompatible-support
virtual-secant no-jump argument. -/
theorem openVertex_one_after_unselected_first
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (U : Support q hR) (hu : c ∉ U.val) :
    ∃ s : ℝ, leftParameter q c < s ∧ s ≤ 1 ∧
      OpenVertex q hR U
        ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (open_count_ge_two q hR U.val)⟩ =
          affinePoint (q 0) (q 1) s := by
  obtain ⟨s,hs0,hs1,hpoint⟩ := openVertex_one_firstEdge q hR U
  refine ⟨s,?_,hs1,hpoint⟩
  by_cases hs : s = 1
  · rw [hs]
    exact (leftParameter_spec q c).2.1
  have hslt : s < 1 := lt_of_le_of_ne hs1 hs
  let i : Fin (openCount q hR U.val) :=
    ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (open_count_ge_two q hR U.val)⟩
  have hr : retained q U.val (cornerEvent q hR U.val (start q) i) :=
    (enumeration q hR U.val (start q) i).property
  change eventPoint q (cornerEvent q hR U.val (start q) i) =
    affinePoint (q 0) (q 1) s at hpoint
  generalize he : cornerEvent q hR U.val (start q) i = z at hr hpoint
  cases z with
  | inl j =>
      exact False.elim (regular_anchor_not_edgeInterior q hR 0 j
        ⟨s,hs0,hslt,hpoint⟩)
  | inr v =>
      rcases v with ⟨d,b⟩
      have hdmem : d ∈ U.val := hr
      have hdc : d ≠ c := fun h => hu (h ▸ hdmem)
      have hdp : crossingPoint q d = affinePoint (q 0) (q 1) s := hpoint
      have hm : edgeInterior q 0 (crossingPoint q d) := ⟨s,hs0,hslt,hdp⟩
      have hd0 : d.val.1 = 0 := by
        by_contra hh
        have hd2 : d.val.2 ≠ 0 := by
          intro hz
          have ho := d.property.1
          rw [hz] at ho
          exact (not_lt_of_ge (Fin.zero_le _)) ho
        exact hR.noTriple d.val.1 d.val.2 0 (crossingPoint q d)
          (ne_of_lt d.property.1) hd2 (Ne.symm hh)
          ⟨(crossingPoint_mem q d).1,(crossingPoint_mem q d).2,hm⟩
      have hp : leftParameter q d = s := by
        apply edge_parameter_unique q hR 0
        have hl := (leftParameter_spec q d).2.2
        rw [hd0] at hl
        exact hl.symm.trans hdp
      rw [← hp]
      exact first_parameter_strict q hR c hc d hd0 hdc

end DirectGLSSW.ActiveArc.Primitive
