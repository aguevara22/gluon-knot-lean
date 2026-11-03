import PhysicalSingletonInterval
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.PhysicalKnotSplit
open PermutationOrbits FiniteCycleOrder SingletonWords Nonalternation
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (c : Crossing q)

theorem closed_singleton_root_sameCycle_right (x : Event q)
    (hx : componentOf (incoming q hR.noTriple {c}) x ≠ openComponent q hR.noTriple {c}) :
    (incoming q hR.noTriple {c}).SameCycle x (Sum.inr (c,true)) := by
  have hi : (eventEnumeration q hR).symm x ∈ intervalSide (leftRank q hR c) (rightRank q hR c) := by
    by_contra hn
    have hm : x ∈ List.ofFn (complementEvents q hR c) :=
      (complementEvents_mem q hR c x).mpr hn
    rw [←open_orbitWord q hR c] at hm
    have hs := (mem_orbitWord_iff _ _ _).mp hm
    exact hx ((componentOf_eq_iff _ _ _).mpr hs.symm)
  let r := intervalEvents q hR c ⟨0,(daughterLengths_pos _ _ (rank_lt q hR c)).1⟩
  have hx' : x ∈ orbitWord (incoming q hR.noTriple {c}) r := by
    rw [interval_orbitWord]
    exact (intervalEvents_mem q hR c x).mpr hi
  have hr : Sum.inr (c,true) ∈ orbitWord (incoming q hR.noTriple {c}) r := by
    rw [interval_orbitWord]
    exact (intervalEvents_mem q hR c _).mpr (right_in_interval q hR c)
  exact ((mem_orbitWord_iff _ _ _).mp hx').symm.trans ((mem_orbitWord_iff _ _ _).mp hr)

theorem closed_singleton_word_offset_isRotated (x : Event q)
    (hx : componentOf (incoming q hR.noTriple {c}) x ≠ openComponent q hR.noTriple {c}) :
    List.ofFn (RetainedWords.vertex q hR {c} x) ~r
      crossingPoint q c :: List.ofFn (fun i : Fin (c.val.2.val-c.val.1.val) =>
        q ⟨c.val.1.val+i.val+1,by have := c.val.2.isLt;omega⟩) := by
  have hh := retainedWord_isRotated_of_sameCycle q hR {c} x (Sum.inr (c,true))
    (closed_singleton_root_sameCycle_right q hR c x hx)
  rw [singleton_closed_word_offset q hR c] at hh
  exact hh
end DirectGLSSW.ActiveArc.PhysicalKnotSplit
