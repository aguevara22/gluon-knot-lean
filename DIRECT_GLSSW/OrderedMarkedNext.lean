import MarkedNextOrder
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.MarkedCycleGaps
open Equiv PermutationOrbits
attribute [local instance] Classical.propDecidable

theorem next_ordered_eq_of_order {α β ι : Type*}
    [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [Fintype ι]
    (a : ι → α) (b : ι → β) (ha : Function.Injective a) (hb : Function.Injective b)
    (horder : ∀ i j, a i < a j ↔ b i < b j) :
    next (orderedCyclicSuccessor α) a ha = next (orderedCyclicSuccessor β) b hb := by
  apply next_eq_of_coordinate_order _ _ (increasingEnumeration α).toEquiv.symm
    (increasingEnumeration β).toEquiv.symm
  · intro x
    simp only [orderedCyclicSuccessor, Equiv.trans_apply, Equiv.symm_apply_apply]
  · intro x
    simp only [orderedCyclicSuccessor, Equiv.trans_apply, Equiv.symm_apply_apply]
  · intro i j
    change (increasingEnumeration α).symm (a i) < (increasingEnumeration α).symm (a j) ↔
      (increasingEnumeration β).symm (b i) < (increasingEnumeration β).symm (b j)
    simpa only [OrderIso.lt_iff_lt] using horder i j
end DirectGLSSW.MarkedCycleGaps
