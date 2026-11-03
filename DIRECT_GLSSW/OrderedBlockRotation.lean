import DirectGLSSW.FiniteCycleOrder
import Mathlib.Tactic.Order

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW
open FiniteCycleOrder

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Rotating an entire initial block preserves the literal strict circular order. -/
theorem strictCyclicBetween_block_rotation (E : α ≃ β) (a : α)
    (horder : ∀ x y : α, E x < E y ↔
      (a ≤ x ∧ y < a) ∨ ((x < a ↔ y < a) ∧ x < y)) (x y z : α) :
    strictCyclicBetween (E x) (E y) (E z) ↔ strictCyclicBetween x y z := by
  have cross (u v : α) (hu : u < a) (hv : ¬ v < a) : u < v :=
    lt_of_lt_of_le hu (not_lt.mp hv)
  have hxy := cross x y
  have hxz := cross x z
  have hyx := cross y x
  have hyz := cross y z
  have hzx := cross z x
  have hzy := cross z y
  clear cross
  simp only [strictCyclicBetween,horder, ← not_lt]
  clear horder
  by_cases hx : x < a <;> by_cases hy : y < a <;> by_cases hz : z < a
  all_goals simp_all
  all_goals aesop (add safe forward [lt_of_lt_of_le, lt_of_le_of_lt, lt_trans])

variable [Fintype α] [Fintype β]

/-- No point lies strictly between an event and its actual ordered successor. -/
theorem orderedCyclicSuccessor_no_strict_between (x z : α) :
    ¬ strictCyclicBetween x z (orderedCyclicSuccessor α x) := by
  intro h
  rcases orderedCyclicSuccessor_order_spec α x with ⟨hxy,hmin⟩ | ⟨hmax,hmin⟩
  · rcases h with ⟨hxz,hzy⟩ | ⟨hzy,hyx⟩ | ⟨hyx,hxz⟩
    · exact (not_lt_of_ge (hmin z hxz)) hzy
    · exact (lt_asymm hxy hyx)
    · exact (lt_asymm hxy hyx)
  · rcases h with ⟨hxz,hzy⟩ | ⟨hzy,hyx⟩ | ⟨hyx,hxz⟩
    · exact (not_lt_of_ge (hmax z)) hxz
    · exact (not_lt_of_ge (hmin z)) hzy
    · exact (not_lt_of_ge (hmax z)) hxz

/-- Circular adjacency with distinct endpoints determines the ordered successor. -/
theorem orderedCyclicSuccessor_eq_of_no_strict_between (x y : α) (hne : y ≠ x)
    (hno : ∀ z : α, ¬ strictCyclicBetween x z y) :
    orderedCyclicSuccessor α x = y := by
  apply orderedCyclicSuccessor_eq_of_order_spec
  by_cases hxy : x < y
  · left
    refine ⟨hxy,?_⟩
    intro z hxz
    apply le_of_not_gt
    intro hzy
    exact hno z (Or.inl ⟨hxz,hzy⟩)
  · right
    have hyx : y < x := lt_of_le_of_ne (not_lt.mp hxy) hne
    constructor
    · intro z
      apply le_of_not_gt
      intro hxz
      exact hno z (Or.inr (Or.inr ⟨hyx,hxz⟩))
    · intro z
      apply le_of_not_gt
      intro hzy
      exact hno z (Or.inr (Or.inl ⟨hzy,hyx⟩))

/-- A circular-order equivalence intertwines actual finite ordered successors. -/
theorem orderedCyclicSuccessor_naturality_of_circular_order (E : α ≃ β)
    (hcircle : ∀ x y z : α,
      strictCyclicBetween (E x) (E y) (E z) ↔ strictCyclicBetween x y z)
    (x : α) : orderedCyclicSuccessor β (E x) = E (orderedCyclicSuccessor α x) := by
  classical
  by_cases hcard : 2 ≤ Fintype.card α
  · apply orderedCyclicSuccessor_eq_of_no_strict_between
    · exact fun h => orderedCyclicSuccessor_ne_self α hcard x (E.injective h)
    · intro z hz
      have hz' : strictCyclicBetween (E x) (E (E.symm z))
          (E (orderedCyclicSuccessor α x)) := by simpa using hz
      exact orderedCyclicSuccessor_no_strict_between x (E.symm z)
        ((hcircle _ _ _).mp hz')
  · have hsmall : Fintype.card α ≤ 1 := by omega
    letI : Subsingleton α := ⟨Fintype.card_le_one_iff.mp hsmall⟩
    letI : Subsingleton β := ⟨fun u v => E.symm.injective (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _

/-- A finite linear order may be rotated at any cut, including a whole block
of polygon events. This does not require the cut block to have one element. -/
theorem orderedCyclicSuccessor_naturality_of_block_rotation (E : α ≃ β) (a : α)
    (horder : ∀ x y : α, E x < E y ↔
      (a ≤ x ∧ y < a) ∨ ((x < a ↔ y < a) ∧ x < y)) (x : α) :
    orderedCyclicSuccessor β (E x) = E (orderedCyclicSuccessor α x) :=
  orderedCyclicSuccessor_naturality_of_circular_order E
    (strictCyclicBetween_block_rotation E a horder) x






end DirectGLSSW
