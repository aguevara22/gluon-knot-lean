import DirectGLSSW.ChordSwaps
import DirectGLSSW.FiniteCycleOrder

/-!
# Nonalternating chord supports and the exact maximal component count
Literal circular betweenness and concrete endpoint swaps. Preproof transcription:
STATEMENTS.md; source lines 131–139. The polygon-identification bridge is separate.
-/
set_option autoImplicit false
namespace DirectGLSSW.ChordNonalternation
open Equiv PermutationOrbits FiniteCycleOrder
universe u
variable {C : Type u} {m : ℕ}

/-- Source nonalternation: both visits of every other selected chord are
on the same strict cyclic side of this chord's actual labelled endpoints. -/
def Nonalternating (e : C × Bool → Fin m) (S : Finset C) : Prop :=
  ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
    (strictCyclicBetween (e (c,false)) (e (d,false)) (e (c,true)) ↔
      strictCyclicBetween (e (c,false)) (e (d,true)) (e (c,true)))

/-- The literal source successor after all selected outgoing endpoints are swapped. -/
noncomputable def smoothing (e : C × Bool → Fin m) (he : Function.Injective e)
    (S : Finset C) : Perm (Fin m) :=
  cyclicSuccessorPerm m * swapProduct e he S

/-- A consistent increasing choice for the two endpoints; no orientation is discarded. -/
def lowerEndpoint (e : C × Bool → Fin m) (c : C) : Fin m :=
  min (e (c,false)) (e (c,true))

def upperEndpoint (e : C × Bool → Fin m) (c : C) : Fin m :=
  max (e (c,false)) (e (c,true))

def chordSide (e : C × Bool → Fin m) (c : C) : Set (Fin m) :=
  intervalSide (lowerEndpoint e c) (upperEndpoint e c)

theorem lowerEndpoint_lt_upperEndpoint (e : C × Bool → Fin m)
    (he : Function.Injective e) (c : C) : lowerEndpoint e c < upperEndpoint e c := by
  have h := endpoints_ne e he c
  rcases lt_or_gt_of_ne h with h | h
  · simpa [lowerEndpoint, upperEndpoint, min_eq_left h.le, max_eq_right h.le]
  · simpa [lowerEndpoint, upperEndpoint, min_eq_right h.le, max_eq_left h.le]

theorem chordSwap_eq_sorted (e : C × Bool → Fin m) (c : C) :
    chordSwap e c = swap (lowerEndpoint e c) (upperEndpoint e c) := by
  by_cases h : e (c,false) ≤ e (c,true)
  · simp [chordSwap, lowerEndpoint, upperEndpoint, min_eq_left h, max_eq_right h]
  · have h' := le_of_not_ge h
    simp [chordSwap, lowerEndpoint, upperEndpoint, min_eq_right h', max_eq_left h', swap_comm]

/-- The half-open sorted-side test is equivalent to the original oriented
strict test for the two visits of a disjoint chord, including reversed labels. -/
theorem chordSide_pair_iff (e : C × Bool → Fin m) (he : Function.Injective e)
    {c d : C} (hcd : c ≠ d) :
    (e (d,false) ∈ chordSide e c ↔ e (d,true) ∈ chordSide e c) ↔
      (strictCyclicBetween (e (c,false)) (e (d,false)) (e (c,true)) ↔
        strictCyclicBetween (e (c,false)) (e (d,true)) (e (c,true))) := by
  have h00 := endpoints_ne_of_ne e he hcd false false
  have h01 := endpoints_ne_of_ne e he hcd false true
  have h10 := endpoints_ne_of_ne e he hcd true false
  have h11 := endpoints_ne_of_ne e he hcd true true
  have h00' : (e (c,false)).val ≠ (e (d,false)).val := fun h => h00 (Fin.ext h)
  have h01' : (e (c,false)).val ≠ (e (d,true)).val := fun h => h01 (Fin.ext h)
  have h10' : (e (c,true)).val ≠ (e (d,false)).val := fun h => h10 (Fin.ext h)
  have h11' : (e (c,true)).val ≠ (e (d,true)).val := fun h => h11 (Fin.ext h)
  by_cases h : e (c,false) ≤ e (c,true)
  · simp only [chordSide, lowerEndpoint, upperEndpoint, min_eq_left h, max_eq_right h,
      intervalSide, Set.mem_setOf_eq, strictCyclicBetween, Fin.lt_def]
    change (e (c,false)).val ≤ (e (c,true)).val at h
    omega
  · have h' := le_of_not_ge h
    simp only [chordSide, lowerEndpoint, upperEndpoint, min_eq_right h', max_eq_left h',
      intervalSide, Set.mem_setOf_eq, strictCyclicBetween, Fin.lt_def]
    change (e (c,true)).val ≤ (e (c,false)).val at h'
    omega

/-- Subsets retain the literal pairwise source relation. -/
theorem Nonalternating.mono (e : C × Bool → Fin m) {S T : Finset C}
    (hT : Nonalternating e T) (hST : S ⊆ T) : Nonalternating e S := by
  intro c hc d hd hcd
  exact hT c (hST hc) d (hST hd) hcd

@[simp] theorem nonalternating_empty (e : C × Bool → Fin m) :
    Nonalternating e ∅ := by simp [Nonalternating]

@[simp] theorem smoothing_empty (e : C × Bool → Fin m) (he : Function.Injective e) :
    smoothing e he ∅ = cyclicSuccessorPerm m := by simp [smoothing]

theorem smoothing_insert [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S) :
    smoothing e he (insert c S) = smoothing e he S * chordSwap e c := by
  rw [smoothing, swapProduct_insert_right e he S c hc, ← mul_assoc]
  rfl

theorem smoothing_erase [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∈ S) :
    smoothing e he S = smoothing e he (S.erase c) * chordSwap e c := by
  rw [smoothing, swapProduct_erase_right e he S c hc, ← mul_assoc]
  rfl

/-- Factor the concrete smoothing through one selected literal circle split. -/
theorem smoothing_factor_split [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∈ S) :
    smoothing e he S = splitPerm (lowerEndpoint e c) (upperEndpoint e c) *
      swapProduct e he (S.erase c) := by
  rw [smoothing, swapProduct_erase e he S c hc, ← mul_assoc, chordSwap_eq_sorted]
  rfl

/-- Each selected side is invariant under all of a nonalternating smoothing. -/
theorem chordSide_smoothing_invariant (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (hS : Nonalternating e S)
    (c : C) (hc : c ∈ S) (x : Fin m) :
    x ∈ chordSide e c ↔ smoothing e he S x ∈ chordSide e c := by
  classical
  rw [smoothing_factor_split e he S c hc, Perm.mul_apply]
  have hs := intervalSide_invariant (lowerEndpoint e c) (upperEndpoint e c)
    (lowerEndpoint_lt_upperEndpoint e he c) (swapProduct e he (S.erase c) x)
  change _ ↔ _ ∈ chordSide e c at hs
  rw [← hs]
  symm
  apply mem_swapProduct_iff e he (S.erase c) (chordSide e c)
  intro d hd
  have hd' := Finset.mem_erase.mp hd
  exact (chordSide_pair_iff e he (Ne.symm hd'.1)).2 (hS c hc d hd'.2 (Ne.symm hd'.1))

/-- A selected nonalternating chord has its two visits in different final components. -/
theorem smoothing_endpoints_separated (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (hS : Nonalternating e S)
    (c : C) (hc : c ∈ S) :
    ¬(smoothing e he S).SameCycle (e (c,false)) (e (c,true)) := by
  intro h
  have hs := mem_iff_of_sameCycle (smoothing e he S) (chordSide e c)
    (chordSide_smoothing_invariant e he S hS c hc) h
  have hne := endpoints_ne e he c
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · simp [chordSide, lowerEndpoint, upperEndpoint, min_eq_left hlt.le,
      max_eq_right hlt.le, intervalSide, hlt] at hs
  · simp [chordSide, lowerEndpoint, upperEndpoint, min_eq_right hlt.le,
      max_eq_left hlt.le, intervalSide, hlt] at hs

/-- The unsmoothed finite circle has one full component, including size one. -/
theorem cyclicSuccessor_componentCount [NeZero m] :
    componentCount (cyclicSuccessorPerm m) = 1 := by
  apply componentCount_eq_one
  constructor
  · exact (cyclicSuccessorPerm m).bijOn (fun _ => Iff.rfl)
  · intro x _ y _
    obtain ⟨i, hi⟩ := (cyclicSuccessorPerm_oneTraversal x).2 y
    exact ⟨(i.val + 1 : ℕ), by simpa using hi⟩

/-- No support can exceed the one-plus-cardinality full component bound. -/
theorem smoothing_componentCount_le [NeZero m] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) :
    componentCount (smoothing e he S) ≤ S.card + 1 := by
  have h := componentCount_mul_swapProduct_le e he (cyclicSuccessorPerm m) S
  rw [cyclicSuccessor_componentCount] at h
  simpa [smoothing, Nat.add_comm] using h

/-- The literal pairwise nonalternation condition attains the maximal count. -/
theorem componentCount_of_nonalternating [NeZero m] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (hS : Nonalternating e S) :
    componentCount (smoothing e he S) = S.card + 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cyclicSuccessor_componentCount]
  | @insert c S hc ih =>
      have hS' : Nonalternating e S := hS.mono e (Finset.subset_insert c S)
      have hsep := smoothing_endpoints_separated e he (insert c S) hS c (Finset.mem_insert_self _ _)
      have hj := componentCount_mul_swap_of_not_sameCycle (smoothing e he (insert c S)) hsep
      rw [smoothing_insert e he S c hc, chordSwap] at hj
      simp only [mul_assoc, swap_mul_self, mul_one] at hj
      rw [smoothing_insert e he S c hc, Finset.card_insert_of_not_mem hc]
      have hi := ih hS'
      change componentCount (smoothing e he S) + 1 =
        componentCount (smoothing e he S * chordSwap e c) at hj
      omega

/-- After one selected cut, another chord shares an orbit exactly when its
actual strict circular side tests agree. Both orientations are covered. -/
theorem after_one_sameCycle_iff (e : C × Bool → Fin m)
    (he : Function.Injective e) {c d : C} (hcd : c ≠ d) :
    (cyclicSuccessorPerm m * chordSwap e c).SameCycle (e (d,false)) (e (d,true)) ↔
      (strictCyclicBetween (e (c,false)) (e (d,false)) (e (c,true)) ↔
        strictCyclicBetween (e (c,false)) (e (d,true)) (e (c,true))) := by
  rw [chordSwap_eq_sorted]
  change (splitPerm (lowerEndpoint e c) (upperEndpoint e c)).SameCycle _ _ ↔ _
  rw [split_sameCycle_iff _ _ (lowerEndpoint_lt_upperEndpoint e he c)]
  exact chordSide_pair_iff e he hcd

/-- Processing an alternating pair first splits and then joins, leaving one
component. This is a statement about the actual two swaps. -/
theorem alternating_pair_componentCount [NeZero m] (e : C × Bool → Fin m)
    (he : Function.Injective e) {c d : C} (hcd : c ≠ d)
    (halt : ¬(strictCyclicBetween (e (c,false)) (e (d,false)) (e (c,true)) ↔
      strictCyclicBetween (e (c,false)) (e (d,true)) (e (c,true)))) :
    componentCount (cyclicSuccessorPerm m * chordSwap e c * chordSwap e d) = 1 := by
  have hsplit : componentCount (cyclicSuccessorPerm m * chordSwap e c) = 2 := by
    change componentCount (cyclicSuccessorPerm m * swap (e (c,false)) (e (c,true))) = 2
    have hsame : (cyclicSuccessorPerm m).SameCycle (e (c,false)) (e (c,true)) := by
      obtain ⟨i, hi⟩ := (cyclicSuccessorPerm_oneTraversal (e (c,false))).2 (e (c,true))
      exact ⟨(i.val + 1 : ℕ), by simpa using hi⟩
    rw [componentCount_mul_swap_of_sameCycle _ (endpoints_ne e he c) hsame,
      cyclicSuccessor_componentCount]
  have hsep : ¬ (cyclicSuccessorPerm m * chordSwap e c).SameCycle
      (e (d,false)) (e (d,true)) := fun h => halt ((after_one_sameCycle_iff e he hcd).1 h)
  have hjoin := componentCount_mul_swap_of_not_sameCycle _ hsep
  change componentCount (cyclicSuccessorPerm m * chordSwap e c * chordSwap e d) + 1 = _ at hjoin
  omega

/-- One alternating pair incurs a strict two-component deficit from the
maximal count, regardless of the remaining selected swaps. -/
theorem componentCount_deficit_of_alternating [NeZero m] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) {c d : C} (hc : c ∈ S) (hd : d ∈ S)
    (hcd : c ≠ d)
    (halt : ¬(strictCyclicBetween (e (c,false)) (e (d,false)) (e (c,true)) ↔
      strictCyclicBetween (e (c,false)) (e (d,true)) (e (c,true)))) :
    componentCount (smoothing e he S) + 2 ≤ S.card + 1 := by
  classical
  have hd' : d ∈ S.erase c := Finset.mem_erase.mpr ⟨Ne.symm hcd, hd⟩
  have hperm : smoothing e he S =
      (cyclicSuccessorPerm m * chordSwap e c * chordSwap e d) *
        swapProduct e he ((S.erase c).erase d) := by
    rw [smoothing, swapProduct_erase e he S c hc,
      swapProduct_erase e he (S.erase c) d hd']
    simp only [mul_assoc]
  have hbound := componentCount_mul_swapProduct_le e he
    (cyclicSuccessorPerm m * chordSwap e c * chordSwap e d) ((S.erase c).erase d)
  rw [alternating_pair_componentCount e he hcd halt, ← hperm] at hbound
  have hcsize := Finset.card_erase_add_one hc
  have hdsize := Finset.card_erase_add_one hd'
  omega

/-- The exact maximal count forces the source pairwise circular relation. -/
theorem nonalternating_of_componentCount [NeZero m] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C)
    (hcount : componentCount (smoothing e he S) = S.card + 1) : Nonalternating e S := by
  by_contra h
  simp only [Nonalternating, not_forall, Classical.not_imp] at h
  obtain ⟨c, hc, d, hd, hcd, halt⟩ := h
  have hdef := componentCount_deficit_of_alternating e he S hc hd hcd halt
  omega

/-- Arbitrary finite-circle version of the source separating-support equivalence.
No count, planarity, genus, splitting or refinement premise is imposed. -/
theorem nonalternating_iff_componentCount [NeZero m] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) :
    Nonalternating e S ↔ componentCount (smoothing e he S) = S.card + 1 :=
  ⟨componentCount_of_nonalternating e he S, nonalternating_of_componentCount e he S⟩

/-- In every prefix of a nonalternating support, the next endpoints still
share one old component. This asserts actual split eligibility in any order. -/
theorem sameCycle_before_insert [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S)
    (hS : Nonalternating e (insert c S)) :
    (smoothing e he S).SameCycle (e (c,false)) (e (c,true)) := by
  have hsep := smoothing_endpoints_separated e he (insert c S) hS c (Finset.mem_insert_self _ _)
  have hjoin := sameCycle_mul_swap_of_not_sameCycle (smoothing e he (insert c S)) hsep
  rw [smoothing_insert e he S c hc, chordSwap] at hjoin
  simpa only [mul_assoc, swap_mul_self, mul_one] using hjoin

/-- Each possible next cut in a nonalternating support refines actual orbits. -/
theorem smoothing_insert_refines [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S)
    (hS : Nonalternating e (insert c S)) {x y : Fin m}
    (hxy : (smoothing e he (insert c S)).SameCycle x y) :
    (smoothing e he S).SameCycle x y := by
  rw [smoothing_insert e he S c hc] at hxy
  exact sameCycle_mul_swap_refines _ (sameCycle_before_insert e he S c hc hS) hxy

/-- All additional nonalternating swaps refine the old incoming-event partition. -/
theorem smoothing_union_refines [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S T : Finset C) (hST : Nonalternating e (S ∪ T))
    {x y : Fin m} (hxy : (smoothing e he (S ∪ T)).SameCycle x y) :
    (smoothing e he S).SameCycle x y := by
  induction T using Finset.induction_on with
  | empty => simpa using hxy
  | @insert c T hc ih =>
      have heq : S ∪ insert c T = insert c (S ∪ T) := by ext; simp
      rw [heq] at hST hxy
      by_cases hc' : c ∈ S ∪ T
      · rw [Finset.insert_eq_of_mem hc'] at hST hxy
        exact ih hST hxy
      · have hbase := hST.mono e (Finset.subset_insert c (S ∪ T))
        exact ih hbase (smoothing_insert_refines e he (S ∪ T) c hc' hST hxy)

/-- Any selected prefix has a coarser partition than the final nonalternating
support. This quantifies over every subset, hence every ordering. -/
theorem smoothing_refines_of_subset (e : C × Bool → Fin m)
    (he : Function.Injective e) (S U : Finset C) (hSU : S ⊆ U)
    (hU : Nonalternating e U) {x y : Fin m}
    (hxy : (smoothing e he U).SameCycle x y) : (smoothing e he S).SameCycle x y := by
  classical
  have heq : S ∪ U = U := Finset.union_eq_right.mpr hSU
  exact smoothing_union_refines e he S U (by simpa [heq] using hU) (by simpa [heq] using hxy)

/-- Every allowed next smoothing step raises the full orbit count by one. -/
theorem componentCount_insert_of_nonalternating [DecidableEq C]
    (e : C × Bool → Fin m) (he : Function.Injective e) (S : Finset C)
    (c : C) (hc : c ∉ S) (hS : Nonalternating e (insert c S)) :
    componentCount (smoothing e he (insert c S)) = componentCount (smoothing e he S) + 1 := by
  rw [smoothing_insert e he S c hc]
  exact componentCount_mul_swap_of_sameCycle _ (endpoints_ne e he c)
    (sameCycle_before_insert e he S c hc hS)

/-- Outgoing original darts use the opposite, literal multiplication order. -/
noncomputable def dartSmoothing (e : C × Bool → Fin m) (he : Function.Injective e)
    (S : Finset C) : Perm (Fin m) := swapProduct e he S * cyclicSuccessorPerm m

/-- The explicit representative map τS transports incoming components to darts. -/
noncomputable def smoothingDartEquiv (e : C × Bool → Fin m) (he : Function.Injective e) (S : Finset C) :
    Component (smoothing e he S) ≃ Component (dartSmoothing e he S) :=
  productOrderEquiv (cyclicSuccessorPerm m) (swapProduct e he S)

@[simp] theorem smoothingDartEquiv_componentOf (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (x : Fin m) :
    smoothingDartEquiv e he S (componentOf (smoothing e he S) x) =
      componentOf (dartSmoothing e he S) (swapProduct e he S x) := rfl

/-- Full component counts agree under the explicit incoming/dart equivalence. -/
theorem dartSmoothing_componentCount (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) :
    componentCount (dartSmoothing e he S) = componentCount (smoothing e he S) :=
  (Fintype.card_congr (smoothingDartEquiv e he S)).symm

/-- The full maximal-count equivalence holds also in the outgoing convention. -/
theorem nonalternating_iff_dart_componentCount [NeZero m] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) :
    Nonalternating e S ↔ componentCount (dartSmoothing e he S) = S.card + 1 := by
  rw [dartSmoothing_componentCount, nonalternating_iff_componentCount]

theorem dartSmoothing_insert [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S) :
    dartSmoothing e he (insert c S) = chordSwap e c * dartSmoothing e he S := by
  rw [dartSmoothing, swapProduct_insert e he S c hc, mul_assoc]
  rfl

/-- An unused chord's endpoints are fixed by τS, so its two conventions have
identical split eligibility on those same ambient labels. -/
theorem dart_sameCycle_before_insert [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S)
    (hS : Nonalternating e (insert c S)) :
    (dartSmoothing e he S).SameCycle (e (c,false)) (e (c,true)) := by
  have hi := (componentOf_eq_iff _ _ _).2 (sameCycle_before_insert e he S c hc hS)
  have hd := congrArg (smoothingDartEquiv e he S) hi
  simp only [smoothingDartEquiv_componentOf,
    swapProduct_endpoint_of_not_mem e he S c hc] at hd
  exact (componentOf_eq_iff _ _ _).1 hd

/-- Every possible next cut refines the actual outgoing-dart partition. -/
theorem dartSmoothing_insert_refines [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S : Finset C) (c : C) (hc : c ∉ S)
    (hS : Nonalternating e (insert c S)) {x y : Fin m}
    (hxy : (dartSmoothing e he (insert c S)).SameCycle x y) :
    (dartSmoothing e he S).SameCycle x y := by
  rw [dartSmoothing_insert e he S c hc] at hxy
  exact sameCycle_swap_mul_refines _ (dart_sameCycle_before_insert e he S c hc hS) hxy

/-- All added nonalternating swaps refine the actual old dart partition. -/
theorem dartSmoothing_union_refines [DecidableEq C] (e : C × Bool → Fin m)
    (he : Function.Injective e) (S T : Finset C) (hST : Nonalternating e (S ∪ T))
    {x y : Fin m} (hxy : (dartSmoothing e he (S ∪ T)).SameCycle x y) :
    (dartSmoothing e he S).SameCycle x y := by
  induction T using Finset.induction_on with
  | empty => simpa using hxy
  | @insert c T hc ih =>
      have heq : S ∪ insert c T = insert c (S ∪ T) := by ext; simp
      rw [heq] at hST hxy
      by_cases hc' : c ∈ S ∪ T
      · rw [Finset.insert_eq_of_mem hc'] at hST hxy
        exact ih hST hxy
      · have hbase := hST.mono e (Finset.subset_insert c (S ∪ T))
        exact ih hbase (dartSmoothing_insert_refines e he (S ∪ T) c hc' hST hxy)

/-- For every subset of a nonalternating final support, the outgoing-dart
component partition refines that of the subset on identical ambient labels. -/
theorem dartSmoothing_refines_of_subset (e : C × Bool → Fin m)
    (he : Function.Injective e) (S U : Finset C) (hSU : S ⊆ U)
    (hU : Nonalternating e U) {x y : Fin m}
    (hxy : (dartSmoothing e he U).SameCycle x y) : (dartSmoothing e he S).SameCycle x y := by
  classical
  have heq : S ∪ U = U := Finset.union_eq_right.mpr hSU
  exact dartSmoothing_union_refines e he S U (by simpa [heq] using hU) (by simpa [heq] using hxy)

end DirectGLSSW.ChordNonalternation
