import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import SM.InterlaceSupports
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import SM.CarrierMarks
import SM.CarrierSuccessor
import SM.CarrierVisitTwin
import SM.CarrierSmoothing
import SM.CarrierSingleSwitch
import SM.CarrierOrbitRefinement
import SM.CycleFiltering
import SM.CarrierFilteredCycles
import SM.CarrierCycleList
import SM.CarrierSplitList
import SM.CarrierSingleSupport
import SM.CarrierInheritedOrder
import SM.CarrierCurrentCycle
import SM.CarrierAmbientTransport
import SM.CarrierUnchangedComponent
import SM.CarrierInsertOrbits

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierComponentFibers.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual quotient forget map has exactly two elements over the affected
old owner: the distinct new incoming owners of the inserted crossing's visits.
Completeness uses the same original split rotation as the checked child data. -/
theorem componentForgetSwitch_fiber_affected (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v))) :
    owner hn hP (insert v.1 T) (Sum.inr v) ≠
        owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) ∧
      (Finset.univ.filter (fun r =>
        componentForgetSwitch hn hP T v hv
          ((owner_eq_iff hn hP T (Sum.inr v) (Sum.inr (visitTwin v))).mp hc) r =
            owner hn hP T (Sum.inr v))) =
        {owner hn hP (insert v.1 T) (Sum.inr v),
          owner hn hP (insert v.1 T) (Sum.inr (visitTwin v))} := by
  obtain ⟨k, A, B, hrot, hNLeft, hNRight, hdisjoint,
      hleft, hright, hactLeft, hactRight⟩ :=
    smoothingSuccessor_insert_child_data hn hP T hI v hv hc
  have hcOrbit := (owner_eq_iff hn hP T (Sum.inr v) (Sum.inr (visitTwin v))).mp hc
  refine ⟨?_, ?_⟩
  · intro he
    have hbLeft := (hleft (Sum.inr (visitTwin v))).mp he.symm
    exact hdisjoint hbLeft List.mem_cons_self
  · ext r
    obtain ⟨m, rfl⟩ := owner_surjective hn hP (insert v.1 T) r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      componentForgetSwitch_owner, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hm
      have hfull : m ∈ Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B) := by
        rw [← hrot]
        exact List.mem_rotate.mpr (mem_markList hn hP m)
      rcases List.mem_cons.mp hfull with he | hfull
      · subst m
        exact Or.inl rfl
      · rcases List.mem_append.mp hfull with hmA | hmB
        · have hmAL : m ∈ A.filter
              (fun x => decide (owner hn hP T x = owner hn hP T (Sum.inr v))) :=
            List.mem_filter.mpr ⟨hmA, by simpa only [decide_eq_true_eq] using hm⟩
          exact Or.inr ((hright m).mpr (List.mem_cons_of_mem _ hmAL))
        · rcases List.mem_cons.mp hmB with he | hmB
          · subst m
            exact Or.inr rfl
          · have hmBL : m ∈ B.filter
                (fun x => decide (owner hn hP T x = owner hn hP T (Sum.inr v))) :=
              List.mem_filter.mpr ⟨hmB, by simpa only [decide_eq_true_eq] using hm⟩
            exact Or.inl ((hleft m).mpr (List.mem_cons_of_mem _ hmBL))
    · rintro (he | he)
      · exact owner_insert_eq_imp hn hP T v hv hcOrbit he
      · exact (owner_insert_eq_imp hn hP T v hv hcOrbit he).trans hc.symm

/-- Every unaffected old component has one element in the actual forget-map
fiber, namely the new owner of any of its actual marks. Its representative is
supplied as a mark with its old-owner equality, not as a component correspondence. -/
theorem componentForgetSwitch_fiber_unaffected (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v))
    (m : Mark P) (hm : owner hn hP T m = q) :
    (Finset.univ.filter (fun r =>
      componentForgetSwitch hn hP T v hv
        ((owner_eq_iff hn hP T (Sum.inr v) (Sum.inr (visitTwin v))).mp hc) r = q)) =
      {owner hn hP (insert v.1 T) m} := by
  ext r
  obtain ⟨z, rfl⟩ := owner_surjective hn hP (insert v.1 T) r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    componentForgetSwitch_owner, Finset.mem_singleton]
  exact (owner_insert_iff_of_unaffected hn hP T v hv hc q hq m hm z).symm

end
end SM.Carrier
