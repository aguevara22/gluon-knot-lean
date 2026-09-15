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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierUnchangedComponent.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual forward successor stays in its incoming owner block for every
support, without independence or inherited-order assumptions. -/
theorem smoothingSuccessor_mapsTo_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    Set.MapsTo (smoothingSuccessor hn hP T)
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} := by
  intro m hm
  exact (owner_successor hn hP T m).trans hm

/-- The inverse actual successor also stays in the same owner block. -/
theorem smoothingSuccessor_symm_mapsTo_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    Set.MapsTo (smoothingSuccessor hn hP T).symm
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} := by
  intro m hm
  exact (owner_predecessor hn hP T m).trans hm

/-- Each actual owner block is invariant bijectively: forward and inverse
preservation provide the restriction of the actual permutation to that block. -/
theorem smoothingSuccessor_bijOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    Set.BijOn (smoothingSuccessor hn hP T)
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} :=
  (smoothingSuccessor hn hP T).bijOn'
    (smoothingSuccessor_mapsTo_owner hn hP T q)
    (smoothingSuccessor_symm_mapsTo_owner hn hP T q)

/-- If a fresh actual crossing's two incoming marks share an old owner, its
insertion changes no outgoing slot in any other actual old owner block. -/
theorem smoothingSuccessor_insert_eqOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v)) :
    Set.EqOn (smoothingSuccessor hn hP (insert v.1 T)) (smoothingSuccessor hn hP T)
      {m | owner hn hP T m = q} := by
  intro m hm
  apply smoothingSuccessor_insert_other hn hP T v hv m
  · intro he
    subst m
    exact hq hm.symm
  · intro he
    subst m
    exact hq (hm.symm.trans hc.symm)

/-- The new actual successor is bijective on every unaffected old owner block,
since its action there agrees with the proved old block bijection. -/
theorem smoothingSuccessor_insert_bijOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v)) :
    Set.BijOn (smoothingSuccessor hn hP (insert v.1 T))
      {m | owner hn hP T m = q} {m | owner hn hP T m = q} :=
  (smoothingSuccessor_insert_eqOn_owner hn hP T v hv hc q hq).bijOn_iff.mpr
    (smoothingSuccessor_bijOn_owner hn hP T q)

/-- Backward traversal on an unaffected old owner block is unchanged as well.
The old inverse remains in that block, where the two forward actions agree. -/
theorem smoothingSuccessor_insert_symm_eqOn_owner (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)))
    (q : Component hn hP T) (hq : q ≠ owner hn hP T (Sum.inr v)) :
    Set.EqOn (smoothingSuccessor hn hP (insert v.1 T)).symm (smoothingSuccessor hn hP T).symm
      {m | owner hn hP T m = q} := by
  intro m hm
  have hx : owner hn hP T ((smoothingSuccessor hn hP T).symm m) = q :=
    (owner_predecessor hn hP T m).trans hm
  have he := smoothingSuccessor_insert_eqOn_owner hn hP T v hv hc q hq hx
  apply (smoothingSuccessor hn hP (insert v.1 T)).injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]

end
end SM.Carrier
