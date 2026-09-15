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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierOrbitRefinement.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable

/-- If each step of a finite permutation stays in an old orbit, every new
orbit stays in an old orbit. Finite orbits admit natural-power witnesses. -/
theorem sameCycle_refines_of_step {α : Type*} [Finite α] (f g : Equiv.Perm α)
    (hstep : ∀ x, f.SameCycle x (g x)) {x y : α} (hxy : g.SameCycle x y) :
    f.SameCycle x y := by
  obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction k with
  | zero => exact Equiv.Perm.SameCycle.refl f x
  | succ k ih =>
    have hs := ih.trans (hstep ((g ^ k) x))
    simpa only [pow_succ', Equiv.Perm.mul_apply] using hs

/-- A swap between two points of one old orbit keeps each new outgoing step
inside that old orbit. The same-current-orbit premise is explicit. -/
theorem mul_swap_sameCycle_step {α : Type*} [DecidableEq α] (f : Equiv.Perm α)
    (a b : α) (hab : f.SameCycle a b) (x : α) :
    f.SameCycle x ((f * Equiv.swap a b) x) := by
  by_cases hxa : x = a
  · subst x
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using hab.apply_right
  · by_cases hxb : x = b
    · subst x
      simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_right] using hab.symm.apply_right
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
      exact (Equiv.Perm.SameCycle.refl f x).apply_right

theorem sameCycle_mul_swap_refines {α : Type*} [Finite α] [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (hab : f.SameCycle a b) {x y : α}
    (hxy : (f * Equiv.swap a b).SameCycle x y) : f.SameCycle x y :=
  sameCycle_refines_of_step f (f * Equiv.swap a b) (mul_swap_sameCycle_step f a b hab) hxy

variable {n : ℕ} [NeZero n]

/-- Actual reconnection refines old carrier orbits when its two actual visits
are currently together. Independence must later establish this premise. -/
theorem smoothingSuccessor_insert_sameCycle_refines (hn : 3 ≤ n)
    {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))
    (v : Visit P) (hv : v.1 ∉ S)
    (hc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    {a b : Mark P} (hab : (smoothingSuccessor hn hP (insert v.1 S)).SameCycle a b) :
    (smoothingSuccessor hn hP S).SameCycle a b := by
  rw [smoothingSuccessor_insert hn hP S v hv] at hab
  exact sameCycle_mul_swap_refines _ _ _ hc hab

theorem owner_insert_eq_imp (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    {a b : Mark P} (hab : owner hn hP (insert v.1 S) a = owner hn hP (insert v.1 S) b) :
    owner hn hP S a = owner hn hP S b :=
  (owner_eq_iff hn hP S a b).mpr
    (smoothingSuccessor_insert_sameCycle_refines hn hP S v hv hc
      ((owner_eq_iff hn hP (insert v.1 S) a b).mp hab))

/-- Previously separated marked owners remain separated under a split step. -/
theorem owner_insert_ne_of_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    {a b : Mark P} (hab : owner hn hP S a ≠ owner hn hP S b) :
    owner hn hP (insert v.1 S) a ≠ owner hn hP (insert v.1 S) b :=
  fun h => hab (owner_insert_eq_imp hn hP S v hv hc h)

/-- The actual quotient map sends a new component to its unique old component.
Its well-definedness is the proved refinement, not a supplied correspondence. -/
def componentForgetSwitch (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v))) :
    Component hn hP (insert v.1 S) → Component hn hP S :=
  Quotient.map id (fun _ _ hab =>
    smoothingSuccessor_insert_sameCycle_refines hn hP S v hv hc hab)

theorem componentForgetSwitch_owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)))
    (a : Mark P) :
    componentForgetSwitch hn hP S v hv hc (owner hn hP (insert v.1 S) a) =
      owner hn hP S a := rfl

theorem componentForgetSwitch_surjective (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v))) :
    Function.Surjective (componentForgetSwitch hn hP S v hv hc) := by
  intro q
  obtain ⟨a, rfl⟩ := owner_surjective hn hP S q
  exact ⟨owner hn hP (insert v.1 S) a, rfl⟩

/-- The proved quotient map gives a weak count inequality. Strict increase by
one still requires the exact two-child split theorem and independence induction. -/
theorem component_card_le_insert (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S)
    (hc : (smoothingSuccessor hn hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v))) :
    Fintype.card (Component hn hP S) ≤ Fintype.card (Component hn hP (insert v.1 S)) :=
  Fintype.card_le_of_surjective _ (componentForgetSwitch_surjective hn hP S v hv hc)

end
end SM.Carrier
