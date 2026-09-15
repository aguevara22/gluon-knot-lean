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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierVisitTwin.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {P : LabelledTuple n}

/-- The other actual visit of the same crossing, chosen from its proved two-visit fiber. -/
def visitTwin (v : Visit P) : Visit P :=
  ⟨v.1, Classical.choose (crossing_other_visit v.1 v.2)⟩

@[simp]
theorem visitTwin_crossing (v : Visit P) : (visitTwin v).1 = v.1 := rfl

/-- The twin is distinct because the chosen crossing member is the other member. -/
theorem visitTwin_ne (v : Visit P) : visitTwin v ≠ v := by
  intro h
  have he := congrArg (fun w : Visit P => w.2.val) h
  exact (Classical.choose_spec (crossing_other_visit v.1 v.2)) (Subtype.ext he)

/-- No visit in this actual crossing fiber is omitted by the two named visits. -/
theorem visit_eq_or_twin (v w : Visit P) (hc : w.1 = v.1) :
    w = v ∨ w = visitTwin v := by
  rcases v with ⟨c, i⟩
  rcases w with ⟨d, j⟩
  change d = c at hc
  subst d
  let k := Classical.choose (crossing_other_visit c i)
  have hik : i ≠ k := (Classical.choose_spec (crossing_other_visit c i)).symm
  rcases crossing_visits_exhaust c i k hik j with he | he
  · exact Or.inl (congrArg (fun l : {k // k ∈ c.val} => (⟨c, l⟩ : Visit P)) he)
  · exact Or.inr (congrArg (fun l : {k // k ∈ c.val} => (⟨c, l⟩ : Visit P)) he)

/-- The distinct visit with the same crossing is uniquely the constructed twin. -/
theorem visitTwin_unique (v w : Visit P) (hc : w.1 = v.1) (hne : w ≠ v) :
    w = visitTwin v :=
  (visit_eq_or_twin v w hc).resolve_left hne

@[simp]
theorem visitTwin_involutive (v : Visit P) : visitTwin (visitTwin v) = v := by
  exact (visitTwin_unique (visitTwin v) v (visitTwin_crossing v).symm
    (visitTwin_ne v).symm).symm

/-- The actual crossing pairing, with the same constructed twin as inverse. -/
def visitTwinPerm : Equiv.Perm (Visit P) where
  toFun := visitTwin
  invFun := visitTwin
  left_inv := visitTwin_involutive
  right_inv := visitTwin_involutive

@[simp]
theorem visitTwinPerm_apply (v : Visit P) : visitTwinPerm v = visitTwin v := rfl

/-- Exchange only the two visits of each selected actual crossing. -/
def selectedVisitTwin (S : Finset (Crossing P)) (v : Visit P) : Visit P :=
  if v.1 ∈ S then visitTwin v else v

theorem selectedVisitTwin_of_mem (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∈ S) : selectedVisitTwin S v = visitTwin v :=
  if_pos hv

theorem selectedVisitTwin_of_not_mem (S : Finset (Crossing P)) (v : Visit P)
    (hv : v.1 ∉ S) : selectedVisitTwin S v = v :=
  if_neg hv

@[simp]
theorem selectedVisitTwin_crossing (S : Finset (Crossing P)) (v : Visit P) :
    (selectedVisitTwin S v).1 = v.1 := by
  by_cases hv : v.1 ∈ S <;> simp [selectedVisitTwin, hv]

@[simp]
theorem selectedVisitTwin_involutive (S : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwin S (selectedVisitTwin S v) = v := by
  by_cases hv : v.1 ∈ S <;>
    simp [selectedVisitTwin, hv, visitTwin_crossing, visitTwin_involutive]

/-- This selected permutation is obtained from actual crossing membership and pairing. -/
def selectedVisitTwinPerm (S : Finset (Crossing P)) : Equiv.Perm (Visit P) where
  toFun := selectedVisitTwin S
  invFun := selectedVisitTwin S
  left_inv := selectedVisitTwin_involutive S
  right_inv := selectedVisitTwin_involutive S

@[simp]
theorem selectedVisitTwinPerm_apply (S : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwinPerm S v = selectedVisitTwin S v := rfl

@[simp]
theorem selectedVisitTwin_empty : selectedVisitTwin (∅ : Finset (Crossing P)) = id := by
  funext v
  simp [selectedVisitTwin]

/-- Exactly the visits of unselected crossings are fixed. -/
theorem selectedVisitTwin_eq_self_iff (S : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwin S v = v ↔ v.1 ∉ S := by
  by_cases hv : v.1 ∈ S <;> simp [selectedVisitTwin, hv, visitTwin_ne]

/-- The actual selected swaps commute, even when the supports overlap. -/
theorem selectedVisitTwin_commute (S T : Finset (Crossing P)) (v : Visit P) :
    selectedVisitTwin S (selectedVisitTwin T v) =
      selectedVisitTwin T (selectedVisitTwin S v) := by
  by_cases hs : v.1 ∈ S <;> by_cases ht : v.1 ∈ T <;>
    simp [selectedVisitTwin, hs, ht, visitTwin_crossing, visitTwin_involutive]

/-- For disjoint crossing supports, composition exchanges each selected pair once.
This gives the support-union step for order-independent reconnections. -/
theorem selectedVisitTwin_union_of_disjoint (S T : Finset (Crossing P))
    (hST : Disjoint S T) (v : Visit P) :
    selectedVisitTwin (S ∪ T) v = selectedVisitTwin S (selectedVisitTwin T v) := by
  by_cases hs : v.1 ∈ S
  · have ht : v.1 ∉ T := fun ht => (Finset.disjoint_left.mp hST) hs ht
    simp [selectedVisitTwin, Finset.mem_union, hs, ht]
  · by_cases ht : v.1 ∈ T <;>
      simp [selectedVisitTwin, Finset.mem_union, hs, ht, visitTwin_crossing]

end
end SM.Carrier
