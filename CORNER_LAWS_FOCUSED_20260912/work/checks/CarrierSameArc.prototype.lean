import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import SM.InterlaceSupports
import Mathlib.Tactic

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


namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {P : LabelledTuple n}

/-- For distinct actual crossings and either ordering of each actual visit pair,
noninterlacement is exactly equality of the two open-arc membership statuses. -/
theorem not_interlaces_iff_same_arc_status (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ Interlaces hn hP x y ↔
      (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ↔
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) := by
  constructor
  · intro hNI
    constructor
    · intro h₀
      by_contra h₁
      exact hNI ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀,
        (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁).mpr h₁⟩
    · intro h₁
      by_contra h₀
      exact hNI ⟨hxy, x₀, x₁, y₁, y₀, hx, hy.symm, h₁,
        (crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₀).mpr h₀⟩
  · intro hsame hI
    obtain ⟨j, hj, hu⟩ := (interlaces_iff_unique hn hP x y x₀ x₁ hx).mp hI |>.2
    have h₀ : crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ := by
      rcases crossing_visits_exhaust y y₀ y₁ hy j with he | he
      · exact he ▸ hj
      · exact hsame.mpr (he ▸ hj)
    exact hy ((hu y₀ h₀).trans (hu y₁ (hsame.mp h₀)).symm)

/-- The equivalent statuses put both actual visits in one of the two oriented
open arcs. The complement law uses distinct crossing positions, so no endpoint
case is silently discarded. -/
theorem not_interlaces_iff_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    ¬ Interlaces hn hP x y ↔
      (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
        crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) ∨
      (crossingVisitBetween hn hP.1 x x₁ x₀ y y₀ ∧
        crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) := by
  rw [not_interlaces_iff_same_arc_status hn hP hxy x₀ x₁ hx y₀ y₁ hy,
    crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₀,
    crossingVisitBetween_complement hn hP hxy x₁ x₀ hx.symm y₁]
  by_cases h₀ : crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ <;>
    by_cases h₁ : crossingVisitBetween hn hP.1 x x₀ x₁ y y₁ <;> simp [h₀, h₁]

/-- No choice of first visit of the second crossing affects its arc membership
when the actual crossings do not interlace. The two input visits may coincide. -/
theorem not_interlaces_all_visits_same_arc (hn : 3 ≤ n) (hP : Generic P)
    {x y : Crossing P} (hxy : x ≠ y) (hNI : ¬ Interlaces hn hP x y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    crossingVisitBetween hn hP.1 x x₀ x₁ y j ↔
      crossingVisitBetween hn hP.1 x x₀ x₁ y k := by
  by_cases hjk : j = k
  · subst k
    exact Iff.rfl
  · exact (not_interlaces_iff_same_arc_status hn hP hxy x₀ x₁ hx j k hjk).mp hNI

/-- Actual independent support supplies noninterlacement for any two distinct
selected crossings; no hypothesis about current carrier ownership is used. -/
theorem independent_crossing_visits_same_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (j k : {i // i ∈ y.val}) :
    crossingVisitBetween hn hP.1 x x₀ x₁ y j ↔
      crossingVisitBetween hn hP.1 x x₀ x₁ y k :=
  not_interlaces_all_visits_same_arc hn hP hxy
    ((mem_independentSupports_iff hn hP S).mp hS x hxS y hyS hxy) x₀ x₁ hx j k

/-- The other selected pair is wholly in one original open arc of the selected
pair, the noninterlacement input needed for the source's splitting induction. -/
theorem independent_crossing_visits_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    {x y : Crossing P} (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (x₀ x₁ : {i // i ∈ x.val}) (hx : x₀ ≠ x₁)
    (y₀ y₁ : {i // i ∈ y.val}) (hy : y₀ ≠ y₁) :
    (crossingVisitBetween hn hP.1 x x₀ x₁ y y₀ ∧
      crossingVisitBetween hn hP.1 x x₀ x₁ y y₁) ∨
    (crossingVisitBetween hn hP.1 x x₁ x₀ y y₀ ∧
      crossingVisitBetween hn hP.1 x x₁ x₀ y y₁) :=
  (not_interlaces_iff_one_open_arc hn hP hxy x₀ x₁ hx y₀ y₁ hy).mp
    ((mem_independentSupports_iff hn hP S).mp hS x hxS y hyS hxy)

/-- The status equivalence for the constructed actual twin pairing, written
literally in physical traversal positions. The pair inequalities are derived
from the checked construction rather than supplied as extra premises. -/
theorem not_interlaces_iff_twin_same_arc (hn : 3 ≤ n) (hP : Generic P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ Interlaces hn hP v.1 w.1 ↔
      (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 (visitTwin v)) ↔
        traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact not_interlaces_iff_same_arc_status hn hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- Noninterlacement places the actual twin pair together on either the forward
or backward open arc of the other actual twin pair, including wraparound. -/
theorem not_interlaces_iff_twin_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    (v w : Visit P) (hvw : v.1 ≠ w.1) :
    ¬ Interlaces hn hP v.1 w.1 ↔
      (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 (visitTwin v)) ∧
        traversalBetween (visitPosition hn hP.1 v)
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) ∨
      (traversalBetween (visitPosition hn hP.1 (visitTwin v)) (visitPosition hn hP.1 w)
          (visitPosition hn hP.1 v) ∧
        traversalBetween (visitPosition hn hP.1 (visitTwin v))
          (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 v)) := by
  have hv : v.2 ≠ (visitTwin v).2 :=
    (Classical.choose_spec (crossing_other_visit v.1 v.2)).symm
  have hw : w.2 ≠ (visitTwin w).2 :=
    (Classical.choose_spec (crossing_other_visit w.1 w.2)).symm
  exact not_interlaces_iff_one_open_arc hn hP hvw
    v.2 (visitTwin v).2 hv w.2 (visitTwin w).2 hw

/-- In an actual independent support, every other selected twin pair lies in
one original oriented open arc of the selected pair. This is a statement about
actual traversal positions, not a supplied current-cycle correspondence. -/
theorem independent_twin_one_open_arc (hn : 3 ≤ n) (hP : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v w : Visit P) (hvS : v.1 ∈ S) (hwS : w.1 ∈ S) (hvw : v.1 ≠ w.1) :
    (traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 (visitTwin v)) ∧
      traversalBetween (visitPosition hn hP.1 v)
        (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 (visitTwin v))) ∨
    (traversalBetween (visitPosition hn hP.1 (visitTwin v)) (visitPosition hn hP.1 w)
        (visitPosition hn hP.1 v) ∧
      traversalBetween (visitPosition hn hP.1 (visitTwin v))
        (visitPosition hn hP.1 (visitTwin w)) (visitPosition hn hP.1 v)) :=
  (not_interlaces_iff_twin_one_open_arc hn hP v w hvw).mp
    ((mem_independentSupports_iff hn hP S).mp hS v.1 hvS w.1 hwS hvw)

end
end SM.Carrier


#print axioms SM.Carrier.not_interlaces_iff_same_arc_status
#print axioms SM.Carrier.not_interlaces_iff_one_open_arc
#print axioms SM.Carrier.not_interlaces_all_visits_same_arc
#print axioms SM.Carrier.independent_crossing_visits_same_arc
#print axioms SM.Carrier.independent_crossing_visits_one_open_arc
#print axioms SM.Carrier.not_interlaces_iff_twin_same_arc
#print axioms SM.Carrier.not_interlaces_iff_twin_one_open_arc
#print axioms SM.Carrier.independent_twin_one_open_arc
