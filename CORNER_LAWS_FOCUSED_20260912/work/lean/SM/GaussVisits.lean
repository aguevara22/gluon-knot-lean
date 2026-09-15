import SM.Traversal
import Mathlib.Data.Fintype.BigOperators

/-! Actual visits of crossings to the half-open traversal circle. This file
proves finiteness, two visits per crossing, the 2|X(P)| total, and injectivity
of their actual traversal positions. No arbitrary word or graph is supplied. -/

namespace SM

variable {n : ℕ}

noncomputable instance crossingFintype [NeZero n] (P : LabelledTuple n) :
    Fintype (Crossing P) := by
  classical
  exact (crossing_set_finite P).fintype

abbrev Visit (P : LabelledTuple n) := Σ c : Crossing P, {i // i ∈ c.val}

noncomputable instance visitFintype [NeZero n] (P : LabelledTuple n) : Fintype (Visit P) := by
  classical
  infer_instance

def crossingSetEquiv [NeZero n] (P : LabelledTuple n) : Crossing P ≃ (crossingSet P) where
  toFun c := ⟨c.val, (mem_crossingSet P c.val).mpr c.property⟩
  invFun c := ⟨c.val, (mem_crossingSet P c.val).mp c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_crossing [NeZero n] (P : LabelledTuple n) :
    Fintype.card (Crossing P) = (crossingSet P).card := by
  classical
  rw [Fintype.card_congr (crossingSetEquiv P), Fintype.card_coe]

theorem visits_per_crossing (P : LabelledTuple n) (c : Crossing P) :
    Fintype.card {i // i ∈ c.val} = 2 := by
  rw [Fintype.card_coe, crossing_card_two c]

theorem card_visit [NeZero n] (P : LabelledTuple n) :
    Fintype.card (Visit P) = 2 * (crossingSet P).card := by
  classical
  rw [Fintype.card_sigma]
  simp only [visits_per_crossing]
  simp [card_crossing, Nat.mul_comm]

noncomputable def visitParameter {P : LabelledTuple n} (v : Visit P) : ℝ :=
  crossingParameter v.1 v.2.val v.2.property

noncomputable def visitPosition (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : TraversalPoint n :=
  (v.2.val, ⟨visitParameter v,
    (crossingParameter_interior hn hP v.1 v.2.val v.2.property).1.le,
    (crossingParameter_interior hn hP v.1 v.2.val v.2.property).2⟩)

theorem visitPosition_edge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : (visitPosition hn hP v).1 = v.2.val := rfl

theorem visitPosition_parameter (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : (visitPosition hn hP v).2.val = visitParameter v := rfl

theorem visitPosition_interior (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : 0 < visitParameter v ∧ visitParameter v < 1 :=
  crossingParameter_interior hn hP v.1 v.2.val v.2.property

theorem visitPosition_evaluation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : traversalEvaluation P (visitPosition hn hP v) = crossingPoint v.1 :=
  (crossingParameter_spec v.1 v.2.val v.2.property).2.2.symm

theorem visitPosition_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Function.Injective (visitPosition hn hP.1) := by
  intro v w hpos
  have hp : crossingPoint v.1 = crossingPoint w.1 := by
    rw [← visitPosition_evaluation hn hP.1 v, ← visitPosition_evaluation hn hP.1 w, hpos]
  have hc := generic_crossingPoint_injective hn hP hp
  have he : v.2.val = w.2.val := congrArg Prod.fst hpos
  cases v with
  | mk c i =>
    cases w with
    | mk d j =>
      dsimp only at hc he
      cases hc
      have hij : i = j := Subtype.ext he
      cases hij
      rfl

noncomputable def visitKey (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (v : Visit P) : ℝ := traversalKey (visitPosition hn hP v)

theorem visitKey_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Function.Injective (visitKey hn hP.1) := by
  haveI : NeZero n := ⟨by omega⟩
  exact traversalKey_injective.comp (visitPosition_injective hn hP)

def visitShift (a : ZMod n) {P : LabelledTuple n} (v : Visit P) : Visit (shift a P) :=
  ⟨crossingShift a v.1, v.2.val - a, mem_crossingShift a v.1 v.2.val v.2.property⟩

theorem visitParameter_shift (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (a : ZMod n) (v : Visit P) : visitParameter (visitShift a v) = visitParameter v :=
  crossingParameter_shift hn hP a v.1 v.2.val v.2.property

theorem visitPosition_shift (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (a : ZMod n) (v : Visit P) :
    visitPosition hn (g1_shift_forward a hP) (visitShift a v) =
      traversalShift a (visitPosition hn hP v) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact visitParameter_shift hn hP a v

end SM
