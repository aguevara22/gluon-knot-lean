import SM.GaussVisits
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Cycle
import Mathlib.Data.Finset.Card

/-! The Gauss sequence is constructed by sorting all actual visits in the
traversal order, then forgetting the choice of first visit via the genuine
rotation quotient. Cyclic relabelling compatibility is proved separately. -/

namespace SM

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

@[instance_reducible]
noncomputable def visitLinearOrder (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    LinearOrder (Visit P) := LinearOrder.lift' (visitKey hn hP.1) (visitKey_injective hn hP)

noncomputable def gaussList (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    List (Visit P) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  letI := visitLinearOrder hn hP
  exact Finset.univ.sort

theorem gaussList_nodup (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (gaussList hn hP).Nodup := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  letI := visitLinearOrder hn hP
  exact Finset.sort_nodup _ _

theorem mem_gaussList (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) : v ∈ gaussList hn hP := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  letI := visitLinearOrder hn hP
  exact (Finset.mem_sort _).mpr (Finset.mem_univ v)

theorem gaussList_toFinset [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) : (gaussList hn hP).toFinset = Finset.univ := by
  classical
  ext v
  simp [mem_gaussList hn hP v]

theorem gaussList_sorted (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (gaussList hn hP).Pairwise (fun v w => visitKey hn hP.1 v ≤ visitKey hn hP.1 w) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  letI := visitLinearOrder hn hP
  exact Finset.pairwise_sort _ _

theorem gaussList_length (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (gaussList hn hP).length = 2 * Nat.card (Crossing P) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  letI := visitLinearOrder hn hP
  change (Finset.univ.sort (α := Visit P)).length = _
  rw [Finset.length_sort, Finset.card_univ, card_visit, Nat.card_eq_fintype_card, card_crossing]

def visitCrossingFiber (P : LabelledTuple n) (c : Crossing P) :
    {v : Visit P // v.1 = c} ≃ {i // i ∈ c.val} where
  toFun v := ⟨v.val.2.val, by simpa only [v.property] using v.val.2.property⟩
  invFun i := ⟨⟨c, i⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨d, i⟩, hd⟩
    dsimp only at hd
    cases hd
    rfl
  right_inv _ := rfl

theorem gaussList_crossing_count (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (c : Crossing P) :
    (gaussList hn hP).countP (fun v => decide (v.1 = c)) = 2 := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  rw [← (gaussList_nodup hn hP).card_eq_countP, gaussList_toFinset]
  rw [← Fintype.card_subtype (fun v : Visit P => v.1 = c)]
  rw [Fintype.card_congr (visitCrossingFiber P c), visits_per_crossing]

/-- The actual cyclic sequence of visits. Its entries retain their edge visit
and crossing identity; there is no arbitrary naming or chosen traversal root. -/
noncomputable def gaussCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Cycle (Visit P) := (gaussList hn hP : Cycle (Visit P))

/-- The same cyclic sequence with each visit labelled by its crossing. -/
noncomputable def gaussWord (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Cycle (Crossing P) := (gaussCycle hn hP).map Sigma.fst

theorem gaussCycle_length (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    (gaussCycle hn hP).length = 2 * Nat.card (Crossing P) := gaussList_length hn hP

theorem gaussCycle_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (k : ℕ) :
    ((gaussList hn hP).rotate k : Cycle (Visit P)) = gaussCycle hn hP :=
  Cycle.coe_eq_coe.mpr (List.IsRotated.forall _ _)

theorem gaussWord_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (k : ℕ) :
    (((gaussList hn hP).rotate k).map Sigma.fst : Cycle (Crossing P)) = gaussWord hn hP := by
  change Cycle.map Sigma.fst (((gaussList hn hP).rotate k : Cycle (Visit P))) = _
  rw [gaussCycle_rotation]
  rfl

end SM
