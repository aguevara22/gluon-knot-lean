namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Exchange the two actual visits of each selected crossing, fixing every
original vertex. No independence hypothesis is needed for this permutation. -/
def selectedMarkPerm {P : LabelledTuple n} (S : Finset (Crossing P)) :
    Equiv.Perm (Mark P) :=
  Equiv.sumCongr (Equiv.refl (ZMod n)) (selectedVisitTwinPerm S)

@[simp]
theorem selectedMarkPerm_vertex {P : LabelledTuple n} (S : Finset (Crossing P))
    (i : ZMod n) : selectedMarkPerm S (Sum.inl i) = Sum.inl i := rfl

@[simp]
theorem selectedMarkPerm_visit {P : LabelledTuple n} (S : Finset (Crossing P))
    (v : Visit P) : selectedMarkPerm S (Sum.inr v) = Sum.inr (selectedVisitTwin S v) := rfl

theorem selectedMarkPerm_involutive {P : LabelledTuple n} (S : Finset (Crossing P))
    (a : Mark P) : selectedMarkPerm S (selectedMarkPerm S a) = a := by
  cases a <;> simp

/-- Both visits of a crossing evaluate to the same physical crossing point,
so switching them preserves the geometric endpoint at the reconnection. -/
theorem selectedMarkPerm_evaluation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (S : Finset (Crossing P)) (a : Mark P) :
    traversalEvaluation P (markPosition hn hP (selectedMarkPerm S a)) =
      traversalEvaluation P (markPosition hn hP a) := by
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, markPosition_evaluation_visit,
      markPosition_evaluation_visit, selectedVisitTwin_crossing]

theorem selectedMarkPerm_commute {P : LabelledTuple n} (S T : Finset (Crossing P))
    (a : Mark P) : selectedMarkPerm S (selectedMarkPerm T a) =
      selectedMarkPerm T (selectedMarkPerm S a) := by
  cases a with
  | inl i => rfl
  | inr v => exact congrArg Sum.inr (selectedVisitTwin_commute S T v)

/-- Disjoint selected supports reconnect each actual outgoing slot once. -/
theorem selectedMarkPerm_union_of_disjoint {P : LabelledTuple n}
    (S T : Finset (Crossing P)) (hST : Disjoint S T) :
    selectedMarkPerm (S ∪ T) = (selectedMarkPerm T).trans (selectedMarkPerm S) := by
  ext a
  cases a with
  | inl i => rfl
  | inr v => exact congrArg Sum.inr (selectedVisitTwin_union_of_disjoint S T hST v)

/-- The source outgoing reconnection rule: at a selected visit, take the
original outgoing arc of its twin; otherwise retain the original outgoing arc. -/
def smoothingSuccessor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Equiv.Perm (Mark P) :=
  (selectedMarkPerm S).trans (markSuccessor hn hP)

theorem smoothingSuccessor_vertex (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (i : ZMod n) :
    smoothingSuccessor hn hP S (Sum.inl i) = markSuccessor hn hP (Sum.inl i) := rfl

theorem smoothingSuccessor_visit_of_mem (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    smoothingSuccessor hn hP S (Sum.inr v) =
      markSuccessor hn hP (Sum.inr (visitTwin v)) := by
  change markSuccessor hn hP (Sum.inr (selectedVisitTwin S v)) = _
  rw [selectedVisitTwin_of_mem S v hv]

theorem smoothingSuccessor_visit_of_not_mem (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∉ S) :
    smoothingSuccessor hn hP S (Sum.inr v) = markSuccessor hn hP (Sum.inr v) := by
  change markSuccessor hn hP (Sum.inr (selectedVisitTwin S v)) = _
  rw [selectedVisitTwin_of_not_mem S v hv]

theorem smoothingSuccessor_empty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    smoothingSuccessor hn hP ∅ = markSuccessor hn hP := by
  ext a
  cases a with
  | inl i => rfl
  | inr v =>
    change markSuccessor hn hP (Sum.inr (selectedVisitTwin ∅ v)) = _
    rw [selectedVisitTwin_empty]
    rfl

/-- Adding disjoint switches acts on outgoing slots of the already reconnected
successor. This is an equality of the constructed permutations. -/
theorem smoothingSuccessor_union_of_disjoint (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S T : Finset (Crossing P)) (hST : Disjoint S T) :
    smoothingSuccessor hn hP (S ∪ T) =
      (selectedMarkPerm T).trans (smoothingSuccessor hn hP S) := by
  rw [smoothingSuccessor, selectedMarkPerm_union_of_disjoint S T hST]
  rfl

/-- Actual cyclic components are the orbits of the constructed finite successor.
Their geometric regularity and independent-support count remain separate claims. -/
def Component (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) :=
  Quotient (Equiv.Perm.SameCycle.setoid (smoothingSuccessor hn hP S))

/-- A mark belongs to its own successor orbit. Keeping the node identity at a
reconnection implements the incoming-arc ownership convention. -/
def owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) : Component hn hP S :=
  Quotient.mk _ a

theorem owner_eq_iff (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a b : Mark P) :
    owner hn hP S a = owner hn hP S b ↔ (smoothingSuccessor hn hP S).SameCycle a b :=
  ⟨Quotient.exact, Quotient.sound⟩

theorem owner_successor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    owner hn hP S (smoothingSuccessor hn hP S a) = owner hn hP S a :=
  (owner_eq_iff hn hP S _ _).mpr (Equiv.Perm.SameCycle.refl _ a).apply_left

theorem owner_predecessor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (a : Mark P) :
    owner hn hP S ((smoothingSuccessor hn hP S).symm a) = owner hn hP S a :=
  (owner_eq_iff hn hP S _ _).mpr (Equiv.Perm.SameCycle.refl _ a).symm_apply_left

theorem owner_surjective (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Function.Surjective (owner hn hP S) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact ⟨a, rfl⟩

instance componentFintype (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : Fintype (Component hn hP S) :=
  Quotient.fintype _

theorem component_card_pos (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) : 0 < Fintype.card (Component hn hP S) :=
  Fintype.card_pos_iff.mpr ⟨owner hn hP S (Sum.inl (0 : ZMod n))⟩

/-- The empty support has a single actual component, since the unmodified
successor traverses every mark. -/
theorem component_empty_subsingleton (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) : Subsingleton (Component hn hP ∅) := by
  constructor
  intro q r
  obtain ⟨a, rfl⟩ := owner_surjective hn hP ∅ q
  obtain ⟨b, rfl⟩ := owner_surjective hn hP ∅ r
  apply (owner_eq_iff hn hP ∅ a b).mpr
  rw [smoothingSuccessor_empty]
  exact markSuccessor_sameCycle hn hP a b

theorem component_card_empty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) :
    Fintype.card (Component hn hP ∅) = 1 := by
  letI := component_empty_subsingleton hn hP
  letI : Inhabited (Component hn hP ∅) := ⟨owner hn hP ∅ (Sum.inl (0 : ZMod n))⟩
  exact Fintype.card_unique

end
end SM.Carrier
