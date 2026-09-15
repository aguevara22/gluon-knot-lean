namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The original traversal's cyclic order restricted to one actual successor
orbit. Compatibility with the reconnected successor is a separate invariant. -/
def componentCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) : Cycle (Mark P) :=
  (markCycle hn hP).filter (fun m => decide (owner hn hP T m = q))

/-- Filtering the complete sorted representative represents the inherited
component cycle. The definition is independent of the chosen first mark. -/
theorem componentCycle_eq_filtered_markList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T) :
    componentCycle hn hP T q =
      ((markList hn hP).filter (fun m => decide (owner hn hP T m = q)) : Cycle (Mark P)) := rfl

/-- Every actual mark occurs in the original circle, so the sole membership
condition in its inherited component cycle is its actual incoming owner. -/
@[simp]
theorem mem_componentCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) (m : Mark P) :
    m ∈ componentCycle hn hP T q ↔ owner hn hP T m = q := by
  simp [componentCycle, Cycle.mem_filter, mem_markCycle]

/-- Restriction retains the original marked circle's absence of repetitions. -/
theorem componentCycle_nodup (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) :
    (componentCycle hn hP T q).Nodup :=
  (markCycle_nodup hn hP).filter (fun m => decide (owner hn hP T m = q))

/-- Every mark belongs to the inherited cycle of its constructed owner. -/
theorem mem_componentCycle_owner (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (m : Mark P) :
    m ∈ componentCycle hn hP T (owner hn hP T m) :=
  (mem_componentCycle hn hP T _ m).mpr rfl

/-- Each actual quotient component has a mark representative; filtering cannot
make its inherited component cycle empty. No crossing-nonempty premise enters. -/
theorem componentCycle_nonempty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (T : Finset (Crossing P)) (q : Component hn hP T) :
    ∃ m : Mark P, m ∈ componentCycle hn hP T q := by
  obtain ⟨m, hm⟩ := owner_surjective hn hP T q
  exact ⟨m, (mem_componentCycle hn hP T q m).mpr hm⟩

/-- Distinct actual components have disjoint mark membership in their inherited
cycles, since every incoming mark has one quotient owner. -/
theorem componentCycle_members_disjoint (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q r : Component hn hP T)
    (hqr : q ≠ r) (m : Mark P) :
    m ∈ componentCycle hn hP T q → m ∉ componentCycle hn hP T r := by
  intro hq hr
  exact hqr (((mem_componentCycle hn hP T q m).mp hq).symm.trans
    ((mem_componentCycle hn hP T r m).mp hr))

/-- Distinct quotient components yield distinct inherited cycles. The proof
uses an actual representative of the nonempty component, not a cycle count. -/
theorem componentCycle_injective (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) :
    Function.Injective (componentCycle hn hP T) := by
  intro q r he
  obtain ⟨m, hm⟩ := componentCycle_nonempty hn hP T q
  have hr : m ∈ componentCycle hn hP T r := he ▸ hm
  exact ((mem_componentCycle hn hP T q m).mp hm).symm.trans
    ((mem_componentCycle hn hP T r m).mp hr)

/-- At empty support every actual mark has the unique original component owner,
so filtering retains the complete original marked circle. -/
theorem componentCycle_empty (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (q : Component hn hP ∅) : componentCycle hn hP ∅ q = markCycle hn hP := by
  unfold componentCycle
  apply Cycle.filter_eq_self
  intro m _
  have hm : owner hn hP ∅ m = q := (component_empty_subsingleton hn hP).elim _ _
  simp only [hm, decide_true]

/-- A rotation giving the original split-list presentation filters literally
between its two retained endpoints. Both filtered intervening lists may be empty;
this identity makes no claim about the current successor on the filtered cycle. -/
theorem componentCycle_eq_filtered_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T)
    (k : ℕ) (a b : Mark P) (A B : List (Mark P))
    (hrot : (markList hn hP).rotate k = a :: (A ++ b :: B))
    (ha : owner hn hP T a = q) (hb : owner hn hP T b = q) :
    componentCycle hn hP T q =
      (a :: (A.filter (fun m => decide (owner hn hP T m = q)) ++
        b :: B.filter (fun m => decide (owner hn hP T m = q))) : Cycle (Mark P)) := by
  have hc : markCycle hn hP = (a :: (A ++ b :: B) : Cycle (Mark P)) := by
    rw [← hrot]
    exact (markCycle_rotation hn hP k).symm
  rw [componentCycle, hc, Cycle.filter_coe]
  simp [List.filter_append, ha, hb]

end
end SM.Carrier
