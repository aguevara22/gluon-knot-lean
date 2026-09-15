namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Process any subset of an actual independent support. The induction maintains
both inherited cyclic order and co-location of every unprocessed actual twin pair. -/
theorem independent_partial_invariants (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) :
    InheritsMarkOrder hn hP T ∧ PendingPairsTogether hn hP S T := by
  revert hTS
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨inheritsMarkOrder_empty hn hP, pendingPairsTogether_empty hn hP S⟩
  | @insert c T hc ih =>
    intro hTS
    have hcS : c ∈ S := hTS (Finset.mem_insert_self c T)
    have hTS' : T ⊆ S := fun z hz => hTS (Finset.mem_insert_of_mem hz)
    obtain ⟨hI, hPending⟩ := ih hTS'
    obtain ⟨i, j, hij⟩ := crossing_visits_exist c
    let v : Visit P := ⟨c, i⟩
    have hvS : v.1 ∈ S := hcS
    have hv : v.1 ∉ T := hc
    have hsame := hPending v hvS hv
    exact ⟨inheritsMarkOrder_insert hn hP T hI v hv hsame,
      pendingPairsTogether_insert hn hP hS T hI hPending v hvS hv⟩

/-- Every actual independent support inherits the original marked cyclic order.
All current-order and same-component induction premises have been discharged. -/
theorem independent_inheritsMarkOrder (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP) :
    InheritsMarkOrder hn hP S :=
  (independent_partial_invariants hn hP hS S (Finset.Subset.refl S)).1

/-- For any partially processed independent support, every remaining actual
crossing still has both visits on a single actual current component. -/
theorem independent_remaining_pair_owners (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (T : Finset (Crossing P)) (hTS : T ⊆ S) (v : Visit P)
    (hvS : v.1 ∈ S) (hv : v.1 ∉ T) :
    owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v)) :=
  (independent_partial_invariants hn hP hS T hTS).2 v hvS hv

/-- The two incoming visits of every selected actual crossing have distinct
final owners. Process all other selected crossings first, then use the exact
actual final split; the support permutation is already independent of order. -/
theorem independent_selected_pair_owners_ne (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (v : Visit P) (hvS : v.1 ∈ S) :
    owner hn hP S (Sum.inr v) ≠ owner hn hP S (Sum.inr (visitTwin v)) := by
  let T := S.erase v.1
  have hTS : T ⊆ S := Finset.erase_subset _ _
  have hv : v.1 ∉ T := by simp [T]
  obtain ⟨hI, hPending⟩ := independent_partial_invariants hn hP hS T hTS
  have hc := hPending v hvS hv
  obtain ⟨k, A, B, hrot, hNL, hNR, hd, hleft, hright, hactL, hactR⟩ :=
    smoothingSuccessor_insert_child_data hn hP T hI v hv hc
  have hne : owner hn hP (insert v.1 T) (Sum.inr v) ≠
      owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) := by
    intro he
    have hbL := (hleft (Sum.inr (visitTwin v))).mp he.symm
    exact hd hbL List.mem_cons_self
  have hins : insert v.1 T = S := Finset.insert_erase hvS
  exact Eq.mp (congrArg (fun U : Finset (Crossing P) =>
    owner hn hP U (Sum.inr v) ≠ owner hn hP U (Sum.inr (visitTwin v))) hins) hne

end
end SM.Carrier
