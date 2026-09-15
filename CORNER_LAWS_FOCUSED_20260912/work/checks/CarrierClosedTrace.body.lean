namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual inherited marked representative of one successor component:
the complete original marked list filtered by its constructed owner. -/
def componentMarkList (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : List (Mark P) :=
  (markList hn hP).filter (fun m => decide (owner hn hP S m = q))

/-- The evaluated finite plane cycle retains every marked list entry. Equal
plane values are not identified, so the actual visit labels remain in the
separate componentMarkList. This is not yet a continuous circle map. -/
def componentPlaneCycle (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Cycle Plane :=
  ((componentMarkList hn hP S q).map
    (fun m => traversalEvaluation P (markPosition hn hP.1 m)) : Cycle Plane)

/-- The constructed list is nonempty and duplicate-free as a list of marks,
represents the actual inherited component cycle, and contains exactly its owners. -/
theorem componentMarkList_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S) :
    (componentMarkList hn hP S q).Nodup ∧
      0 < (componentMarkList hn hP S q).length ∧
      (componentMarkList hn hP S q : Cycle (Mark P)) = componentCycle hn hP S q ∧
      ∀ m : Mark P, m ∈ componentMarkList hn hP S q ↔ owner hn hP S m = q := by
  let L := componentMarkList hn hP S q
  have hL : componentCycle hn hP S q = (L : Cycle (Mark P)) :=
    componentCycle_eq_filtered_markList hn hP S q
  have hmem := componentCycle_list_mem_iff hn hP S q L hL
  obtain ⟨m, hm⟩ := owner_surjective hn hP S q
  exact ⟨componentCycle_list_nodup hn hP S q L hL,
    List.length_pos_of_mem ((hmem m).mpr hm), hL.symm, hmem⟩

/-- Independence supplies inherited order for the actual filtered list. Its
cyclic next index, including the last-to-first step, is the smoothed successor. -/
theorem componentMarkList_getElem_successor (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (i : Fin (componentMarkList hn hP S q).length) :
    let L := componentMarkList hn hP S q
    smoothingSuccessor hn hP S (L[i.val]'i.isLt) =
      L[(i.val + 1) % L.length]'(Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)) := by
  let L := componentMarkList hn hP S q
  have hdata := componentMarkList_data hn hP S q
  have he := componentCycle_list_eqOn hn hP S (independent_inheritsMarkOrder hn hP hS)
    q L hdata.2.2.1.symm
  exact (he (List.getElem_mem i.isLt)).symm.trans
    (List.formPerm_apply_getElem L hdata.1 i.val i.isLt)

/-- The affine edge between successive evaluated entries of the actual
component marked list. The modular index explicitly retains the closing edge. -/
def componentTraceEdge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S)
    (i : Fin (componentMarkList hn hP S q).length) (u : ℝ) : Plane :=
  let L := componentMarkList hn hP S q
  let j : Fin L.length :=
    ⟨(i.val + 1) % L.length, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  traversalEvaluation P (markPosition hn hP.1 (L[i.val]'i.isLt)) +
    u • (traversalEvaluation P (markPosition hn hP.1 (L[j.val]'j.isLt)) -
      traversalEvaluation P (markPosition hn hP.1 (L[i.val]'i.isLt)))

/-- Every edge of an independent component's actual finite trace is its
constructed smoothing segment, has positive Euclidean endpoint displacement,
and joins the next modular-index edge. Continuity is proved for each edge;
no global circle parameterization or true-corner polygon is asserted here. -/
theorem componentTraceEdge_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (i : Fin (componentMarkList hn hP S q).length) :
    let L := componentMarkList hn hP S q
    let j : Fin L.length :=
      ⟨(i.val + 1) % L.length, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
    (∀ u : ℝ, componentTraceEdge hn hP S q i u =
      smoothingSegment hn hP S (L[i.val]'i.isLt) u) ∧
      0 < euclideanLength
        (componentTraceEdge hn hP S q i 1 - componentTraceEdge hn hP S q i 0) ∧
      componentTraceEdge hn hP S q i 1 = componentTraceEdge hn hP S q j 0 ∧
      Continuous (componentTraceEdge hn hP S q i) := by
  let L := componentMarkList hn hP S q
  let j : Fin L.length :=
    ⟨(i.val + 1) % L.length, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  have hseg (k : Fin L.length) (u : ℝ) : componentTraceEdge hn hP S q k u =
      smoothingSegment hn hP S (L[k.val]'k.isLt) u := by
    dsimp only [componentTraceEdge, smoothingSegment]
    rw [componentMarkList_getElem_successor hn hP hS q k]
  refine ⟨hseg i, ?_, ?_, ?_⟩
  · rw [hseg i 1, hseg i 0, smoothingSegment_one, smoothingSegment_zero]
    exact smoothingSegment_length_pos hn hP S (L[i.val]'i.isLt)
  · rw [hseg i 1, hseg j 0, smoothingSegment_one, smoothingSegment_zero,
      componentMarkList_getElem_successor hn hP hS q i]
  · have he : componentTraceEdge hn hP S q i =
        smoothingSegment hn hP S (L[i.val]'i.isLt) := funext (hseg i)
    rw [he]
    exact continuous_smoothingSegment hn hP S (L[i.val]'i.isLt)

end
end SM.Carrier
