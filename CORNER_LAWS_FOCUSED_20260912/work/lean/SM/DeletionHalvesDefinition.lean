import SM.ContactHalfSegments
import SM.NamedWallPredicates

/-! Full source def:deletion-halves: actual inherited vertices and cyclic
order, the two positive cut segments, and invariance under parent relabelling. -/

namespace SM

variable {n : ℕ} [NeZero n]

structure DeletionData (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) : Prop where
  vertices : ∀ i, deleteVertex P j i = P (deletionIndex j i)
  injective_labels : Function.Injective (deletionIndex (n := n) j)
  omits_deleted : ∀ i : ZMod n, deletionIndex j i ≠ j
  exhaustive_labels : ∀ k : ZMod (n + 1), k ≠ j → ∃ i : ZMod n, deletionIndex j i = k
  first_label : deletionIndex (n := n) j 0 = j + 1
  last_label : deletionIndex (n := n) j (-1) = j - 1
  next_label : ∀ i : ZMod n, i ≠ -1 → deletionIndex j (i + 1) = deletionIndex j i + 1
  inherited_edges : ∀ i : ZMod n, i ≠ -1 → edge (deleteVertex P j) i = edge P (deletionIndex j i)
  fused_edge : edge (deleteVertex P j) (-1) = P (j + 1) - P (j - 1)
  relabel : ∀ r : ZMod (n + 1), deleteVertex (shift r P) (j - r) = deleteVertex P j

theorem deletion_data (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) : DeletionData P j where
  vertices := deleteVertex_apply P j
  injective_labels := deletionIndex_injective j
  omits_deleted := deletionIndex_ne_deleted j
  exhaustive_labels := fun _ hk => deletionIndex_exhaust j hk
  first_label := deletionIndex_zero j
  last_label := deletionIndex_last j
  next_label := fun _ hi => deletionIndex_next j hi
  inherited_edges := fun _ hi => edge_deleteVertex P j hi
  fused_edge := edge_deleteVertex_last P j
  relabel := deleteVertex_relabel P j

structure HalvesData (P : LabelledTuple n) (M a : ZMod n) : Prop where
  sizes : firstHalfSize M a = (a - M).val + 1 ∧ secondHalfSize M a = n - (a - M).val
  first_vertices : ∀ i : ZMod (firstHalfSize M a), firstHalf P M a i = P (M + (i.val : ZMod n))
  second_vertices : ∀ i : ZMod (secondHalfSize M a),
    secondHalf P M a i = P (if i = 0 then M else a + (i.val : ZMod n))
  first_injective_labels : Function.Injective (firstHalfIndex M a)
  second_injective_labels : Function.Injective (secondHalfIndex M a)
  first_range : ∀ x : ZMod n, (∃ i, firstHalfIndex M a i = x) ↔ (x - M).val < firstHalfSize M a
  second_range : ∀ x : ZMod n,
    (∃ i, secondHalfIndex M a i = x) ↔ (x - (a + 1)).val < secondHalfSize M a
  first_endpoints : firstHalf P M a 0 = P M ∧ firstHalf P M a (-1) = P a
  second_endpoints : secondHalf P M a 0 = P M ∧ secondHalf P M a 1 = P (a + 1) ∧
    secondHalf P M a (-1) = P (M - 1)
  first_next_label : ∀ i : ZMod (firstHalfSize M a), i ≠ -1 →
    firstHalfIndex M a (i + 1) = firstHalfIndex M a i + 1
  second_next_label : ∀ i : ZMod (secondHalfSize M a), i ≠ 0 →
    secondHalfIndex M a (i + 1) = secondHalfEdgeIndex M a i + 1
  first_edges : ∀ i : ZMod (firstHalfSize M a), i ≠ -1 →
    edge (firstHalf P M a) i = edge P (firstHalfIndex M a i)
  second_edges : ∀ i : ZMod (secondHalfSize M a), i ≠ 0 →
    edge (secondHalf P M a) i = edge P (secondHalfEdgeIndex M a i)
  cut_segments : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ P M = edgePoint P a r ∧
    edge (firstHalf P M a) (-1) = r • edge P a ∧
    edge (secondHalf P M a) 0 = (1 - r) • edge P a ∧
    (∀ t : ℝ, edgePoint (firstHalf P M a) (-1) t = edgePoint P a (r * t)) ∧
    (∀ t : ℝ, edgePoint (secondHalf P M a) 0 t = edgePoint P a (r + (1 - r) * t))
  first_interior_inclusions : ∀ i,
    edgeInterior (firstHalf P M a) i ⊆ edgeInterior P (firstHalfIndex M a i)
  second_interior_inclusions : ∀ i,
    edgeInterior (secondHalf P M a) i ⊆ edgeInterior P (secondHalfEdgeIndex M a i)
  first_segment_inclusions : ∀ i,
    edgeSegment (firstHalf P M a) i ⊆ edgeSegment P (firstHalfIndex M a i)
  second_segment_inclusions : ∀ i,
    edgeSegment (secondHalf P M a) i ⊆ edgeSegment P (secondHalfEdgeIndex M a i)
  relabel : ∀ r : ZMod n,
    HEq (firstHalf (shift r P) (M - r) (a - r)) (firstHalf P M a) ∧
    HEq (secondHalf (shift r P) (M - r) (a - r)) (secondHalf P M a)

theorem halves_data (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) : HalvesData P M a := by
  refine {
    sizes := ⟨rfl, rfl⟩
    first_vertices := fun _ => rfl
    second_vertices := fun _ => rfl
    first_injective_labels := firstHalfIndex_injective M a
    second_injective_labels := secondHalfIndex_injective M a
    first_range := firstHalfIndex_range M a
    second_range := secondHalfIndex_range_iff M a
    first_endpoints := ⟨firstHalf_zero P M a, firstHalf_last P M a⟩
    second_endpoints := ⟨secondHalf_zero P M a, secondHalf_one hn h P, secondHalf_last hn h P⟩
    first_next_label := fun _ hi => firstHalfIndex_next M a hi
    second_next_label := fun _ hi => secondHalfIndex_next M a hi
    first_edges := fun _ hi => edge_firstHalf P M a hi
    second_edges := fun _ hi => edge_secondHalf P M a hi
    cut_segments := ?_
    first_interior_inclusions := firstHalf_interior_subset hm
    second_interior_inclusions := secondHalf_interior_subset hn h hm
    first_segment_inclusions := firstHalf_segment_subset hm
    second_segment_inclusions := secondHalf_segment_subset hn h hm
    relabel := fun r => ⟨firstHalf_relabel P M a r, secondHalf_relabel P M a r⟩ }
  obtain ⟨r, hr0, hr1, hr⟩ := hm
  exact ⟨r, hr0, hr1, hr, firstHalf_cut_vector hr, secondHalf_cut_vector hn h hr,
    edgePoint_firstHalf_cut hr, edgePoint_secondHalf_cut hn h hr⟩

def DeletionHalvesDefinitionData : Prop :=
  (∀ k : ℕ, ∀ _ : NeZero k, ∀ hk : 3 ≤ k,
    ∀ P : LabelledTuple (k + 1), ∀ j : ZMod (k + 1), DeletionData P j) ∧
  (∀ k : ℕ, ∀ _ : NeZero k, ∀ hk : 3 ≤ k, ∀ g : WallGerm k,
    ∀ M a : ZMod k, g.VertexEdgeAt M a → HalvesData g.center M a)

theorem deletion_halves_definition : DeletionHalvesDefinitionData := by
  exact ⟨fun _ _ _ P j => deletion_data P j,
    fun _ _ hk g _ _ h => halves_data hk h.1 h.2.2.2.1⟩

end SM
