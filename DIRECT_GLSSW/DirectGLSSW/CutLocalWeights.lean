import DirectGLSSW.CutIncidence

/-!
# Local and final cut incidence and weights

Source: `ep:factorization`. Local cuts are the final cuts restricted to
an outer open gap. The edge and triple identities retain the actual
neighbouring vertices in the final list.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- Restricting final vertices to a closed outer edge gives precisely the
vertices of the local cut list, including both endpoints. -/
theorem cutVertices_local_iff {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) (hST : S ⊆ T)
    {e : ℕ × ℕ} (he : e ∈ cutEdges i j S) {k : ℕ} :
    k ∈ cutVertices e.1 e.2 (T ∩ Finset.Ioo e.1 e.2) ↔
      k ∈ cutVertices i j T ∧ e.1 ≤ k ∧ k ≤ e.2 := by
  have he' : e ∈ (cutVertices i j S).zip (cutVertices i j S).tail := by
    simpa only [cutEdges, List.mem_toFinset] using he
  obtain ⟨ha, hb, hab, _⟩ := adjacent_separation (cutVertices_pairwise hij hS) he'
  have hsub : ∀ x ∈ cutVertices i j S, x ∈ cutVertices i j T := by
    intro x hx
    simp only [cutVertices, List.mem_cons, List.mem_append, List.mem_singleton,
      Finset.mem_sort, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with (rfl | hx) | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (hST hx))
    · exact Or.inr rfl
  constructor
  · intro hk
    simp only [cutVertices, List.mem_cons, List.mem_append, List.mem_singleton,
      Finset.mem_sort, List.not_mem_nil, or_false] at hk
    rcases hk with (rfl | hk) | rfl
    · exact ⟨hsub _ ha, le_rfl, hab.le⟩
    · obtain ⟨hkT, hkint⟩ := Finset.mem_inter.mp hk
      obtain ⟨hak, hkb⟩ := Finset.mem_Ioo.mp hkint
      exact ⟨by simp [cutVertices, hkT], hak.le, hkb.le⟩
    · exact ⟨hsub _ hb, hab.le, le_rfl⟩
  · rintro ⟨hk, hak, hkb⟩
    by_cases hka : k = e.1
    · simp [cutVertices, hka]
    by_cases hkb' : k = e.2
    · simp [cutVertices, hkb']
    have hstrict : e.1 < k ∧ k < e.2 := by omega
    have hparent := cutEdges_gap_subset hij hS he (Finset.mem_Ioo.mpr hstrict)
    have hkij := Finset.mem_Ioo.mp (Finset.mem_sdiff.mp hparent).1
    have hkT : k ∈ T := by
      simp only [cutVertices, List.mem_cons, List.mem_append, List.mem_singleton,
        Finset.mem_sort, List.not_mem_nil, or_false] at hk
      rcases hk with (hk | hk) | hk
      · omega
      · exact hk
      · omega
    simp [cutVertices, Finset.mem_inter.mpr ⟨hkT, Finset.mem_Ioo.mpr hstrict⟩]

/-- Every point before the last endpoint lies in a consecutive half-open
edge. This includes points that themselves are outer cuts. -/
private theorem exists_adjacent_halfOpen_aux {i j k : ℕ} {l : List ℕ}
    (hik : i ≤ k) (hkj : k < j) :
    ∃ e ∈ (i :: l ++ [j]).zip (l ++ [j]), e.1 ≤ k ∧ k < e.2 := by
  induction l generalizing i with
  | nil => exact ⟨(i, j), by simp, hik, hkj⟩
  | cons x xs ih =>
      by_cases hkx : k < x
      · exact ⟨(i, x), by simp, hik, hkx⟩
      · obtain ⟨e, he, hek⟩ := ih (by omega : x ≤ k)
        refine ⟨e, ?_, hek⟩
        simp only [List.cons_append, List.zip_cons_cons, List.mem_cons]
        exact Or.inr he

/-- Every point in the parent half-open interval lies in an outer edge's
half-open interval. -/
theorem cutEdges_exists_halfOpen {i j k : ℕ} (S : Finset ℕ)
    (hik : i ≤ k) (hkj : k < j) :
    ∃ e ∈ cutEdges i j S, e.1 ≤ k ∧ k < e.2 := by
  obtain ⟨e, he, hek⟩ := exists_adjacent_halfOpen_aux (l := S.sort (· ≤ ·)) hik hkj
  exact ⟨e, by simpa only [cutEdges, cutVertices, List.tail_cons,
    List.mem_toFinset] using he, hek⟩

/-- A positive-length segment contained in two closed consecutive edges
forces those outer edges to coincide. -/
theorem cutEdges_segment_unique {i j a b : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {e f : ℕ × ℕ}
    (he : e ∈ cutEdges i j S) (hf : f ∈ cutEdges i j S)
    (hab : a < b) (hea : e.1 ≤ a) (hbe : b ≤ e.2)
    (hfa : f.1 ≤ a) (hbf : b ≤ f.2) : e = f := by
  have he' : e ∈ (cutVertices i j S).zip (cutVertices i j S).tail := by
    simpa only [cutEdges, List.mem_toFinset] using he
  have hf' : f ∈ (cutVertices i j S).zip (cutVertices i j S).tail := by
    simpa only [cutEdges, List.mem_toFinset] using hf
  obtain ⟨hea', heb', _, hsepE⟩ := adjacent_separation (cutVertices_pairwise hij hS) he'
  obtain ⟨hfa', hfb', _, hsepF⟩ := adjacent_separation (cutVertices_pairwise hij hS) hf'
  have h₁ := hsepE f.1 hfa'
  have h₂ := hsepF e.1 hea'
  have h₃ := hsepE f.2 hfb'
  have h₄ := hsepF e.2 heb'
  apply Prod.ext <;> omega

/-- A local edge is exactly a final edge lying in the closed outer gap. -/
theorem cutEdges_local_iff {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j)
    {e : ℕ × ℕ} (he : e ∈ cutEdges i j S) {a b : ℕ} :
    (a, b) ∈ cutEdges e.1 e.2 (T ∩ Finset.Ioo e.1 e.2) ↔
      (a, b) ∈ cutEdges i j T ∧ e.1 ≤ a ∧ b ≤ e.2 := by
  have hedata := (cutEdges_mem_iff hij hS).mp he
  have helt := hedata.2.2.1
  rw [cutEdges_mem_iff helt Finset.inter_subset_right]
  constructor
  · rintro ⟨ha, hb, hab, hsep⟩
    obtain ⟨haT, hea, hae⟩ := (cutVertices_local_iff hij hS hST he).mp ha
    obtain ⟨hbT, heb, hbe⟩ := (cutVertices_local_iff hij hS hST he).mp hb
    refine ⟨(cutEdges_mem_iff hij hT).mpr ⟨haT, hbT, hab, ?_⟩, hea, hbe⟩
    intro x hx
    by_cases hleft : x < e.1
    · exact Or.inl (by omega)
    by_cases hright : e.2 < x
    · exact Or.inr (by omega)
    exact hsep x ((cutVertices_local_iff hij hS hST he).mpr ⟨hx, by omega, by omega⟩)
  · rintro ⟨habT, hea, hbe⟩
    obtain ⟨ha, hb, hab, hsep⟩ := (cutEdges_mem_iff hij hT).mp habT
    refine ⟨(cutVertices_local_iff hij hS hST he).mpr ⟨ha, hea, by omega⟩,
      (cutVertices_local_iff hij hS hST he).mpr ⟨hb, by omega, hbe⟩, hab, ?_⟩
    intro x hx
    exact hsep x ((cutVertices_local_iff hij hS hST he).mp hx).1

/-- Each final edge belongs to some local cut list; adjacency prevents it
from straddling an outer cut. -/
theorem cutEdges_exists_local {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j)
    {a b : ℕ} (hab : (a, b) ∈ cutEdges i j T) :
    ∃ e ∈ cutEdges i j S,
      (a, b) ∈ cutEdges e.1 e.2 (T ∩ Finset.Ioo e.1 e.2) := by
  obtain ⟨ha, hb, hlt, hsep⟩ := (cutEdges_mem_iff hij hT).mp hab
  have hbound : ∀ x ∈ cutVertices i j T, i ≤ x ∧ x ≤ j := by
    intro x hx
    simp only [cutVertices, List.mem_cons, List.mem_append, List.mem_singleton,
      Finset.mem_sort, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | hx) | rfl
    · exact ⟨le_rfl, hij.le⟩
    · exact ⟨(Finset.mem_Ioo.mp (hT hx)).1.le, (Finset.mem_Ioo.mp (hT hx)).2.le⟩
    · exact ⟨hij.le, le_rfl⟩
  obtain ⟨e, he, hea, hae⟩ := cutEdges_exists_halfOpen S (hbound a ha).1
    (by have := (hbound b hb).2; omega : a < j)
  have heb := ((cutEdges_mem_iff hij hS).mp he).2.1
  have hebT : e.2 ∈ cutVertices i j T := by
    simp only [cutVertices, List.mem_cons, List.mem_append, List.mem_singleton,
      Finset.mem_sort, List.not_mem_nil, or_false] at heb ⊢
    rcases heb with (heb | heb) | heb
    · exact Or.inl (Or.inl heb)
    · exact Or.inl (Or.inr (hST heb))
    · exact Or.inr heb
  have hbe : b ≤ e.2 := by have := hsep e.2 hebT; omega
  exact ⟨e, he, (cutEdges_local_iff hij hS hST hT he).mpr ⟨hab, hea, hbe⟩⟩

/-- Local edge sets are pairwise disjoint, including empty local cut sets. -/
theorem cutEdges_local_pairwiseDisjoint {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j) :
    Set.PairwiseDisjoint (cutEdges i j S : Set (ℕ × ℕ))
      (fun e => cutEdges e.1 e.2 (T ∩ Finset.Ioo e.1 e.2)) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  rintro ⟨a,b⟩ habE habF
  obtain ⟨hab, hea, hbe⟩ := (cutEdges_local_iff hij hS hST hT he).mp habE
  obtain ⟨_, hfa, hbf⟩ := (cutEdges_local_iff hij hS hST hT hf).mp habF
  exact hef (cutEdges_segment_unique hij hS he hf
    ((cutEdges_mem_iff hij hT).mp hab).2.2.1 hea hbe hfa hbf)

/-- The disjoint union of local edges is exactly the final edge set. -/
theorem cutEdges_local_biUnion {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j) :
    (cutEdges i j S).biUnion
      (fun e => cutEdges e.1 e.2 (T ∩ Finset.Ioo e.1 e.2)) = cutEdges i j T := by
  ext ⟨a,b⟩
  constructor
  · intro hab
    obtain ⟨e, he, hab⟩ := Finset.mem_biUnion.mp hab
    exact ((cutEdges_local_iff hij hS hST hT he).mp hab).1
  · intro hab
    exact Finset.mem_biUnion.mpr (cutEdges_exists_local hij hS hST hT hab)

/-- Multiplying local branch products preserves each actual final edge
factor exactly once. -/
theorem local_product_branch (X : IntervalArray) {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j) :
    (∏ e ∈ cutEdges i j S,
      branchProduct X (cutVertices e.1 e.2 (T ∩ Finset.Ioo e.1 e.2))) =
      branchProduct X (cutVertices i j T) := by
  rw [branchProduct_eq_prod_cutEdges X hij hT,
    ← cutEdges_local_biUnion hij hS hST hT,
    Finset.prod_biUnion (cutEdges_local_pairwiseDisjoint hij hS hST hT)]
  apply Finset.prod_congr rfl
  intro e he
  exact branchProduct_eq_prod_cutEdges X
    ((cutEdges_mem_iff hij hS).mp he).2.2.1 Finset.inter_subset_right

/-- A local consecutive triple is precisely a final consecutive triple
whose middle vertex lies in the outer open gap. -/
theorem cutTriples_local_iff {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j)
    {e : ℕ × ℕ} (he : e ∈ cutEdges i j S) {a b c : ℕ} :
    (a, b, c) ∈ cutTriples e.1 e.2 (T ∩ Finset.Ioo e.1 e.2) ↔
      (a, b, c) ∈ cutTriples i j T ∧ b ∈ Finset.Ioo e.1 e.2 := by
  have helt := ((cutEdges_mem_iff hij hS).mp he).2.2.1
  rw [cutTriples_mem_iff helt Finset.inter_subset_right]
  constructor
  · rintro ⟨hab, hbc⟩
    obtain ⟨habT, hea, _⟩ := (cutEdges_local_iff hij hS hST hT he).mp hab
    obtain ⟨hbcT, _, hce⟩ := (cutEdges_local_iff hij hS hST hT he).mp hbc
    have hablt := ((cutEdges_mem_iff hij hT).mp habT).2.2.1
    have hbclt := ((cutEdges_mem_iff hij hT).mp hbcT).2.2.1
    exact ⟨(cutTriples_mem_iff hij hT).mpr ⟨habT, hbcT⟩,
      Finset.mem_Ioo.mpr (by omega)⟩
  · rintro ⟨ht, hb⟩
    obtain ⟨hab, hbc⟩ := (cutTriples_mem_iff hij hT).mp ht
    have hbint := Finset.mem_Ioo.mp hb
    have heleft : e.1 ∈ cutVertices i j T :=
      ((cutVertices_local_iff hij hS hST he).mp (by simp [cutVertices])).1
    have heright : e.2 ∈ cutVertices i j T :=
      ((cutVertices_local_iff hij hS hST he).mp (by simp [cutVertices])).1
    have hea : e.1 ≤ a := by
      have := ((cutEdges_mem_iff hij hT).mp hab).2.2.2 e.1 heleft
      omega
    have hce : c ≤ e.2 := by
      have := ((cutEdges_mem_iff hij hT).mp hbc).2.2.2 e.2 heright
      omega
    exact ⟨(cutEdges_local_iff hij hS hST hT he).mpr ⟨hab, hea, hbint.2.le⟩,
      (cutEdges_local_iff hij hS hST hT he).mpr ⟨hbc, hbint.1.le, hce⟩⟩

/-- Distinct outer gaps have disjoint local triple sets because their
middle vertices lie in disjoint open intervals. -/
theorem cutTriples_local_pairwiseDisjoint {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j) :
    Set.PairwiseDisjoint (cutEdges i j S : Set (ℕ × ℕ))
      (fun e => cutTriples e.1 e.2 (T ∩ Finset.Ioo e.1 e.2)) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  rintro ⟨a,b,c⟩ htE htF
  have hbE := ((cutTriples_local_iff hij hS hST hT he).mp htE).2
  have hbF := ((cutTriples_local_iff hij hS hST hT hf).mp htF).2
  exact Finset.disjoint_left.mp (cutEdges_gaps_pairwiseDisjoint hij hS he hf hef) hbE hbF

/-- Local triples form exactly the final triples at the inner cuts. In
particular their predecessor and successor are the final neighbours. -/
theorem cutTriples_local_biUnion {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j) :
    (cutEdges i j S).biUnion
      (fun e => cutTriples e.1 e.2 (T ∩ Finset.Ioo e.1 e.2)) =
      (cutTriples i j T).filter (fun t => t.2.1 ∉ S) := by
  ext ⟨a,b,c⟩
  constructor
  · intro ht
    obtain ⟨e, he, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨htT, hb⟩ := (cutTriples_local_iff hij hS hST hT he).mp ht
    exact Finset.mem_filter.mpr ⟨htT,
      (Finset.mem_sdiff.mp (cutEdges_gap_subset hij hS he hb)).2⟩
  · intro ht
    obtain ⟨ht, hbnot⟩ := Finset.mem_filter.mp ht
    have hbT := cutTriples_middle_mem hij hT ht
    have hbgap : b ∈ (cutEdges i j S).biUnion (fun e => Finset.Ioo e.1 e.2) := by
      rw [cutEdges_biUnion_Ioo hij hS]
      exact Finset.mem_sdiff.mpr ⟨hT hbT, hbnot⟩
    obtain ⟨e, he, hb⟩ := Finset.mem_biUnion.mp hbgap
    exact Finset.mem_biUnion.mpr
      ⟨e, he, (cutTriples_local_iff hij hS hST hT he).mpr ⟨ht, hb⟩⟩

/-- Local near-only gate products use exactly the final-neighbour triple
at each final cut that is not outer. -/
theorem local_product_near (D : TripleArray) {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j) :
    (∏ e ∈ cutEdges i j S,
      gateProduct D (fun _ _ _ => 0) e.1 e.2
        (cutVertices e.1 e.2 (T ∩ Finset.Ioo e.1 e.2))) =
      ∏ t ∈ (cutTriples i j T).filter (fun t => t.2.1 ∉ S),
        D t.1 t.2.1 t.2.2 / 2 := by
  rw [← cutTriples_local_biUnion hij hS hST hT,
    Finset.prod_biUnion (cutTriples_local_pairwiseDisjoint hij hS hST hT)]
  apply Finset.prod_congr rfl
  intro e he
  simpa only [sub_zero] using gateProduct_eq_prod_cutTriples D (fun _ _ _ => 0)
    ((cutEdges_mem_iff hij hS).mp he).2.2.1
    (Finset.inter_subset_right : T ∩ Finset.Ioo e.1 e.2 ⊆ Finset.Ioo e.1 e.2)

end DirectGLSSW
