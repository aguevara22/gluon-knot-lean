namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

theorem ending_old_lt_A (s k : Fin n) (hk : k < s) : old s k < A s := by
  have h := (old_strictMono s) hk
  simpa only [old_self] using h

/-- The source row order is B only, then A and B. The tail section maps
s to B; the old section maps s to A. Both sections are already defined. -/
def endingCutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (i : Fin 2) : BoundaryCutSet I :=
  expandCuts s I hI C (endingRows s I hI C hL hR i)

theorem ending_core_right (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hR : I.right = B s) :
    (collapseInterval s I hI).right = s := by
  change collapse s I.right = s
  rw [hR, collapse_B]

theorem ending_core_cut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) : s ∈ C.cuts := by
  have hm := C.right_mem
  exact (congrArg (fun x : Fin n => x ∈ C.cuts) (ending_core_right s I hI hR)).mp hm

/-- Every tail-section cut is inside the actual ending interval. -/
theorem ending_tail_cut_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (k : Fin n) (hk : k ∈ C.cuts) :
    I.left ≤ startingTailEmbedding s k ∧ startingTailEmbedding s k ≤ I.right := by
  have hb := C.bounds k hk
  have hks : k ≤ s := by simpa only [ending_core_right s I hI hR] using hb.2
  have hp : I.left ≠ B s := ne_of_lt (lt_trans hL (A_lt_B s))
  have hcs : collapse s I.left ≠ s := by
    intro he
    rcases (collapse_eq_s_iff s I.left).mp he with he | he
    · exact (ne_of_lt hL) he
    · exact hp he
  constructor
  · have hleft := (startingTailEmbedding s).monotone hb.1
    change startingTailEmbedding s (collapse s I.left) ≤ startingTailEmbedding s k at hleft
    rwa [startingTail_eq_old s _ hcs, old_collapse_of_ne_B s I.left hp] at hleft
  · rw [hR, ← startingTail_self s]
    exact (startingTailEmbedding s).monotone hks

/-- The B-only presentation is the entire tail-section image of core cuts. -/
theorem endingCutSet_zero_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (endingCutSet s I hI C hL hR 0).cuts = C.cuts.image (startingTailEmbedding s) := by
  ext p
  have hm := mem_expandCuts s I hI C (endingRows s I hI C hL hR 0) p
  change p ∈ (endingCutSet s I hI C hL hR 0).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (endingRows s I hI C hL hR 0).val at hm
  simp only [endingRows, Matrix.cons_val_zero, Finset.mem_singleton] at hm
  rw [hm]
  constructor
  · rintro (h | rfl)
    · have he := (collapse_eq_iff_of_ne s (collapse s p) h.2.2 p).mp rfl
      exact Finset.mem_image.mpr ⟨collapse s p, h.2.1,
        (startingTail_eq_old s _ h.2.2).trans he.symm⟩
    · exact Finset.mem_image.mpr ⟨s, ending_core_cut s I hI C hR, startingTail_self s⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    by_cases hks : k = s
    · exact Or.inr (by rw [hks, startingTail_self])
    · left
      exact ⟨ending_tail_cut_bounds s I hI C hL hR k hk,
        by simpa only [collapse_startingTail] using hk,
        by simpa only [collapse_startingTail] using hks⟩

theorem endingCutSet_one_insert_A (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (endingCutSet s I hI C hL hR 1).cuts =
      insert (A s) (endingCutSet s I hI C hL hR 0).cuts := by
  ext p
  simp only [endingCutSet, mem_expandCuts, endingRows, Matrix.cons_val_zero,
    Matrix.cons_val_one, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The both-cut presentation is the full old-section image followed by B. -/
theorem endingCutSet_one_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (endingCutSet s I hI C hL hR 1).cuts = insert (B s) (C.cuts.image (old s)) := by
  rw [endingCutSet_one_insert_A, endingCutSet_zero_cuts]
  exact (starting_sections_cut_image s C.cuts (ending_core_cut s I hI C hR)).symm

/-- The last actual part of the raw core composition, including a unary one. -/
def endingLastChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    BoundaryInterval n :=
  C.toComposition.part ⟨C.toComposition.parts - 1, by have := C.toComposition.parts_pos; omega⟩

theorem endingLastChild_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    C.Consecutive (endingLastChild s I hI C) := by
  simpa only [endingLastChild, BoundaryCutSet.toComposition_cutSet] using
    C.toComposition.part_consecutive
      ⟨C.toComposition.parts - 1, by have := C.toComposition.parts_pos; omega⟩

theorem endingLastChild_right (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) : (endingLastChild s I hI C).right = s := by
  let k : Fin C.toComposition.parts :=
    ⟨C.toComposition.parts - 1, by have := C.toComposition.parts_pos; omega⟩
  change C.toComposition.cut k.succ = s
  have hk : k.succ = Fin.last C.toComposition.parts := by
    apply Fin.ext
    change C.toComposition.parts - 1 + 1 = C.toComposition.parts
    have := C.toComposition.parts_pos
    omega
  rw [hk, C.toComposition.last, ending_core_right s I hI hR]

theorem endingLastChild_left (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) :
    (endingLastChild s I hI C).left < s ∧ (endingLastChild s I hI C).left ∈ C.cuts := by
  exact ⟨lt_of_lt_of_eq (endingLastChild s I hI C).increasing
      (endingLastChild_right s I hI C hR),
    (endingLastChild_consecutive s I hI C).1⟩

theorem endingLastChild_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (K : BoundaryInterval n) (hK : C.Consecutive K) (hk : K.right = s) :
    K = endingLastChild s I hI C :=
  C.consecutive_eq_of_right hK (endingLastChild_consecutive s I hI C)
    (hk.trans (endingLastChild_right s I hI C hR).symm)

theorem endingLastChild_left_ge (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (k : Fin n) (hk : k ∈ C.cuts) (hks : k < s) :
    k ≤ (endingLastChild s I hI C).left := by
  apply le_of_not_gt
  intro hlt
  exact (endingLastChild_consecutive s I hI C).2.2 k hk
    ⟨hlt, lt_of_lt_of_eq hks (endingLastChild_right s I hI C hR).symm⟩

def endingChildrenZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {J : BoundaryInterval (n + 1) // (endingCutSet s I hI C hL hR 0).Consecutive J} :=
  consecutiveOrderedImageEquiv (startingTailEmbedding s) C (endingCutSet s I hI C hL hR 0)
    (endingCutSet_zero_cuts s I hI C hL hR)

theorem ending_old_cut_lt_B (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (k : Fin n) (hk : k ∈ C.cuts) : old s k < B s := by
  have hks : k ≤ s := by
    simpa only [ending_core_right s I hI hR] using (C.bounds k hk).2
  have ha : old s k ≤ A s := by
    rw [← old_self s]
    exact (old_strictMono s).monotone hks
  exact lt_of_le_of_lt ha (A_lt_B s)

/-- Adjoining B after the old image preserves every actual mapped core child. -/
theorem ending_one_mapped_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (K : BoundaryInterval n) (hK : C.Consecutive K) :
    (endingCutSet s I hI C hL hR 1).Consecutive
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) := by
  let U := OrderedBoundaryTransport.cutSet (startingOldEmbedding s) C
  have hU : U.Consecutive (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) :=
    (consecutive_ordered_image_iff (startingOldEmbedding s) C U rfl K).mpr hK
  refine ⟨?_, ?_, ?_⟩
  · rw [endingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K.left, hK.1, rfl⟩)
  · rw [endingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K.right, hK.2.1, rfl⟩)
  · intro p hp hb
    rw [endingCutSet_one_cuts] at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact lt_asymm (ending_old_cut_lt_B s I hI C hR K.right hK.2.1) hb.2
    · exact hU.2.2 p hp hb

/-- The only additional child is the actual final interval A,B. -/
theorem ending_one_duplicate_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (endingCutSet s I hI C hL hR 1).Consecutive (duplicateInterval s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [endingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨s, ending_core_cut s I hI C hR, old_self s⟩)
  · rw [endingCutSet_one_cuts]
    exact Finset.mem_insert_self _ _
  · intro p _ hb
    have hl : s.val < p.val := hb.1
    have hr : p.val < s.val + 1 := hb.2
    omega

/-- Every row-one consecutive interval is a mapped core child or the final singleton. -/
theorem ending_one_consecutive_iff (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (J : BoundaryInterval (n + 1)) :
    (endingCutSet s I hI C hL hR 1).Consecutive J ↔
      J = duplicateInterval s ∨ ∃ K : BoundaryInterval n,
        C.Consecutive K ∧ OrderedBoundaryTransport.interval (startingOldEmbedding s) K = J := by
  constructor
  · intro hJ
    by_cases hjb : J.right = B s
    · exact Or.inl ((endingCutSet s I hI C hL hR 1).consecutive_eq_of_right hJ
        (ending_one_duplicate_consecutive s I hI C hL hR) hjb)
    · right
      have hr : J.right ∈ C.cuts.image (old s) := by
        have hm := hJ.2.1
        rw [endingCutSet_one_cuts] at hm
        exact (Finset.mem_insert.mp hm).resolve_left hjb
      have hlb : J.left < B s := by
        have hb := ((endingCutSet s I hI C hL hR 1).bounds J.right hJ.2.1).2
        have hbr : J.right ≤ B s := by simpa only [hR] using hb
        exact lt_of_lt_of_le J.increasing hbr
      have hl : J.left ∈ C.cuts.image (old s) := by
        have hm := hJ.1
        rw [endingCutSet_one_cuts] at hm
        exact (Finset.mem_insert.mp hm).resolve_left (ne_of_lt hlb)
      let U := OrderedBoundaryTransport.cutSet (startingOldEmbedding s) C
      have hU : U.Consecutive J := by
        refine ⟨hl, hr, ?_⟩
        intro p hp hb
        have ht : p ∈ (endingCutSet s I hI C hL hR 1).cuts := by
          rw [endingCutSet_one_cuts]
          exact Finset.mem_insert_of_mem hp
        exact hJ.2.2 p ht hb
      exact consecutive_ordered_image_exhaust (startingOldEmbedding s) C U rfl J hU
  · rintro (rfl | ⟨K, hK, rfl⟩)
    · exact ending_one_duplicate_consecutive s I hI C hL hR
    · exact ending_one_mapped_consecutive s I hI C hL hR K hK

/-- The left summand denotes the geometrically final singleton. The sum
index is used for a child-domain bijection, not an asserted ordering of children. -/
def endingChildOneMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (Unit ⊕ {K : BoundaryInterval n // C.Consecutive K}) →
      {J : BoundaryInterval (n + 1) // (endingCutSet s I hI C hL hR 1).Consecutive J} :=
  Sum.elim
    (fun _ : Unit => ⟨duplicateInterval s, ending_one_duplicate_consecutive s I hI C hL hR⟩)
    (fun K => ⟨OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val,
      ending_one_mapped_consecutive s I hI C hL hR K.val K.property⟩)

/-- Exact child-domain equivalence: one final singleton and every old-section
core child, with the same sum-side convention as the starting packet. -/
def endingChildrenOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (Unit ⊕ {K : BoundaryInterval n // C.Consecutive K}) ≃
      {J : BoundaryInterval (n + 1) // (endingCutSet s I hI C hL hR 1).Consecutive J} :=
  Equiv.ofBijective (endingChildOneMap s I hI C hL hR) ⟨by
    intro a b he
    cases a with
    | inl u =>
      cases b with
      | inl v => cases u; cases v; rfl
      | inr K =>
        have hx : B s = old s K.val.right := congrArg (fun J => J.val.right) he
        exact False.elim ((ne_of_gt (ending_old_cut_lt_B s I hI C hR K.val.right K.property.2.1)) hx)
    | inr K =>
      cases b with
      | inl u =>
        have hx : old s K.val.right = B s := congrArg (fun J => J.val.right) he
        exact False.elim ((ne_of_lt (ending_old_cut_lt_B s I hI C hR K.val.right K.property.2.1)) hx)
      | inr L =>
        have hval : K.val = L.val := OrderedBoundaryTransport.interval_injective
          (startingOldEmbedding s) (congrArg Subtype.val he)
        exact congrArg Sum.inr (Subtype.ext hval), by
    intro J
    rcases (ending_one_consecutive_iff s I hI C hL hR J.val).mp J.property with h | ⟨K, hK, he⟩
    · exact ⟨Sum.inl (), Subtype.ext h.symm⟩
    · exact ⟨Sum.inr ⟨K, hK⟩, Subtype.ext he⟩⟩

/-- The B-only last child has the actual exterior endpoint and contains the soft edge. -/
theorem ending_last_zero_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) :
    (OrderedBoundaryTransport.interval (startingTailEmbedding s) (endingLastChild s I hI C)).left =
      old s (endingLastChild s I hI C).left ∧
    (OrderedBoundaryTransport.interval (startingTailEmbedding s) (endingLastChild s I hI C)).right = B s ∧
    old s (endingLastChild s I hI C).left < A s := by
  refine ⟨startingTail_eq_old s _ (ne_of_lt (endingLastChild_left s I hI C hR).1), ?_,
    ending_old_lt_A s _ (endingLastChild_left s I hI C hR).1⟩
  change startingTailEmbedding s (endingLastChild s I hI C).right = B s
  rw [endingLastChild_right s I hI C hR, startingTail_self]

/-- Before the final singleton the same last core child ends at the retained A. -/
theorem ending_last_one_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) :
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) (endingLastChild s I hI C)).left =
      old s (endingLastChild s I hI C).left ∧
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) (endingLastChild s I hI C)).right = A s := by
  refine ⟨rfl, ?_⟩
  change old s (endingLastChild s I hI C).right = A s
  rw [endingLastChild_right s I hI C hR, old_self]

theorem ending_otherChild_right_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ endingLastChild s I hI C) : K.right < s := by
  have hle : K.right ≤ s := by
    simpa only [ending_core_right s I hI hR] using (C.bounds K.right hK.2.1).2
  apply lt_of_le_of_ne hle
  intro he
  exact hne (endingLastChild_unique s I hI C hR K hK he)

/-- Every child other than the actual last one is identical in both rows. -/
theorem ending_otherChild_map_eq (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ endingLastChild s I hI C) :
    OrderedBoundaryTransport.interval (startingTailEmbedding s) K =
      OrderedBoundaryTransport.interval (startingOldEmbedding s) K := by
  have hr := ending_otherChild_right_lt s I hI C hR K hK hne
  apply BoundaryInterval.eq_of_endpoints
  · exact startingTail_eq_old s K.left (ne_of_lt (lt_trans K.increasing hr))
  · exact startingTail_eq_old s K.right (ne_of_lt hr)

end
end SM.SoftDuplication
