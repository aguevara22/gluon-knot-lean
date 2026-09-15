namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The unique presentation when the core cut set omits the distinguished position. -/
def emptySpanningCutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : BoundaryCutSet I :=
  expandCuts s I hI C (emptyCutFiber s I hI C hs)

/-- The mandatory endpoints also avoid the missing core cut, so this identity
needs no extra exterior bounds on I. -/
theorem emptySpanningCutSet_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : (emptySpanningCutSet s I hI C hs).cuts = C.cuts.image (old s) := by
  have hcl : collapse s I.left ≠ s := by
    intro he
    exact hs ((congrArg (fun k : Fin n => k ∈ C.cuts) he).mp C.left_mem)
  have hcr : collapse s I.right ≠ s := by
    intro he
    exact hs ((congrArg (fun k : Fin n => k ∈ C.cuts) he).mp C.right_mem)
  have hlB : I.left ≠ B s := by
    intro he
    exact hcl (by rw [he, collapse_B])
  have hrB : I.right ≠ B s := by
    intro he
    exact hcr (by rw [he, collapse_B])
  have bounds (k : Fin n) (hk : k ∈ C.cuts) :
      I.left ≤ old s k ∧ old s k ≤ I.right := by
    have hb := C.bounds k hk
    constructor
    · have hl := (old_strictMono s).monotone hb.1
      change old s (collapse s I.left) ≤ old s k at hl
      rwa [old_collapse_of_ne_B s I.left hlB] at hl
    · have hr := (old_strictMono s).monotone hb.2
      change old s k ≤ old s (collapse s I.right) at hr
      rwa [old_collapse_of_ne_B s I.right hrB] at hr
  ext p
  have hm := mem_expandCuts s I hI C (emptyCutFiber s I hI C hs) p
  change p ∈ (emptySpanningCutSet s I hI C hs).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (emptyCutFiber s I hI C hs).val at hm
  simp only [emptyCutFiber, Finset.not_mem_empty, or_false] at hm
  rw [hm]
  constructor
  · intro hp
    have he := (collapse_eq_iff_of_ne s (collapse s p) hp.2.2 p).mp rfl
    exact Finset.mem_image.mpr ⟨collapse s p, hp.2.1, he.symm⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hks : k ≠ s := by
      intro he
      exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hk)
    exact ⟨bounds k hk, by simpa only [collapse_old] using hk,
      by simpa only [collapse_old] using hks⟩

theorem emptySpanningCutSet_old_mem (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (k : Fin n) :
    old s k ∈ (emptySpanningCutSet s I hI C hs).cuts ↔ k ∈ C.cuts := by
  rw [emptySpanningCutSet_cuts]
  exact cut_mem_ordered_image (startingOldEmbedding s) C k

/-- Every actual expanded child is one old-mapped core child, including unary C. -/
def emptySpanningChildrenEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {J : BoundaryInterval (n + 1) // (emptySpanningCutSet s I hI C hs).Consecutive J} :=
  consecutiveOrderedImageEquiv (startingOldEmbedding s) C (emptySpanningCutSet s I hI C hs)
    (emptySpanningCutSet_cuts s I hI C hs)

@[simp]
theorem emptySpanningChildrenEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (K : {K : BoundaryInterval n // C.Consecutive K}) :
    ((emptySpanningChildrenEquiv s I hI C hs) K).val =
      OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val := rfl

/-- The canonical half-open part containing s is strictly spanning because s is not a cut. -/
theorem exists_spanning_part (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    ∃ k : Fin C.toComposition.parts,
      (C.toComposition.part k).left < s ∧ s < (C.toComposition.part k).right := by
  have hb : (collapseInterval s I hI).left < s ∧ s < (collapseInterval s I hI).right :=
    span_collapsed_bounds s I hL hR
  obtain ⟨k, hk⟩ := C.toComposition.exists_halfOpen_part s hb.1.le hb.2
  have hc : C.Consecutive (C.toComposition.part k) := by
    simpa only [BoundaryCutSet.toComposition_cutSet] using C.toComposition.part_consecutive k
  have hne : (C.toComposition.part k).left ≠ s := by
    intro he
    exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hc.1)
  exact ⟨k, lt_of_le_of_ne hk.1 hne, hk.2⟩

/-- This is an actual part of the complete core composition, not an assumed containing interval. -/
def spanningChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) : BoundaryInterval n :=
  C.toComposition.part (Classical.choose (exists_spanning_part s I hI C hL hR hs))

theorem spanningChild_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    C.Consecutive (spanningChild s I hI C hL hR hs) := by
  simpa only [spanningChild, BoundaryCutSet.toComposition_cutSet] using
    C.toComposition.part_consecutive (Classical.choose (exists_spanning_part s I hI C hL hR hs))

theorem spanningChild_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    (spanningChild s I hI C hL hR hs).left < s ∧
      s < (spanningChild s I hI C hL hR hs).right := by
  simpa only [spanningChild] using
    Classical.choose_spec (exists_spanning_part s I hI C hL hR hs)

/-- Every consecutive core interval strictly spanning s is that same actual part. -/
theorem spanningChild_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hk : K.left < s ∧ s < K.right) :
    K = spanningChild s I hI C hL hR hs := by
  have hc : C.toComposition.cutSet.Consecutive K := by
    simpa only [BoundaryCutSet.toComposition_cutSet] using hK
  obtain ⟨k, he⟩ := C.toComposition.exists_part_of_consecutive K hc
  have hks : (C.toComposition.part k).left < s ∧ s < (C.toComposition.part k).right := by
    simpa only [he] using hk
  have hi := C.toComposition.part_interior_unique s hks
    (Classical.choose_spec (exists_spanning_part s I hI C hL hR hs))
  change K = C.toComposition.part (Classical.choose (exists_spanning_part s I hI C hL hR hs))
  exact he.symm.trans (congrArg C.toComposition.part hi)

/-- Every other actual core child lies strictly on one side of the missing cut. -/
theorem spanningChild_other (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningChild s I hI C hL hR hs) : K.right < s ∨ s < K.left := by
  have hleft : K.left ≠ s := by
    intro he
    exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hK.1)
  have hright : K.right ≠ s := by
    intro he
    exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hK.2.1)
  by_cases hr : K.right < s
  · exact Or.inl hr
  · right
    have hsr : s < K.right := lt_of_le_of_ne (le_of_not_gt hr) hright.symm
    have hn : ¬ K.left < s := by
      intro hl
      exact hne (spanningChild_unique s I hI C hL hR hs K hK ⟨hl, hsr⟩)
    exact lt_of_le_of_ne (le_of_not_gt hn) hleft.symm

/-- The distinguished expanded child strictly contains both physical duplicate positions. -/
theorem emptySpanning_spanningChild_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    (OrderedBoundaryTransport.interval (startingOldEmbedding s)
      (spanningChild s I hI C hL hR hs)).left < A s ∧
    B s < (OrderedBoundaryTransport.interval (startingOldEmbedding s)
      (spanningChild s I hI C hL hR hs)).right := by
  have hb := spanningChild_bounds s I hI C hL hR hs
  constructor
  · change old s (spanningChild s I hI C hL hR hs).left < A s
    exact lt_of_lt_of_eq (old_strictMono s hb.1) (old_self s)
  · exact starting_B_lt_old s _ hb.2

theorem emptySpanning_otherChild_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningChild s I hI C hL hR hs) :
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) K).right < A s ∨
      B s < (OrderedBoundaryTransport.interval (startingOldEmbedding s) K).left := by
  rcases spanningChild_other s I hI C hL hR hs K hK hne with hr | hl
  · left
    change old s K.right < A s
    exact lt_of_lt_of_eq (old_strictMono s hr) (old_self s)
  · exact Or.inr (starting_B_lt_old s K.left hl)

theorem emptySpanning_spanningChild_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    (emptySpanningCutSet s I hI C hs).Consecutive
      (OrderedBoundaryTransport.interval (startingOldEmbedding s)
        (spanningChild s I hI C hL hR hs)) :=
  (consecutive_ordered_image_iff (startingOldEmbedding s) C (emptySpanningCutSet s I hI C hs)
    (emptySpanningCutSet_cuts s I hI C hs) _).mpr (spanningChild_consecutive s I hI C hL hR hs)

/-- This is an exhaustive statement about the actual expanded child domain. -/
theorem emptySpanning_child_trichotomy (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (J : BoundaryInterval (n + 1)) (hJ : (emptySpanningCutSet s I hI C hs).Consecutive J) :
    J = OrderedBoundaryTransport.interval (startingOldEmbedding s)
        (spanningChild s I hI C hL hR hs) ∨ J.right < A s ∨ B s < J.left := by
  obtain ⟨K, hK, he⟩ := consecutive_ordered_image_exhaust (startingOldEmbedding s) C
    (emptySpanningCutSet s I hI C hs) (emptySpanningCutSet_cuts s I hI C hs) J hJ
  by_cases hk : K = spanningChild s I hI C hL hR hs
  · exact Or.inl (he.symm.trans (congrArg (OrderedBoundaryTransport.interval (startingOldEmbedding s)) hk))
  · right
    have hb := emptySpanning_otherChild_bounds s I hI C hL hR hs K hK hk
    simpa only [he] using hb

theorem emptySpanning_spanningChild_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (J : BoundaryInterval (n + 1)) (hJ : (emptySpanningCutSet s I hI C hs).Consecutive J)
    (hj : J.left < A s ∧ B s < J.right) :
    J = OrderedBoundaryTransport.interval (startingOldEmbedding s)
      (spanningChild s I hI C hL hR hs) := by
  rcases emptySpanning_child_trichotomy s I hI C hL hR hs J hJ with he | hr | hl
  · exact he
  · exact False.elim (lt_asymm (lt_trans (A_lt_B s) hj.2) hr)
  · exact False.elim (lt_asymm (lt_trans hj.1 (A_lt_B s)) hl)

end
end SM.SoftDuplication
