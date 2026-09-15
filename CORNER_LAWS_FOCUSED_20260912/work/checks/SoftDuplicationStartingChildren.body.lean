namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Exact membership in an increasing image of a complete cut set. -/
theorem cut_mem_ordered_image {m : ℕ} (e : Fin n ↪o Fin m)
    {J : BoundaryInterval n} (C : BoundaryCutSet J) (k : Fin n) :
    e k ∈ C.cuts.image e ↔ k ∈ C.cuts := by
  constructor
  · intro h
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h
    exact e.injective he ▸ hl
  · intro h
    exact Finset.mem_image.mpr ⟨k, h, rfl⟩

/-- Consecutiveness is preserved and reflected by an actual cut-set image. -/
theorem consecutive_ordered_image_iff {m : ℕ} [NeZero m]
    (e : Fin n ↪o Fin m) {J : BoundaryInterval n} {I : BoundaryInterval m}
    (C : BoundaryCutSet J) (T : BoundaryCutSet I) (hcuts : T.cuts = C.cuts.image e)
    (K : BoundaryInterval n) :
    T.Consecutive (OrderedBoundaryTransport.interval e K) ↔ C.Consecutive K := by
  constructor
  · rintro ⟨hl, hr, hn⟩
    have hcl : K.left ∈ C.cuts := (cut_mem_ordered_image e C K.left).mp (by
      rw [← hcuts]; exact hl)
    have hcr : K.right ∈ C.cuts := (cut_mem_ordered_image e C K.right).mp (by
      rw [← hcuts]; exact hr)
    refine ⟨hcl, hcr, ?_⟩
    intro k hk hb
    have hm : e k ∈ T.cuts := by
      rw [hcuts]
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    exact hn (e k) hm ⟨e.strictMono hb.1, e.strictMono hb.2⟩
  · rintro ⟨hl, hr, hn⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hcuts]
      exact Finset.mem_image.mpr ⟨K.left, hl, rfl⟩
    · rw [hcuts]
      exact Finset.mem_image.mpr ⟨K.right, hr, rfl⟩
    · intro p hp hb
      rw [hcuts] at hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      exact hn k hk ⟨e.strictMono.lt_iff_lt.mp hb.1, e.strictMono.lt_iff_lt.mp hb.2⟩

/-- Every child of the image cut set comes from an actual core child. -/
theorem consecutive_ordered_image_exhaust {m : ℕ} [NeZero m]
    (e : Fin n ↪o Fin m) {J : BoundaryInterval n} {I : BoundaryInterval m}
    (C : BoundaryCutSet J) (T : BoundaryCutSet I) (hcuts : T.cuts = C.cuts.image e)
    (K : BoundaryInterval m) (hK : T.Consecutive K) :
    ∃ L : BoundaryInterval n, C.Consecutive L ∧ OrderedBoundaryTransport.interval e L = K := by
  have hl : K.left ∈ C.cuts.image e := by rw [← hcuts]; exact hK.1
  have hr : K.right ∈ C.cuts.image e := by rw [← hcuts]; exact hK.2.1
  obtain ⟨l, hlc, hel⟩ := Finset.mem_image.mp hl
  obtain ⟨r, hrc, her⟩ := Finset.mem_image.mp hr
  have hlr : l < r := e.strictMono.lt_iff_lt.mp (by rw [hel, her]; exact K.increasing)
  let L : BoundaryInterval n := ⟨l, r, hlr⟩
  have he : OrderedBoundaryTransport.interval e L = K :=
    BoundaryInterval.eq_of_endpoints hel her
  refine ⟨L, (consecutive_ordered_image_iff e C T hcuts L).mp ?_, he⟩
  rw [he]
  exact hK

def consecutiveOrderedImageEquiv {m : ℕ} [NeZero m]
    (e : Fin n ↪o Fin m) {J : BoundaryInterval n} {I : BoundaryInterval m}
    (C : BoundaryCutSet J) (T : BoundaryCutSet I) (hcuts : T.cuts = C.cuts.image e) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {L : BoundaryInterval m // T.Consecutive L} :=
  Equiv.ofBijective (fun K => ⟨OrderedBoundaryTransport.interval e K.val,
    (consecutive_ordered_image_iff e C T hcuts K.val).mpr K.property⟩) ⟨by
    intro K L he
    apply Subtype.ext
    exact OrderedBoundaryTransport.interval_injective e (congrArg Subtype.val he), by
    intro L
    obtain ⟨K, hK, he⟩ := consecutive_ordered_image_exhaust e C T hcuts L.val L.property
    exact ⟨⟨K, hK⟩, Subtype.ext he⟩⟩

def startingOldEmbedding (s : Fin n) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (old s) (old_strictMono s)

/-- The increasing section which retains the core endpoint at B instead of A. -/
def startingTailEmbedding (s : Fin n) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono ((A s).succAbove) (Fin.strictMono_succAbove (A s))

@[simp] theorem startingTail_self (s : Fin n) : startingTailEmbedding s s = B s :=
  Fin.succAbove_castSucc_self s

@[simp] theorem collapse_startingTail (s k : Fin n) :
    collapse s (startingTailEmbedding s k) = k := Fin.predAbove_succAbove s k

theorem startingTail_eq_old (s k : Fin n) (hk : k ≠ s) :
    startingTailEmbedding s k = old s k :=
  (collapse_eq_iff_of_ne s k hk _).mp (collapse_startingTail s k)

theorem starting_B_lt_old (s k : Fin n) (hk : s < k) : B s < old s k := by
  have h := (startingTailEmbedding s).strictMono hk
  simpa only [startingTail_self, startingTail_eq_old s k (ne_of_gt hk)] using h

def startingCutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (i : Fin 2) : BoundaryCutSet I :=
  expandCuts s I hI C (startingRows s I hI C hL hR i)

theorem starting_core_left (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left = A s) :
    (collapseInterval s I hI).left = s := by
  change collapse s I.left = s
  rw [hL, collapse_A]

theorem starting_core_cut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) : s ∈ C.cuts := by
  have hm := C.left_mem
  exact (congrArg (fun x : Fin n => x ∈ C.cuts) (starting_core_left s I hI hL)).mp hm

theorem starting_old_cut_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (k : Fin n) (hk : k ∈ C.cuts) :
    I.left ≤ old s k ∧ old s k ≤ I.right := by
  have hb := C.bounds k hk
  have hsk : s ≤ k := by simpa only [starting_core_left s I hI hL] using hb.1
  constructor
  · rw [hL, ← old_self s]
    exact (old_strictMono s).monotone hsk
  · have hright := (old_strictMono s).monotone hb.2
    change old s k ≤ old s (collapse s I.right) at hright
    rwa [old_collapse_of_ne_B s I.right (ne_of_gt hR)] at hright

/-- Row zero is exactly the old-position image, with no cut at B. -/
theorem startingCutSet_zero_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 0).cuts = C.cuts.image (old s) := by
  ext p
  have hm := mem_expandCuts s I hI C (startingRows s I hI C hL hR 0) p
  change p ∈ (startingCutSet s I hI C hL hR 0).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (startingRows s I hI C hL hR 0).val at hm
  simp only [startingRows, Matrix.cons_val_zero, Finset.mem_singleton] at hm
  rw [hm]
  constructor
  · rintro (h | rfl)
    · have he := (collapse_eq_iff_of_ne s (collapse s p) h.2.2 p).mp rfl
      exact Finset.mem_image.mpr ⟨collapse s p, h.2.1, he.symm⟩
    · exact Finset.mem_image.mpr ⟨s, starting_core_cut s I hI C hL, old_self s⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    by_cases hks : k = s
    · exact Or.inr (by rw [hks, old_self])
    · left
      exact ⟨starting_old_cut_bounds s I hI C hL hR k hk,
        by simpa only [collapse_old] using hk, by simpa only [collapse_old] using hks⟩

theorem startingCutSet_one_insert_B (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).cuts =
      insert (B s) (startingCutSet s I hI C hL hR 0).cuts := by
  ext p
  simp only [startingCutSet, mem_expandCuts, startingRows, Matrix.cons_val_zero,
    Matrix.cons_val_one, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem starting_sections_cut_image (s : Fin n) (C : Finset (Fin n)) (hs : s ∈ C) :
    insert (B s) (C.image (old s)) = insert (A s) (C.image (startingTailEmbedding s)) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hs, startingTail_self s⟩)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      by_cases hks : k = s
      · exact Finset.mem_insert.mpr (Or.inl (by rw [hks, old_self]))
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨k, hk, startingTail_eq_old s k hks⟩)
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hs, old_self s⟩)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      by_cases hks : k = s
      · exact Finset.mem_insert.mpr (Or.inl (by rw [hks, startingTail_self]))
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨k, hk, (startingTail_eq_old s k hks).symm⟩)

/-- Row one is a leading A followed by the entire core cut list based at B. -/
theorem startingCutSet_one_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).cuts =
      insert (A s) (C.cuts.image (startingTailEmbedding s)) := by
  rw [startingCutSet_one_insert_B, startingCutSet_zero_cuts]
  exact starting_sections_cut_image s C.cuts (starting_core_cut s I hI C hL)

/-- The actual first child is defined even when the core composition is unary. -/
def startingFirstChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    BoundaryInterval n := C.toComposition.part ⟨0, C.toComposition.parts_pos⟩

theorem startingFirstChild_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    C.Consecutive (startingFirstChild s I hI C) := by
  simpa only [startingFirstChild, BoundaryCutSet.toComposition_cutSet] using
    C.toComposition.part_consecutive ⟨0, C.toComposition.parts_pos⟩

theorem startingFirstChild_left (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) : (startingFirstChild s I hI C).left = s := by
  change C.toComposition.cut 0 = s
  rw [C.toComposition.first, starting_core_left s I hI hL]

theorem startingFirstChild_right (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) :
    s < (startingFirstChild s I hI C).right ∧ (startingFirstChild s I hI C).right ∈ C.cuts := by
  refine ⟨?_, (startingFirstChild_consecutive s I hI C).2.1⟩
  exact lt_of_eq_of_lt (startingFirstChild_left s I hI C hL).symm
    (startingFirstChild s I hI C).increasing

theorem startingFirstChild_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (K : BoundaryInterval n) (hK : C.Consecutive K) (hk : K.left = s) :
    K = startingFirstChild s I hI C :=
  C.consecutive_eq_of_left hK (startingFirstChild_consecutive s I hI C)
    (hk.trans (startingFirstChild_left s I hI C hL).symm)

theorem startingFirstChild_right_le (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (k : Fin n) (hk : k ∈ C.cuts) (hsk : s < k) :
    (startingFirstChild s I hI C).right ≤ k := by
  apply le_of_not_gt
  intro hlt
  exact (startingFirstChild_consecutive s I hI C).2.2 k hk
    ⟨by rw [startingFirstChild_left s I hI C hL]; exact hsk, hlt⟩

def startingChildrenZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {J : BoundaryInterval (n + 1) // (startingCutSet s I hI C hL hR 0).Consecutive J} :=
  consecutiveOrderedImageEquiv (startingOldEmbedding s) C (startingCutSet s I hI C hL hR 0)
    (startingCutSet_zero_cuts s I hI C hL hR)

theorem starting_tail_cut_gt_A (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (k : Fin n) (hk : k ∈ C.cuts) : A s < startingTailEmbedding s k := by
  have hsk : s ≤ k := by
    simpa only [starting_core_left s I hI hL] using (C.bounds k hk).1
  have hb : B s ≤ startingTailEmbedding s k := by
    rw [← startingTail_self s]
    exact (startingTailEmbedding s).monotone hsk
  exact lt_of_lt_of_le (A_lt_B s) hb

/-- Every core child remains consecutive after renaming its first endpoint
to B and adjoining the leading cut A. -/
theorem starting_one_mapped_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (K : BoundaryInterval n) (hK : C.Consecutive K) :
    (startingCutSet s I hI C hL hR 1).Consecutive
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) := by
  let U := OrderedBoundaryTransport.cutSet (startingTailEmbedding s) C
  have hU : U.Consecutive (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) :=
    (consecutive_ordered_image_iff (startingTailEmbedding s) C U rfl K).mpr hK
  refine ⟨?_, ?_, ?_⟩
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K.left, hK.1, rfl⟩)
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K.right, hK.2.1, rfl⟩)
  · intro p hp hb
    rw [startingCutSet_one_cuts] at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact lt_asymm (starting_tail_cut_gt_A s I hI C hL K.left hK.1) hb.1
    · exact hU.2.2 p hp hb

/-- The only extra child in row one is the actual consecutive interval A,B. -/
theorem starting_one_duplicate_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).Consecutive (duplicateInterval s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_self _ _
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨s, starting_core_cut s I hI C hL, startingTail_self s⟩)
  · intro p _ hb
    have hl : s.val < p.val := hb.1
    have hr : p.val < s.val + 1 := hb.2
    omega

/-- Exhaustive classification of actual row-one consecutive children. -/
theorem starting_one_consecutive_iff (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (J : BoundaryInterval (n + 1)) :
    (startingCutSet s I hI C hL hR 1).Consecutive J ↔
      J = duplicateInterval s ∨ ∃ K : BoundaryInterval n,
        C.Consecutive K ∧ OrderedBoundaryTransport.interval (startingTailEmbedding s) K = J := by
  constructor
  · intro hJ
    by_cases hja : J.left = A s
    · exact Or.inl ((startingCutSet s I hI C hL hR 1).consecutive_eq_of_left hJ
        (starting_one_duplicate_consecutive s I hI C hL hR) hja)
    · right
      have hl : J.left ∈ C.cuts.image (startingTailEmbedding s) := by
        have hm := hJ.1
        rw [startingCutSet_one_cuts] at hm
        exact (Finset.mem_insert.mp hm).resolve_left hja
      have har : A s < J.right := by
        have hb := ((startingCutSet s I hI C hL hR 1).bounds J.left hJ.1).1
        have hal : A s ≤ J.left := by simpa only [hL] using hb
        exact lt_of_le_of_lt hal J.increasing
      have hr : J.right ∈ C.cuts.image (startingTailEmbedding s) := by
        have hm := hJ.2.1
        rw [startingCutSet_one_cuts] at hm
        exact (Finset.mem_insert.mp hm).resolve_left (ne_of_gt har)
      let U := OrderedBoundaryTransport.cutSet (startingTailEmbedding s) C
      have hU : U.Consecutive J := by
        refine ⟨hl, hr, ?_⟩
        intro p hp hb
        have ht : p ∈ (startingCutSet s I hI C hL hR 1).cuts := by
          rw [startingCutSet_one_cuts]
          exact Finset.mem_insert_of_mem hp
        exact hJ.2.2 p ht hb
      exact consecutive_ordered_image_exhaust (startingTailEmbedding s) C U rfl J hU
  · rintro (rfl | ⟨K, hK, rfl⟩)
    · exact starting_one_duplicate_consecutive s I hI C hL hR
    · exact starting_one_mapped_consecutive s I hI C hL hR K hK

def startingChildOneMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    Unit ⊕ {K : BoundaryInterval n // C.Consecutive K} →
      {J : BoundaryInterval (n + 1) // (startingCutSet s I hI C hL hR 1).Consecutive J} :=
  Sum.elim (fun _ : Unit => ⟨duplicateInterval s, starting_one_duplicate_consecutive s I hI C hL hR⟩)
    (fun K => ⟨OrderedBoundaryTransport.interval (startingTailEmbedding s) K.val,
      starting_one_mapped_consecutive s I hI C hL hR K.val K.property⟩)

/-- Actual child-domain bijection: one singleton plus every core child. -/
def startingChildrenOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (Unit ⊕ {K : BoundaryInterval n // C.Consecutive K}) ≃
      {J : BoundaryInterval (n + 1) // (startingCutSet s I hI C hL hR 1).Consecutive J} :=
  Equiv.ofBijective (startingChildOneMap s I hI C hL hR) ⟨by
    intro a b he
    cases a with
    | inl u =>
      cases b with
      | inl v => cases u; cases v; rfl
      | inr K =>
        have hx : A s = startingTailEmbedding s K.val.left :=
          congrArg (fun J => J.val.left) he
        exact False.elim ((ne_of_lt (starting_tail_cut_gt_A s I hI C hL K.val.left K.property.1)) hx)
    | inr K =>
      cases b with
      | inl u =>
        have hx : startingTailEmbedding s K.val.left = A s :=
          congrArg (fun J => J.val.left) he
        exact False.elim ((ne_of_gt (starting_tail_cut_gt_A s I hI C hL K.val.left K.property.1)) hx)
      | inr L =>
        have hval : K.val = L.val := OrderedBoundaryTransport.interval_injective
          (startingTailEmbedding s) (congrArg Subtype.val he)
        exact congrArg Sum.inr (Subtype.ext hval), by
    intro J
    rcases (starting_one_consecutive_iff s I hI C hL hR J.val).mp J.property with h | ⟨K, hK, he⟩
    · exact ⟨Sum.inl (), Subtype.ext h.symm⟩
    · exact ⟨Sum.inr ⟨K, hK⟩, Subtype.ext he⟩⟩

/-- The row-zero first child really spans both duplicate occurrences. -/
theorem starting_first_zero_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) :
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)).left = A s ∧
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)).right =
      old s (startingFirstChild s I hI C).right ∧
    B s < old s (startingFirstChild s I hI C).right := by
  refine ⟨?_, rfl, starting_B_lt_old s _ (startingFirstChild_right s I hI C hL).1⟩
  change old s (startingFirstChild s I hI C).left = A s
  rw [startingFirstChild_left s I hI C hL, old_self]

/-- After the singleton, the same first core child starts at B. -/
theorem starting_first_one_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) :
    (OrderedBoundaryTransport.interval (startingTailEmbedding s) (startingFirstChild s I hI C)).left = B s ∧
    (OrderedBoundaryTransport.interval (startingTailEmbedding s) (startingFirstChild s I hI C)).right =
      old s (startingFirstChild s I hI C).right := by
  constructor
  · change startingTailEmbedding s (startingFirstChild s I hI C).left = B s
    rw [startingFirstChild_left s I hI C hL, startingTail_self]
  · exact startingTail_eq_old s _ (ne_of_gt (startingFirstChild_right s I hI C hL).1)

theorem starting_otherChild_left_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ startingFirstChild s I hI C) : s < K.left := by
  have hle : s ≤ K.left := by
    simpa only [starting_core_left s I hI hL] using (C.bounds K.left hK.1).1
  apply lt_of_le_of_ne hle
  intro he
  exact hne (startingFirstChild_unique s I hI C hL K hK he.symm)

/-- Every other child interval is literally the same in both presentations. -/
theorem starting_otherChild_map_eq (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ startingFirstChild s I hI C) :
    OrderedBoundaryTransport.interval (startingTailEmbedding s) K =
      OrderedBoundaryTransport.interval (startingOldEmbedding s) K := by
  have hl := starting_otherChild_left_gt s I hI C hL K hK hne
  apply BoundaryInterval.eq_of_endpoints
  · exact startingTail_eq_old s K.left (ne_of_gt hl)
  · exact startingTail_eq_old s K.right (ne_of_gt (lt_trans hl K.increasing))

end
end SM.SoftDuplication
