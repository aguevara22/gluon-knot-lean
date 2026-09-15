namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Interior membership removes precisely the two fixed endpoint cuts. -/
theorem starting_mem_interior_iff {m : ℕ} [NeZero m] {J : BoundaryInterval m}
    (C : BoundaryCutSet J) (k : Fin m) :
    k ∈ C.interior.val ↔ k ∈ C.cuts ∧ J.left < k ∧ k < J.right := by
  constructor
  · intro hk
    refine ⟨?_, C.interior.property k hk⟩
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
  · rintro ⟨hk, hl, hr⟩
    exact Finset.mem_erase.mpr ⟨ne_of_lt hr,
      Finset.mem_erase.mpr ⟨ne_of_gt hl, hk⟩⟩

theorem starting_old_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left = A s) (hR : B s < I.right) :
    old s (collapseInterval s I hI).left = I.left ∧
      old s (collapseInterval s I hI).right = I.right := by
  constructor
  · rw [starting_core_left s I hI hL, old_self, hL]
  · exact old_collapse_of_ne_B s I.right (ne_of_gt hR)

/-- The distinguished endpoint is never a core interior gate. -/
theorem starting_interior_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (x : {k : Fin n // k ∈ C.interior.val}) : s < x.val := by
  have hx := (C.interior.property x.val x.property).1
  simpa only [starting_core_left s I hI hL] using hx

/-- Row zero retains exactly the old images of the core interior cuts. -/
theorem starting_zero_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 0).interior.val = C.interior.val.image (old s) := by
  have he := starting_old_endpoints s I hI hL hR
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpl, hpr⟩ := (starting_mem_interior_iff _ p).mp hp
    rw [startingCutSet_zero_cuts] at hpc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hpc
    apply Finset.mem_image.mpr
    refine ⟨k, (starting_mem_interior_iff C k).mpr ⟨hk, ?_, ?_⟩, rfl⟩
    · apply (old_strictMono s).lt_iff_lt.mp
      exact lt_of_eq_of_lt he.1 hpl
    · apply (old_strictMono s).lt_iff_lt.mp
      exact lt_of_lt_of_eq hpr he.2.symm
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hkc, hkl, hkr⟩ := (starting_mem_interior_iff C k).mp hk
    apply (starting_mem_interior_iff _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [startingCutSet_zero_cuts]
      exact Finset.mem_image.mpr ⟨k, hkc, rfl⟩
    · exact lt_of_eq_of_lt he.1.symm (old_strictMono s hkl)
    · exact lt_of_lt_of_eq (old_strictMono s hkr) he.2

/-- Row one adds precisely the new interior position B. -/
theorem starting_one_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).interior.val =
      insert (B s) (C.interior.val.image (old s)) := by
  rw [← starting_zero_interior s I hI C hL hR]
  ext p
  simp only [starting_mem_interior_iff, startingCutSet_one_insert_B, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hl, hr⟩
    exact hp.elim Or.inl (fun h => Or.inr ⟨h, hl, hr⟩)
  · rintro (rfl | ⟨hp, hl, hr⟩)
    · exact ⟨Or.inl rfl, by rw [hL]; exact A_lt_B s, hR⟩
    · exact ⟨Or.inr hp, hl, hr⟩

def startingInteriorZeroMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 0).interior.val} :=
  ⟨old s x.val, by
    rw [starting_zero_interior]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

/-- The actual old-position map, with every core interior cut represented once. -/
def startingInteriorZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    {k : Fin n // k ∈ C.interior.val} ≃
      {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 0).interior.val} :=
  Equiv.ofBijective (startingInteriorZeroMap s I hI C hL hR) ⟨by
    intro x y he
    apply Subtype.ext
    exact old_injective s (congrArg Subtype.val he), by
    intro p
    have hp := p.property
    rw [starting_zero_interior] at hp
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp] theorem startingInteriorZeroEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((startingInteriorZeroEquiv s I hI C hL hR) x).val = old s x.val := rfl

def startingInteriorOneMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    Unit ⊕ {k : Fin n // k ∈ C.interior.val} →
      {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 1).interior.val}
  | Sum.inl _ => ⟨B s, by rw [starting_one_interior]; exact Finset.mem_insert_self _ _⟩
  | Sum.inr x => ⟨old s x.val, by
      rw [starting_one_interior]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)⟩

/-- The new B gate and all inherited gates form a disjoint, exhaustive domain. -/
def startingInteriorOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (Unit ⊕ {k : Fin n // k ∈ C.interior.val}) ≃
      {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 1).interior.val} :=
  Equiv.ofBijective (startingInteriorOneMap s I hI C hL hR) ⟨by
    intro x y he
    have hv := congrArg Subtype.val he
    cases x with
    | inl u =>
      cases y with
      | inl v => cases u; cases v; rfl
      | inr y => exact False.elim (old_ne_B s y.val hv.symm)
    | inr x =>
      cases y with
      | inl u => exact False.elim (old_ne_B s x.val hv)
      | inr y => exact congrArg Sum.inr (Subtype.ext (old_injective s hv))
    , by
    intro p
    have hp := p.property
    rw [starting_one_interior] at hp
    rcases Finset.mem_insert.mp hp with he | hp
    · exact ⟨Sum.inl (), Subtype.ext he.symm⟩
    · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
      exact ⟨Sum.inr ⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp] theorem startingInteriorOneEquiv_inl_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (u : Unit) :
    ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inl u)).val = B s := rfl

@[simp] theorem startingInteriorOneEquiv_inr_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)).val = old s x.val := rfl

/-- Both actual near neighbors in row zero are old images of core neighbors. -/
theorem starting_zero_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 0).nearAtCut
        ((startingInteriorZeroEquiv s I hI C hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.nearAtCut x) := by
  let S := startingCutSet s I hI C hL hR 0
  let y := (startingInteriorZeroEquiv s I hI C hL hR) x
  have hl := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (startingCutSet_zero_cuts s I hI C hL hR) (C.nearLeftInterval x)).mpr
      (C.nearLeftInterval_consecutive x)
  have hr := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (startingCutSet_zero_cuts s I hI C hL hR) (C.nearRightInterval x)).mpr
      (C.nearRightInterval_consecutive x)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change old s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle])
  · change (S.nearAtCut y).middle = old s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle]
    rfl
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change old s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle])

theorem starting_zero_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 0).farAtCut
        ((startingInteriorZeroEquiv s I hI C hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := starting_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((startingCutSet s I hI C hL hR 0).farAtCut
        ((startingInteriorZeroEquiv s I hI C hL hR) x)).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- Row one's inherited near triples use the tail section, including its B endpoint. -/
theorem starting_one_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 1).nearAtCut
        ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.nearAtCut x) := by
  let S := startingCutSet s I hI C hL hR 1
  let y := (startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)
  have hx : startingTailEmbedding s x.val = old s x.val :=
    startingTail_eq_old s x.val (ne_of_gt (starting_interior_gt s I hI C hL x))
  have hl := starting_one_mapped_consecutive s I hI C hL hR
    (C.nearLeftInterval x) (C.nearLeftInterval_consecutive x)
  have hr := starting_one_mapped_consecutive s I hI C hL hR
    (C.nearRightInterval x) (C.nearRightInterval_consecutive x)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change startingTailEmbedding s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle, hx])
  · change (S.nearAtCut y).middle = startingTailEmbedding s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle, hx]
    rfl
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change startingTailEmbedding s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle, hx])

/-- Far triples retain the full parent left endpoint A, even in row one. -/
theorem starting_one_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 1).farAtCut
        ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := starting_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((startingCutSet s I hI C hL hR 1).farAtCut
        ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x))).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- The new B gate sees the actual singleton on its left and first tail child on its right. -/
theorem starting_new_near_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    let T := (startingCutSet s I hI C hL hR 1).nearAtCut
      ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inl ()))
    T.lower = A s ∧ T.middle = B s ∧
      T.upper = old s (startingFirstChild s I hI C).right := by
  let S := startingCutSet s I hI C hL hR 1
  let y := (startingInteriorOneEquiv s I hI C hL hR) (Sum.inl ())
  have hl := starting_one_duplicate_consecutive s I hI C hL hR
  have hr := starting_one_mapped_consecutive s I hI C hL hR
    (startingFirstChild s I hI C) (startingFirstChild_consecutive s I hI C)
  have he := starting_first_one_endpoints s I hI C hL
  refine ⟨?_, ?_, ?_⟩
  · exact S.nearAtCut_lower_eq_of_consecutive y (duplicateInterval s) hl rfl
  · exact S.nearAtCut_middle y
  · exact (S.nearAtCut_upper_eq_of_consecutive y
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) (startingFirstChild s I hI C))
      hr he.1).trans he.2

theorem starting_new_far_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    let T := (startingCutSet s I hI C hL hR 1).farAtCut
      ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inl ()))
    T.lower = A s ∧ T.middle = B s ∧ T.upper = I.right := by
  refine ⟨hL, ?_, rfl⟩
  exact (startingCutSet s I hI C hL hR 1).farAtCut_middle _

end
end SM.SoftDuplication
