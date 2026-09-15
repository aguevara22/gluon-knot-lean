namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The concrete old section recovers both strictly spanning endpoints. -/
theorem emptySpanning_old_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right) :
    old s (collapseInterval s I hI).left = I.left ∧
      old s (collapseInterval s I hI).right = I.right :=
  ⟨old_collapse_of_ne_B s I.left (ne_of_lt (lt_trans hL (A_lt_B s))),
    old_collapse_of_ne_B s I.right (ne_of_gt hR)⟩

theorem emptySpanning_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) :
    (emptySpanningCutSet s I hI C hs).interior.val = C.interior.val.image (old s) := by
  have he := emptySpanning_old_endpoints s I hI hL hR
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpl, hpr⟩ := (starting_mem_interior_iff _ p).mp hp
    rw [emptySpanningCutSet_cuts] at hpc
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
    · rw [emptySpanningCutSet_cuts]
      exact Finset.mem_image.mpr ⟨k, hkc, rfl⟩
    · exact lt_of_eq_of_lt he.1.symm (old_strictMono s hkl)
    · exact lt_of_lt_of_eq (old_strictMono s hkr) he.2


def emptySpanningInteriorMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    {p : Fin (n + 1) // p ∈ (emptySpanningCutSet s I hI C hs).interior.val} :=
  ⟨old s x.val, by
    rw [emptySpanning_interior s I hI C hs hL hR]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

/-- The actual old-position map, with every core interior cut represented once. -/
def emptySpanningInteriorEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) :
    {k : Fin n // k ∈ C.interior.val} ≃
      {p : Fin (n + 1) // p ∈ (emptySpanningCutSet s I hI C hs).interior.val} :=
  Equiv.ofBijective (emptySpanningInteriorMap s I hI C hs hL hR) ⟨by
    intro x y he
    apply Subtype.ext
    exact old_injective s (congrArg Subtype.val he), by
    intro p
    have hp : p.val ∈ C.interior.val.image (old s) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (emptySpanning_interior s I hI C hs hL hR)) p.property
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp]
theorem emptySpanningInteriorEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((emptySpanningInteriorEquiv s I hI C hs hL hR) x).val = old s x.val := rfl


theorem emptySpanning_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (emptySpanningCutSet s I hI C hs).nearAtCut
        ((emptySpanningInteriorEquiv s I hI C hs hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.nearAtCut x) := by
  let S := emptySpanningCutSet s I hI C hs
  let y := (emptySpanningInteriorEquiv s I hI C hs hL hR) x
  have hl := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (emptySpanningCutSet_cuts s I hI C hs) (C.nearLeftInterval x)).mpr
      (C.nearLeftInterval_consecutive x)
  have hr := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (emptySpanningCutSet_cuts s I hI C hs) (C.nearRightInterval x)).mpr
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

theorem emptySpanning_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (emptySpanningCutSet s I hI C hs).farAtCut
        ((emptySpanningInteriorEquiv s I hI C hs hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := emptySpanning_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((emptySpanningCutSet s I hI C hs).farAtCut
        ((emptySpanningInteriorEquiv s I hI C hs hL hR) x)).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm


theorem emptySpanning_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((emptySpanningCutSet s I hI C hs).nearAtCut
      (emptySpanningInteriorEquiv s I hI C hs hL hR x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((emptySpanningCutSet s I hI C hs).farAtCut
      (emptySpanningInteriorEquiv s I hI C hs hL hR x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [emptySpanning_nearTriple, tripleLift_startingOld]
  · rw [emptySpanning_farTriple, tripleLift_startingOld]


theorem emptySpanning_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (emptySpanningCutSet s I hI C hs)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (emptySpanningInteriorEquiv s I hI C hs hL hR)
  intro x
  have h := emptySpanning_gate_values s I hI C hs hL hR D0 H0 tD tH x
  rw [h.1, h.2]


end
end SM.SoftDuplication
