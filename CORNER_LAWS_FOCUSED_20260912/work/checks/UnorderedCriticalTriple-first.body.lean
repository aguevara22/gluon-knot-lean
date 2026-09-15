namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every source vertex label occurs in the actual boundary reading at a root. -/
theorem boundaryIndex_surjective (g : ZMod n) : Function.Surjective (boundaryIndex g) := by
  intro k
  refine ⟨⟨(k - g - 1).val, ZMod.val_lt _⟩, ?_⟩
  change g + ((k - g - 1).val : ZMod n) + 1 = k
  rw [ZMod.natCast_zmod_val]
  ring

namespace IncreasingBoundaryTriple

/-- Sorting three distinct positions loses no ordering case. -/
theorem exists_positionSet (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ t : IncreasingBoundaryTriple n, t.positionSet = {a, b, c} := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact ⟨⟨a, b, c, hab, hbc⟩, rfl⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · refine ⟨⟨a, c, b, hac, hcb⟩, ?_⟩
        ext x
        simp [positionSet, or_comm, or_left_comm, or_assoc]
      · refine ⟨⟨c, a, b, hca, hab⟩, ?_⟩
        ext x
        simp [positionSet, or_comm, or_left_comm, or_assoc]
  · rcases lt_or_gt_of_ne hac with hac | hca
    · refine ⟨⟨b, a, c, hba, hac⟩, ?_⟩
      ext x
      simp [positionSet, or_comm, or_left_comm, or_assoc]
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · refine ⟨⟨b, c, a, hbc, hca⟩, ?_⟩
        ext x
        simp [positionSet, or_comm, or_left_comm, or_assoc]
      · refine ⟨⟨c, b, a, hcb, hba⟩, ?_⟩
        ext x
        simp [positionSet, or_comm, or_left_comm, or_assoc]

/-- Every unordered three-vertex support has one exact increasing boundary
triple at the chosen root. This uses labels only, not geometric distinctness. -/
theorem existsUnique_vertexSet (g : ZMod n) (K : Finset (ZMod n)) (hK : K.card = 3) :
    ∃! t : IncreasingBoundaryTriple n, t.vertexSet g = K := by
  classical
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hK
  obtain ⟨a, ha⟩ := boundaryIndex_surjective g i
  obtain ⟨b, hb⟩ := boundaryIndex_surjective g j
  obtain ⟨c, hc⟩ := boundaryIndex_surjective g k
  have hab : a ≠ b := by
    intro he
    exact hij (ha.symm.trans ((congrArg (boundaryIndex g) he).trans hb))
  have hac : a ≠ c := by
    intro he
    exact hik (ha.symm.trans ((congrArg (boundaryIndex g) he).trans hc))
  have hbc : b ≠ c := by
    intro he
    exact hjk (hb.symm.trans ((congrArg (boundaryIndex g) he).trans hc))
  obtain ⟨t, ht⟩ := exists_positionSet a b c hab hac hbc
  have hv : t.vertexSet g = {i, j, k} := by
    simp only [vertexSet, ht, Finset.image_insert, Finset.image_singleton, ha, hb, hc]
  exact ⟨t, hv, fun u hu => vertexSet_injective g (hu.trans hv.symm)⟩

end IncreasingBoundaryTriple

/-- Transport physical pairwise distinctness on the source support to the three
ordered points. The geometric hypothesis is never inferred from zero support. -/
theorem boundary_points_distinct_of_support (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (K : Finset (ZMod n)) (hK : t.vertexSet g = K)
    (hsep : (K : Set (ZMod n)).Pairwise (fun i j => P i ≠ P j)) :
    boundaryWord P g t.middle ≠ boundaryWord P g t.lower ∧
      boundaryWord P g t.upper ≠ boundaryWord P g t.middle ∧
      boundaryWord P g t.upper ≠ boundaryWord P g t.lower := by
  have hm (k : Fin n) (hk : k ∈ t.positionSet) : boundaryIndex g k ∈ (K : Set (ZMod n)) := by
    change boundaryIndex g k ∈ K
    rw [← hK]
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  have hlo := hm t.lower (by simp [IncreasingBoundaryTriple.positionSet])
  have hmid := hm t.middle (by simp [IncreasingBoundaryTriple.positionSet])
  have hup := hm t.upper (by simp [IncreasingBoundaryTriple.positionSet])
  refine ⟨?_, ?_, ?_⟩
  · apply hsep hmid hlo
    intro he
    exact (ne_of_gt t.lower_middle) (boundaryIndex_injective g he)
  · apply hsep hup hmid
    intro he
    exact (ne_of_gt t.middle_upper) (boundaryIndex_injective g he)
  · apply hsep hup hlo
    intro he
    exact (ne_of_gt (lt_trans t.lower_middle t.middle_upper)) (boundaryIndex_injective g he)

namespace WallGerm

theorem chi_signChanges_cyclic (w : WallGerm n) (i j k : ZMod n) :
    w.SignChanges (fun P => (chi P j k i : ℝ)) ↔
      w.SignChanges (fun P => (chi P i j k : ℝ)) := by
  simp only [chi_cyclic]

theorem chi_signChanges_swap_last (w : WallGerm n) (i j k : ZMod n) :
    w.SignChanges (fun P => (chi P i k j : ℝ)) ↔
      w.SignChanges (fun P => (chi P i j k : ℝ)) := by
  simp only [chi_swap_last, SignType.coe_neg, w.signChanges_neg]

/-- Reordering the exact three-element support preserves SignChanges. Odd
permutations negate both evaluations, so their product has the same sign. -/
theorem chi_signChanges_of_support_eq (w : WallGerm n) (a b c i j k : ZMod n)
    (he : ({i, j, k} : Finset (ZMod n)) = {a, b, c})
    (hc : ({a, b, c} : Finset (ZMod n)).card = 3)
    (h : w.SignChanges (fun P => (chi P a b c : ℝ))) :
    w.SignChanges (fun P => (chi P i j k : ℝ)) :=
  three_support_predicate (fun a b c => w.SignChanges (fun P => (chi P a b c : ℝ)))
    (w.chi_signChanges_cyclic) (w.chi_signChanges_swap_last) he hc h

/-- The source's unordered critical support and physical distinctness supply
all ordered boundary premises used by the checked response, uniquely at each
root. No named-wall restriction or choice of orientation is added. -/
theorem single_triple_boundary_data (w : WallGerm n) (g : ZMod n)
    (K : Finset (ZMod n)) (hZ : pointZeroTriples w.center = {K})
    (hsep : (K : Set (ZMod n)).Pairwise (fun i j => w.center i ≠ w.center j))
    (a b c : ZMod n) (habc : ({a, b, c} : Finset (ZMod n)) = K)
    (hchange : w.SignChanges (fun P => (chi P a b c : ℝ))) :
    ∃! t : IncreasingBoundaryTriple n,
      t.vertexSet g = K ∧
      (boundaryWord w.center g t.middle ≠ boundaryWord w.center g t.lower ∧
        boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.middle ∧
        boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.lower) ∧
      w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
        (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) := by
  have hcard : K.card = 3 := (singlePointTriple_data hZ).1
  obtain ⟨t, ht, hu⟩ := IncreasingBoundaryTriple.existsUnique_vertexSet g K hcard
  have hpoints := boundary_points_distinct_of_support w.center g t K ht hsep
  have he : ({boundaryIndex g t.upper, boundaryIndex g t.middle,
      boundaryIndex g t.lower} : Finset (ZMod n)) = {a, b, c} :=
    (t.vertexSet_reversed g).symm.trans (ht.trans habc.symm)
  have hsign := w.chi_signChanges_of_support_eq a b c _ _ _ he
    (by simpa only [habc] using hcard) hchange
  exact ⟨t, ⟨ht, hpoints, hsign⟩, fun u hup => hu u hup.1⟩

end WallGerm
end
end SM
