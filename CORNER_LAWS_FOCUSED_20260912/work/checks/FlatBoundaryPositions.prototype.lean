import SM.CriticalSourceResponse
import SM.UnorderedWallTriples


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IncreasingBoundaryTriple

def positionSet (t : IncreasingBoundaryTriple n) : Finset (Fin n) :=
  {t.lower, t.middle, t.upper}

theorem positionSet_bounds (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ∈ t.positionSet) : t.lower ≤ x ∧ x ≤ t.upper := by
  simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨le_rfl, le_of_lt (lt_trans t.lower_middle t.middle_upper)⟩
  · exact ⟨le_of_lt t.lower_middle, le_of_lt t.middle_upper⟩
  · exact ⟨le_of_lt (lt_trans t.lower_middle t.middle_upper), le_rfl⟩

/-- The unordered position set determines the increasing triple. Min/max
fix both endpoints, and the distinct remaining position fixes the middle. -/
theorem positionSet_injective : Function.Injective (positionSet (n := n)) := by
  intro t u he
  have hl : t.lower = u.lower := by
    apply le_antisymm
    · exact (t.positionSet_bounds u.lower (by rw [he]; simp [positionSet])).1
    · exact (u.positionSet_bounds t.lower (by rw [← he]; simp [positionSet])).1
  have hr : t.upper = u.upper := by
    apply le_antisymm
    · exact (u.positionSet_bounds t.upper (by rw [← he]; simp [positionSet])).2
    · exact (t.positionSet_bounds u.upper (by rw [he]; simp [positionSet])).2
  have hm : t.middle = u.middle := by
    have hx : t.middle ∈ u.positionSet := by rw [← he]; simp [positionSet]
    simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ((ne_of_gt t.lower_middle) (h.trans hl.symm)).elim
    · exact h
    · exact ((ne_of_lt t.middle_upper) (h.trans hr.symm)).elim
  exact eq_of_entries hl hm hr

/-- The actual unordered source vertex support in the chosen root reading. -/
def vertexSet (g : ZMod n) (t : IncreasingBoundaryTriple n) : Finset (ZMod n) :=
  t.positionSet.image (boundaryIndex g)

theorem vertexSet_injective (g : ZMod n) : Function.Injective (vertexSet g) := by
  intro t u he
  apply positionSet_injective
  exact Finset.image_injective (boundaryIndex_injective g) he

theorem vertexSet_reversed (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    t.vertexSet g = {boundaryIndex g t.upper, boundaryIndex g t.middle, boundaryIndex g t.lower} := by
  ext x
  simp [vertexSet, positionSet, or_comm, or_left_comm, or_assoc]

end IncreasingBoundaryTriple

/-- Unique zero support implies every other increasing boundary triple has
a nonzero determinant sign. This uses label injectivity of the root reading,
without inferring geometric vertex distinctness from singleton Zpt at n=3. -/
theorem boundary_chi_nonzero_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g})
    (u : IncreasingBoundaryTriple n) (hu : u ≠ t) :
    chi P (boundaryIndex g u.upper) (boundaryIndex g u.middle) (boundaryIndex g u.lower) ≠ 0 := by
  apply chi_nonzero_outside_singleton hP
  · exact fun h => (ne_of_gt u.middle_upper) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt u.lower_middle) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt (lt_trans u.lower_middle u.middle_upper)) (boundaryIndex_injective g h)
  · intro he
    have hs : u.vertexSet g = t.vertexSet g := (u.vertexSet_reversed g).trans he
    exact hu (IncreasingBoundaryTriple.vertexSet_injective g hs)

end
end SM

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
  have he : (fun P : LabelledTuple n => (chi P i k j : ℝ)) =
      (fun P => -(chi P i j k : ℝ)) := by
    funext P
    rw [chi_swap_last, SignType.coe_neg]
  rw [he, w.signChanges_neg]

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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryIndex_first (g : ZMod n) (hn : 0 < n) :
    boundaryIndex g ⟨0, hn⟩ = g + 1 := by simp [boundaryIndex]

theorem boundaryIndex_last (g : ZMod n) (hn : 0 < n) :
    boundaryIndex g ⟨n - 1, by omega⟩ = g := by
  have hsum : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by simp
      _ = (n : ZMod n) := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.sub_add_cancel hn)
      _ = 0 := ZMod.natCast_self n
  simp only [boundaryIndex, add_assoc, hsum, add_zero]

/-- A nonincident root places the deleted vertex strictly inside the word.
Either endpoint position would force one of the two excluded root edges. -/
theorem boundaryIndex_nonincident_interior (g j : ZMod n) (k : Fin n)
    (hk : boundaryIndex g k = j) (h : ¬ incident j g) :
    0 < k.val ∧ k.val + 1 < n := by
  have hn : 0 < n := NeZero.pos n
  constructor
  · by_contra hzero
    have hz : k.val = 0 := by omega
    have he : g + 1 = j := by simpa [boundaryIndex, hz] using hk
    apply h
    left
    linear_combination he
  · by_contra hlast
    have hl : k = ⟨n - 1, by omega⟩ := Fin.ext (by change k.val = n - 1; have := k.isLt; omega)
    have he : g = j := by simpa only [hl, boundaryIndex_last g hn] using hk
    exact h (Or.inr he)

def consecutiveBoundaryTriple (k : Fin n) (h0 : 0 < k.val) (hLast : k.val + 1 < n) :
    IncreasingBoundaryTriple n where
  lower := ⟨k.val - 1, by omega⟩
  middle := k
  upper := ⟨k.val + 1, hLast⟩
  lower_middle := by change k.val - 1 < k.val; omega
  middle_upper := by change k.val < k.val + 1; omega

theorem consecutiveBoundaryTriple_labels (g j : ZMod n) (k : Fin n)
    (h0 : 0 < k.val) (hLast : k.val + 1 < n) (hk : boundaryIndex g k = j) :
    boundaryIndex g (consecutiveBoundaryTriple k h0 hLast).lower = j - 1 ∧
      boundaryIndex g (consecutiveBoundaryTriple k h0 hLast).middle = j ∧
      boundaryIndex g (consecutiveBoundaryTriple k h0 hLast).upper = j + 1 := by
  have he : g + (k.val : ZMod n) + 1 = j := hk
  refine ⟨?_, hk, ?_⟩
  · change g + ((k.val - 1 : ℕ) : ZMod n) + 1 = j - 1
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    linear_combination he
  · change g + ((k.val + 1 : ℕ) : ZMod n) + 1 = j + 1
    rw [Nat.cast_add, Nat.cast_one]
    linear_combination he

theorem consecutiveBoundaryTriple_gaps (k : Fin n) (h0 : 0 < k.val) (hLast : k.val + 1 < n) :
    (consecutiveBoundaryTriple k h0 hLast).leftInterval.leaves = 1 ∧
      (consecutiveBoundaryTriple k h0 hLast).rightInterval.leaves = 1 := by
  dsimp [consecutiveBoundaryTriple, IncreasingBoundaryTriple.leftInterval,
    IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem consecutiveBoundaryTriple_proper (hn : 4 ≤ n) (k : Fin n)
    (h0 : 0 < k.val) (hLast : k.val + 1 < n) :
    (consecutiveBoundaryTriple k h0 hLast).spanInterval ≠ fullBoundaryInterval (by omega) := by
  intro he
  have hl := congrArg (fun J : BoundaryInterval n => J.left.val) he
  have hr := congrArg (fun J : BoundaryInterval n => J.right.val) he
  dsimp [IncreasingBoundaryTriple.spanInterval, consecutiveBoundaryTriple, fullBoundaryInterval] at hl hr
  omega

/-- The nonincident case supplies the exact critical support, consecutive
labels, singleton gaps, and proper span from the physical root condition. -/
theorem flat_nonincident_boundary_data (hn : 4 ≤ n) (g j : ZMod n) (h : ¬ incident j g) :
    ∃ t : IncreasingBoundaryTriple n,
      t.vertexSet g = turnSupport j ∧
      boundaryIndex g t.lower = j - 1 ∧ boundaryIndex g t.middle = j ∧
      boundaryIndex g t.upper = j + 1 ∧
      t.leftInterval.leaves = 1 ∧ t.rightInterval.leaves = 1 ∧
      t.spanInterval ≠ fullBoundaryInterval (by omega) := by
  obtain ⟨k, hk⟩ := boundaryIndex_surjective g j
  have hb := boundaryIndex_nonincident_interior g j k hk h
  let t := consecutiveBoundaryTriple k hb.1 hb.2
  have hl := consecutiveBoundaryTriple_labels g j k hb.1 hb.2 hk
  have hg := consecutiveBoundaryTriple_gaps k hb.1 hb.2
  refine ⟨t, ?_, hl.1, hl.2.1, hl.2.2, hg.1, hg.2,
    consecutiveBoundaryTriple_proper hn k hb.1 hb.2⟩
  dsimp only [t]
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, turnSupport]

def incomingFlatTriple (hn : 4 ≤ n) : IncreasingBoundaryTriple n where
  lower := ⟨0, by omega⟩
  middle := ⟨1, by omega⟩
  upper := ⟨n - 1, by omega⟩
  lower_middle := by change 0 < 1; omega
  middle_upper := by change 1 < n - 1; omega

def outgoingFlatTriple (hn : 4 ≤ n) : IncreasingBoundaryTriple n where
  lower := ⟨0, by omega⟩
  middle := ⟨n - 2, by omega⟩
  upper := ⟨n - 1, by omega⟩
  lower_middle := by change 0 < n - 2; omega
  middle_upper := by change n - 2 < n - 1; omega

theorem incomingFlatTriple_labels (hn : 4 ≤ n) (j : ZMod n) :
    boundaryIndex (j - 1) (incomingFlatTriple hn).lower = j ∧
      boundaryIndex (j - 1) (incomingFlatTriple hn).middle = j + 1 ∧
      boundaryIndex (j - 1) (incomingFlatTriple hn).upper = j - 1 := by
  refine ⟨?_, ?_, boundaryIndex_last (j - 1) (by omega)⟩
  · simp only [incomingFlatTriple, boundaryIndex, Nat.cast_zero]
    ring
  · simp only [incomingFlatTriple, boundaryIndex, Nat.cast_one]
    ring

theorem outgoingFlatTriple_labels (hn : 4 ≤ n) (j : ZMod n) :
    boundaryIndex j (outgoingFlatTriple hn).lower = j + 1 ∧
      boundaryIndex j (outgoingFlatTriple hn).middle = j - 1 ∧
      boundaryIndex j (outgoingFlatTriple hn).upper = j := by
  refine ⟨boundaryIndex_first j (by omega), ?_, boundaryIndex_last j (by omega)⟩
  change j + ((n - 2 : ℕ) : ZMod n) + 1 = j - 1
  rw [Nat.cast_sub (by omega), ZMod.natCast_self]
  norm_num
  ring

theorem incomingFlatTriple_intervals (hn : 4 ≤ n) :
    (incomingFlatTriple hn).spanInterval = fullBoundaryInterval (by omega) ∧
      (incomingFlatTriple hn).leftInterval.leaves = 1 ∧
      (incomingFlatTriple hn).rightInterval.leaves = n - 2 := by
  refine ⟨rfl, rfl, ?_⟩
  dsimp [incomingFlatTriple, IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem outgoingFlatTriple_intervals (hn : 4 ≤ n) :
    (outgoingFlatTriple hn).spanInterval = fullBoundaryInterval (by omega) ∧
      (outgoingFlatTriple hn).leftInterval.leaves = n - 2 ∧
      (outgoingFlatTriple hn).rightInterval.leaves = 1 := by
  refine ⟨rfl, rfl, ?_⟩
  dsimp [outgoingFlatTriple, IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem incomingFlatTriple_support (hn : 4 ≤ n) (j : ZMod n) :
    (incomingFlatTriple hn).vertexSet (j - 1) = turnSupport j := by
  have hl := incomingFlatTriple_labels hn j
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, turnSupport]
  ext k
  simp [or_comm, or_left_comm, or_assoc]

theorem outgoingFlatTriple_support (hn : 4 ≤ n) (j : ZMod n) :
    (outgoingFlatTriple hn).vertexSet j = turnSupport j := by
  have hl := outgoingFlatTriple_labels hn j
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, turnSupport]
  ext k
  simp [or_comm, or_left_comm, or_assoc]

end
end SM

#check SM.boundaryIndex_first
#print axioms SM.boundaryIndex_first

#check SM.boundaryIndex_last
#print axioms SM.boundaryIndex_last

#check SM.boundaryIndex_nonincident_interior
#print axioms SM.boundaryIndex_nonincident_interior

#check SM.consecutiveBoundaryTriple
#print axioms SM.consecutiveBoundaryTriple

#check SM.consecutiveBoundaryTriple_labels
#print axioms SM.consecutiveBoundaryTriple_labels

#check SM.consecutiveBoundaryTriple_gaps
#print axioms SM.consecutiveBoundaryTriple_gaps

#check SM.consecutiveBoundaryTriple_proper
#print axioms SM.consecutiveBoundaryTriple_proper

#check SM.flat_nonincident_boundary_data
#print axioms SM.flat_nonincident_boundary_data

#check SM.incomingFlatTriple
#print axioms SM.incomingFlatTriple

#check SM.outgoingFlatTriple
#print axioms SM.outgoingFlatTriple

#check SM.incomingFlatTriple_labels
#print axioms SM.incomingFlatTriple_labels

#check SM.outgoingFlatTriple_labels
#print axioms SM.outgoingFlatTriple_labels

#check SM.incomingFlatTriple_intervals
#print axioms SM.incomingFlatTriple_intervals

#check SM.outgoingFlatTriple_intervals
#print axioms SM.outgoingFlatTriple_intervals

#check SM.incomingFlatTriple_support
#print axioms SM.incomingFlatTriple_support

#check SM.outgoingFlatTriple_support
#print axioms SM.outgoingFlatTriple_support
