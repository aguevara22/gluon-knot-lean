import SM.FusionIndices
import SM.CriticalSourceResponse
import SM.UnorderedWallTriples
import SM.ContactHalfTuples
import Mathlib.Tactic

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

namespace SM.IncreasingBoundaryTriple

noncomputable section
variable {n : ℕ}

/-- Contract the entire positive-length critical arc to one leaf by deleting
exactly its strictly interior positions, retaining both endpoints. -/
def erasedInteriorCount (t : IncreasingBoundaryTriple n) : ℕ :=
  t.upper.val - t.lower.val - 1

def contractedSize (t : IncreasingBoundaryTriple n) : ℕ :=
  n - t.erasedInteriorCount

theorem erasedInteriorCount_pos (t : IncreasingBoundaryTriple n) :
    0 < t.erasedInteriorCount := by
  have hl := t.lower_middle
  have hr := t.middle_upper
  change t.lower.val < t.middle.val at hl
  change t.middle.val < t.upper.val at hr
  unfold erasedInteriorCount
  omega

/-- Both endpoints survive, even when the contracted word is one formal
leaf. No arity-three polygon amplitude is inferred from this bound. -/
theorem contractedSize_bounds (t : IncreasingBoundaryTriple n) :
    t.lower.val + 2 ≤ t.contractedSize ∧ t.contractedSize ≤ n := by
  have hu := t.upper.isLt
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold contractedSize erasedInteriorCount
  omega

def expandPosition (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) : Fin n :=
  if hk : k.val ≤ t.lower.val then
    ⟨k.val, lt_of_le_of_lt hk t.lower.isLt⟩
  else
    ⟨k.val + t.erasedInteriorCount, by
      have hb := k.isLt
      unfold contractedSize at hb
      omega⟩

theorem expandPosition_val (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    (t.expandPosition k).val =
      if k.val ≤ t.lower.val then k.val else k.val + t.erasedInteriorCount := by
  unfold expandPosition
  split_ifs <;> rfl

theorem expandPosition_strict (t : IncreasingBoundaryTriple n) : StrictMono t.expandPosition := by
  intro a b hab
  change a.val < b.val at hab
  change (t.expandPosition a).val < (t.expandPosition b).val
  rw [expandPosition_val, expandPosition_val]
  split_ifs <;> omega

theorem expandPosition_lower (t : IncreasingBoundaryTriple n) :
    t.expandPosition ⟨t.lower.val, by have := t.contractedSize_bounds; omega⟩ = t.lower := by
  apply Fin.ext
  rw [expandPosition_val]
  simp

/-- The distinguished surviving edge expands from the old first endpoint
directly to the old last endpoint, not to the old critical middle vertex. -/
theorem expandPosition_upper (t : IncreasingBoundaryTriple n) :
    t.expandPosition ⟨t.lower.val + 1, by have := t.contractedSize_bounds; omega⟩ = t.upper := by
  apply Fin.ext
  rw [expandPosition_val]
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  simp only [show ¬ t.lower.val + 1 ≤ t.lower.val by omega, ite_false]
  unfold erasedInteriorCount
  omega

theorem expandPosition_survives (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    t.expandPosition k ≤ t.lower ∨ t.upper ≤ t.expandPosition k := by
  change (t.expandPosition k).val ≤ t.lower.val ∨ t.upper.val ≤ (t.expandPosition k).val
  rw [expandPosition_val]
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold erasedInteriorCount
  split_ifs <;> omega

/-- Translate back only surviving positions. The range condition excludes
every deleted interior position explicitly. -/
def contractPosition (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ≤ t.lower ∨ t.upper ≤ x) : Fin t.contractedSize :=
  ⟨if x.val ≤ t.lower.val then x.val else x.val - t.erasedInteriorCount, by
    have hb := t.contractedSize_bounds
    have hxn := x.isLt
    change x.val ≤ t.lower.val ∨ t.upper.val ≤ x.val at hx
    have hl := lt_trans t.lower_middle t.middle_upper
    change t.lower.val < t.upper.val at hl
    unfold contractedSize erasedInteriorCount at *
    split_ifs <;> omega⟩

theorem expand_contractPosition (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ≤ t.lower ∨ t.upper ≤ x) : t.expandPosition (t.contractPosition x hx) = x := by
  apply Fin.ext
  rw [expandPosition_val]
  simp only [contractPosition]
  change x.val ≤ t.lower.val ∨ t.upper.val ≤ x.val at hx
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold erasedInteriorCount
  split_ifs <;> omega

theorem contract_expandPosition (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    t.contractPosition (t.expandPosition k) (t.expandPosition_survives k) = k := by
  apply Fin.ext
  change (if (t.expandPosition k).val ≤ t.lower.val then (t.expandPosition k).val
    else (t.expandPosition k).val - t.erasedInteriorCount) = k.val
  rw [expandPosition_val]
  split_ifs <;> omega

/-- A bijection onto every surviving boundary position, in the original
linear reading. It deletes exactly the open critical arc. -/
def survivingPositionEquiv (t : IncreasingBoundaryTriple n) :
    Fin t.contractedSize ≃ {x : Fin n // x ≤ t.lower ∨ t.upper ≤ x} where
  toFun k := ⟨t.expandPosition k, t.expandPosition_survives k⟩
  invFun x := t.contractPosition x.val x.property
  left_inv := t.contract_expandPosition
  right_inv x := Subtype.ext (t.expand_contractPosition x.val x.property)

end
end SM.IncreasingBoundaryTriple

namespace SM

noncomputable section

theorem consecutive_erased_one {n : ℕ} (k : Fin n) (h0 : 0 < k.val) (hLast : k.val + 1 < n) :
    (consecutiveBoundaryTriple k h0 hLast).erasedInteriorCount = 1 := by
  dsimp [IncreasingBoundaryTriple.erasedInteriorCount, consecutiveBoundaryTriple]
  omega

theorem consecutive_contracted_size {q : ℕ} (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1) :
    (consecutiveBoundaryTriple k h0 hLast).contractedSize = q := by
  unfold IncreasingBoundaryTriple.contractedSize
  rw [consecutive_erased_one]
  omega

variable {q : ℕ} [NeZero q]

/-- The actual deletion root is the surviving old root, expressed in the
child's cyclic labels. Its natural representative is proved before casting. -/
theorem nonincident_fusionIndex_eq (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g) :
    fusionIndex j g = ((q - k.val - 1 : ℕ) : ZMod q) := by
  have hj : g ≠ j := fun he => hroot (Or.inr he)
  have he : g + (k.val : ZMod (q + 1)) + 1 = j := hk
  have hq : (q : ZMod (q + 1)) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (q + 1)
  have hc : g - (j + 1) = ((q - k.val - 1 : ℕ) : ZMod (q + 1)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q - k.val), Nat.cast_sub (by omega : k.val ≤ q), Nat.cast_one]
    linear_combination he - hq
  have hv : (g - (j + 1)).val = q - k.val - 1 := by
    rw [hc, ZMod.val_natCast_of_lt (by omega)]
  rw [fusionIndex, if_neg hj, hv]

theorem nonincident_fusionIndex_cut_relation (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g) :
    fusionIndex j g + ((k.val + 1 : ℕ) : ZMod q) = 0 := by
  rw [nonincident_fusionIndex_eq g j k h0 hLast hk hroot]
  rw [Nat.cast_sub (by omega : 1 ≤ q - k.val), Nat.cast_sub (by omega : k.val ≤ q),
    Nat.cast_add, Nat.cast_one, ZMod.natCast_self]
  ring

/-- Exact representatives for the cyclic shift across a cut. Both intervals
include their boundary cases; all natural subtractions have proved bounds. -/
theorem zmod_cut_shift_val (k : ℕ) (hk : k < q) (u a : ZMod q)
    (ha : a + ((k + 1 : ℕ) : ZMod q) = 0) :
    (u + a).val = if (u - 1).val < k then (u - 1).val + q - k else (u - 1).val - k := by
  have hv : (u - 1).val < q := ZMod.val_lt _
  have hu : ((u - 1).val : ZMod q) = u - 1 := ZMod.natCast_zmod_val _
  have ha' : a + (k : ZMod q) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using ha
  have he : u + a = ((u - 1).val : ZMod q) - (k : ZMod q) := by
    linear_combination ha' - hu
  by_cases h : (u - 1).val < k
  · rw [if_pos h]
    have hc : u + a = (((u - 1).val + q - k : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]
      exact he
    rw [hc, ZMod.val_natCast_of_lt (by omega)]
  · rw [if_neg h]
    have hc : u + a = (((u - 1).val - k : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega)]
      exact he
    rw [hc, ZMod.val_natCast_of_lt (by omega)]

end
end SM

namespace SM.IncreasingBoundaryTriple

noncomputable section
variable {n : ℕ} [NeZero n]

theorem expandPosition_initial (t : IncreasingBoundaryTriple n) :
    (t.expandPosition ⟨0, by have := t.contractedSize_bounds; omega⟩).val = 0 := by
  rw [expandPosition_val]
  simp

/-- Both ends of the complete linear word survive contraction. Together
with the first-position identity this preserves the physical closing edge. -/
theorem expandPosition_final (t : IncreasingBoundaryTriple n) :
    (t.expandPosition ⟨t.contractedSize - 1, by have := t.contractedSize_bounds; omega⟩).val = n - 1 := by
  rw [expandPosition_val]
  have hb := t.contractedSize_bounds
  have he : ¬ t.contractedSize - 1 ≤ t.lower.val := by omega
  rw [if_neg he]
  change t.contractedSize - 1 + t.erasedInteriorCount = n - 1
  unfold contractedSize at *
  omega

/-- Exactly the full-span case contracts the complete word to one formal
leaf. This characterizes, rather than suppresses, the two-position case. -/
theorem contractedSize_eq_two_iff (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n) :
    t.contractedSize = 2 ↔ t.spanInterval = fullBoundaryInterval hn := by
  constructor
  · intro hs
    have hb := t.contractedSize_bounds
    have hl : t.lower.val = 0 := by omega
    have hu : t.upper.val = n - 1 := by
      have hu := t.upper.isLt
      have hlt := lt_trans t.lower_middle t.middle_upper
      change t.lower.val < t.upper.val at hlt
      unfold contractedSize erasedInteriorCount at hs
      omega
    apply BoundaryInterval.eq_of_endpoints
    · apply Fin.ext
      exact hl
    · apply Fin.ext
      exact hu
  · intro he
    have hl := congrArg (fun I : BoundaryInterval n => I.left.val) he
    have hu := congrArg (fun I : BoundaryInterval n => I.right.val) he
    change t.lower.val = 0 at hl
    change t.upper.val = n - 1 at hu
    unfold contractedSize erasedInteriorCount
    rw [hl, hu]
    omega

/-- Every proper critical span leaves at least three actual positions, so
the final contracted polygon may use the source's arity-three amplitude. -/
theorem contractedSize_of_proper (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn) : 3 ≤ t.contractedSize := by
  have hb := t.contractedSize_bounds
  have he : t.contractedSize ≠ 2 := fun h => hproper ((t.contractedSize_eq_two_iff hn).mp h)
  omega

end
end SM.IncreasingBoundaryTriple

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The structural lower bound supplies the finite cyclic label instance;
it is a proved fact, not an additional geometric hypothesis. -/
theorem IncreasingBoundaryTriple.contractedSize_neZero (t : IncreasingBoundaryTriple n) :
    NeZero t.contractedSize := by
  constructor
  have hb := t.contractedSize_bounds
  omega

/-- Read every surviving position in order. Residue zero labels the last
survivor, so the local root zero is the original physical closing edge. -/
def contractedVertexIndex (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (j : ZMod t.contractedSize) : ZMod n := by
  letI := t.contractedSize_neZero
  exact boundaryIndex g (t.expandPosition ⟨(j - 1).val, ZMod.val_lt _⟩)

theorem contractedVertexIndex_injective (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    Function.Injective (contractedVertexIndex g t) := by
  letI := t.contractedSize_neZero
  intro i j he
  have hp := t.expandPosition_strict.injective (boundaryIndex_injective g he)
  have hv := congrArg Fin.val hp
  have hz : i - 1 = j - 1 := ZMod.val_injective t.contractedSize hv
  simpa only [sub_add_cancel] using congrArg (fun v : ZMod t.contractedSize => v + 1) hz

def contractedWordTuple (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) : LabelledTuple t.contractedSize :=
  fun j => P (contractedVertexIndex g t j)

theorem contractedWord_boundary (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    boundaryWord (contractedWordTuple P g t) 0 k = boundaryWord P g (t.expandPosition k) := by
  letI := t.contractedSize_neZero
  unfold boundaryWord contractedWordTuple contractedVertexIndex boundaryIndex
  have hz : (0 + (k.val : ZMod t.contractedSize) + 1) - 1 =
      (k.val : ZMod t.contractedSize) := by ring
  simp only [hz, ZMod.val_natCast_of_lt k.isLt]

theorem contractedWord_first_vertex (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) : contractedWordTuple P g t 1 = P (g + 1) := by
  letI := t.contractedSize_neZero
  have hs : 0 < t.contractedSize := by have := t.contractedSize_bounds; omega
  have hn : 0 < n := NeZero.pos n
  have hp : t.expandPosition ⟨0, hs⟩ = ⟨0, hn⟩ := Fin.ext t.expandPosition_initial
  have h := contractedWord_boundary P g t ⟨0, hs⟩
  rw [hp, boundaryWord_first, boundaryWord_first] at h
  simpa only [zero_add] using h

theorem contractedWord_last_vertex (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) : contractedWordTuple P g t 0 = P g := by
  letI := t.contractedSize_neZero
  have hs : 0 < t.contractedSize := by have := t.contractedSize_bounds; omega
  have hn : 0 < n := NeZero.pos n
  have hp : t.expandPosition ⟨t.contractedSize - 1, by omega⟩ =
      ⟨n - 1, by omega⟩ := Fin.ext t.expandPosition_final
  have h := contractedWord_boundary P g t ⟨t.contractedSize - 1, by omega⟩
  rw [hp, boundaryWord_last (contractedWordTuple P g t) 0 hs, boundaryWord_last P g hn] at h
  exact h

/-- Equality of the actual directed edges, not merely an abstract root label. -/
theorem contractedWord_physical_root (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) : edge (contractedWordTuple P g t) 0 = edge P g := by
  simp only [edge, zero_add, contractedWord_first_vertex, contractedWord_last_vertex]

/-- Every contracted distinct-label triple avoids the unique zero support:
the critical middle position is strictly inside the deleted arc. -/
theorem contractedWord_G1 (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g}) :
    G1 (contractedWordTuple P g t) := by
  letI := t.contractedSize_neZero
  intro i j k hij hjk hik
  change chi P (contractedVertexIndex g t i) (contractedVertexIndex g t j)
    (contractedVertexIndex g t k) ≠ 0
  apply chi_nonzero_outside_singleton hZ
  · exact fun he => hij (contractedVertexIndex_injective g t he)
  · exact fun he => hjk (contractedVertexIndex_injective g t he)
  · exact fun he => hik (contractedVertexIndex_injective g t he)
  · intro he
    have hm : boundaryIndex g t.middle ∈ ({contractedVertexIndex g t i,
        contractedVertexIndex g t j, contractedVertexIndex g t k} : Finset (ZMod n)) := by
      rw [he]
      simp [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet]
    have hx (v : ZMod t.contractedSize)
        (hv : boundaryIndex g t.middle = contractedVertexIndex g t v) : False := by
      have hp : t.middle = t.expandPosition ⟨(v - 1).val, ZMod.val_lt _⟩ :=
        boundaryIndex_injective g hv
      have hs := t.expandPosition_survives ⟨(v - 1).val, ZMod.val_lt _⟩
      rw [← hp] at hs
      rcases hs with hl | hr
      · exact (not_le_of_gt t.lower_middle) hl
      · exact (not_le_of_gt t.middle_upper) hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hi | hj | hk
    · exact hx i hi
    · exact hx j hj
    · exact hx k hk

/-- The proper-span source polygon has the required arity and G1, while
its local root zero is precisely the original physical root. No two-gon
amplitude is constructed in the full-span case. -/
theorem proper_contracted_polygon_data (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hZ : pointZeroTriples P = {t.vertexSet g})
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    3 ≤ t.contractedSize ∧ G1 (contractedWordTuple P g t) ∧
      edge (contractedWordTuple P g t) 0 = edge P g := by
  exact ⟨t.contractedSize_of_proper hn hproper, contractedWord_G1 P g t hZ,
    contractedWord_physical_root P g t⟩

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Root a cuts the cyclic contact order at B: B,X,A. -/
def contactBaseTriple (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    IncreasingBoundaryTriple n where
  lower := ⟨0, by omega⟩
  middle := ⟨n - contactDistance M a - 1, by
    have hd := contactDistance_bounds hn hc
    omega⟩
  upper := ⟨n - 1, by omega⟩
  lower_middle := by
    change 0 < n - contactDistance M a - 1
    have hd := contactDistance_bounds hn hc
    omega
  middle_upper := by
    change n - contactDistance M a - 1 < n - 1
    have hd := contactDistance_bounds hn hc
    omega

/-- A root on the original X-to-A arc cuts the critical labels as A,B,X.
The representative u includes zero, hence the edge starting at X. -/
def contactFirstArcTriple (g M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : (g - M).val < contactDistance M a) : IncreasingBoundaryTriple n where
  lower := ⟨contactDistance M a - (g - M).val - 1, by
    have hd := contactDistance_bounds hn hc
    omega⟩
  middle := ⟨contactDistance M a - (g - M).val, by
    have hd := contactDistance_bounds hn hc
    omega⟩
  upper := ⟨n - (g - M).val - 1, by omega⟩
  lower_middle := by
    change contactDistance M a - (g - M).val - 1 < contactDistance M a - (g - M).val
    omega
  middle_upper := by
    change contactDistance M a - (g - M).val < n - (g - M).val - 1
    have hd := contactDistance_bounds hn hc
    omega

/-- A root on the original B-to-X arc cuts the critical labels as X,A,B.
The final representative n-1 includes the edge ending at X. -/
def contactSecondArcTriple (g M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : contactDistance M a < (g - M).val) : IncreasingBoundaryTriple n where
  lower := ⟨n - (g - M).val - 1, by omega⟩
  middle := ⟨n - (g - M).val + contactDistance M a - 1, by
    have huN : (g - M).val < n := ZMod.val_lt _
    omega⟩
  upper := ⟨n - (g - M).val + contactDistance M a, by
    have huN : (g - M).val < n := ZMod.val_lt _
    omega⟩
  lower_middle := by
    change n - (g - M).val - 1 < n - (g - M).val + contactDistance M a - 1
    have hd := contactDistance_bounds hn hc
    have huN : (g - M).val < n := ZMod.val_lt _
    omega
  middle_upper := by
    change n - (g - M).val + contactDistance M a - 1 < n - (g - M).val + contactDistance M a
    have huN : (g - M).val < n := ZMod.val_lt _
    omega

theorem contactBaseTriple_labels (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    boundaryIndex a (contactBaseTriple M a hn hc).lower = a + 1 ∧
      boundaryIndex a (contactBaseTriple M a hn hc).middle = M ∧
      boundaryIndex a (contactBaseTriple M a hn hc).upper = a := by
  have hd := contactDistance_bounds hn hc
  refine ⟨?_, ?_, ?_⟩
  · change a + ((0 : ℕ) : ZMod n) + 1 = a + 1
    simp
  · change a + ((n - contactDistance M a - 1 : ℕ) : ZMod n) + 1 = M
    rw [Nat.cast_sub (by omega : 1 ≤ n - contactDistance M a),
      Nat.cast_sub (by omega : contactDistance M a ≤ n), Nat.cast_one,
      ZMod.natCast_self, contactDistance_cast]
    ring
  · change a + ((n - 1 : ℕ) : ZMod n) + 1 = a
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, ZMod.natCast_self]
    ring

theorem contactFirstArcTriple_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    boundaryIndex g (contactFirstArcTriple g M a hn hc hu).lower = a ∧
      boundaryIndex g (contactFirstArcTriple g M a hn hc hu).middle = a + 1 ∧
      boundaryIndex g (contactFirstArcTriple g M a hn hc hu).upper = M := by
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hdZ := contactDistance_cast M a
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  refine ⟨?_, ?_, ?_⟩
  · change g + ((contactDistance M a - (g - M).val - 1 : ℕ) : ZMod n) + 1 = a
    rw [Nat.cast_sub (by omega : 1 ≤ contactDistance M a - (g - M).val),
      Nat.cast_sub (by omega : (g - M).val ≤ contactDistance M a), Nat.cast_one, hdZ, huZ]
    ring
  · change g + ((contactDistance M a - (g - M).val : ℕ) : ZMod n) + 1 = a + 1
    rw [Nat.cast_sub (by omega : (g - M).val ≤ contactDistance M a), hdZ, huZ]
    ring
  · change g + ((n - (g - M).val - 1 : ℕ) : ZMod n) + 1 = M
    rw [Nat.cast_sub (by omega : 1 ≤ n - (g - M).val),
      Nat.cast_sub (by omega : (g - M).val ≤ n), Nat.cast_one, ZMod.natCast_self, huZ]
    ring

theorem contactSecondArcTriple_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    boundaryIndex g (contactSecondArcTriple g M a hn hc hu).lower = M ∧
      boundaryIndex g (contactSecondArcTriple g M a hn hc hu).middle = a ∧
      boundaryIndex g (contactSecondArcTriple g M a hn hc hu).upper = a + 1 := by
  have huN : (g - M).val < n := ZMod.val_lt _
  have hdZ := contactDistance_cast M a
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  refine ⟨?_, ?_, ?_⟩
  · change g + ((n - (g - M).val - 1 : ℕ) : ZMod n) + 1 = M
    rw [Nat.cast_sub (by omega : 1 ≤ n - (g - M).val),
      Nat.cast_sub (by omega : (g - M).val ≤ n), Nat.cast_one, ZMod.natCast_self, huZ]
    ring
  · change g + ((n - (g - M).val + contactDistance M a - 1 : ℕ) : ZMod n) + 1 = a
    rw [Nat.cast_sub (by omega : 1 ≤ n - (g - M).val + contactDistance M a),
      Nat.cast_add, Nat.cast_sub (by omega : (g - M).val ≤ n), Nat.cast_one,
      ZMod.natCast_self, hdZ, huZ]
    ring
  · change g + ((n - (g - M).val + contactDistance M a : ℕ) : ZMod n) + 1 = a + 1
    rw [Nat.cast_add, Nat.cast_sub (by omega : (g - M).val ≤ n),
      ZMod.natCast_self, hdZ, huZ]
    ring

theorem contactBaseTriple_gaps (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    (contactBaseTriple M a hn hc).leftInterval.leaves = n - contactDistance M a - 1 ∧
      (contactBaseTriple M a hn hc).rightInterval.leaves = contactDistance M a := by
  have hd := contactDistance_bounds hn hc
  dsimp [contactBaseTriple, IncreasingBoundaryTriple.leftInterval,
    IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem contactFirstArcTriple_gaps (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).leftInterval.leaves = 1 ∧
      (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves = n - contactDistance M a - 1 := by
  have hd := contactDistance_bounds hn hc
  dsimp [contactFirstArcTriple, IncreasingBoundaryTriple.leftInterval,
    IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem contactSecondArcTriple_gaps (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves = contactDistance M a ∧
      (contactSecondArcTriple g M a hn hc hu).rightInterval.leaves = 1 := by
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  dsimp [contactSecondArcTriple, IncreasingBoundaryTriple.leftInterval,
    IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem contactBaseTriple_full (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    (contactBaseTriple M a hn hc).spanInterval = fullBoundaryInterval hn := rfl

theorem contactFirstArcTriple_proper (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).spanInterval ≠ fullBoundaryInterval hn := by
  intro he
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hl := congrArg (fun J : BoundaryInterval n => J.left.val) he
  have hr := congrArg (fun J : BoundaryInterval n => J.right.val) he
  dsimp [IncreasingBoundaryTriple.spanInterval, contactFirstArcTriple, fullBoundaryInterval] at hl hr
  omega

theorem contactSecondArcTriple_proper (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).spanInterval ≠ fullBoundaryInterval hn := by
  intro he
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hl := congrArg (fun J : BoundaryInterval n => J.left.val) he
  have hr := congrArg (fun J : BoundaryInterval n => J.right.val) he
  dsimp [IncreasingBoundaryTriple.spanInterval, contactSecondArcTriple, fullBoundaryInterval] at hl hr
  omega

/-- Only arity is identified here; no tuple equality is inferred from it. -/
theorem contactFirstArcTriple_contractedSize (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).contractedSize = firstHalfSize M a := by
  have hd := contactDistance_bounds hn hc
  dsimp [IncreasingBoundaryTriple.contractedSize, IncreasingBoundaryTriple.erasedInteriorCount,
    contactFirstArcTriple, firstHalfSize]
  omega

/-- Only arity is identified here; the whole contracted tuple needs its own proof. -/
theorem contactSecondArcTriple_contractedSize (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).contractedSize = secondHalfSize M a := by
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  dsimp [IncreasingBoundaryTriple.contractedSize, IncreasingBoundaryTriple.erasedInteriorCount,
    contactSecondArcTriple, secondHalfSize]
  omega

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Exact representatives when the origin moves from M to a. Both sides
of the cut retain proved natural-subtraction and residue bounds. -/
theorem contact_relative_offset_val (M a g : ZMod n) :
    (g - a).val = if (g - M).val < contactDistance M a then
      (g - M).val + n - contactDistance M a else (g - M).val - contactDistance M a := by
  have hv := ZMod.val_lt (g - M)
  have hd := ZMod.val_lt (a - M)
  change contactDistance M a < n at hd
  by_cases h : (g - M).val < contactDistance M a
  · rw [if_pos h]
    have he : g - a = (((g - M).val + n - contactDistance M a : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
        ZMod.natCast_zmod_val, contactDistance_cast]
      ring
    rw [he, ZMod.val_natCast_of_lt (by omega)]
  · rw [if_neg h]
    have he : g - a = (((g - M).val - contactDistance M a : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val, contactDistance_cast]
      ring
    rw [he, ZMod.val_natCast_of_lt (by omega)]

/-- First-half inherited edges are exactly the original M-to-a arc,
excluding its new closing edge. -/
theorem firstHalf_inherited_root_iff (M a g : ZMod n) :
    (∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) ↔
      (g - M).val < contactDistance M a := by
  constructor
  · rintro ⟨i, hi, he⟩
    have hv := cyclicRangeIndex_offset (firstHalfSize_le M a) M i
    change (firstHalfIndex M a i - M).val = i.val at hv
    rw [he] at hv
    have hn := ZMod.val_lt (i + 1)
    rw [zmod_val_next_of_ne_last hi] at hn
    change i.val + 1 < contactDistance M a + 1 at hn
    omega
  · intro hg
    obtain ⟨i, hi⟩ := (firstHalfIndex_range M a g).mpr
      (by change (g - M).val < contactDistance M a + 1; omega)
    refine ⟨i, ?_, hi⟩
    intro he
    rw [he, firstHalfIndex_last] at hi
    subst g
    exact Nat.lt_irrefl _ hg

theorem secondHalfEdgeIndex_range_iff (M a g : ZMod n) :
    (∃ i : ZMod (secondHalfSize M a), secondHalfEdgeIndex M a i = g) ↔
      (g - a).val < secondHalfSize M a :=
  cyclicRangeIndex_range (secondHalfSize_le M a) a g

/-- Second-half inherited edges are exactly the remaining original arc,
excluding its new opening edge at child label zero. -/
theorem secondHalf_inherited_root_iff (M a g : ZMod n) :
    (∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) ↔
      contactDistance M a < (g - M).val := by
  constructor
  · rintro ⟨i, hi, he⟩
    have hv := cyclicRangeIndex_offset (secondHalfSize_le M a) a i
    change (secondHalfEdgeIndex M a i - a).val = i.val at hv
    rw [he, contact_relative_offset_val M a g] at hv
    have hb := i.val_lt
    change i.val < n - contactDistance M a at hb
    have hpos : 0 < i.val := by
      by_contra h
      have hz : i.val = 0 := by omega
      apply hi
      apply ZMod.val_injective (secondHalfSize M a)
      simpa only [ZMod.val_zero] using hz
    by_cases h : (g - M).val < contactDistance M a
    · rw [if_pos h] at hv
      have hd : contactDistance M a < n := ZMod.val_lt (a - M)
      omega
    · rw [if_neg h] at hv
      omega
  · intro hg
    have hv := ZMod.val_lt (g - M)
    have hr : (g - a).val < secondHalfSize M a := by
      rw [contact_relative_offset_val M a g, if_neg (by omega)]
      unfold secondHalfSize
      omega
    obtain ⟨i, hi⟩ := (secondHalfEdgeIndex_range_iff M a g).mpr hr
    refine ⟨i, ?_, hi⟩
    intro he
    rw [he, secondHalfEdgeIndex_zero] at hi
    subst g
    exact Nat.lt_irrefl _ hg

/-- Every original physical root belongs to one of the source's three
rows. Endpoint incident edges remain included in the two inherited arcs. -/
theorem contact_root_cases (M a g : ZMod n) :
    g = a ∨
      (∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) ∨
      (∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) := by
  rcases lt_trichotomy (g - M).val (contactDistance M a) with h | h | h
  · exact Or.inr (Or.inl ((firstHalf_inherited_root_iff M a g).mpr h))
  · left
    have hc := congrArg (fun x : ℕ => (x : ZMod n)) h
    rw [ZMod.natCast_zmod_val, contactDistance_cast] at hc
    exact sub_left_injective hc
  · exact Or.inr (Or.inr ((secondHalf_inherited_root_iff M a g).mpr h))

/-- The three source root rows are pairwise disjoint, including their
cyclic endpoints. This does not require geometric genericity. -/
theorem contact_root_cases_disjoint (M a g : ZMod n) :
    (g = a → ¬ ∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) ∧
    (g = a → ¬ ∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) ∧
    ((∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g) →
      ¬ ∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g) := by
  rw [firstHalf_inherited_root_iff, secondHalf_inherited_root_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro hg
    subst g
    exact Nat.lt_irrefl _
  · intro hg
    subst g
    exact Nat.lt_irrefl _
  · omega

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every vertex surviving the first-arc contraction has its exact first-half
label. The natural cut calculation includes local label zero and root M. -/
theorem contactFirstArc_contracted_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a)
    (i : ZMod (contactFirstArcTriple g M a hn hc hu).contractedSize) :
    contractedVertexIndex g (contactFirstArcTriple g M a hn hc hu) i =
      firstHalfIndex M a
        (ZMod.ringEquivCongr (contactFirstArcTriple_contractedSize g M a hn hc hu) i +
          ((g - M).val : ZMod (firstHalfSize M a))) := by
  let t := contactFirstArcTriple g M a hn hc hu
  let e := ZMod.ringEquivCongr (contactFirstArcTriple_contractedSize g M a hn hc hu)
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hv : (i - 1).val = (e i - 1).val := by
    have hh := ZMod.ringEquivCongr_val (contactFirstArcTriple_contractedSize g M a hn hc hu) (i - 1)
    simpa only [map_sub, map_one] using hh.symm
  have hrel : ((g - M).val : ZMod (firstHalfSize M a)) +
      ((contactDistance M a - (g - M).val + 1 : ℕ) : ZMod (firstHalfSize M a)) = 0 := by
    rw [← Nat.cast_add]
    have he : (g - M).val + (contactDistance M a - (g - M).val + 1) = firstHalfSize M a := by
      unfold firstHalfSize
      omega
    rw [he, ZMod.natCast_self]
  have hcut := zmod_cut_shift_val (contactDistance M a - (g - M).val)
    (by unfold firstHalfSize; omega : contactDistance M a - (g - M).val < firstHalfSize M a)
    (e i) ((g - M).val : ZMod (firstHalfSize M a)) hrel
  have hlower : t.lower.val = contactDistance M a - (g - M).val - 1 := rfl
  have herase : t.erasedInteriorCount = n - contactDistance M a - 1 := by
    dsimp [t, IncreasingBoundaryTriple.erasedInteriorCount, contactFirstArcTriple]
    omega
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  change g + ((t.expandPosition ⟨(i - 1).val, ZMod.val_lt _⟩).val : ZMod n) + 1 =
    M + ((e i + ((g - M).val : ZMod (firstHalfSize M a))).val : ZMod n)
  rw [IncreasingBoundaryTriple.expandPosition_val, hlower, herase, hv, hcut]
  by_cases hk : (e i - 1).val < contactDistance M a - (g - M).val
  · rw [if_pos hk, if_pos (by omega : (e i - 1).val ≤ contactDistance M a - (g - M).val - 1)]
    have he : (e i - 1).val + firstHalfSize M a - (contactDistance M a - (g - M).val) =
        (e i - 1).val + (g - M).val + 1 := by
      unfold firstHalfSize
      omega
    rw [he, Nat.cast_add, Nat.cast_add, Nat.cast_one, huZ]
    ring
  · rw [if_neg hk, if_neg (by omega : ¬ (e i - 1).val ≤ contactDistance M a - (g - M).val - 1)]
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ n - contactDistance M a),
      Nat.cast_sub (by omega : contactDistance M a ≤ n), Nat.cast_one, ZMod.natCast_self,
      Nat.cast_sub (by omega : contactDistance M a - (g - M).val ≤ (e i - 1).val),
      Nat.cast_sub (by omega : (g - M).val ≤ contactDistance M a), huZ]
    ring

/-- Every surviving vertex of the second-arc contraction agrees with the
second half at its inherited root; the canonical range formula handles zero. -/
theorem contactSecondArc_contracted_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val)
    (i : ZMod (contactSecondArcTriple g M a hn hc hu).contractedSize) :
    contractedVertexIndex g (contactSecondArcTriple g M a hn hc hu) i =
      secondHalfIndex M a
        (ZMod.ringEquivCongr (contactSecondArcTriple_contractedSize g M a hn hc hu) i +
          ((g - a).val : ZMod (secondHalfSize M a))) := by
  let t := contactSecondArcTriple g M a hn hc hu
  let e := ZMod.ringEquivCongr (contactSecondArcTriple_contractedSize g M a hn hc hu)
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hvroot : (g - a).val = (g - M).val - contactDistance M a := by
    rw [contact_relative_offset_val M a g, if_neg (by omega)]
  have hv : (i - 1).val = (e i - 1).val := by
    have hh := ZMod.ringEquivCongr_val (contactSecondArcTriple_contractedSize g M a hn hc hu) (i - 1)
    simpa only [map_sub, map_one] using hh.symm
  have hrel : (((g - a).val : ZMod (secondHalfSize M a)) - 1) +
      ((n - (g - M).val + 1 : ℕ) : ZMod (secondHalfSize M a)) = 0 := by
    have he : (g - a).val + (n - (g - M).val) = secondHalfSize M a := by
      unfold secondHalfSize
      omega
    calc
      _ = (((g - a).val + (n - (g - M).val) : ℕ) : ZMod (secondHalfSize M a)) := by
        push_cast
        ring
      _ = 0 := by rw [he, ZMod.natCast_self]
  have hcut := zmod_cut_shift_val (n - (g - M).val)
    (by unfold secondHalfSize; omega : n - (g - M).val < secondHalfSize M a)
    (e i) (((g - a).val : ZMod (secondHalfSize M a)) - 1) hrel
  have hlower : t.lower.val = n - (g - M).val - 1 := rfl
  have herase : t.erasedInteriorCount = contactDistance M a := by
    dsimp [t, IncreasingBoundaryTriple.erasedInteriorCount, contactSecondArcTriple]
    omega
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  have hvZ : ((g - a).val : ZMod n) = g - a := ZMod.natCast_zmod_val _
  rw [secondHalfIndex_range]
  change g + ((t.expandPosition ⟨(i - 1).val, ZMod.val_lt _⟩).val : ZMod n) + 1 =
    a + 1 + ((e i + ((g - a).val : ZMod (secondHalfSize M a)) - 1).val : ZMod n)
  have hearg : e i + ((g - a).val : ZMod (secondHalfSize M a)) - 1 =
      e i + (((g - a).val : ZMod (secondHalfSize M a)) - 1) := by ring
  rw [IncreasingBoundaryTriple.expandPosition_val, hlower, herase, hv, hearg, hcut]
  by_cases hk : (e i - 1).val < n - (g - M).val
  · rw [if_pos hk, if_pos (by omega : (e i - 1).val ≤ n - (g - M).val - 1)]
    have he : (e i - 1).val + secondHalfSize M a - (n - (g - M).val) =
        (e i - 1).val + (g - a).val := by
      unfold secondHalfSize
      omega
    rw [he, Nat.cast_add, hvZ]
    ring
  · rw [if_neg hk, if_neg (by omega : ¬ (e i - 1).val ≤ n - (g - M).val - 1)]
    rw [Nat.cast_add, Nat.cast_sub (by omega : n - (g - M).val ≤ (e i - 1).val),
      Nat.cast_sub (by omega : (g - M).val ≤ n), ZMod.natCast_self, huZ, contactDistance_cast]
    ring

/-- Full first-half tuple identity after the proved arity transport. -/
theorem contactFirstArc_contracted_tuple (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (fun u : ZMod (firstHalfSize M a) => contractedWordTuple P g
      (contactFirstArcTriple g M a hn hc hu)
      ((ZMod.ringEquivCongr (contactFirstArcTriple_contractedSize g M a hn hc hu)).symm u)) =
      shift ((g - M).val : ZMod (firstHalfSize M a)) (firstHalf P M a) := by
  funext u
  unfold contractedWordTuple shift firstHalf
  rw [contactFirstArc_contracted_labels g M a hn hc hu]
  simp only [RingEquiv.apply_symm_apply]

/-- Full second-half tuple identity, at every label of the inherited root cut. -/
theorem contactSecondArc_contracted_tuple (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (fun u : ZMod (secondHalfSize M a) => contractedWordTuple P g
      (contactSecondArcTriple g M a hn hc hu)
      ((ZMod.ringEquivCongr (contactSecondArcTriple_contractedSize g M a hn hc hu)).symm u)) =
      shift ((g - a).val : ZMod (secondHalfSize M a)) (secondHalf P M a) := by
  funext u
  unfold contractedWordTuple shift secondHalf
  rw [contactSecondArc_contracted_labels g M a hn hc hu]
  simp only [RingEquiv.apply_symm_apply]

end
end SM

#check SM.contactFirstArc_contracted_labels
#print axioms SM.contactFirstArc_contracted_labels
#check SM.contactSecondArc_contracted_labels
#print axioms SM.contactSecondArc_contracted_labels
#check SM.contactFirstArc_contracted_tuple
#print axioms SM.contactFirstArc_contracted_tuple
#check SM.contactSecondArc_contracted_tuple
#print axioms SM.contactSecondArc_contracted_tuple
