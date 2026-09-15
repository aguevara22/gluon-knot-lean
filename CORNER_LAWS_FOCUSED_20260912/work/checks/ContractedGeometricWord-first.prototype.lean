import SM.CriticalSourceResponse
import SM.FiniteChiStability

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
  rfl

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
  rw [hp, boundaryWord_last, boundaryWord_last] at h
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

#check SM.IncreasingBoundaryTriple.contractedSize_neZero
#print axioms SM.IncreasingBoundaryTriple.contractedSize_neZero
#check SM.contractedVertexIndex
#print axioms SM.contractedVertexIndex
#check SM.contractedVertexIndex_injective
#print axioms SM.contractedVertexIndex_injective
#check SM.contractedWordTuple
#print axioms SM.contractedWordTuple
#check SM.contractedWord_boundary
#print axioms SM.contractedWord_boundary
#check SM.contractedWord_first_vertex
#print axioms SM.contractedWord_first_vertex
#check SM.contractedWord_last_vertex
#print axioms SM.contractedWord_last_vertex
#check SM.contractedWord_physical_root
#print axioms SM.contractedWord_physical_root
#check SM.contractedWord_G1
#print axioms SM.contractedWord_G1
#check SM.proper_contracted_polygon_data
#print axioms SM.proper_contracted_polygon_data
