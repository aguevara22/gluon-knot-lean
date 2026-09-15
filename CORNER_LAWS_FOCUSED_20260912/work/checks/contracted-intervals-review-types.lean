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


namespace SM.IncreasingBoundaryTriple

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] contractedSize_neZero

/-- Expand both retained endpoints of an arbitrary contracted interval. -/
def expandInterval (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) : BoundaryInterval n where
  left := t.expandPosition J.left
  right := t.expandPosition J.right
  increasing := t.expandPosition_strict J.increasing

def expandTriple (t : IncreasingBoundaryTriple n)
    (u : IncreasingBoundaryTriple t.contractedSize) : IncreasingBoundaryTriple n where
  lower := t.expandPosition u.lower
  middle := t.expandPosition u.middle
  upper := t.expandPosition u.upper
  lower_middle := t.expandPosition_strict u.lower_middle
  middle_upper := t.expandPosition_strict u.middle_upper

/-- The distinguished formal leaf retains exactly the two critical endpoints. -/
def contractedLeaf (t : IncreasingBoundaryTriple n) : BoundaryInterval t.contractedSize where
  left := ⟨t.lower.val, by have := t.contractedSize_bounds; omega⟩
  right := ⟨t.lower.val + 1, by have := t.contractedSize_bounds; omega⟩
  increasing := by change t.lower.val < t.lower.val + 1; omega

theorem contractedLeaf_leaves (t : IncreasingBoundaryTriple n) : t.contractedLeaf.leaves = 1 := by
  simp [contractedLeaf, BoundaryInterval.leaves]

theorem expandInterval_contractedLeaf (t : IncreasingBoundaryTriple n) :
    t.expandInterval t.contractedLeaf = t.spanInterval := by
  apply BoundaryInterval.eq_of_endpoints
  · exact t.expandPosition_lower
  · exact t.expandPosition_upper

/-- Containment of the complete old arc is exactly containment of the
distinguished new leaf; no extra cut or marked-composition assumption is used. -/
theorem expandInterval_contains (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    ((t.expandInterval J).left ≤ t.lower ∧ t.upper ≤ (t.expandInterval J).right) ↔
      (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) := by
  change (t.expandPosition J.left ≤ t.lower ∧ t.upper ≤ t.expandPosition J.right) ↔ _
  rw [← t.expandPosition_lower, ← t.expandPosition_upper]
  exact and_congr t.expandPosition_strict.le_iff_le t.expandPosition_strict.le_iff_le

theorem expandInterval_injective (t : IncreasingBoundaryTriple n) :
    Function.Injective t.expandInterval := by
  intro I J he
  apply BoundaryInterval.eq_of_endpoints
  · exact t.expandPosition_strict.injective (congrArg BoundaryInterval.left he)
  · exact t.expandPosition_strict.injective (congrArg BoundaryInterval.right he)

/-- Contract any interval whose two endpoints survive. In particular this
includes every interval containing the entire critical arc. -/
def contractInterval (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n)
    (hl : I.left ≤ t.lower ∨ t.upper ≤ I.left)
    (hr : I.right ≤ t.lower ∨ t.upper ≤ I.right) : BoundaryInterval t.contractedSize where
  left := t.contractPosition I.left hl
  right := t.contractPosition I.right hr
  increasing := by
    apply t.expandPosition_strict.lt_iff_lt.mp
    rw [t.expand_contractPosition, t.expand_contractPosition]
    exact I.increasing

theorem expand_contractInterval (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n)
    (hl : I.left ≤ t.lower ∨ t.upper ≤ I.left)
    (hr : I.right ≤ t.lower ∨ t.upper ≤ I.right) :
    t.expandInterval (t.contractInterval I hl hr) = I := by
  apply BoundaryInterval.eq_of_endpoints
  · exact t.expand_contractPosition I.left hl
  · exact t.expand_contractPosition I.right hr

theorem contract_expandInterval (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    t.contractInterval (t.expandInterval J) (t.expandPosition_survives J.left)
      (t.expandPosition_survives J.right) = J := by
  apply t.expandInterval_injective
  exact t.expand_contractInterval _ _ _

/-- Every containing source interval is represented, including the critical
interval and the complete boundary interval. -/
theorem containing_interval_is_expanded (t : IncreasingBoundaryTriple n)
    (I : BoundaryInterval n) (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    ∃ J : BoundaryInterval t.contractedSize,
      t.expandInterval J = I ∧ J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right := by
  let J := t.contractInterval I (Or.inl hI.1) (Or.inr hI.2)
  have he : t.expandInterval J = I := t.expand_contractInterval I _ _
  refine ⟨J, he, (t.expandInterval_contains J).mp ?_⟩
  simpa only [he] using hI

theorem expandInterval_full (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    t.expandInterval (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) =
      fullBoundaryInterval hn := by
  apply BoundaryInterval.eq_of_endpoints
  · apply Fin.ext
    exact t.expandPosition_initial
  · apply Fin.ext
    exact t.expandPosition_final

/-- A contracted interval properly containing the formal leaf has at least
two leaves, so its unit-array equation has the required zero right side. -/
theorem containing_contracted_nonleaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) : 2 ≤ J.leaves := by
  have hl : J.left.val ≤ t.lower.val := hJ.1
  have hr : t.lower.val + 1 ≤ J.right.val := hJ.2
  by_contra h
  have hv : J.right.val - J.left.val < 2 := Nat.lt_of_not_ge h
  have he : J = t.contractedLeaf := by
    apply BoundaryInterval.eq_of_endpoints
    · apply Fin.ext
      change J.left.val = t.lower.val
      omega
    · apply Fin.ext
      change J.right.val = t.lower.val + 1
      omega
  exact hne he

end
end SM.IncreasingBoundaryTriple

namespace ContractedIntervalsIndependentReview
open SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

-- The expansion range is exactly all intervals with two surviving endpoints.
theorem interval_range_iff_surviving_endpoints (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n) :
    (∃ J : BoundaryInterval t.contractedSize, t.expandInterval J = I) ↔
      (I.left ≤ t.lower ∨ t.upper ≤ I.left) ∧ (I.right ≤ t.lower ∨ t.upper ≤ I.right) := by
  constructor
  · rintro ⟨J, rfl⟩
    exact ⟨t.expandPosition_survives J.left, t.expandPosition_survives J.right⟩
  · rintro ⟨hl, hr⟩
    exact ⟨t.contractInterval I hl hr, t.expand_contractInterval I hl hr⟩

-- Every containing old interval occurs exactly once and its contraction contains the formal leaf.
theorem containing_interval_unique_preimage (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n)
    (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    ∃! J : BoundaryInterval t.contractedSize,
      t.expandInterval J = I ∧ J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right := by
  obtain ⟨J, hJ⟩ := t.containing_interval_is_expanded I hI
  refine ⟨J, hJ, ?_⟩
  intro K hK
  exact t.expandInterval_injective (hK.1.trans hJ.1.symm)

-- Precisely the distinguished formal leaf expands to the original critical span.
theorem critical_interval_iff_formal_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    t.expandInterval J = t.spanInterval ↔ J = t.contractedLeaf := by
  constructor
  · intro h
    exact t.expandInterval_injective (h.trans t.expandInterval_contractedLeaf.symm)
  · rintro rfl
    exact t.expandInterval_contractedLeaf

-- Every strictly larger containing source interval has an actual nonleaf contraction.
theorem all_strictly_larger_intervals_contract_to_nonleaf (t : IncreasingBoundaryTriple n)
    (I : BoundaryInterval n) (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) (hne : I ≠ t.spanInterval) :
    ∃ J : BoundaryInterval t.contractedSize, t.expandInterval J = I ∧ 2 ≤ J.leaves := by
  obtain ⟨J, he, hc⟩ := t.containing_interval_is_expanded I hI
  refine ⟨J, he, t.containing_contracted_nonleaf J hc ?_⟩
  intro hj
  apply hne
  rw [← he, hj]
  exact t.expandInterval_contractedLeaf

-- The actual inverse has value one on the formal leaf, including a complete size-two word.
theorem actual_inverse_formal_leaf_value {R : Type*} [CommRing R] [Invertible (2 : R)]
    (t : IncreasingBoundaryTriple n) (H : TripleArray t.contractedSize R) :
    farOnlyCoordinates H t.contractedLeaf = 1 :=
  farOnlyCoordinates_leaf H t.contractedLeaf t.contractedLeaf_leaves

-- The proper containing-interval hypothesis is sufficient for the zero equation used in propagation.
theorem actual_inverse_strict_containing_equation {R : Type*} [CommRing R] [Invertible (2 : R)]
    (t : IncreasingBoundaryTriple n) (H : TripleArray t.contractedSize R)
    (J : BoundaryInterval t.contractedSize)
    (hc : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) :
    farTransform H (farOnlyCoordinates H) J = 0 :=
  farOnly_nonleaf_E H J (t.containing_contracted_nonleaf J hc hne)

-- Contraction of the critical span returns its exact formal leaf, not merely an interval of the same length.
theorem critical_span_contracts_exactly_to_leaf (t : IncreasingBoundaryTriple n) :
    t.contractInterval t.spanInterval (Or.inl le_rfl) (Or.inr le_rfl) = t.contractedLeaf := by
  apply t.expandInterval_injective
  rw [t.expand_contractInterval]
  exact t.expandInterval_contractedLeaf.symm

-- The entire increasing triple is retained injectively by the actual position expansion.
theorem triple_expansion_injective (t : IncreasingBoundaryTriple n) :
    Function.Injective t.expandTriple := by
  intro u v he
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact t.expandPosition_strict.injective (congrArg IncreasingBoundaryTriple.lower he)
  · exact t.expandPosition_strict.injective (congrArg IncreasingBoundaryTriple.middle he)
  · exact t.expandPosition_strict.injective (congrArg IncreasingBoundaryTriple.upper he)

-- No expanded triple can reintroduce the deleted critical middle and equal the critical triple.
theorem expanded_triple_is_not_critical (t : IncreasingBoundaryTriple n)
    (u : IncreasingBoundaryTriple t.contractedSize) : t.expandTriple u ≠ t := by
  intro he
  have hm := congrArg IncreasingBoundaryTriple.middle he
  have hs := t.expandPosition_survives u.middle
  change t.expandPosition u.middle = t.middle at hm
  rw [hm] at hs
  rcases hs with hl | hr
  · exact (not_le_of_gt t.lower_middle) hl
  · exact (not_le_of_gt t.middle_upper) hr

end
end ContractedIntervalsIndependentReview

#check SM.IncreasingBoundaryTriple.expandInterval
#print axioms SM.IncreasingBoundaryTriple.expandInterval
#check SM.IncreasingBoundaryTriple.expandTriple
#print axioms SM.IncreasingBoundaryTriple.expandTriple
#check SM.IncreasingBoundaryTriple.contractedLeaf
#print axioms SM.IncreasingBoundaryTriple.contractedLeaf
#check SM.IncreasingBoundaryTriple.contractedLeaf_leaves
#print axioms SM.IncreasingBoundaryTriple.contractedLeaf_leaves
#check SM.IncreasingBoundaryTriple.expandInterval_contractedLeaf
#print axioms SM.IncreasingBoundaryTriple.expandInterval_contractedLeaf
#check SM.IncreasingBoundaryTriple.expandInterval_contains
#print axioms SM.IncreasingBoundaryTriple.expandInterval_contains
#check SM.IncreasingBoundaryTriple.expandInterval_injective
#print axioms SM.IncreasingBoundaryTriple.expandInterval_injective
#check SM.IncreasingBoundaryTriple.contractInterval
#print axioms SM.IncreasingBoundaryTriple.contractInterval
#check SM.IncreasingBoundaryTriple.expand_contractInterval
#print axioms SM.IncreasingBoundaryTriple.expand_contractInterval
#check SM.IncreasingBoundaryTriple.contract_expandInterval
#print axioms SM.IncreasingBoundaryTriple.contract_expandInterval
#check SM.IncreasingBoundaryTriple.containing_interval_is_expanded
#print axioms SM.IncreasingBoundaryTriple.containing_interval_is_expanded
#check SM.IncreasingBoundaryTriple.expandInterval_full
#print axioms SM.IncreasingBoundaryTriple.expandInterval_full
#check SM.IncreasingBoundaryTriple.containing_contracted_nonleaf
#print axioms SM.IncreasingBoundaryTriple.containing_contracted_nonleaf
#check ContractedIntervalsIndependentReview.interval_range_iff_surviving_endpoints
#print axioms ContractedIntervalsIndependentReview.interval_range_iff_surviving_endpoints
#check ContractedIntervalsIndependentReview.containing_interval_unique_preimage
#print axioms ContractedIntervalsIndependentReview.containing_interval_unique_preimage
#check ContractedIntervalsIndependentReview.critical_interval_iff_formal_leaf
#print axioms ContractedIntervalsIndependentReview.critical_interval_iff_formal_leaf
#check ContractedIntervalsIndependentReview.all_strictly_larger_intervals_contract_to_nonleaf
#print axioms ContractedIntervalsIndependentReview.all_strictly_larger_intervals_contract_to_nonleaf
#check ContractedIntervalsIndependentReview.actual_inverse_formal_leaf_value
#print axioms ContractedIntervalsIndependentReview.actual_inverse_formal_leaf_value
#check ContractedIntervalsIndependentReview.actual_inverse_strict_containing_equation
#print axioms ContractedIntervalsIndependentReview.actual_inverse_strict_containing_equation
#check ContractedIntervalsIndependentReview.critical_span_contracts_exactly_to_leaf
#print axioms ContractedIntervalsIndependentReview.critical_span_contracts_exactly_to_leaf
#check ContractedIntervalsIndependentReview.triple_expansion_injective
#print axioms ContractedIntervalsIndependentReview.triple_expansion_injective
#check ContractedIntervalsIndependentReview.expanded_triple_is_not_critical
#print axioms ContractedIntervalsIndependentReview.expanded_triple_is_not_critical
