import SM.CriticalSourceResponse
import SM.FiniteChiStability
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

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

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Expand every raw cut while preserving the part count, including unary
compositions. The skipped critical interior occurs within one expanded part. -/
def expandComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) :
    IntervalComposition (t.expandInterval J) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => t.expandPosition (π.cut k)
  strict := t.expandPosition_strict.comp π.strict
  first := congrArg t.expandPosition π.first
  last := congrArg t.expandPosition π.last

/-- This exact domain excludes only cuts strictly inside the deleted arc. -/
def SurvivingCuts (t : IncreasingBoundaryTriple n) {I : BoundaryInterval n}
    (π : IntervalComposition I) : Prop :=
  ∀ k : Fin (π.parts + 1), π.cut k ≤ t.lower ∨ t.upper ≤ π.cut k

theorem expandComposition_survives (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) :
    SurvivingCuts t (expandComposition t π) := by
  intro k
  exact t.expandPosition_survives (π.cut k)

/-- Contract exactly the original surviving cut list. Endpoint identities
show the result is a composition of J, not an arbitrary new interval. -/
def contractComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition (t.expandInterval J))
    (hπ : SurvivingCuts t π) : IntervalComposition J where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => t.contractPosition (π.cut k) (hπ k)
  strict := by
    intro a b hab
    apply t.expandPosition_strict.lt_iff_lt.mp
    rw [t.expand_contractPosition, t.expand_contractPosition]
    exact π.strict hab
  first := by
    apply t.expandPosition_strict.injective
    rw [t.expand_contractPosition]
    exact π.first
  last := by
    apply t.expandPosition_strict.injective
    rw [t.expand_contractPosition]
    exact π.last

theorem contract_expandComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) :
    contractComposition t (expandComposition t π) (expandComposition_survives t π) = π := by
  apply eq_of_parts_cut (π := contractComposition t (expandComposition t π)
    (expandComposition_survives t π)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact t.contract_expandPosition (π.cut k)

theorem expand_contractComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition (t.expandInterval J))
    (hπ : SurvivingCuts t π) : expandComposition t (contractComposition t π hπ) = π := by
  apply eq_of_parts_cut (π := expandComposition t (contractComposition t π hπ)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact t.expand_contractPosition (π.cut k) (hπ k)

/-- Bijection of the complete raw composition types with every original
composition whose cuts survive. No unary or zero-weight term is discarded. -/
def survivingCompositionEquiv (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    IntervalComposition J ≃ {π : IntervalComposition (t.expandInterval J) // SurvivingCuts t π} where
  toFun π := ⟨expandComposition t π, expandComposition_survives t π⟩
  invFun π := contractComposition t π.val π.property
  left_inv := contract_expandComposition t
  right_inv π := Subtype.ext (expand_contractComposition t π.val π.property)

theorem expandComposition_part (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (k : Fin π.parts) :
    (expandComposition t π).part k = t.expandInterval (π.part k) := rfl

theorem expandComposition_nearTriple (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (k : Fin (π.parts - 1)) :
    (expandComposition t π).nearTriple k = t.expandTriple (π.nearTriple k) := rfl

theorem expandComposition_farTriple (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (k : Fin (π.parts - 1)) :
    (expandComposition t π).farTriple k = t.expandTriple (π.farTriple k) := rfl

/-- If one child contains the whole critical arc, each cut lies before its
left endpoint or after its right endpoint. Consecutive cut indices leave
no third possibility. -/
theorem survivingCuts_of_containing_child (t : IncreasingBoundaryTriple n)
    {I : BoundaryInterval n} (π : IntervalComposition I) (k : Fin π.parts)
    (hk : (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right) :
    SurvivingCuts t π := by
  intro j
  by_cases hj : j.val ≤ k.val
  · left
    exact le_trans (π.strict.monotone (show j ≤ k.castSucc from hj)) hk.1
  · right
    have hs : k.succ ≤ j := by change k.val + 1 ≤ j.val; omega
    exact le_trans hk.2 (π.strict.monotone hs)

/-- Conversely, the child covering the critical left endpoint must reach
the critical right endpoint because its next cut survives the deletion. -/
theorem containing_child_of_survivingCuts (t : IncreasingBoundaryTriple n)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) (hπ : SurvivingCuts t π) :
    ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right := by
  have hr : t.lower < I.right := lt_of_lt_of_le
    (lt_trans t.lower_middle t.middle_upper) hI.2
  obtain ⟨k, hkl, hkr⟩ := π.exists_halfOpen_part t.lower hI.1 hr
  refine ⟨k, hkl, ?_⟩
  rcases hπ k.succ with h | h
  · exact False.elim ((not_le_of_gt hkr) h)
  · exact h

theorem survivingCuts_iff_containing_child (t : IncreasingBoundaryTriple n)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    SurvivingCuts t π ↔
      ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right := by
  constructor
  · exact containing_child_of_survivingCuts t π hI
  · rintro ⟨k, hk⟩
    exact survivingCuts_of_containing_child t π k hk

/-- Source propagation correspondence: every contracted composition
corresponds to exactly one original composition with a containing child.
The separate positive-interval uniqueness theorem makes that child unique. -/
def containingCompositionEquiv (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    IntervalComposition J ≃ {π : IntervalComposition (t.expandInterval J) //
      ∃ k : Fin π.parts, (π.part k).left ≤ t.lower ∧ t.upper ≤ (π.part k).right} where
  toFun π := ⟨expandComposition t π,
    containing_child_of_survivingCuts t (expandComposition t π)
      ((t.expandInterval_contains J).mpr hJ) (expandComposition_survives t π)⟩
  invFun π := contractComposition t π.val
    ((survivingCuts_iff_containing_child t π.val ((t.expandInterval_contains J).mpr hJ)).mpr π.property)
  left_inv π := contract_expandComposition t π
  right_inv π := Subtype.ext (expand_contractComposition t π.val _)

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

namespace IncreasingBoundaryTriple

/-- Since the distinguished leaf joins adjacent positions, an interval
excluding it lies wholly on one side. There is no partially overlapping case. -/
theorem contractedInterval_side (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    J.right ≤ t.contractedLeaf.left ∨ t.contractedLeaf.right ≤ J.left := by
  change ¬ (J.left.val ≤ t.lower.val ∧ t.lower.val + 1 ≤ J.right.val) at hJ
  change J.right.val ≤ t.lower.val ∨ t.lower.val + 1 ≤ J.left.val
  omega

/-- Outside the distinguished leaf expansion is a translation, hence
preserves the exact number of leaves and the formal unit-array value. -/
theorem expandInterval_leaves_off_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    (t.expandInterval J).leaves = J.leaves := by
  have hj : J.left.val < J.right.val := J.increasing
  change (t.expandPosition J.right).val - (t.expandPosition J.left).val =
    J.right.val - J.left.val
  rw [expandPosition_val, expandPosition_val]
  rcases t.contractedInterval_side J hJ with h | h
  · have hr : J.right.val ≤ t.lower.val := h
    have hl : J.left.val ≤ t.lower.val := by omega
    rw [if_pos hr, if_pos hl]
  · have hl : t.lower.val + 1 ≤ J.left.val := h
    rw [if_neg (by omega), if_neg (by omega)]
    omega

/-- A subinterval of an interval excluding the leaf still excludes it. -/
theorem subinterval_off_leaf (t : IncreasingBoundaryTriple n)
    (I J : BoundaryInterval t.contractedSize)
    (hI : ¬ (I.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ I.right))
    (hJI : I.left ≤ J.left ∧ J.right ≤ I.right) :
    ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) := by
  rintro ⟨hl, hr⟩
  exact hI ⟨hJI.1.trans hl, hr.trans hJI.2⟩

end IncreasingBoundaryTriple

namespace IntervalComposition

theorem every_cut_survives_off_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (π : IntervalComposition (t.expandInterval J)) : SurvivingCuts t π := by
  intro k
  rcases t.contractedInterval_side J hJ with h | h
  · left
    have he : t.expandPosition J.right ≤ t.lower := by
      rw [← t.expandPosition_lower]
      exact t.expandPosition_strict.monotone h
    exact (π.cut_bounds k).2.trans he
  · right
    have he : t.upper ≤ t.expandPosition J.left := by
      rw [← t.expandPosition_upper]
      exact t.expandPosition_strict.monotone h
    exact he.trans (π.cut_bounds k).1

/-- Away from the leaf every original raw composition survives, so the
correspondence covers the entire composition type, without a subtype filter. -/
def offLeafCompositionEquiv (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    IntervalComposition J ≃ IntervalComposition (t.expandInterval J) where
  toFun := expandComposition t
  invFun π := contractComposition t π (every_cut_survives_off_leaf t J hJ π)
  left_inv := contract_expandComposition t
  right_inv π := expand_contractComposition t π _

end IntervalComposition

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

def contractedTripleArray (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    TripleArray t.contractedSize R := fun u => H (t.expandTriple u)

theorem IntervalComposition.expandComposition_weight (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J) (D H : TripleArray n R) :
    (expandComposition t π).nearFarWeight D H =
      π.nearFarWeight (contractedTripleArray t D) (contractedTripleArray t H) := rfl

/-- Complete equation transport on every interval away from the new leaf.
This is proved by the raw composition bijection, retaining all gate factors. -/
theorem nearFarTransform_expanded_off_leaf (t : IncreasingBoundaryTriple n)
    (D H : TripleArray n R) (X : IntervalArray n R)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    nearFarTransform (contractedTripleArray t D) (contractedTripleArray t H)
      (fun I => X (t.expandInterval I)) J = nearFarTransform D H X (t.expandInterval J) := by
  unfold nearFarTransform
  exact Fintype.sum_equiv (IntervalComposition.offLeafCompositionEquiv t J hJ) _ _ (fun _ => rfl)

theorem boundaryUnitArray_expanded_off_leaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    boundaryUnitArray (R := R) (t.expandInterval J) = boundaryUnitArray J := by
  have he := t.expandInterval_leaves_off_leaf J hJ
  have hi := (t.expandInterval J).increasing
  have hj := J.increasing
  change (t.expandInterval J).left.val < (t.expandInterval J).right.val at hi
  change J.left.val < J.right.val at hj
  change (t.expandInterval J).right.val - (t.expandInterval J).left.val =
    J.right.val - J.left.val at he
  have hc : (t.expandInterval J).right.val = (t.expandInterval J).left.val + 1 ↔
      J.right.val = J.left.val + 1 := by omega
  simp only [boundaryUnitArray, hc]

/-- Actual inverse coordinates agree on every unchanged other child.
The induction compares the transported original equation with the unique
contracted equation, using equality only on strictly shorter children. -/
theorem farOnlyCoordinates_expanded_off_leaf (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hJ : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    farOnlyCoordinates H (t.expandInterval J) = farOnlyCoordinates (contractedTripleArray t H) J := by
  have he := nearFarTransform_expanded_off_leaf t 0 H (farOnlyCoordinates H) J hJ
  change nearFarTransform 0 (contractedTripleArray t H)
    (fun I => farOnlyCoordinates H (t.expandInterval I)) J =
      farTransform H (farOnlyCoordinates H) (t.expandInterval J) at he
  rw [farOnlyCoordinates_equation, boundaryUnitArray_expanded_off_leaf t J hJ] at he
  have hq := congrFun (farOnlyCoordinates_equation (contractedTripleArray t H)) J
  change nearFarTransform 0 (contractedTripleArray t H)
    (farOnlyCoordinates (contractedTripleArray t H)) J = boundaryUnitArray J at hq
  rw [nearFarTransform_eq_triangular] at he hq
  unfold triangularTransform at he hq
  have hs : (∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
      π.val.nearFarWeight 0 (contractedTripleArray t H) *
        ∏ k : Fin π.val.parts, farOnlyCoordinates H (t.expandInterval (π.val.part k))) =
      ∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
        π.val.nearFarWeight 0 (contractedTripleArray t H) *
          ∏ k : Fin π.val.parts, farOnlyCoordinates (contractedTripleArray t H) (π.val.part k) := by
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact farOnlyCoordinates_expanded_off_leaf t H (π.val.part k)
      (t.subinterval_off_leaf J (π.val.part k) hJ (π.val.part_bounds k))
  rw [hs] at he
  exact add_right_cancel (he.trans hq.symm)
termination_by J.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- No triple of surviving positions can be the critical triple because
its middle position was deleted. This is purely about actual boundary labels. -/
theorem IncreasingBoundaryTriple.expandTriple_ne_critical (t : IncreasingBoundaryTriple n)
    (u : IncreasingBoundaryTriple t.contractedSize) : t.expandTriple u ≠ t := by
  intro he
  have hm : t.expandPosition u.middle = t.middle := congrArg IncreasingBoundaryTriple.middle he
  have hs := t.expandPosition_survives u.middle
  rw [hm] at hs
  rcases hs with hl | hr
  · exact (not_le_of_gt t.lower_middle) hl
  · exact (not_le_of_gt t.middle_upper) hr

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Both punctured arrays have exactly the same contracted array whenever
the only entry permitted to differ is the critical one. -/
theorem contractedTripleArray_eq_off_critical (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    contractedTripleArray t H₁ = contractedTripleArray t H₂ := by
  funext u
  exact h (t.expandTriple u) (t.expandTriple_ne_critical u)

theorem contractedTripleArray_neg (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    contractedTripleArray t (-H) = -contractedTripleArray t H := rfl

/-- The contracted array is the chirotope array of the actual contracted
polygon at its retained physical closing root. No genericity is needed for
this equality of the sampled determinants. -/
theorem geometricBoundaryArray_contractedWord (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := R) (contractedWordTuple P g t) 0 =
      contractedTripleArray t (geometricBoundaryArray P g) := by
  funext u
  simp only [contractedTripleArray, geometricBoundaryArray, chi]
  change ((SignType.sign (det
    (boundaryWord (contractedWordTuple P g t) 0 u.middle -
      boundaryWord (contractedWordTuple P g t) 0 u.upper)
    (boundaryWord (contractedWordTuple P g t) 0 u.lower -
      boundaryWord (contractedWordTuple P g t) 0 u.upper)) : ℤ) : R) = _
  rw [contractedWord_boundary, contractedWord_boundary, contractedWord_boundary]
  rfl

/-- The propagation base uses the formal open-word leaf value one, also
when the complete contraction has only two positions. -/
theorem contracted_leaf_inverse_value (t : IncreasingBoundaryTriple n) (H : TripleArray n R) :
    farOnlyCoordinates (contractedTripleArray t H) t.contractedLeaf = 1 :=
  farOnlyCoordinates_leaf _ _ t.contractedLeaf_leaves

/-- For a proper contraction the complete barred output is the actual
rooted tree coefficient of Q. The G1 and arity proofs are supplied locally;
the physical root is the one identified by contractedWord_physical_root. -/
theorem contracted_output_tree (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hZ : pointZeroTriples P = {t.vertexSet g})
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    farOnlyOutput (contractedTripleArray t (geometricBoundaryArray (R := R) P g))
      (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) =
      (treeCoefficient (contractedWordTuple P g t) (contractedWord_G1 P g t hZ) 0
        (t.contractedSize_of_proper hn hproper) : R) := by
  rw [← geometricBoundaryArray_contractedWord]
  exact (treeCoefficient_farOnly (contractedWordTuple P g t)
    (contractedWord_G1 P g t hZ) 0 (t.contractedSize_of_proper hn hproper)).symm

end
end SM

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A positive-length interval belongs to at most one full child. This
also covers a contracted formal leaf without an interior vertex label. -/
theorem part_contains_unique (π : IntervalComposition I) (J : BoundaryInterval n)
    {k l : Fin π.parts}
    (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (hl : (π.part l).left ≤ J.left ∧ J.right ≤ (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact ((not_le_of_gt J.increasing) (hk.2.trans ((π.part_order h).trans hl.1))).elim
  · exact h
  · exact ((not_le_of_gt J.increasing) (hl.2.trans ((π.part_order h).trans hk.1))).elim

theorem other_part_excludes (π : IntervalComposition I) (J : BoundaryInterval n)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)
    (l : Fin π.parts) (hl : l ≠ k) :
    ¬ ((π.part l).left ≤ J.left ∧ J.right ≤ (π.part l).right) := by
  intro hc
  exact hl (π.part_contains_unique J hc hk)

variable {R : Type*} [CommRing R]

/-- If no child contains the critical span, every child inverse coordinate
is unchanged, hence so is the complete child product. -/
theorem child_product_unchanged (π : IntervalComposition I) (J : BoundaryInterval n)
    (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (hπ : ∀ k : Fin π.parts, ¬ ((π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right)) :
    (∏ k : Fin π.parts, X₁ (π.part k)) = ∏ k : Fin π.parts, X₂ (π.part k) := by
  apply Finset.prod_congr rfl
  intro k _
  exact h _ (hπ k)

/-- Remove the unique potentially changing child from each full product.
Every remaining factor agrees; subtraction gives exactly one changed factor,
with no division and no product of two changes, including zero coordinates. -/
theorem child_product_difference (π : IntervalComposition I) (J : BoundaryInterval n)
    (X₁ X₂ : IntervalArray n R)
    (h : ∀ K, ¬ (K.left ≤ J.left ∧ J.right ≤ K.right) → X₁ K = X₂ K)
    (k : Fin π.parts) (hk : (π.part k).left ≤ J.left ∧ J.right ≤ (π.part k).right) :
    (∏ l : Fin π.parts, X₂ (π.part l)) - (∏ l : Fin π.parts, X₁ (π.part l)) =
      (X₂ (π.part k) - X₁ (π.part k)) *
        ∏ l ∈ Finset.univ.erase k, X₁ (π.part l) := by
  classical
  have hp : (∏ l ∈ Finset.univ.erase k, X₂ (π.part l)) =
      ∏ l ∈ Finset.univ.erase k, X₁ (π.part l) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact (h _ (π.other_part_excludes J k hk l (Finset.mem_erase.mp hl).1)).symm
  rw [← Finset.mul_prod_erase Finset.univ (fun l => X₂ (π.part l)) (Finset.mem_univ k)]
  rw [← Finset.mul_prod_erase Finset.univ (fun l => X₁ (π.part l)) (Finset.mem_univ k)]
  rw [hp]
  ring

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every complete contracted composition has exactly one child containing
the distinguished formal leaf. Adjacent children may share endpoints, but
cannot both contain its positive length. -/
theorem IntervalComposition.unique_contracted_leaf_child (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    ∃! k : Fin π.parts,
      (π.part k).left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := containing_child_of_survivingCuts t (expandComposition t π)
    ((t.expandInterval_contains J).mpr hJ) (expandComposition_survives t π)
  have hc := (t.expandInterval_contains (π.part k)).mp hk
  exact ⟨k, hc, fun l hl => π.part_contains_unique t.contractedLeaf hl hc⟩

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- A conditional product step for the interval-length induction. The only
response premise is on containing children; off-leaf factors are the actual
inverse coordinates, whose transport is already proved. No division is used. -/
theorem expanded_child_product_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) (s : R)
    (hchild : ∀ k : Fin π.parts,
      (π.part k).left ≤ t.contractedLeaf.left → t.contractedLeaf.right ≤ (π.part k).right →
      farOnlyCoordinates H₂ (t.expandInterval (π.part k)) -
        farOnlyCoordinates H₁ (t.expandInterval (π.part k)) =
        s * farOnlyCoordinates (contractedTripleArray t H₁) (π.part k)) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part k))) -
      (∏ k : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part k))) =
      s * ∏ k : Fin π.parts, farOnlyCoordinates (contractedTripleArray t H₁) (π.part k) := by
  classical
  obtain ⟨k, hk, _⟩ := π.unique_contracted_leaf_child t hJ
  have hspan : ((IntervalComposition.expandComposition t π).part k).left ≤ t.spanInterval.left ∧
      t.spanInterval.right ≤ ((IntervalComposition.expandComposition t π).part k).right :=
    (t.expandInterval_contains (π.part k)).mpr hk
  have hd := (IntervalComposition.expandComposition t π).child_product_difference t.spanInterval
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂)
    (fun K hK => farOnlyCoordinates_unchanged_off_critical H₁ H₂ t hH K hK) k hspan
  change (∏ l : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part l))) -
    (∏ l : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part l))) =
    (farOnlyCoordinates H₂ (t.expandInterval (π.part k)) -
      farOnlyCoordinates H₁ (t.expandInterval (π.part k))) *
      ∏ l ∈ Finset.univ.erase k, farOnlyCoordinates H₁ (t.expandInterval (π.part l)) at hd
  have hp : (∏ l ∈ Finset.univ.erase k, farOnlyCoordinates H₁ (t.expandInterval (π.part l))) =
      ∏ l ∈ Finset.univ.erase k, farOnlyCoordinates (contractedTripleArray t H₁) (π.part l) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact farOnlyCoordinates_expanded_off_leaf t H₁ (π.part l)
      (π.other_part_excludes t.contractedLeaf k hk l (Finset.mem_erase.mp hl).1)
  rw [hchild k hk.1 hk.2, hp] at hd
  rw [hd]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun l => farOnlyCoordinates (contractedTripleArray t H₁) (π.part l)) (Finset.mem_univ k)]
  ring

/-- An original composition whose cut list does not survive has no child
containing the whole critical interval, so its entire child product agrees
on the two sides. This justifies discarding its difference, not its value. -/
theorem nonsurviving_child_product_unchanged (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hπ : ¬ IntervalComposition.SurvivingCuts t π) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k)) =
      ∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k) := by
  apply π.child_product_unchanged t.spanInterval
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂)
    (fun K hK => farOnlyCoordinates_unchanged_off_critical H₁ H₂ t hH K hK)
  intro k hk
  exact hπ (π.survivingCuts_of_containing_child t k hk)

end
end SM

namespace OffLeafContractionIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

theorem excluded_leaf_iff_wholly_on_one_side (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    (¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) ↔
      J.right ≤ t.contractedLeaf.left ∨ t.contractedLeaf.right ≤ J.left := by
  constructor
  · exact t.contractedInterval_side J
  · rintro (h | h) hc
    · exact (not_le_of_gt t.contractedLeaf.increasing) (hc.2.trans h)
    · exact (not_le_of_gt t.contractedLeaf.increasing) (h.trans hc.1)

theorem every_original_raw_composition_roundtrips (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (π : IntervalComposition (t.expandInterval J)) :
    IntervalComposition.expandComposition t
      ((IntervalComposition.offLeafCompositionEquiv t J hj).symm π) = π :=
  (IntervalComposition.offLeafCompositionEquiv t J hj).apply_symm_apply π

theorem every_raw_part_and_child_preserved (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition J) :
    (IntervalComposition.expandComposition t π).parts = π.parts ∧
      ∀ k : Fin π.parts, (IntervalComposition.expandComposition t π).part k = t.expandInterval (π.part k) :=
  ⟨rfl, fun _ => rfl⟩

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem complete_raw_sum_with_arbitrary_zero_or_nonzero_weights (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (W : IntervalComposition (t.expandInterval J) → R) :
    (∑ π : IntervalComposition J, W (IntervalComposition.expandComposition t π)) =
      ∑ π : IntervalComposition (t.expandInterval J), W π :=
  Fintype.sum_equiv (IntervalComposition.offLeafCompositionEquiv t J hj) _ _ (fun _ => rfl)

theorem inverse_transport_allows_touching_left_endpoint (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : J.right ≤ t.contractedLeaf.left) :
    farOnlyCoordinates H (t.expandInterval J) = farOnlyCoordinates (contractedTripleArray t H) J := by
  apply farOnlyCoordinates_expanded_off_leaf t H J
  intro h
  exact (not_le_of_gt t.contractedLeaf.increasing) (h.2.trans hj)

theorem inverse_transport_allows_touching_right_endpoint (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : t.contractedLeaf.right ≤ J.left) :
    farOnlyCoordinates H (t.expandInterval J) = farOnlyCoordinates (contractedTripleArray t H) J := by
  apply farOnlyCoordinates_expanded_off_leaf t H J
  intro h
  exact (not_le_of_gt t.contractedLeaf.increasing) (hj.trans h.1)

theorem all_actual_child_inverse_values_transport (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (π : IntervalComposition J) (k : Fin π.parts) :
    farOnlyCoordinates H ((IntervalComposition.expandComposition t π).part k) =
      farOnlyCoordinates (contractedTripleArray t H) (π.part k) :=
  farOnlyCoordinates_expanded_off_leaf t H (π.part k)
    (t.subinterval_off_leaf J (π.part k) hj (π.part_bounds k))

theorem off_leaf_one_leaf_values_stay_one (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right))
    (hleaf : J.leaves = 1) :
    farOnlyCoordinates H (t.expandInterval J) = 1 ∧
      farOnlyCoordinates (contractedTripleArray t H) J = 1 :=
  ⟨farOnlyCoordinates_leaf H _ ((t.expandInterval_leaves_off_leaf J hj).trans hleaf),
    farOnlyCoordinates_leaf _ J hleaf⟩

theorem full_reversed_transform_transports (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (X : IntervalArray n R) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    farTransform (-(contractedTripleArray t H)) (fun I => X (t.expandInterval I)) J =
      farTransform (-H) X (t.expandInterval J) := by
  have h := nearFarTransform_expanded_off_leaf t 0 (-H) X J hj
  exact h

theorem two_side_arrays_have_identical_entire_contracted_inverse (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (h : ∀ u, u ≠ t → H₁ u = H₂ u) :
    farOnlyCoordinates (contractedTripleArray t H₁) = farOnlyCoordinates (contractedTripleArray t H₂) := by
  rw [contractedTripleArray_eq_off_critical t H₁ H₂ h]

theorem arbitrary_critical_entry_is_deleted_from_contracted_array (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (v : R) :
    contractedTripleArray t (Function.update H t v) = contractedTripleArray t H := by
  apply contractedTripleArray_eq_off_critical t
  intro u hu
  exact Function.update_of_ne hu v H

theorem actual_geometric_inverse_transport_off_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (J : BoundaryInterval t.contractedSize)
    (hj : ¬ (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)) :
    farOnlyCoordinates (geometricBoundaryArray (R := R) P g) (t.expandInterval J) =
      farOnlyCoordinates (geometricBoundaryArray (contractedWordTuple P g t) 0) J := by
  rw [geometricBoundaryArray_contractedWord]
  exact farOnlyCoordinates_expanded_off_leaf t _ J hj

theorem full_contraction_uses_formal_leaf_inverse (t : IncreasingBoundaryTriple n)
    (H : TripleArray n R) (hn : 3 ≤ n) (hfull : t.spanInterval = fullBoundaryInterval hn) :
    t.contractedSize = 2 ∧ farOnlyCoordinates (contractedTripleArray t H) t.contractedLeaf = 1 :=
  ⟨(t.contractedSize_eq_two_iff hn).mpr hfull, contracted_leaf_inverse_value t H⟩

theorem actual_proper_output_retains_the_physical_root (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {t.vertexSet g}) (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    farOnlyOutput (contractedTripleArray t (geometricBoundaryArray (R := R) P g))
      (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) =
      (treeCoefficient (contractedWordTuple P g t) (contractedWord_G1 P g t hz) 0
        (t.contractedSize_of_proper hn hproper) : R) ∧
    edge (contractedWordTuple P g t) 0 = edge P g :=
  ⟨contracted_output_tree P g t hn hz hproper, contractedWord_physical_root P g t⟩

theorem actual_contracted_geometry_commutes_with_reversal (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    -(geometricBoundaryArray (R := R) (contractedWordTuple P g t) 0) =
      contractedTripleArray t (-geometricBoundaryArray P g) := by
  rw [geometricBoundaryArray_contractedWord, contractedTripleArray_neg]

theorem every_nonunary_expanded_child_is_strictly_shorter (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition J)
    (hπ : 2 ≤ π.parts) (k : Fin π.parts) :
    (t.expandInterval (π.part k)).leaves < (t.expandInterval J).leaves :=
  (IntervalComposition.expandComposition t π).part_leaves_lt hπ k

theorem unary_composition_still_has_one_distinguished_child (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hj : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    ∃! k : Fin (IntervalComposition.single J).parts,
      ((IntervalComposition.single J).part k).left ≤ t.contractedLeaf.left ∧
        t.contractedLeaf.right ≤ ((IntervalComposition.single J).part k).right :=
  (IntervalComposition.single J).unique_contracted_leaf_child t hj

theorem zero_contracted_factor_annuls_conditional_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition J)
    (hj : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) (s : R)
    (hchild : ∀ k : Fin π.parts,
      (π.part k).left ≤ t.contractedLeaf.left → t.contractedLeaf.right ≤ (π.part k).right →
      farOnlyCoordinates H₂ (t.expandInterval (π.part k)) - farOnlyCoordinates H₁ (t.expandInterval (π.part k)) =
        s * farOnlyCoordinates (contractedTripleArray t H₁) (π.part k))
    (l : Fin π.parts) (hz : farOnlyCoordinates (contractedTripleArray t H₁) (π.part l) = 0) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part k))) -
      (∏ k : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part k))) = 0 := by
  rw [expanded_child_product_response t H₁ H₂ hH π hj s hchild]
  have hp : (∏ k : Fin π.parts, farOnlyCoordinates (contractedTripleArray t H₁) (π.part k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ l) hz
  rw [hp, mul_zero]

theorem nonsurviving_lists_have_zero_difference_not_zero_value (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (I : BoundaryInterval n) (π : IntervalComposition I) (hπ : ¬ IntervalComposition.SurvivingCuts t π) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
      (∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k)) = 0 :=
  sub_eq_zero.mpr (nonsurviving_child_product_unchanged t H₁ H₂ hH π hπ).symm

end
end OffLeafContractionIndependentReview

#check SM.IncreasingBoundaryTriple.contractedInterval_side
#print axioms SM.IncreasingBoundaryTriple.contractedInterval_side
#check SM.IncreasingBoundaryTriple.expandInterval_leaves_off_leaf
#print axioms SM.IncreasingBoundaryTriple.expandInterval_leaves_off_leaf
#check SM.IncreasingBoundaryTriple.subinterval_off_leaf
#print axioms SM.IncreasingBoundaryTriple.subinterval_off_leaf
#check SM.IntervalComposition.every_cut_survives_off_leaf
#print axioms SM.IntervalComposition.every_cut_survives_off_leaf
#check SM.IntervalComposition.offLeafCompositionEquiv
#print axioms SM.IntervalComposition.offLeafCompositionEquiv
#check SM.contractedTripleArray
#print axioms SM.contractedTripleArray
#check SM.IntervalComposition.expandComposition_weight
#print axioms SM.IntervalComposition.expandComposition_weight
#check SM.nearFarTransform_expanded_off_leaf
#print axioms SM.nearFarTransform_expanded_off_leaf
#check SM.boundaryUnitArray_expanded_off_leaf
#print axioms SM.boundaryUnitArray_expanded_off_leaf
#check SM.farOnlyCoordinates_expanded_off_leaf
#print axioms SM.farOnlyCoordinates_expanded_off_leaf
#check SM.IncreasingBoundaryTriple.expandTriple_ne_critical
#print axioms SM.IncreasingBoundaryTriple.expandTriple_ne_critical
#check SM.contractedTripleArray_eq_off_critical
#print axioms SM.contractedTripleArray_eq_off_critical
#check SM.contractedTripleArray_neg
#print axioms SM.contractedTripleArray_neg
#check SM.geometricBoundaryArray_contractedWord
#print axioms SM.geometricBoundaryArray_contractedWord
#check SM.contracted_leaf_inverse_value
#print axioms SM.contracted_leaf_inverse_value
#check SM.contracted_output_tree
#print axioms SM.contracted_output_tree
#check SM.IntervalComposition.unique_contracted_leaf_child
#print axioms SM.IntervalComposition.unique_contracted_leaf_child
#check SM.expanded_child_product_response
#print axioms SM.expanded_child_product_response
#check SM.nonsurviving_child_product_unchanged
#print axioms SM.nonsurviving_child_product_unchanged
#print SM.IncreasingBoundaryTriple.erasedInteriorCount
#print SM.IncreasingBoundaryTriple.contractedSize
#print SM.IncreasingBoundaryTriple.expandPosition
#print SM.IncreasingBoundaryTriple.contractPosition
#print SM.IncreasingBoundaryTriple.expandInterval
#print SM.IncreasingBoundaryTriple.expandTriple
#print SM.IncreasingBoundaryTriple.contractedLeaf
#print SM.IntervalComposition.expandComposition
#print SM.IntervalComposition.contractComposition
#print SM.IntervalComposition.SurvivingCuts
#print SM.IntervalComposition.offLeafCompositionEquiv
#print SM.IntervalComposition
#print SM.IntervalComposition.part
#print SM.IntervalComposition.nearFarWeight
#print SM.nearFarTransform
#print SM.triangularTransform
#print SM.farOnlyCoordinates
#print SM.farOnlyOutput
#print SM.boundaryUnitArray
#print SM.contractedTripleArray
#print SM.contractedVertexIndex
#print SM.contractedWordTuple
#print SM.geometricBoundaryArray
#check SM.IntervalComposition.part_leaves_lt
#check SM.IntervalComposition.part_bounds
#check SM.IntervalComposition.expandComposition_part
#check SM.IntervalComposition.expandComposition_nearTriple
#check SM.IntervalComposition.expandComposition_farTriple
#check SM.IncreasingBoundaryTriple.expandInterval_contains
#check SM.IncreasingBoundaryTriple.expandPosition_strict
#check SM.IntervalComposition.containingCompositionEquiv
#check SM.IntervalComposition.child_product_difference
#check SM.IntervalComposition.other_part_excludes
#check SM.nearFarTransform_eq_triangular
#check SM.farOnlyCoordinates_equation
#check SM.contractedWord_G1
#check SM.contractedWord_physical_root
#check SM.IncreasingBoundaryTriple.contractedSize_of_proper
#print axioms OffLeafContractionIndependentReview.excluded_leaf_iff_wholly_on_one_side
#print axioms OffLeafContractionIndependentReview.every_original_raw_composition_roundtrips
#print axioms OffLeafContractionIndependentReview.every_raw_part_and_child_preserved
#print axioms OffLeafContractionIndependentReview.complete_raw_sum_with_arbitrary_zero_or_nonzero_weights
#print axioms OffLeafContractionIndependentReview.inverse_transport_allows_touching_left_endpoint
#print axioms OffLeafContractionIndependentReview.inverse_transport_allows_touching_right_endpoint
#print axioms OffLeafContractionIndependentReview.all_actual_child_inverse_values_transport
#print axioms OffLeafContractionIndependentReview.off_leaf_one_leaf_values_stay_one
#print axioms OffLeafContractionIndependentReview.full_reversed_transform_transports
#print axioms OffLeafContractionIndependentReview.two_side_arrays_have_identical_entire_contracted_inverse
#print axioms OffLeafContractionIndependentReview.arbitrary_critical_entry_is_deleted_from_contracted_array
#print axioms OffLeafContractionIndependentReview.actual_geometric_inverse_transport_off_leaf
#print axioms OffLeafContractionIndependentReview.full_contraction_uses_formal_leaf_inverse
#print axioms OffLeafContractionIndependentReview.actual_proper_output_retains_the_physical_root
#print axioms OffLeafContractionIndependentReview.actual_contracted_geometry_commutes_with_reversal
#print axioms OffLeafContractionIndependentReview.every_nonunary_expanded_child_is_strictly_shorter
#print axioms OffLeafContractionIndependentReview.unary_composition_still_has_one_distinguished_child
#print axioms OffLeafContractionIndependentReview.zero_contracted_factor_annuls_conditional_response
#print axioms OffLeafContractionIndependentReview.nonsurviving_lists_have_zero_difference_not_zero_value
