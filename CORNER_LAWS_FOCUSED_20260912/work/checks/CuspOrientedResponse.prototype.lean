import SM.CuspDefinition
import SM.GermTurnSigns
import SM.NamedWallPredicates
import SM.FusionIndices
import SM.DeletionG1
import SM.UnorderedWallTriples
import SM.RestrictedWordRoot
import SM.GermTurnSigns
import SM.EuclideanPlane
import Mathlib.Data.Sign.Basic
import SM.GermNeighborhood
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


namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The raw expansion preserves the exact nonunary part-count condition. -/
def expandNonunaryComposition (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize}
    (π : {π : IntervalComposition J // 2 ≤ π.parts}) :
    {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts} :=
  ⟨expandComposition t π.val, π.property⟩

theorem expandNonunaryComposition_injective (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    Function.Injective (expandNonunaryComposition t (J := J)) := by
  intro π ρ he
  have hc : expandComposition t π.val = expandComposition t ρ.val :=
    congrArg (fun q : {q : IntervalComposition (t.expandInterval J) // 2 ≤ q.parts} => q.val) he
  apply Subtype.ext
  exact (survivingCompositionEquiv t J).injective (Subtype.ext hc)

/-- Its range is all surviving original nonunary compositions, with no
extra geometric, root, or weight condition. -/
theorem mem_range_expandNonunary (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}) :
    π ∈ Set.range (expandNonunaryComposition t (J := J)) ↔ SurvivingCuts t π.val := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact expandComposition_survives t ρ.val
  · intro hπ
    refine ⟨⟨contractComposition t π.val hπ, π.property⟩, ?_⟩
    exact Subtype.ext (expand_contractComposition t π.val hπ)

variable {R : Type*} [AddCommMonoid R]

/-- Reindex the entire nonunary response sum when nonsurviving terms have
zero response. The premise concerns the summand's difference, not the value
of either side's original composition term. -/
theorem sum_nonunary_expansion (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (f : IntervalComposition (t.expandInterval J) → R)
    (hzero : ∀ π : IntervalComposition (t.expandInterval J),
      2 ≤ π.parts → ¬ SurvivingCuts t π → f π = 0) :
    (∑ π : {π : IntervalComposition J // 2 ≤ π.parts}, f (expandComposition t π.val)) =
      ∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}, f π.val := by
  apply Fintype.sum_of_injective (expandNonunaryComposition t)
    (expandNonunaryComposition_injective t J)
  · intro π hπ
    exact hzero π.val π.property (fun h => hπ ((mem_range_expandNonunary t J π).mpr h))
  · intro π
    rfl

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Propagate the actual critical inverse-coordinate difference through
every containing interval. The source difference is defined by the actual
inverse arrays; neither its geometric value nor a propagation law is assumed. -/
theorem farOnlyCoordinates_contraction_propagation (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    farOnlyCoordinates H₂ (t.expandInterval J) - farOnlyCoordinates H₁ (t.expandInterval J) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyCoordinates (contractedTripleArray t H₁) J := by
  classical
  by_cases hleaf : J = t.contractedLeaf
  · subst J
    rw [t.expandInterval_contractedLeaf, farOnlyCoordinates_leaf _ _ t.contractedLeaf_leaves, mul_one]
  · let s := farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval
    let Hq := contractedTripleArray t H₁
    have hI : t.expandInterval J ≠ t.spanInterval := by
      intro he
      exact hleaf (t.expandInterval_injective (he.trans t.expandInterval_contractedLeaf.symm))
    have hJ2 : 2 ≤ J.leaves := t.containing_contracted_nonleaf J hJ hleaf
    have hI2 : 2 ≤ (t.expandInterval J).leaves := by
      have hc := (t.expandInterval_contains J).mpr hJ
      have hl : (t.expandInterval J).left.val ≤ t.lower.val := hc.1
      have hr : t.upper.val ≤ (t.expandInterval J).right.val := hc.2
      have hxy : t.lower.val < t.middle.val := t.lower_middle
      have hyz : t.middle.val < t.upper.val := t.middle_upper
      change 2 ≤ (t.expandInterval J).right.val - (t.expandInterval J).left.val
      omega
    let f (π : IntervalComposition (t.expandInterval J)) :=
      π.nearFarWeight 0 H₁ *
        ((∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
          ∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k))
    have hfzero (π : IntervalComposition (t.expandInterval J)) (_hp : 2 ≤ π.parts)
        (hπ : ¬ IntervalComposition.SurvivingCuts t π) : f π = 0 := by
      have hp := nonsurviving_child_product_unchanged t H₁ H₂ hH π hπ
      simp only [f, hp, sub_self, mul_zero]
    have hreindex := IntervalComposition.sum_nonunary_expansion t J f hfzero
    have hsum :
        (∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts},
          π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₂ (π.val.part k)) -
        (∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts},
          π.val.nearFarWeight 0 H₁ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k)) =
        s * ∑ π : {π : IntervalComposition J // 2 ≤ π.parts},
          π.val.nearFarWeight 0 Hq * ∏ k : Fin π.val.parts, farOnlyCoordinates Hq (π.val.part k) := by
      rw [← Finset.sum_sub_distrib]
      have hd :
          (∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts},
            ((π.val.nearFarWeight 0 H₂ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₂ (π.val.part k)) -
            (π.val.nearFarWeight 0 H₁ * ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (π.val.part k)))) =
          ∑ π : {π : IntervalComposition (t.expandInterval J) // 2 ≤ π.parts}, f π.val := by
        apply Finset.sum_congr rfl
        intro π _
        rw [← π.val.farWeight_unchanged_off_span t H₁ H₂ hH hI]
        dsimp only [f]
        ring
      rw [hd, ← hreindex, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _
      have hp := expanded_child_product_response t H₁ H₂ hH π.val hJ s
        (fun k hkl hkr => farOnlyCoordinates_contraction_propagation t H₁ H₂ hH
          (π.val.part k) ⟨hkl, hkr⟩)
      change (IntervalComposition.expandComposition t π.val).nearFarWeight 0 H₁ *
        ((∏ k : Fin π.val.parts, farOnlyCoordinates H₂ (t.expandInterval (π.val.part k))) -
          ∏ k : Fin π.val.parts, farOnlyCoordinates H₁ (t.expandInterval (π.val.part k))) = _
      rw [hp]
      change π.val.nearFarWeight 0 Hq *
        (s * ∏ k : Fin π.val.parts, farOnlyCoordinates Hq (π.val.part k)) = _
      ring
    have he₁ := farOnly_nonleaf_E H₁ (t.expandInterval J) hI2
    have he₂ := farOnly_nonleaf_E H₂ (t.expandInterval J) hI2
    have heq := farOnly_nonleaf_E Hq J hJ2
    unfold farTransform at he₁ he₂ heq
    rw [nearFarTransform_eq_triangular] at he₁ he₂ heq
    unfold triangularTransform at he₁ he₂ heq
    change farOnlyCoordinates H₂ (t.expandInterval J) - farOnlyCoordinates H₁ (t.expandInterval J) =
      s * farOnlyCoordinates Hq J
    linear_combination he₂ - he₁ - hsum - s * heq
termination_by (t.expandInterval J).leaves
decreasing_by
  exact (IntervalComposition.expandComposition t π.val).part_leaves_lt π.property k

end
end SM

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The expansion of complete raw compositions is injective, including unary ones. -/
theorem expandComposition_injective (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    Function.Injective (expandComposition t (J := J)) := by
  intro π ρ he
  exact (survivingCompositionEquiv t J).injective (Subtype.ext he)

theorem mem_range_expandComposition (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) (π : IntervalComposition (t.expandInterval J)) :
    π ∈ Set.range (expandComposition t (J := J)) ↔ SurvivingCuts t π := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact expandComposition_survives t ρ
  · intro hπ
    exact ⟨contractComposition t π hπ, expand_contractComposition t π hπ⟩

variable {R : Type*} [AddCommMonoid R]

/-- Reindex the entire response sum. Only zero responses outside the surviving
range are discarded; unary and all original zero-weight terms remain included. -/
theorem sum_composition_expansion (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (f : IntervalComposition (t.expandInterval J) → R)
    (hzero : ∀ π, ¬ SurvivingCuts t π → f π = 0) :
    (∑ π : IntervalComposition J, f (expandComposition t π)) =
      ∑ π : IntervalComposition (t.expandInterval J), f π := by
  apply Fintype.sum_of_injective (expandComposition t)
    (expandComposition_injective t J)
  · intro π hπ
    exact hzero π (fun h => hπ ((mem_range_expandComposition t J π).mpr h))
  · intro π
    rfl

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The propagation formula covers every original containing interval through
the actual contraction of its retained endpoints. -/
theorem farOnlyCoordinates_response_containing (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (I : BoundaryInterval n) (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    farOnlyCoordinates H₂ I - farOnlyCoordinates H₁ I =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyCoordinates (contractedTripleArray t H₁)
          (t.contractInterval I (Or.inl hI.1) (Or.inr hI.2)) := by
  let J := t.contractInterval I (Or.inl hI.1) (Or.inr hI.2)
  have he : t.expandInterval J = I := t.expand_contractInterval I _ _
  have hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right :=
    (t.expandInterval_contains J).mp (by simpa only [he] using hI)
  simpa only [he] using farOnlyCoordinates_contraction_propagation t H₁ H₂ hH J hJ

/-- Apply the completed inverse propagation to a complete far transform with
independent coefficient arrays. The parent must properly contain the critical
span so its coefficient formula is unchanged. No response premise is assumed. -/
theorem farTransform_contraction_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ K₁ K₂ : TripleArray n R)
    (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (hK : ∀ u, u ≠ t → K₁ u = K₂ u)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) :
    farTransform K₂ (farOnlyCoordinates H₂) (t.expandInterval J) -
      farTransform K₁ (farOnlyCoordinates H₁) (t.expandInterval J) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farTransform (contractedTripleArray t K₁)
          (farOnlyCoordinates (contractedTripleArray t H₁)) J := by
  classical
  let s := farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval
  have hI : t.expandInterval J ≠ t.spanInterval := by
    intro he
    exact hne (t.expandInterval_injective (he.trans t.expandInterval_contractedLeaf.symm))
  let f (π : IntervalComposition (t.expandInterval J)) :=
    π.nearFarWeight 0 K₁ *
      ((∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
        ∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k))
  have hfzero (π : IntervalComposition (t.expandInterval J))
      (hπ : ¬ IntervalComposition.SurvivingCuts t π) : f π = 0 := by
    have hp := nonsurviving_child_product_unchanged t H₁ H₂ hH π hπ
    simp only [f, hp, sub_self, mul_zero]
  have hreindex := IntervalComposition.sum_composition_expansion t J f hfzero
  unfold farTransform nearFarTransform
  rw [← Finset.sum_sub_distrib]
  have hd :
      (∑ π : IntervalComposition (t.expandInterval J),
        ((π.nearFarWeight 0 K₂ * ∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k)) -
          (π.nearFarWeight 0 K₁ * ∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k)))) =
      ∑ π : IntervalComposition (t.expandInterval J), f π := by
    apply Finset.sum_congr rfl
    intro π _
    rw [← π.farWeight_unchanged_off_span t K₁ K₂ hK hI]
    dsimp only [f]
    ring
  rw [hd, ← hreindex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hp := expanded_child_product_response t H₁ H₂ hH π hJ s
    (fun k hkl hkr => farOnlyCoordinates_contraction_propagation t H₁ H₂ hH
      (π.part k) ⟨hkl, hkr⟩)
  change (IntervalComposition.expandComposition t π).nearFarWeight 0 K₁ *
    ((∏ k : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part k))) -
      ∏ k : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part k))) = _
  rw [hp]
  change π.nearFarWeight 0 (contractedTripleArray t K₁) *
    (s * ∏ k : Fin π.parts, farOnlyCoordinates (contractedTripleArray t H₁) (π.part k)) = _
  ring

/-- Reversing the far coefficients gives the barred output response on every
properly containing interval, with the same source jump and complete output. -/
theorem farOnlyOutput_contraction_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) :
    farOnlyOutput H₂ (t.expandInterval J) - farOnlyOutput H₁ (t.expandInterval J) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyOutput (contractedTripleArray t H₁) J := by
  exact farTransform_contraction_response t H₁ H₂ (-H₁) (-H₂) hH
    (fun u hu => congrArg Neg.neg (hH u hu)) J hJ hne

/-- Proper contraction gives the full-output factorization on the exact full
boundary intervals. The arity of the contracted polygon is proved from properness. -/
theorem farOnlyOutput_full_contraction (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    (hn : 3 ≤ n) (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    farOnlyOutput H₂ (fullBoundaryInterval hn) - farOnlyOutput H₁ (fullBoundaryInterval hn) =
      (farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval) *
        farOnlyOutput (contractedTripleArray t H₁)
          (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) := by
  let J := fullBoundaryInterval (t.contractedSize_of_proper hn hproper)
  have he : t.expandInterval J = fullBoundaryInterval hn := t.expandInterval_full hn hproper
  have hc : (fullBoundaryInterval hn).left ≤ t.lower ∧ t.upper ≤ (fullBoundaryInterval hn).right := by
    constructor
    · change 0 ≤ t.lower.val
      omega
    · change t.upper.val ≤ n - 1
      have := t.upper.isLt
      omega
  have hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right :=
    (t.expandInterval_contains J).mp (by simpa only [he] using hc)
  have hne : J ≠ t.contractedLeaf := by
    intro hj
    have hi : t.expandInterval J = t.spanInterval := hj ▸ t.expandInterval_contractedLeaf
    exact hproper (hi.symm.trans he)
  simpa only [he] using farOnlyOutput_contraction_response t H₁ H₂ hH J hJ hne

end
end SM

namespace SM

noncomputable section

/-- The far sign on three actual points, in the source's reversed order. -/
def pointFarSign (a r c : Plane) : SignType :=
  SignType.sign (det (r - c) (a - c))

/-- A nonzero scalar has an involutive sign, so rescaling a determinant
can be inverted at the level of signs even when that determinant is0. -/
theorem sign_rescale_nonzero (s a : ℝ) (hs : s ≠ 0) :
    SignType.sign a = SignType.sign s * SignType.sign (s * a) := by
  have hh : SignType.sign s * SignType.sign s = 1 :=
    mul_inv_cancel₀ (sign_ne_zero.mpr hs)
  rw [sign_mul, ← mul_assoc, hh, one_mul]

def wallLeftEpsilon (x y z : ℝ) : SignType := SignType.sign ((y - x) / (z - x))

def wallRightEpsilon (x y z : ℝ) : SignType := SignType.sign ((z - y) / (z - x))

/-- The printed distinct scalar coordinates make both epsilon ratios nonzero. -/
theorem wall_epsilons_nonzero (x y z : ℝ) (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    wallLeftEpsilon x y z ≠ 0 ∧ wallRightEpsilon x y z ≠ 0 := by
  exact ⟨sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hyx) (sub_ne_zero.mpr hzx)),
    sign_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx))⟩

theorem wall_epsilons_one_or_neg_one (x y z : ℝ)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    (wallLeftEpsilon x y z = 1 ∨ wallLeftEpsilon x y z = -1) ∧
      (wallRightEpsilon x y z = 1 ∨ wallRightEpsilon x y z = -1) := by
  have hn := wall_epsilons_nonzero x y z hyx hzy hzx
  constructor
  · rcases SignType.trichotomy (wallLeftEpsilon x y z) with h | h | h
    · exact Or.inr h
    · exact (hn.1 h).elim
    · exact Or.inl h
  · rcases SignType.trichotomy (wallRightEpsilon x y z) with h | h | h
    · exact Or.inr h
    · exact (hn.2 h).elim
    · exact Or.inl h

/-- The two actual ratios sum to1, so at least one epsilon is positive.
This does not assume where the middle labelled point lies on the line. -/
theorem wall_epsilon_positive (x y z : ℝ) (hzx : z ≠ x) :
    wallLeftEpsilon x y z = 1 ∨ wallRightEpsilon x y z = 1 := by
  have he : (y - x) / (z - x) + (z - y) / (z - x) = 1 := by
    rw [← add_div]
    have ha : y - x + (z - y) = z - x := by ring
    rw [ha, div_self (sub_ne_zero.mpr hzx)]
  by_cases hl : 0 < (y - x) / (z - x)
  · exact Or.inl (sign_eq_one_iff.mpr hl)
  · have hr : 0 < (z - y) / (z - x) := by linarith [le_of_not_gt hl]
    exact Or.inr (sign_eq_one_iff.mpr hr)

theorem affine_line_difference (p ω : Plane) (x y : ℝ) :
    (p + y • ω) - (p + x • ω) = (y - x) • ω := by
  ext <;> dsimp <;> ring

/-- The left-gap far-sign identity uses the actual common first endpoint. -/
theorem collinear_left_gate_sign (a b c r : Plane) (s : ℝ) (hs : s ≠ 0)
    (h : b - a = s • (c - a)) :
    pointFarSign a r c = SignType.sign s * pointFarSign a r b := by
  unfold pointFarSign
  rw [area_cyclic a c r, area_cyclic a b r, h]
  have hd : det (s • (c - a)) (r - a) = s * det (c - a) (r - a) := by
    dsimp [det]
    ring
  rw [hd]
  exact sign_rescale_nonzero s _ hs

/-- The right-gap far-sign identity uses the actual common last endpoint. -/
theorem collinear_right_gate_sign (a b c r : Plane) (s : ℝ) (hs : s ≠ 0)
    (h : b - c = s • (a - c)) :
    pointFarSign a r c = SignType.sign s * pointFarSign b r c := by
  unfold pointFarSign
  rw [h]
  have hd : det (r - c) (s • (a - c)) = s * det (r - c) (a - c) := by
    dsimp [det]
    ring
  rw [hd]
  exact sign_rescale_nonzero s _ hs

/-- Substitute the source's affine coordinates and its actual left ratio. -/
theorem affine_collinear_left_gate (p ω r : Plane) (x y z : ℝ)
    (hyx : y ≠ x) (hzx : z ≠ x) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      wallLeftEpsilon x y z * pointFarSign (p + x • ω) r (p + y • ω) := by
  apply collinear_left_gate_sign _ _ _ _ ((y - x) / (z - x))
    (div_ne_zero (sub_ne_zero.mpr hyx) (sub_ne_zero.mpr hzx))
  rw [affine_line_difference, affine_line_difference, smul_smul,
    div_mul_cancel₀ _ (sub_ne_zero.mpr hzx)]

/-- The right ratio has the printed orientation; both differences reverse
together when expressed using vectors based at the last endpoint. -/
theorem affine_collinear_right_gate (p ω r : Plane) (x y z : ℝ)
    (hzy : z ≠ y) (hzx : z ≠ x) :
    pointFarSign (p + x • ω) r (p + z • ω) =
      wallRightEpsilon x y z * pointFarSign (p + y • ω) r (p + z • ω) := by
  apply collinear_right_gate_sign _ _ _ _ ((z - y) / (z - x))
    (div_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx))
  rw [affine_line_difference, affine_line_difference, smul_smul]
  have he : ((z - y) / (z - x)) * (x - z) = y - z := by
    field_simp [sub_ne_zero.mpr hzx]
    ring
  rw [he]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- The actual geometric far-array entry is the reversed-order point sign,
cast through the source integer sign into the allowed coefficient ring. -/
theorem geometricBoundaryArray_pointFarSign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := R) P g t =
      ((pointFarSign (boundaryWord P g t.lower) (boundaryWord P g t.middle)
        (boundaryWord P g t.upper) : ℤ) : R) := rfl

/-- The source left-gap identity at actual boundary positions and actual
geometric array entries. The intermediate vertex may be anywhere in the gap. -/
theorem boundary_collinear_left_sign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzx : z ≠ x) (r : Fin n)
    (hl : t.lower < r) (hr : r < t.middle) :
    geometricBoundaryArray (R := R) P g
        ⟨t.lower, r, t.upper, hl, lt_trans hr t.middle_upper⟩ =
      (((wallLeftEpsilon x y z : ℤ) : R)) *
        geometricBoundaryArray P g ⟨t.lower, r, t.middle, hl, hr⟩ := by
  have hs := affine_collinear_left_gate p ω (boundaryWord P g r) x y z hyx hzx
  rw [← hx, ← hy, ← hz] at hs
  have hc := congrArg (fun s : SignType => ((s : ℤ) : R)) hs
  simpa only [geometricBoundaryArray_pointFarSign, SignType.coe_mul, Int.cast_mul] using hc

/-- The source right-gap identity retains the original physical last
endpoint and the printed orientation of epsilon_R. -/
theorem boundary_collinear_right_sign (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hzy : z ≠ y) (hzx : z ≠ x) (r : Fin n)
    (hl : t.middle < r) (hr : r < t.upper) :
    geometricBoundaryArray (R := R) P g
        ⟨t.lower, r, t.upper, lt_trans t.lower_middle hl, hr⟩ =
      (((wallRightEpsilon x y z : ℤ) : R)) *
        geometricBoundaryArray P g ⟨t.middle, r, t.upper, hl, hr⟩ := by
  have hs := affine_collinear_right_gate p ω (boundaryWord P g r) x y z hzy hzx
  rw [← hx, ← hy, ← hz] at hs
  have hc := congrArg (fun s : SignType => ((s : ℤ) : R)) hs
  simpa only [geometricBoundaryArray_pointFarSign, SignType.coe_mul, Int.cast_mul] using hc

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The full reversed-far output on J depends only on the far array inside
J. All coefficient factors and every actual child inverse value are compared
in the complete composition sum, including the unary case. -/
theorem farOnlyOutput_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ u : IncreasingBoundaryTriple n, J.left ≤ u.lower → u.upper ≤ J.right → H₁ u = H₂ u) :
    farOnlyOutput H₁ J = farOnlyOutput H₂ J := by
  unfold farOnlyOutput farTransform nearFarTransform
  apply Finset.sum_congr rfl
  intro π _
  have hw : π.nearFarWeight 0 (-H₁) = π.nearFarWeight 0 (-H₂) := by
    unfold IntervalComposition.nearFarWeight
    apply Finset.prod_congr rfl
    intro k _
    simp only [Pi.zero_apply, Pi.neg_apply]
    rw [h (π.farTriple k) le_rfl le_rfl]
  rw [hw]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  apply farOnlyCoordinates_local (π.part k) H₁ H₂
  intro u hl hr
  exact h u (le_trans (π.part_bounds k).1 hl) (le_trans hr (π.part_bounds k).2)

/-- Changing a single far entry leaves every full output coordinate whose
interval excludes the complete critical span unchanged. -/
theorem farOnlyOutput_unchanged_off_critical (H₁ H₂ : TripleArray n R)
    (t : IncreasingBoundaryTriple n) (h : ∀ u, u ≠ t → H₁ u = H₂ u)
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    farOnlyOutput H₁ J = farOnlyOutput H₂ J := by
  apply farOnlyOutput_local J H₁ H₂
  intro u hl hr
  apply h u
  intro he
  subst u
  exact hJ ⟨hl, hr⟩

end
end SM

namespace SM

open Filter Topology

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- A single neighborhood preserves every noncritical geometric far entry
simultaneously. The proof uses actual finite chirotope stability and the exact
unordered-support/increasing-triple correspondence. -/
theorem geometric_array_persists_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g}) :
    ∀ᶠ Q in 𝓝 P, ∀ u : IncreasingBoundaryTriple n, u ≠ t →
      geometricBoundaryArray (R := R) Q g u = geometricBoundaryArray P g u := by
  filter_upwards [finite_nonzero_chi_persists (P := P)] with Q hQ
  intro u hu
  exact congrArg (fun s : SignType => ((s : ℤ) : R))
    (hQ (boundaryIndex g u.upper) (boundaryIndex g u.middle) (boundaryIndex g u.lower)
      (boundary_chi_nonzero_off_critical P g t hP u hu))

/-- All inverse coordinates outside the critical span retain their wall
values on one common neighborhood, not separate radii for separate intervals. -/
theorem geometric_inverse_persists_off_span (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g}) :
    ∀ᶠ Q in 𝓝 P, ∀ J : BoundaryInterval n,
      ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
      farOnlyCoordinates (geometricBoundaryArray (R := R) Q g) J =
        farOnlyCoordinates (geometricBoundaryArray P g) J := by
  filter_upwards [geometric_array_persists_off_critical (R := R) P g t hP] with Q hQ
  intro J hJ
  exact farOnlyCoordinates_unchanged_off_critical _ _ t hQ J hJ

/-- The complete B outputs on all excluded intervals also retain their
wall values on a common neighborhood, with one-leaf outputs included. -/
theorem geometric_output_persists_off_span (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g}) :
    ∀ᶠ Q in 𝓝 P, ∀ J : BoundaryInterval n,
      ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
      farOnlyOutput (geometricBoundaryArray (R := R) Q g) J =
        farOnlyOutput (geometricBoundaryArray P g) J := by
  filter_upwards [geometric_array_persists_off_critical (R := R) P g t hP] with Q hQ
  intro J hJ
  exact farOnlyOutput_unchanged_off_critical _ _ t hQ J hJ

end
end SM

namespace SM.WallGerm

open Filter Topology

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- One positive radius preserves all noncritical geometric far entries and
all inverse/output coordinates outside the critical span, on both sides of the
actual continuous germ. The center is included in this local assertion. -/
theorem boundary_values_stable_near_center (w : WallGerm n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g}) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧ ∀ s : w.Parameter, |s.val| < δ →
      (∀ u : IncreasingBoundaryTriple n, u ≠ t →
        geometricBoundaryArray (R := R) (w.curve s) g u =
          geometricBoundaryArray w.center g u) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyCoordinates (geometricBoundaryArray (R := R) (w.curve s) g) J =
          farOnlyCoordinates (geometricBoundaryArray w.center g) J) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyOutput (geometricBoundaryArray (R := R) (w.curve s) g) J =
          farOnlyOutput (geometricBoundaryArray w.center g) J) := by
  apply (w.eventually_center_iff_radius _).mp
  have h : ContinuousAt w.curve w.zeroParameter := w.continuous_curve.continuousAt
  filter_upwards [h.eventually (geometric_array_persists_off_critical (R := R) w.center g t hZ),
    h.eventually (geometric_inverse_persists_off_span (R := R) w.center g t hZ),
    h.eventually (geometric_output_persists_off_span (R := R) w.center g t hZ)] with s hA hC hB
  exact ⟨hA, hC, hB⟩

end
end SM.WallGerm

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The source U switches between the exact unit array E and full B output.
Its consumers require the actual wall epsilon to be either1 or-1. -/
def wallGapU (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then boundaryUnitArray I else farOnlyOutput H I

/-- The source V interchanges the same two complete interval values. -/
def wallGapV (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then farOnlyOutput H I else boundaryUnitArray I

/-- Every raw composition is retained. The actual signed far gates identify
the complete weighted sum with source U through the proved inverse equation. -/
theorem cutWeightedSum_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum f (farOnlyCoordinates H) I = wallGapU H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapU, if_pos rfl]
    calc
      cutWeightedSum f (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using h π k
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I
  · rw [wallGapU, if_neg (by decide)]
    change cutWeightedSum f (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using h π k

/-- Reversing every far gate interchanges E and B, including the unary gap
whose empty gate product remains1. -/
theorem cutWeightedSum_neg_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum (-f) (farOnlyCoordinates H) I = wallGapV H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapV, if_pos rfl]
    change cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using congrArg Neg.neg (h π k)
  · rw [wallGapV, if_neg (by decide)]
    calc
      cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using congrArg Neg.neg (h π k)
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Every interior cut of the actual left gap samples a noncritical triple
at each pair of endpoints. Thus nearby-array agreement transfers the wall sign
identity to its complete composition gate, even though the nearby points need
not themselves be collinear. -/
theorem boundary_left_gap_gate (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzx : z ≠ x)
    (π : IntervalComposition t.leftInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) =
      -((((wallLeftEpsilon x y z : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R) := by
  have hl : t.lower < π.interiorPosition k := (π.farTriple k).lower_middle
  have hr : π.interiorPosition k < t.middle := (π.farTriple k).middle_upper
  have hu : π.interiorPosition k < t.upper := lt_trans hr t.middle_upper
  have hwhole : (⟨t.lower, π.interiorPosition k, t.upper, hl, hu⟩ : IncreasingBoundaryTriple n) ≠ t := by
    intro he
    have hm := congrArg IncreasingBoundaryTriple.middle he
    exact (ne_of_lt hr) hm
  have hgap : π.farTriple k ≠ t := by
    intro he
    have hu := congrArg IncreasingBoundaryTriple.upper he
    exact (ne_of_lt t.middle_upper) hu
  have hs : H ⟨t.lower, π.interiorPosition k, t.upper, hl, hu⟩ =
      (((wallLeftEpsilon x y z : ℤ) : R)) * H (π.farTriple k) := by
    rw [hH _ hwhole, hH _ hgap]
    exact boundary_collinear_left_sign P g t p ω x y z hx hy hz hyx hzx
      (π.interiorPosition k) hl hr
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨hl, hu⟩, hs]

/-- The right-gap transfer retains the actual last endpoint and the source's
right epsilon orientation. The local triple differs from the critical triple
already at its first endpoint. -/
theorem boundary_right_gap_gate (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hzy : z ≠ y) (hzx : z ≠ x)
    (π : IntervalComposition t.rightInterval) (k : Fin (π.parts - 1)) :
    t.fixedFarGate H (π.interiorPosition k) =
      -((((wallRightEpsilon x y z : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R) := by
  have hl : t.middle < π.interiorPosition k := (π.farTriple k).lower_middle
  have hr : π.interiorPosition k < t.upper := (π.farTriple k).middle_upper
  have hd : t.lower < π.interiorPosition k := lt_trans t.lower_middle hl
  have hwhole : (⟨t.lower, π.interiorPosition k, t.upper, hd, hr⟩ : IncreasingBoundaryTriple n) ≠ t := by
    intro he
    have hm := congrArg IncreasingBoundaryTriple.middle he
    exact (ne_of_gt hl) hm
  have hgap : π.farTriple k ≠ t := by
    intro he
    have hd := congrArg IncreasingBoundaryTriple.lower he
    exact (ne_of_gt t.lower_middle) hd
  have hs : H ⟨t.lower, π.interiorPosition k, t.upper, hd, hr⟩ =
      (((wallRightEpsilon x y z : ℤ) : R)) * H (π.farTriple k) := by
    rw [hH _ hwhole, hH _ hgap]
    exact boundary_collinear_right_sign P g t p ω x y z hx hy hz hzy hzx
      (π.interiorPosition k) hl hr
  rw [IncreasingBoundaryTriple.fixedFarGate, dif_pos ⟨hd, hr⟩, hs]

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Geometric wall signs identify both complete gap sums and their reversed
counterparts with the source U/V values. Agreement is required only away from
the critical triple; the nearby array need not have a zero critical gate. -/
theorem geometric_gap_sums (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H : TripleArray n R)
    (hH : ∀ u, u ≠ t → H u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.leftInterval =
      wallGapU H t.leftInterval (wallLeftEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate H) (farOnlyCoordinates H) t.rightInterval =
      wallGapU H t.rightInterval (wallRightEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate (-H)) (farOnlyCoordinates H) t.leftInterval =
      wallGapV H t.leftInterval (wallLeftEpsilon x y z)) ∧
    (cutWeightedSum (t.fixedFarGate (-H)) (farOnlyCoordinates H) t.rightInterval =
      wallGapV H t.rightInterval (wallRightEpsilon x y z)) := by
  have hε := wall_epsilons_one_or_neg_one x y z hyx hzy hzx
  have hL := boundary_left_gap_gate P g t H hH p ω x y z hx hy hz hyx hzx
  have hR := boundary_right_gap_gate P g t H hH p ω x y z hx hy hz hzy hzx
  have hn : t.fixedFarGate (-H) = -t.fixedFarGate H :=
    funext (t.fixedFarGate_neg H)
  refine ⟨cutWeightedSum_signed_inverse _ H _ _ hε.1 hL,
    cutWeightedSum_signed_inverse _ H _ _ hε.2 hR, ?_, ?_⟩
  · rw [hn]
    exact cutWeightedSum_neg_signed_inverse _ H _ _ hε.1 hL
  · rw [hn]
    exact cutWeightedSum_neg_signed_inverse _ H _ _ hε.2 hR

/-- The derived critical inverse jump now uses the actual geometric U gap
values. This is a critical-span formula, not a propagation assumption. -/
theorem geometric_critical_inverse_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyCoordinates H₂ t.spanInterval - farOnlyCoordinates H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z)) := by
  have hs := geometric_gap_sums P g t H₁ h₁ p ω x y z hx hy hz hyx hzy hzx
  rw [critical_inverse_source_jump H₁ H₂ t (fun u hu => (h₁ u hu).trans (h₂ u hu).symm),
    hs.1, hs.2.1]

/-- Both ordinary and reversed geometric gap contributions occur in the
complete critical output response. No contracted output is used or presumed. -/
theorem geometric_critical_output_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyOutput H₂ t.spanInterval - farOnlyOutput H₁ t.spanInterval =
      ((H₂ t - H₁ t) * ⅟ (2 : R)) *
        ((wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z)) +
         (wallGapV H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapV H₁ t.rightInterval (wallRightEpsilon x y z))) := by
  have hs := geometric_gap_sums P g t H₁ h₁ p ω x y z hx hy hz hyx hzy hzx
  rw [critical_output_source_jump H₁ H₂ t (fun u hu => (h₁ u hu).trans (h₂ u hu).symm),
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]

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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Combine the derived source jump with complete proper-output contraction.
The factor on the contracted polygon is its actual rooted tree coefficient,
with G1 and its arity proved from the wall support and proper contraction. -/
theorem geometric_proper_output_response (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hZ : pointZeroTriples P = {t.vertexSet g})
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn)
    (H₁ H₂ : TripleArray n R)
    (h₁ : ∀ u, u ≠ t → H₁ u = geometricBoundaryArray P g u)
    (h₂ : ∀ u, u ≠ t → H₂ u = geometricBoundaryArray P g u)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord P g t.lower = p + x • ω)
    (hy : boundaryWord P g t.middle = p + y • ω)
    (hz : boundaryWord P g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    farOnlyOutput H₂ (fullBoundaryInterval hn) - farOnlyOutput H₁ (fullBoundaryInterval hn) =
      (((H₂ t - H₁ t) * ⅟ (2 : R)) *
        (wallGapU H₁ t.leftInterval (wallLeftEpsilon x y z) *
          wallGapU H₁ t.rightInterval (wallRightEpsilon x y z))) *
        (treeCoefficient (contractedWordTuple P g t) (contractedWord_G1 P g t hZ) 0
          (t.contractedSize_of_proper hn hproper) : R) := by
  have hH : ∀ u, u ≠ t → H₁ u = H₂ u := fun u hu => (h₁ u hu).trans (h₂ u hu).symm
  have hQ : contractedTripleArray t H₁ = contractedTripleArray t (geometricBoundaryArray P g) :=
    contractedTripleArray_eq_off_critical t H₁ (geometricBoundaryArray P g) h₁
  rw [farOnlyOutput_full_contraction t H₁ H₂ hH hn hproper,
    geometric_critical_inverse_response P g t H₁ H₂ h₁ h₂ p ω x y z hx hy hz hyx hzy hzx,
    hQ, contracted_output_tree P g t hn hZ hproper]

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The proper-span response for actual tree coefficients on both sufficiently
close punctured sides of the continuous germ. All gap and contracted data on
the right are at the wall center. Sign-change normalization is a separate step. -/
theorem proper_span_tree_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
          (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
          (((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
            geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R)) *
            (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) *
            (treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
              (t.contractedSize_of_proper hn hproper) : R) := by
  obtain ⟨δ, hδ, hrad, hs⟩ := w.boundary_values_stable_near_center (R := R) g t hZ
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hsMinus := hs sMinus hnearMinus
  have hsPlus := hs sPlus hnearPlus
  have hleft : ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  have hright : ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl
  have hL := hsMinus.2.2 t.leftInterval hleft
  have hR := hsMinus.2.2 t.rightInterval hright
  have hc := geometric_proper_output_response w.center g t hn hZ hproper
    (geometricBoundaryArray (R := R) (w.curve sMinus) g)
    (geometricBoundaryArray (w.curve sPlus) g) hsMinus.1 hsPlus.1
    p ω x y z hx hy hz hyx hzy hzx
  rw [treeCoefficient_farOnly (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn,
    treeCoefficient_farOnly (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn]
  simpa only [wallGapU, hL, hR] using hc

end
end SM.WallGerm

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual rooted tree coefficients satisfy the full-span response on
both sufficiently close punctured sides of the genuine continuous germ. All
four gap values are evaluated at the wall center. This establishes the displayed
full-span identity; the proper-span contraction branch is separate. -/
theorem full_span_tree_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hspan : t.spanInterval = fullBoundaryInterval hn)
    (p ω : Plane) (x y z : ℝ)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
          (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
          ((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
            geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R)) *
            ((wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
             (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
              wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z))) := by
  obtain ⟨δ, hδ, hrad, hs⟩ := w.boundary_values_stable_near_center (R := R) g t hZ
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hsMinus := hs sMinus hnearMinus
  have hsPlus := hs sPlus hnearPlus
  have hleft : ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  have hright : ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl
  have hL := hsMinus.2.2 t.leftInterval hleft
  have hR := hsMinus.2.2 t.rightInterval hright
  have hc := geometric_critical_output_response w.center g t
    (geometricBoundaryArray (R := R) (w.curve sMinus) g)
    (geometricBoundaryArray (w.curve sPlus) g) hsMinus.1 hsPlus.1
    p ω x y z hx hy hz hyx hzy hzx
  rw [hspan] at hc
  rw [treeCoefficient_farOnly (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn,
    treeCoefficient_farOnly (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn]
  simpa only [wallGapU, wallGapV, hL, hR] using hc

end
end SM.WallGerm

namespace SM

noncomputable section

/-- Actual distinct collinear points admit the affine coordinates used in the
wall theorem. The direction is the endpoint difference; no choice of a
collinearity oracle or additional dimension assumption is required. -/
theorem distinct_collinear_affine_data (a b c : Plane)
    (hba : b ≠ a) (hcb : c ≠ b) (hca : c ≠ a)
    (hd : det (b - a) (c - a) = 0) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ a = p + x • ω ∧ b = p + y • ω ∧ c = p + z • ω ∧
      y ≠ x ∧ z ≠ y ∧ z ≠ x := by
  have hω : c - a ≠ 0 := sub_ne_zero.mpr hca
  let q := planeDot (c - a) (b - a) / planeDot (c - a) (c - a)
  have hd' : det (c - a) (b - a) = 0 := by rw [det_swap, hd, neg_zero]
  have hs : b - a = q • (c - a) := scalar_of_det_zero hω hd'
  have hb : b = a + q • (c - a) := by
    calc
      b = a + (b - a) := by abel
      _ = a + q • (c - a) := by rw [hs]
  have hc : c = a + (1 : ℝ) • (c - a) := by simp
  have hq0 : q ≠ 0 := by
    intro hq
    exact hba (by simpa only [hq, zero_smul, add_zero] using hb)
  have h1q : (1 : ℝ) ≠ q := by
    intro hq
    exact hcb (hc.trans ((congrArg (fun r : ℝ => a + r • (c - a)) hq).trans hb.symm))
  exact ⟨a, c - a, 0, q, 1, hω, by simp, hb, hc, hq0, h1q, by norm_num⟩

variable {n : ℕ} [NeZero n]

/-- Apply the constructed affine coordinates to the actual critical boundary
points. Physical pairwise distinctness is explicit and is not inferred from
a singleton zero support, which would fail at arity three. -/
theorem critical_boundary_affine_data (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hba : boundaryWord P g t.middle ≠ boundaryWord P g t.lower)
    (hcb : boundaryWord P g t.upper ≠ boundaryWord P g t.middle)
    (hca : boundaryWord P g t.upper ≠ boundaryWord P g t.lower) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ boundaryWord P g t.lower = p + x • ω ∧
      boundaryWord P g t.middle = p + y • ω ∧
      boundaryWord P g t.upper = p + z • ω ∧ y ≠ x ∧ z ≠ y ∧ z ≠ x := by
  have hdata := singlePointTriple_data hZ
  have hχ : chi P (boundaryIndex g t.lower) (boundaryIndex g t.middle)
      (boundaryIndex g t.upper) = 0 := by
    apply hdata.2
    all_goals rw [t.vertexSet_reversed g]; simp
  have hd : det (boundaryWord P g t.middle - boundaryWord P g t.lower)
      (boundaryWord P g t.upper - boundaryWord P g t.lower) = 0 := sign_eq_zero_iff.mp hχ
  exact distinct_collinear_affine_data _ _ _ hba hcb hca hd

end
end SM

namespace SM

noncomputable section
variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The half-difference of opposite sign values equals the positive-side
sign after the exact integer-to-ring cast. No nontrivial-ring premise is needed. -/
theorem sign_half_difference (s t : SignType) (h : s = -t) :
    (((s : ℤ) : R) - ((t : ℤ) : R)) * ⅟ (2 : R) = ((s : ℤ) : R) := by
  have hi : (s : ℤ) - (t : ℤ) = 2 * (s : ℤ) := by
    subst s
    cases t <;> decide
  have hr : ((s : ℤ) : R) - ((t : ℤ) : R) = 2 * ((s : ℤ) : R) := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun z : ℤ => (z : R)) hi
  rw [hr, mul_right_comm, mul_invOf_self, one_mul]

end

namespace WallGerm

noncomputable section
variable {n : ℕ}

/-- Source sign change, together with connected generic sides, gives opposite
nonzero chirotopes at independent side parameters, not merely paired times. -/
theorem side_chi_signChanges_opposite (w : WallGerm n) (i j k : ZMod n)
    (h : w.SignChanges (fun P => (chi P i j k : ℝ))) (s t : w.SideParameter) :
    chi (w.sideTuple true s).val i j k = -chi (w.sideTuple false t).val i j k ∧
      chi (w.sideTuple true s).val i j k ≠ 0 := by
  obtain ⟨δ, hδ, hδr, hchange⟩ := h
  let t₀ : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have ht₀ : t₀.val < δ := by dsimp [t₀]; linarith
  have hc := (signType_cast_product_neg_iff _ _).mp (hchange t₀ ht₀)
  rw [generic_family_chi_constant (w.continuous_sideTuple true) s t₀ i j k,
    generic_family_chi_constant (w.continuous_sideTuple false) t t₀ i j k]
  exact hc

/-- The constant signed value is fixed at the positive-side base point; every
actual negative parameter has its opposite. All evaluations stay inside w. -/
theorem chi_signChanges_parameters (w : WallGerm n) (i j k : ZMod n)
    (h : w.SignChanges (fun P => (chi P i j k : ℝ)))
    (sMinus sPlus : w.Parameter) (hMinus : sMinus.val < 0) (hPlus : 0 < sPlus.val) :
    chi (w.curve sPlus) i j k = chi (w.sideTuple true w.sideBase).val i j k ∧
      chi (w.curve sMinus) i j k = -chi (w.sideTuple true w.sideBase).val i j k ∧
      chi (w.sideTuple true w.sideBase).val i j k ≠ 0 := by
  let s : w.SideParameter := ⟨sPlus.val, hPlus, sPlus.property.2⟩
  let t : w.SideParameter := ⟨-sMinus.val, neg_pos.mpr hMinus, by linarith [sMinus.property.1]⟩
  have hp : (w.sideTuple true s).val = w.curve sPlus := by
    apply congrArg w.curve
    apply Subtype.ext
    rfl
  have hm : (w.sideTuple false t).val = w.curve sMinus := by
    apply congrArg w.curve
    apply Subtype.ext
    change -(-sMinus.val) = sMinus.val
    exact neg_neg _
  have hb := generic_family_chi_constant (w.continuous_sideTuple true) s w.sideBase i j k
  have hc := w.side_chi_signChanges_opposite i j k h s t
  rw [hp] at hb
  rw [hp, hm, hb] at hc
  refine ⟨hb, ?_, hc.2⟩
  calc
    chi (w.curve sMinus) i j k = -(-chi (w.curve sMinus) i j k) := (neg_neg _).symm
    _ = -chi (w.sideTuple true w.sideBase).val i j k := congrArg Neg.neg hc.1.symm

variable [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The actual critical half-jump is one fixed integer sign on all independent
punctured side points. This proves the source normalization instead of assuming it. -/
theorem boundary_half_jump_signed (w : WallGerm n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n)
    (h : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ))) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧
      ∀ sMinus sPlus : w.Parameter, sMinus.val < 0 → 0 < sPlus.val →
        (geometricBoundaryArray (R := R) (w.curve sPlus) g t -
          geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R) = (d : R) := by
  let σ := chi (w.sideTuple true w.sideBase).val (boundaryIndex g t.upper)
    (boundaryIndex g t.middle) (boundaryIndex g t.lower)
  have hσ : σ ≠ 0 := (w.side_chi_signChanges_opposite _ _ _ h w.sideBase w.sideBase).2
  refine ⟨(σ : ℤ), ?_, ?_⟩
  · rcases signType_nonzero_cases hσ with hn | hp
    · left
      rw [hn]
      rfl
    · right
      rw [hp]
      rfl
  · intro sMinus sPlus hMinus hPlus
    have hs := w.chi_signChanges_parameters _ _ _ h sMinus sPlus hMinus hPlus
    have hop : chi (w.curve sPlus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) =
        -chi (w.curve sMinus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
          (boundaryIndex g t.lower) := by rw [hs.1, hs.2.1, neg_neg]
    change (((chi (w.curve sPlus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) : ℤ) : R) -
      ((chi (w.curve sMinus) (boundaryIndex g t.upper) (boundaryIndex g t.middle)
        (boundaryIndex g t.lower) : ℤ) : R)) * ⅟ (2 : R) = _
    rw [sign_half_difference _ _ hop, hs.1]

end
end WallGerm
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero
attribute [local instance] Classical.propDecidable

/-- Both single-triple response branches, with an actual fixed signed jump,
for every affine coordinate choice satisfying the printed source conditions.
The piecewise expression uses a closed contracted polygon only in the proper
branch; the full-span branch uses the separately proved barred source jump. -/
theorem single_triple_tree_response_of_affine (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hZc : concurrenceTriples w.center = ∅)
    (hchange : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)))
    (p ω : Plane) (x y z : ℝ) (hω : ω ≠ 0)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        ((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
          geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R) = (d : R)) ∧
        ((treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
          (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
          (d : R) *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) *
                (treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                  (t.contractedSize_of_proper hn hp) : R)
            else
              (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
              (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)))) := by
  obtain ⟨d, hd, hjump⟩ := w.boundary_half_jump_signed (R := R) g t hchange
  refine ⟨d, hd, ?_⟩
  by_cases hp : t.spanInterval ≠ fullBoundaryInterval hn
  · obtain ⟨δ, hδ, hrad, hresponse⟩ :=
      w.proper_span_tree_response (R := R) g hn t hZ hp p ω x y z hx hy hz hyx hzy hzx
    refine ⟨δ, hδ, hrad, ?_⟩
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    have hj := hjump sMinus sPlus hMinus hPlus
    have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    refine ⟨hj, ?_⟩
    rw [dif_pos hp]
    rw [hj] at hr
    simpa only [mul_assoc] using hr
  · have hfull : t.spanInterval = fullBoundaryInterval hn := not_ne_iff.mp hp
    obtain ⟨δ, hδ, hrad, hresponse⟩ :=
      w.full_span_tree_response (R := R) g hn t hZ hfull p ω x y z hx hy hz hyx hzy hzx
    refine ⟨δ, hδ, hrad, ?_⟩
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    have hj := hjump sMinus sPlus hMinus hPlus
    have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    refine ⟨hj, ?_⟩
    rw [dif_neg hp]
    rw [hj] at hr
    exact hr

/-- The printed physically distinct wall domain supplies the affine data as
well as the response, including arity three. The preceding theorem separately
establishes the response for every valid affine representation, not just this
constructed witness. No author-supplied coordinate choice remains necessary. -/
theorem single_triple_tree_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hZc : concurrenceTriples w.center = ∅)
    (hba : boundaryWord w.center g t.middle ≠ boundaryWord w.center g t.lower)
    (hcb : boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.middle)
    (hca : boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.lower)
    (hchange : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ))) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ boundaryWord w.center g t.lower = p + x • ω ∧
      boundaryWord w.center g t.middle = p + y • ω ∧
      boundaryWord w.center g t.upper = p + z • ω ∧ y ≠ x ∧ z ≠ y ∧ z ≠ x ∧
      (wallLeftEpsilon x y z = 1 ∨ wallLeftEpsilon x y z = -1) ∧
      (wallRightEpsilon x y z = 1 ∨ wallRightEpsilon x y z = -1) ∧
      (wallLeftEpsilon x y z = 1 ∨ wallRightEpsilon x y z = 1) ∧
      ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
        ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
          |sMinus.val| < δ → |sPlus.val| < δ →
          ((geometricBoundaryArray (R := R) (w.curve sPlus) g t -
            geometricBoundaryArray (w.curve sMinus) g t) * ⅟ (2 : R) = (d : R)) ∧
          ((treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn : R) -
            (treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn : R) =
            (d : R) *
              (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
                (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                  wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) *
                  (treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                    (t.contractedSize_of_proper hn hp) : R)
              else
                (wallGapU (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                  wallGapU (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)) +
                (wallGapV (geometricBoundaryArray w.center g) t.leftInterval (wallLeftEpsilon x y z) *
                  wallGapV (geometricBoundaryArray w.center g) t.rightInterval (wallRightEpsilon x y z)))) := by
  obtain ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx⟩ :=
    critical_boundary_affine_data w.center g t hZ hba hcb hca
  have hε := wall_epsilons_one_or_neg_one x y z hyx hzy hzx
  refine ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx,
    hε.1, hε.2, wall_epsilon_positive x y z hzx, ?_⟩
  exact w.single_triple_tree_response_of_affine (R := R) g hn t hZ hZc hchange
    p ω x y z hω hx hy hz hyx hzy hzx

end
end SM.WallGerm

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The label map for the already defined closed contiguous word, with
residue zero still labeling its actual last vertex. -/
def restrictedVertexIndex (g : ZMod n) (J : BoundaryInterval n)
    (j : ZMod (J.leaves + 1)) : ZMod n :=
  boundaryIndex g (J.globalPosition ⟨(j - 1).val, ZMod.val_lt _⟩)

theorem restrictedVertexIndex_injective (g : ZMod n) (J : BoundaryInterval n) :
    Function.Injective (restrictedVertexIndex g J) := by
  intro i j he
  have hp := J.globalPosition_strict.injective (boundaryIndex_injective g he)
  have hv := congrArg Fin.val hp
  have hz : i - 1 = j - 1 := ZMod.val_injective (J.leaves + 1) hv
  simpa only [sub_add_cancel] using congrArg (fun v : ZMod (J.leaves + 1) => v + 1) hz

/-- A closed contiguous word excluding the complete critical span has no
zero distinct-label triple. This proves its actual G1 condition directly from
the singleton zero-support hypothesis, without assuming global G1 at the wall. -/
theorem restrictedWord_G1_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    G1 (restrictedWordTuple P g J) := by
  intro i j k hij hjk hik
  change chi P (restrictedVertexIndex g J i) (restrictedVertexIndex g J j)
    (restrictedVertexIndex g J k) ≠ 0
  apply chi_nonzero_outside_singleton hZ
  · exact fun he => hij (restrictedVertexIndex_injective g J he)
  · exact fun he => hjk (restrictedVertexIndex_injective g J he)
  · exact fun he => hik (restrictedVertexIndex_injective g J he)
  · intro he
    have hb (a : Fin n) (v : ZMod (J.leaves + 1))
        (h : boundaryIndex g a = restrictedVertexIndex g J v) :
        J.left ≤ a ∧ a ≤ J.right := by
      have hp : a = J.globalPosition ⟨(v - 1).val, ZMod.val_lt _⟩ :=
        boundaryIndex_injective g h
      rw [hp]
      exact J.globalPosition_bounds _
    have hs (a : Fin n)
        (ha : boundaryIndex g a ∈ ({restrictedVertexIndex g J i,
          restrictedVertexIndex g J j, restrictedVertexIndex g J k} : Finset (ZMod n))) :
        J.left ≤ a ∧ a ≤ J.right := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with hi | hj | hk
      · exact hb a i hi
      · exact hb a j hj
      · exact hb a k hk
    have hl := hs t.lower (by
      rw [he]
      simp [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet])
    have hu := hs t.upper (by
      rw [he]
      simp [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet])
    exact hJ ⟨hl.1, hu.2⟩

/-- Both nonleaf closed gap polygons satisfy G1. The explicit leaf-count
premises retain the source distinction between polygon amplitudes and the
formal one-leaf convention. -/
theorem critical_closed_gaps_G1 (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g}) :
    (2 ≤ t.leftInterval.leaves → G1 (restrictedWordTuple P g t.leftInterval)) ∧
      (2 ≤ t.rightInterval.leaves → G1 (restrictedWordTuple P g t.rightInterval)) := by
  constructor
  · intro _
    apply restrictedWord_G1_off_critical P g t hZ
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  · intro _
    apply restrictedWord_G1_off_critical P g t hZ
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem IncreasingBoundaryTriple.leftInterval_excludes_span (t : IncreasingBoundaryTriple n) :
    ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
  rintro ⟨_, hr⟩
  exact (not_le_of_gt t.middle_upper) hr

theorem IncreasingBoundaryTriple.rightInterval_excludes_span (t : IncreasingBoundaryTriple n) :
    ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
  rintro ⟨hl, _⟩
  exact (not_le_of_gt t.lower_middle) hl

/-- The integer B value on a noncritical interval is one on a formal leaf and
otherwise the actual closed endpoint polygon's tree coefficient. The latter
has proved G1 and at least three vertices. No inverse over the integers is used. -/
def criticalIntervalIntegerOutput (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) : ℤ :=
  if hl : J.leaves = 1 then 1 else
    treeCoefficient (restrictedWordTuple P g J) (restrictedWord_G1_off_critical P g t hZ J hJ) 0
      (by have := J.leaves_pos; omega)

/-- Source U as an integer: the exact unit array or the proved integral B value. -/
def criticalGapUInteger (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) : ℤ :=
  if ε = 1 then boundaryUnitArray (R := ℤ) J else criticalIntervalIntegerOutput P g t hZ J hJ

/-- Source V interchanges the same two integer values. -/
def criticalGapVInteger (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) : ℤ :=
  if ε = 1 then criticalIntervalIntegerOutput P g t hZ J hJ else boundaryUnitArray (R := ℤ) J

theorem critical_integer_leaf_values (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right))
    (hl : J.leaves = 1) (ε : SignType) :
    criticalIntervalIntegerOutput P g t hZ J hJ = 1 ∧
      criticalGapUInteger P g t hZ J hJ ε = 1 ∧ criticalGapVInteger P g t hZ J hJ ε = 1 := by
  have hb : criticalIntervalIntegerOutput P g t hZ J hJ = 1 := by
    simp only [criticalIntervalIntegerOutput, dif_pos hl]
  have hr : J.right.val = J.left.val + 1 := by
    have hpos := J.increasing
    change J.left.val < J.right.val at hpos
    change J.right.val - J.left.val = 1 at hl
    omega
  have he : boundaryUnitArray (R := ℤ) J = 1 := by simp [boundaryUnitArray, hr]
  simp only [criticalGapUInteger, criticalGapVInteger, hb, he, ite_self, and_self]

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem boundaryUnitArray_intCast (J : BoundaryInterval n) :
    ((boundaryUnitArray (R := ℤ) J : ℤ) : R) = boundaryUnitArray (R := R) J := by
  by_cases h : J.right.val = J.left.val + 1 <;> simp [boundaryUnitArray, h]

/-- Only the complete B output is identified with an integer cast. The
constructed inverse coordinates themselves may have denominators. -/
theorem criticalIntervalIntegerOutput_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    (criticalIntervalIntegerOutput P g t hZ J hJ : R) =
      farOnlyOutput (geometricBoundaryArray P g) J := by
  by_cases hl : J.leaves = 1
  · rw [criticalIntervalIntegerOutput, dif_pos hl, Int.cast_one]
    exact (farOnly_leaf_values (geometricBoundaryArray P g) J hl).2.symm
  · rw [criticalIntervalIntegerOutput, dif_neg hl]
    have htwo : 2 ≤ J.leaves := by have := J.leaves_pos; omega
    exact (farOnlyOutput_restricted_tree P g J htwo
      (restrictedWord_G1_off_critical P g t hZ J hJ)).symm

theorem criticalGapUInteger_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    (criticalGapUInteger P g t hZ J hJ ε : R) = wallGapU (geometricBoundaryArray P g) J ε := by
  by_cases hε : ε = 1
  · simp only [criticalGapUInteger, wallGapU, if_pos hε]
    exact boundaryUnitArray_intCast J
  · simp only [criticalGapUInteger, wallGapU, if_neg hε]
    exact criticalIntervalIntegerOutput_cast P g t hZ J hJ

theorem criticalGapVInteger_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    (criticalGapVInteger P g t hZ J hJ ε : R) = wallGapV (geometricBoundaryArray P g) J ε := by
  by_cases hε : ε = 1
  · simp only [criticalGapVInteger, wallGapV, if_pos hε]
    exact criticalIntervalIntegerOutput_cast P g t hZ J hJ
  · simp only [criticalGapVInteger, wallGapV, if_neg hε]
    exact boundaryUnitArray_intCast J

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)

theorem geometricBoundaryArray_intCast {R : Type*} [CommRing R]
    (P : LabelledTuple n) (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    ((geometricBoundaryArray (R := ℤ) P g t : ℤ) : R) =
      geometricBoundaryArray (R := R) P g t := by
  simp only [geometricBoundaryArray, Int.cast_id]

/-- Recover the exact integer jump from its faithful rational half-jump.
Multiplication by two avoids imposing integer division conventions. -/
theorem integer_jump_of_rat_half (A B d : ℤ)
    (h : ((A : ℚ) - (B : ℚ)) * ⅟ (2 : ℚ) = (d : ℚ)) : A - B = 2 * d := by
  have he : (A : ℚ) - (B : ℚ) = 2 * (d : ℚ) := by
    rw [← h, mul_left_comm, mul_invOf_self, mul_one]
  exact_mod_cast he

namespace WallGerm
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero
attribute [local instance] Classical.propDecidable

/-- Integer single-triple response for every valid affine representation.
The rational response is specialized faithfully; only complete gap outputs,
never the inverse coordinates, are asserted to be integral. -/
theorem single_triple_integer_response_of_affine (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hZc : concurrenceTriples w.center = ∅)
    (hchange : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)))
    (p ω : Plane) (x y z : ℝ) (hω : ω ≠ 0)
    (hx : boundaryWord w.center g t.lower = p + x • ω)
    (hy : boundaryWord w.center g t.middle = p + y • ω)
    (hz : boundaryWord w.center g t.upper = p + z • ω)
    (hyx : y ≠ x) (hzy : z ≠ y) (hzx : z ≠ x) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (geometricBoundaryArray (R := ℤ) (w.curve sPlus) g t -
          geometricBoundaryArray (R := ℤ) (w.curve sMinus) g t = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) *
                treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                  (t.contractedSize_of_proper hn hp)
            else
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) +
              (criticalGapVInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapVInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)))) := by
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_tree_response_of_affine (R := ℚ) g hn t hZ hZc hchange
      p ω x y z hω hx hy hz hyx hzy hzx
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  refine ⟨?_, ?_⟩
  · apply integer_jump_of_rat_half
    simpa only [geometricBoundaryArray_intCast] using hr.1
  · apply Int.cast_injective (α := ℚ)
    by_cases hp : t.spanInterval ≠ fullBoundaryInterval hn
    · rw [dif_pos hp] at hr ⊢
      simpa only [Int.cast_sub, Int.cast_mul, criticalGapUInteger_cast] using hr.2
    · rw [dif_neg hp] at hr ⊢
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_add,
        criticalGapUInteger_cast, criticalGapVInteger_cast] using hr.2

end WallGerm
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

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero
attribute [local instance] Classical.propDecidable

/-- Construct the affine data and the complete integer response from the
physically distinct critical points, including arity three. -/
theorem single_triple_integer_response (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g})
    (hZc : concurrenceTriples w.center = ∅)
    (hba : boundaryWord w.center g t.middle ≠ boundaryWord w.center g t.lower)
    (hcb : boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.middle)
    (hca : boundaryWord w.center g t.upper ≠ boundaryWord w.center g t.lower)
    (hchange : w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ))) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ boundaryWord w.center g t.lower = p + x • ω ∧
      boundaryWord w.center g t.middle = p + y • ω ∧
      boundaryWord w.center g t.upper = p + z • ω ∧ y ≠ x ∧ z ≠ y ∧ z ≠ x ∧
      (wallLeftEpsilon x y z = 1 ∨ wallLeftEpsilon x y z = -1) ∧
      (wallRightEpsilon x y z = 1 ∨ wallRightEpsilon x y z = -1) ∧
      (wallLeftEpsilon x y z = 1 ∨ wallRightEpsilon x y z = 1) ∧
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (geometricBoundaryArray (R := ℤ) (w.curve sPlus) g t -
          geometricBoundaryArray (R := ℤ) (w.curve sMinus) g t = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) *
                treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZ) 0
                  (t.contractedSize_of_proper hn hp)
            else
              (criticalGapUInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) +
              (criticalGapVInteger w.center g t hZ t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapVInteger w.center g t hZ t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)))) := by
  obtain ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx⟩ :=
    critical_boundary_affine_data w.center g t hZ hba hcb hca
  have hε := wall_epsilons_one_or_neg_one x y z hyx hzy hzx
  refine ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx,
    hε.1, hε.2, wall_epsilon_positive x y z hzx, ?_⟩
  exact w.single_triple_integer_response_of_affine g hn t hZ hZc hchange
    p ω x y z hω hx hy hz hyx hzy hzx

/-- A supplied unordered support yields its unique boundary reading, affine
coordinates, signed normalization, and both integer wall equations. Every
conversion is constructed from the source premises; no ordering, coordinate
choice, or additional geometric genericity premise is required of the caller. -/
theorem single_triple_integer_response_of_support (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (K : Finset (ZMod n)) (hZ : pointZeroTriples w.center = {K})
    (hZc : concurrenceTriples w.center = ∅)
    (hsep : (K : Set (ZMod n)).Pairwise (fun i j => w.center i ≠ w.center j))
    (a b c : ZMod n) (habc : ({a, b, c} : Finset (ZMod n)) = K)
    (hchange : w.SignChanges (fun P => (chi P a b c : ℝ))) :
    ∃ t : IncreasingBoundaryTriple n, ∃ hZt : pointZeroTriples w.center = {t.vertexSet g},
      t.vertexSet g = K ∧ (∀ u : IncreasingBoundaryTriple n, u.vertexSet g = K → u = t) ∧
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ boundaryWord w.center g t.lower = p + x • ω ∧
      boundaryWord w.center g t.middle = p + y • ω ∧
      boundaryWord w.center g t.upper = p + z • ω ∧ y ≠ x ∧ z ≠ y ∧ z ≠ x ∧
      (wallLeftEpsilon x y z = 1 ∨ wallLeftEpsilon x y z = -1) ∧
      (wallRightEpsilon x y z = 1 ∨ wallRightEpsilon x y z = -1) ∧
      (wallLeftEpsilon x y z = 1 ∨ wallRightEpsilon x y z = 1) ∧
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (geometricBoundaryArray (R := ℤ) (w.curve sPlus) g t -
          geometricBoundaryArray (R := ℤ) (w.curve sMinus) g t = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d *
            (if hp : t.spanInterval ≠ fullBoundaryInterval hn then
              (criticalGapUInteger w.center g t hZt t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZt t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) *
                treeCoefficient (contractedWordTuple w.center g t) (contractedWord_G1 w.center g t hZt) 0
                  (t.contractedSize_of_proper hn hp)
            else
              (criticalGapUInteger w.center g t hZt t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapUInteger w.center g t hZt t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)) +
              (criticalGapVInteger w.center g t hZt t.leftInterval t.leftInterval_excludes_span
                  (wallLeftEpsilon x y z) *
                criticalGapVInteger w.center g t hZt t.rightInterval t.rightInterval_excludes_span
                  (wallRightEpsilon x y z)))) := by
  obtain ⟨t, ht, _⟩ := w.single_triple_boundary_data g K hZ hsep a b c habc hchange
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by rw [ht.1]; exact hZ
  refine ⟨t, hZt, ht.1, ?_, ?_⟩
  · intro u hu
    exact IncreasingBoundaryTriple.vertexSet_injective g (hu.trans ht.1.symm)
  · exact w.single_triple_integer_response g hn t hZt hZc
      ht.2.1.1 ht.2.1.2.1 ht.2.1.2.2 ht.2.2

end
end SM.WallGerm

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

namespace SM

noncomputable section

theorem flat_epsilons_nonincident (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 0 r 1 = 1 ∧ wallRightEpsilon 0 r 1 = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (1 - 0)
    simpa using hr0
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (1 - 0)
    simpa using sub_pos.mpr hr1

theorem flat_epsilons_incoming (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon r 1 0 = -1 ∧ wallRightEpsilon r 1 0 = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr
    change (1 - r) / (0 - r) < 0
    exact div_neg_of_pos_of_neg (by linarith) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (0 - r)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)

theorem flat_epsilons_outgoing (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 1 0 r = 1 ∧ wallRightEpsilon 1 0 r = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (r - 1)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
  · apply sign_eq_neg_one_iff.mpr
    change (r - 0) / (r - 1) < 0
    exact div_neg_of_pos_of_neg (by linarith) (by linarith)

/-- The printed strict betweenness supplies concrete affine coordinates.
The two other root orders use the same three equations in cyclic order. -/
theorem strictBetween_flat_affine (a x b : Plane) (h : StrictBetween a x b) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ b - a ≠ 0 ∧
      a = a + (0 : ℝ) • (b - a) ∧ x = a + r • (b - a) ∧
      b = a + (1 : ℝ) • (b - a) := by
  obtain ⟨hab, r, hr0, hr1, hx⟩ := h
  refine ⟨r, hr0, hr1, sub_ne_zero.mpr hab.symm, ?_, hx, ?_⟩
  · simp
  · simp

variable {n : ℕ} [NeZero n]

/-- These are exactly the three cyclic orders of the critical labels in the
root word. This predicate introduces no geometric or wall assumption. -/
def CyclicTurnBoundaryOrder (g j : ZMod n) (t : IncreasingBoundaryTriple n) : Prop :=
    (boundaryIndex g t.lower = j - 1 ∧ boundaryIndex g t.middle = j ∧
      boundaryIndex g t.upper = j + 1) ∨
    (boundaryIndex g t.lower = j ∧ boundaryIndex g t.middle = j + 1 ∧
      boundaryIndex g t.upper = j - 1) ∨
    (boundaryIndex g t.lower = j + 1 ∧ boundaryIndex g t.middle = j - 1 ∧
      boundaryIndex g t.upper = j)

/-- Reversing each of the three even cyclic orders negates the same turn. -/
theorem turn_far_cyclic_signs (P : LabelledTuple n) (j : ZMod n) :
    chi P (j + 1) j (j - 1) = -turn P j ∧
      chi P (j - 1) (j + 1) j = -turn P j ∧
      chi P j (j - 1) (j + 1) = -turn P j := by
  exact ⟨chi_swap_outer P (j - 1) j (j + 1),
    chi_swap_last P (j - 1) j (j + 1), chi_swap_first P (j - 1) j (j + 1)⟩

theorem flat_boundary_chi_eq_neg_turn (P : LabelledTuple n) (g j : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicTurnBoundaryOrder g j t) :
    chi P (boundaryIndex g t.upper) (boundaryIndex g t.middle) (boundaryIndex g t.lower) =
      -turn P j := by
  have hc := turn_far_cyclic_signs P j
  rcases h with h | h | h
  · simpa only [h.1, h.2.1, h.2.2] using hc.1
  · simpa only [h.1, h.2.1, h.2.2] using hc.2.1
  · simpa only [h.1, h.2.1, h.2.2] using hc.2.2

theorem flat_boundary_geometric_sign (P : LabelledTuple n) (g j : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicTurnBoundaryOrder g j t) :
    geometricBoundaryArray (R := ℤ) P g t = -(turn P j : ℤ) := by
  simp only [geometricBoundaryArray, flat_boundary_chi_eq_neg_turn P g j t h,
    Int.cast_id, SignType.coe_neg]

/-- The existing turn sign-change hypothesis gives precisely the reverse
boundary chi premise required by the integer single-triple response. -/
theorem WallGerm.flat_boundary_chi_signChanges (w : WallGerm n) (g j : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicTurnBoundaryOrder g j t)
    (hturn : w.SignChanges (fun P => (turn P j : ℝ))) :
    w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) := by
  have he : (fun P : LabelledTuple n => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) =
      (fun P => -(turn P j : ℝ)) := by
    funext P
    rw [flat_boundary_chi_eq_neg_turn P g j t h, SignType.coe_neg]
  rw [he, w.signChanges_neg]
  exact hturn

end
end SM

namespace SM

noncomputable section
variable {m : ℕ}

/-- The incoming nonleaf gap samples every retained vertex in order,
including the wrap at child index zero. -/
theorem incoming_flat_gap_labels (j : ZMod (m + 4)) (i : ZMod (m + 3)) :
    restrictedVertexIndex (j - 1) (incomingFlatTriple (n := m + 4) (by omega)).rightInterval i =
      deletionIndex j (i - 1) := by
  change (j - 1) + ((1 + (i - 1).val : ℕ) : ZMod (m + 4)) + 1 =
    ((i - 1).val : ZMod (m + 4)) + (j + 1)
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- The outgoing nonleaf gap has the same complete retained label word. -/
theorem outgoing_flat_gap_labels (j : ZMod (m + 4)) (i : ZMod (m + 3)) :
    restrictedVertexIndex j (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval i =
      deletionIndex j (i - 1) := by
  change j + ((0 + (i - 1).val : ℕ) : ZMod (m + 4)) + 1 =
    ((i - 1).val : ZMod (m + 4)) + (j + 1)
  rw [Nat.zero_add]
  ring

/-- Equality is pointwise on the entire closed tuple. The shift makes local
root zero the deleted polygon's closing root minus one. -/
theorem incoming_flat_gap_tuple (P : LabelledTuple (m + 4)) (j : ZMod (m + 4)) :
    restrictedWordTuple P (j - 1) (incomingFlatTriple (n := m + 4) (by omega)).rightInterval =
      shift (-1 : ZMod (m + 3)) (deleteVertex P j) := by
  funext i
  change P (restrictedVertexIndex (j - 1)
    (incomingFlatTriple (n := m + 4) (by omega)).rightInterval i) =
    P (deletionIndex j ((show ZMod (m + 3) from i) + (-1 : ZMod (m + 3))))
  erw [incoming_flat_gap_labels, sub_eq_add_neg]

theorem outgoing_flat_gap_tuple (P : LabelledTuple (m + 4)) (j : ZMod (m + 4)) :
    restrictedWordTuple P j (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval =
      shift (-1 : ZMod (m + 3)) (deleteVertex P j) := by
  funext i
  change P (restrictedVertexIndex j
    (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval i) =
    P (deletionIndex j ((show ZMod (m + 3) from i) + (-1 : ZMod (m + 3))))
  erw [outgoing_flat_gap_labels, sub_eq_add_neg]

/-- Transport an actual tree coefficient across tuple equality, including
its dependent G1 witness. Proof irrelevance identifies proofs after substitution. -/
theorem treeCoefficient_congr_tuple {k : ℕ} [NeZero k]
    (P Q : LabelledTuple k) (hP : G1 P) (hQ : G1 Q) (he : P = Q)
    (g : ZMod k) (hk : 3 ≤ k) : treeCoefficient P hP g hk = treeCoefficient Q hQ g hk := by
  subst Q
  rfl

/-- The incoming source B value is exactly the deletion coefficient at the
physical fused root. G1 follows from the sole turn support, not parent G1. -/
theorem incoming_flat_integer_gap (P : LabelledTuple (m + 4)) (j : ZMod (m + 4))
    (hz : pointZeroTriples P = {turnSupport j}) :
    criticalIntervalIntegerOutput P (j - 1) (incomingFlatTriple (n := m + 4) (by omega))
      (by simpa only [incomingFlatTriple_support] using hz)
      (incomingFlatTriple (n := m + 4) (by omega)).rightInterval
      (incomingFlatTriple (n := m + 4) (by omega)).rightInterval_excludes_span =
      treeCoefficient (deleteVertex P j) (g1_deleteVertex hz)
        (fusionIndex j (j - 1)) (by omega) := by
  have hleaf : (incomingFlatTriple (n := m + 4) (by omega)).rightInterval.leaves ≠ 1 := by
    change m + 2 ≠ 1
    omega
  rw [criticalIntervalIntegerOutput, dif_neg hleaf, fusionIndex_prev]
  change treeCoefficient (n := m + 3)
      (restrictedWordTuple P (j - 1) (incomingFlatTriple (n := m + 4) (by omega)).rightInterval) _ 0 _ =
    treeCoefficient (n := m + 3) (deleteVertex P j) (g1_deleteVertex hz) (-1) _
  calc
    _ = treeCoefficient (shift (-1) (deleteVertex P j))
        (g1_shift_forward (-1) (g1_deleteVertex hz)) 0 (by omega) :=
      treeCoefficient_congr_tuple (k := m + 3) _ _ _ _ (incoming_flat_gap_tuple P j) 0 (by omega)
    _ = _ := by
      simpa only [sub_self] using
        treeCoefficient_shift (deleteVertex P j) (g1_deleteVertex hz) (-1) (-1) (by omega)

/-- The outgoing source B value uses the same fused physical edge. -/
theorem outgoing_flat_integer_gap (P : LabelledTuple (m + 4)) (j : ZMod (m + 4))
    (hz : pointZeroTriples P = {turnSupport j}) :
    criticalIntervalIntegerOutput P j (outgoingFlatTriple (n := m + 4) (by omega))
      (by simpa only [outgoingFlatTriple_support] using hz)
      (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval
      (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval_excludes_span =
      treeCoefficient (deleteVertex P j) (g1_deleteVertex hz)
        (fusionIndex j j) (by omega) := by
  have hleaf : (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval.leaves ≠ 1 := by
    change m + 2 ≠ 1
    omega
  rw [criticalIntervalIntegerOutput, dif_neg hleaf, fusionIndex_deleted]
  change treeCoefficient (n := m + 3)
      (restrictedWordTuple P j (outgoingFlatTriple (n := m + 4) (by omega)).leftInterval) _ 0 _ =
    treeCoefficient (n := m + 3) (deleteVertex P j) (g1_deleteVertex hz) (-1) _
  calc
    _ = treeCoefficient (shift (-1) (deleteVertex P j))
        (g1_shift_forward (-1) (g1_deleteVertex hz)) 0 (by omega) :=
      treeCoefficient_congr_tuple (k := m + 3) _ _ _ _ (outgoing_flat_gap_tuple P j) 0 (by omega)
    _ = _ := by
      simpa only [sub_self] using
        treeCoefficient_shift (deleteVertex P j) (g1_deleteVertex hz) (-1) (-1) (by omega)

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryUnitArray_nonleaf_zero {R : Type*} [CommRing R]
    (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) : boundaryUnitArray (R := R) J = 0 := by
  have he : J.right.val ≠ J.left.val + 1 := by
    change 2 ≤ J.right.val - J.left.val at hJ
    omega
  simp only [boundaryUnitArray, if_neg he]

/-- Two singleton gaps give the proper-span unit multiplier for all signs. -/
theorem integer_wall_factor_two_leaves (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : t.rightInterval.leaves = 1) (εL εR : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 1 := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL εL
  have hr := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR εR
  rw [hl.2.1, hr.2.1, one_mul]

/-- At the incoming root, epsilon (-,+) annihilates the unbarred product;
the barred product is precisely the nonleaf right-gap B output. -/
theorem integer_wall_factor_left_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 =
      criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL (-1)
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    simp only [criticalGapUInteger, ite_true, he, mul_zero]
  · rw [hl.2.2]
    simp only [criticalGapVInteger, ite_true, one_mul]

/-- At the outgoing root epsilon (+,-) reverses the roles of the two gaps. -/
theorem integer_wall_factor_right_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) =
      criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) := by
  have hr := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR (-1)
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hr.2.1]
    simp only [criticalGapUInteger, ite_true, he, zero_mul]
  · rw [hr.2.2]
    simp only [criticalGapVInteger, ite_true, mul_one]

end
end SM

namespace SM.WallGerm

noncomputable section
variable {m : ℕ}
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Assemble the incoming incident response from actual affine, gap and
deletion-root identities. The sign is fixed before the independent side points. -/
theorem flat_incoming_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.FlatAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 (j - 1) (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 (j - 1) (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j (j - 1)) (by omega)) := by
  let t := incomingFlatTriple (n := m + 4) (by omega)
  have hlabels := incomingFlatTriple_labels (n := m + 4) (by omega) j
  have horder : CyclicTurnBoundaryOrder (j - 1) j t := Or.inr (Or.inl hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet (j - 1)} := by
    simpa only [t, incomingFlatTriple_support, pointZeros] using hf.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hM, hB⟩ := strictBetween_flat_affine
    (w.center (j - 1)) (w.center j) (w.center (j + 1)) hf.2.2.2.1
  have hchange := w.flat_boundary_chi_signChanges (j - 1) j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine (j - 1) (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) r 1 0 hω
      ((congrArg w.center hlabels.1).trans hM)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by linarith) (by norm_num) (by linarith)
  have hintervals := incomingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hε := flat_epsilons_incoming r hr0 hr1
  have hfactors := integer_wall_factor_left_leaf w.center (j - 1) t hZt
    hintervals.2.1 (by change 2 ≤ m + 2; omega)
  have hgap : criticalIntervalIntegerOutput w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j (j - 1)) (by omega) := incoming_flat_integer_gap w.center j hf.2.1
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hε.1, hε.2, hfactors.1, hfactors.2, zero_add, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ (j - 1) j t horder, sub_neg_eq_add] using hr.1

/-- Assemble the outgoing incident response from actual affine, gap and
deletion-root identities. The sign is fixed before the independent side points. -/
theorem flat_outgoing_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.FlatAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 j (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 j (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j j) (by omega)) := by
  let t := outgoingFlatTriple (n := m + 4) (by omega)
  have hlabels := outgoingFlatTriple_labels (n := m + 4) (by omega) j
  have horder : CyclicTurnBoundaryOrder j j t := Or.inr (Or.inr hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet j} := by
    simpa only [t, outgoingFlatTriple_support, pointZeros] using hf.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hM, hB⟩ := strictBetween_flat_affine
    (w.center (j - 1)) (w.center j) (w.center (j + 1)) hf.2.2.2.1
  have hchange := w.flat_boundary_chi_signChanges j j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine j (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 1 0 r hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hM)
      (by norm_num) (by linarith) (by linarith)
  have hintervals := outgoingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hε := flat_epsilons_outgoing r hr0 hr1
  have hfactors := integer_wall_factor_right_leaf w.center j t hZt
    (by change 2 ≤ m + 2; omega) hintervals.2.2
  have hgap : criticalIntervalIntegerOutput w.center j t hZt t.leftInterval t.leftInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j j) (by omega) := outgoing_flat_integer_gap w.center j hf.2.1
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hε.1, hε.2, hfactors.1, hfactors.2, zero_add, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ j j t horder, sub_neg_eq_add] using hr.1

/-- Both incident physical roots, with no assumption about which time side
is the source right side. That final turn-side normalization remains separate. -/
theorem flat_incident_signed_response (w : WallGerm (m + 4)) (j g : ZMod (m + 4))
    (hf : w.FlatAt j) (hg : incident j g) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by omega)) := by
  rcases hg with h | h
  · subst g
    exact w.flat_incoming_signed_response j hf
  · subst g
    exact w.flat_outgoing_signed_response j hf

end
end SM.WallGerm

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every permitted source size is covered: FlatAt proves n+1 >= 4,
so the child size is m+3 for a constructed natural m. No extra arity
restriction is imposed by the earlier normalized tuple calculation. -/
theorem flat_incident_signed_response_all_sizes (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) (hg : incident j g) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by have := hf.1; omega⟩
  exact w.flat_incident_signed_response j g hf hg

end
end SM.WallGerm


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

namespace SM

noncomputable section
variable {n q : ℕ} [NeZero n] [NeZero q]

/-- Reindexing by a proved equality of sizes preserves G1 by equality
induction. This assumes no invariance under an arbitrary permutation. -/
theorem g1_reindex_size (h : n = q) (P : LabelledTuple n) (hP : G1 P) :
    G1 (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i)) := by
  subst q
  cases n <;> exact hP

/-- The same equality induction transports the full coefficient and its
actual root. No cyclic covariance or root independence is assumed here. -/
theorem treeCoefficient_reindex_size (h : n = q) (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i))
      (g1_reindex_size h P hP) (ZMod.ringEquivCongr h g) (by omega) = treeCoefficient P hP g hn := by
  subst q
  cases n <;> rfl

/-- A proved pointwise tuple identity after size transport identifies the
two coefficients at root zero, including their dependent G1 witnesses. -/
theorem treeCoefficient_of_reindexed_tuple_eq (h : n = q)
    (P : LabelledTuple n) (Q : LabelledTuple q) (hP : G1 P) (hQ : G1 Q)
    (he : (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i)) = Q) (hn : 3 ≤ n) :
    treeCoefficient P hP 0 hn = treeCoefficient Q hQ 0 (by omega) := by
  subst q
  cases n
  all_goals
    have hpq : P = Q := he
    clear he
    subst Q
    rfl

end
end SM

namespace SM

noncomputable section
variable {q : ℕ} [NeZero q]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every surviving physical vertex, including local label zero, agrees
with deletion followed by the proved physical-root cyclic shift. -/
theorem nonincident_flat_contracted_labels (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g)
    (i : ZMod (consecutiveBoundaryTriple k h0 hLast).contractedSize) :
    contractedVertexIndex g (consecutiveBoundaryTriple k h0 hLast) i =
      deletionIndex j (ZMod.ringEquivCongr (consecutive_contracted_size k h0 hLast) i +
        fusionIndex j g) := by
  let t := consecutiveBoundaryTriple k h0 hLast
  let e := ZMod.ringEquivCongr (consecutive_contracted_size k h0 hLast)
  have hv : (i - 1).val = (e i - 1).val := by
    have hh := ZMod.ringEquivCongr_val (consecutive_contracted_size k h0 hLast) (i - 1)
    simpa only [map_sub, map_one] using hh.symm
  have hcut := zmod_cut_shift_val k.val (by omega : k.val < q) (e i) (fusionIndex j g)
    (nonincident_fusionIndex_cut_relation g j k h0 hLast hk hroot)
  have he : g + (k.val : ZMod (q + 1)) + 1 = j := hk
  have hq : (q : ZMod (q + 1)) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (q + 1)
  change g + ((t.expandPosition ⟨(i - 1).val, ZMod.val_lt _⟩).val : ZMod (q + 1)) + 1 =
    ((e i + fusionIndex j g).val : ZMod (q + 1)) + (j + 1)
  rw [IncreasingBoundaryTriple.expandPosition_val]
  change g + ((if (i - 1).val ≤ t.lower.val then (i - 1).val
      else (i - 1).val + t.erasedInteriorCount : ℕ) : ZMod (q + 1)) + 1 =
    ((e i + fusionIndex j g).val : ZMod (q + 1)) + (j + 1)
  have hlower : t.lower.val = k.val - 1 := rfl
  have herase : t.erasedInteriorCount = 1 := consecutive_erased_one k h0 hLast
  rw [hlower, herase, hv, hcut]
  by_cases hc : (e i - 1).val < k.val
  · rw [if_pos hc, if_pos (by omega : (e i - 1).val ≤ k.val - 1)]
    rw [Nat.cast_sub (by omega : k.val ≤ (e i - 1).val + q), Nat.cast_add]
    linear_combination he - hq
  · rw [if_neg hc, if_neg (by omega : ¬ (e i - 1).val ≤ k.val - 1)]
    rw [Nat.cast_sub (by omega : k.val ≤ (e i - 1).val), Nat.cast_add, Nat.cast_one]
    linear_combination he

/-- Equality of whole tuples after the explicit arity transport; this is
stronger than merely identifying the root endpoints. -/
theorem nonincident_flat_contracted_tuple (P : LabelledTuple (q + 1))
    (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g) :
    (fun u : ZMod q => contractedWordTuple P g (consecutiveBoundaryTriple k h0 hLast)
      ((ZMod.ringEquivCongr (consecutive_contracted_size k h0 hLast)).symm u)) =
        shift (fusionIndex j g) (deleteVertex P j) := by
  funext u
  unfold contractedWordTuple shift deleteVertex
  rw [nonincident_flat_contracted_labels g j k h0 hLast hk hroot]
  simp only [RingEquiv.apply_symm_apply, add_comm]

/-- The same consecutive triple is exactly the source's critical turn support. -/
theorem nonincident_flat_contracted_support (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1) (hk : boundaryIndex g k = j) :
    (consecutiveBoundaryTriple k h0 hLast).vertexSet g = turnSupport j := by
  have hl := consecutiveBoundaryTriple_labels g j k h0 hLast hk
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, turnSupport]

/-- Size transport, the proved full tuple identity, and cyclic covariance
identify the actual contracted coefficient at the exact fused root. -/
theorem nonincident_flat_contracted_coefficient (P : LabelledTuple (q + 1))
    (g j : ZMod (q + 1)) (k : Fin (q + 1))
    (h0 : 0 < k.val) (hLast : k.val + 1 < q + 1)
    (hk : boundaryIndex g k = j) (hroot : ¬ incident j g)
    (hz : pointZeroTriples P = {turnSupport j}) (hq : 3 ≤ q) :
    treeCoefficient (contractedWordTuple P g (consecutiveBoundaryTriple k h0 hLast))
      (contractedWord_G1 P g (consecutiveBoundaryTriple k h0 hLast)
        (by rw [nonincident_flat_contracted_support g j k h0 hLast hk]; exact hz))
      0 (by rw [consecutive_contracted_size]; exact hq) =
      treeCoefficient (deleteVertex P j) (g1_deleteVertex hz) (fusionIndex j g) hq := by
  have he := treeCoefficient_of_reindexed_tuple_eq (consecutive_contracted_size k h0 hLast)
    (contractedWordTuple P g (consecutiveBoundaryTriple k h0 hLast))
    (shift (fusionIndex j g) (deleteVertex P j))
    (contractedWord_G1 P g (consecutiveBoundaryTriple k h0 hLast)
      (by rw [nonincident_flat_contracted_support g j k h0 hLast hk]; exact hz))
    (g1_shift_forward (fusionIndex j g) (g1_deleteVertex hz))
    (nonincident_flat_contracted_tuple P g j k h0 hLast hk hroot)
    (by rw [consecutive_contracted_size]; exact hq)
  have hs := treeCoefficient_shift (deleteVertex P j) (g1_deleteVertex hz)
    (fusionIndex j g) (fusionIndex j g) hq
  rw [sub_self] at hs
  exact he.trans hs

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The nonincident flat response uses the actual center deletion and fused
physical root. Both singleton gaps and the proper span are proved from FlatAt. -/
theorem flat_nonincident_signed_response (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) (hg : ¬ incident j g) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  obtain ⟨k, hk⟩ := boundaryIndex_surjective g j
  have hb := boundaryIndex_nonincident_interior g j k hk hg
  let t := consecutiveBoundaryTriple k hb.1 hb.2
  have hlabels := consecutiveBoundaryTriple_labels g j k hb.1 hb.2 hk
  have horder : CyclicTurnBoundaryOrder g j t := Or.inl hlabels
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [nonincident_flat_contracted_support g j k hb.1 hb.2 hk]
    exact hf.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hM, hB⟩ := strictBetween_flat_affine
    (w.center (j - 1)) (w.center j) (w.center (j + 1)) hf.2.2.2.1
  have hchange := w.flat_boundary_chi_signChanges g j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g (by have := hf.1; omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 0 r 1 hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hM)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by linarith) (by linarith) (by norm_num)
  have hproper := consecutiveBoundaryTriple_proper hf.1 k hb.1 hb.2
  have hgaps := consecutiveBoundaryTriple_gaps k hb.1 hb.2
  have hfactors := integer_wall_factor_two_leaves w.center g t hZt hgaps.1 hgaps.2
    (wallLeftEpsilon 0 r 1) (wallRightEpsilon 0 r 1)
  have hcoeff := nonincident_flat_contracted_coefficient w.center g j k hb.1 hb.2 hk hg
    hf.2.1 (by have := hf.1; omega)
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_pos hproper, hfactors, one_mul, hcoeff] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ g j t horder, sub_neg_eq_add] using hr.1

end
end SM.WallGerm


namespace SM.WallGerm

noncomputable section
variable {n : ℕ}

/-- Actual punctured parameters with right/left turn signs occupy opposite
time sides. The proof uses the existing connected generic-side constancy,
not any convention identifying positive time with the source right side. -/
theorem turn_right_left_opposite_time_sides (w : WallGerm n) (j : ZMod n)
    (sRight sLeft : w.Parameter)
    (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hRight : turn (w.curve sRight) j = -1)
    (hLeft : turn (w.curve sLeft) j = 1) :
    (sLeft.val < 0 ∧ 0 < sRight.val) ∨
      (sRight.val < 0 ∧ 0 < sLeft.val) := by
  obtain ⟨b, r, hr⟩ := w.sideTime_surjective_punctured sRight hRight0
  obtain ⟨c, l, hl⟩ := w.sideTime_surjective_punctured sLeft hLeft0
  have hbc : b ≠ c := by
    intro heq
    subst c
    have he : turn (w.curve (w.sideTime b r)) j =
        turn (w.curve (w.sideTime b l)) j :=
      w.side_turn_constant b r l j
    rw [hr, hl, hRight, hLeft] at he
    norm_num at he
  cases b <;> cases c
  · exact (hbc rfl).elim
  · right
    constructor
    · rw [← hr]
      change -r.val < 0
      linarith [r.property.1]
    · rw [← hl]
      change 0 < l.val
      exact l.property.1
  · left
    constructor
    · rw [← hl]
      change -l.val < 0
      linarith [l.property.1]
    · rw [← hr]
      change 0 < r.val
      exact r.property.1
  · exact (hbc rfl).elim

/-- Orient a fixed signed integer response by the source's actual turn
convention: right has turn -1 and left has turn +1. The signed response
and the conclusion cover independent parameters in the same positive
radius. F is arbitrary; no chamber constancy of F is assumed. -/
theorem turn_response_right_minus_left (w : WallGerm n) (j : ZMod n)
    (F : w.Parameter → ℤ) (C d : ℤ) (δ : ℝ)
    (hd : d = -1 ∨ d = 1) (hδ : 0 < δ) (hδr : δ ≤ w.radius)
    (hresponse :
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
          (F sPlus - F sMinus = d * C))
    (sRight sLeft : w.Parameter)
    (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hRight : turn (w.curve sRight) j = -1)
    (hLeft : turn (w.curve sLeft) j = 1)
    (hRightNear : |sRight.val| < δ) (hLeftNear : |sLeft.val| < δ) :
    F sRight - F sLeft = C := by
  rcases w.turn_right_left_opposite_time_sides j sRight sLeft
      hRight0 hLeft0 hRight hLeft with ⟨hMinus, hPlus⟩ | ⟨hMinus, hPlus⟩
  · have h := hresponse sLeft sRight hMinus hPlus hLeftNear hRightNear
    have hj := h.1
    rw [hRight, hLeft] at hj
    have hdpos : d = 1 := by
      norm_num at hj
      omega
    simpa only [hdpos, one_mul] using h.2
  · have h := hresponse sRight sLeft hMinus hPlus hRightNear hLeftNear
    have hj := h.1
    rw [hLeft, hRight] at hj
    have hdneg : d = -1 := by
      norm_num at hj
      omega
    have hF : F sLeft - F sRight = -C := by
      simpa only [hdneg, neg_one_mul] using h.2
    omega

end
end SM.WallGerm

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Exhaust all physical roots using the two incident cases and the proved
nonincident contraction. No root condition remains as a hypothesis. -/
theorem flat_signed_response_all_roots (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  by_cases hg : incident j g
  · exact w.flat_incident_signed_response_all_sizes j g hf hg
  · exact w.flat_nonincident_signed_response j g hf hg

/-- Source right-minus-left orientation of the actual coefficient response,
for every root and independent nearby punctured parameters. -/
theorem flat_right_minus_left_near (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sRight sLeft : w.Parameter, ∀ hRight0 : sRight.val ≠ 0, ∀ hLeft0 : sLeft.val ≠ 0,
        turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
        |sRight.val| < δ → |sLeft.val| < δ →
        treeCoefficient (w.curve sRight) (w.generic_punctured sRight hRight0).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sLeft) (w.generic_punctured sLeft hLeft0).1 g
            (by have := hf.1; omega) =
          treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega) := by
  classical
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ := w.flat_signed_response_all_roots j g hf
  let F : w.Parameter → ℤ := fun s =>
    if hs : s.val ≠ 0 then
      treeCoefficient (w.curve s) (w.generic_punctured s hs).1 g (by have := hf.1; omega)
    else 0
  have hFresponse :
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
          (F sPlus - F sMinus = d *
            treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
              (fusionIndex j g) (by have := hf.1; omega)) := by
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    simpa only [F, dif_pos (ne_of_gt hPlus), dif_pos (ne_of_lt hMinus)] using
      hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sRight sLeft hRight0 hLeft0 hRight hLeft hRightNear hLeftNear
  have h := w.turn_response_right_minus_left j F
    (treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
      (fusionIndex j g) (by have := hf.1; omega)) d δ hd hδ hrad hFresponse
    sRight sLeft hRight0 hLeft0 hRight hLeft hRightNear hLeftNear
  simpa only [F, dif_pos hRight0, dif_pos hLeft0] using h

end
end SM.WallGerm



namespace SM.WallGerm

noncomputable section
variable {n : ℕ}

/-- Every actual punctured parameter has a representative arbitrarily close
to the center on the same connected generic side, with the entire chirotope
unchanged. The representative is explicitly constructed at distance δ/2. -/
theorem nearby_same_chirotope (w : WallGerm n) (δ : ℝ) (hδ : 0 < δ) (hδr : δ ≤ w.radius)
    (s : w.Parameter) (hs : s.val ≠ 0) :
    ∃ u : w.Parameter, u.val ≠ 0 ∧ |u.val| < δ ∧
      ∀ i j k : ZMod n, chi (w.curve u) i j k = chi (w.curve s) i j k := by
  obtain ⟨b, r, hr⟩ := w.sideTime_surjective_punctured s hs
  let t0 : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  refine ⟨w.sideTime b t0, w.sideTime_ne_zero b t0, ?_, ?_⟩
  · have hv : |(w.sideTime b t0).val| = δ / 2 := by
      cases b <;> simp [sideTime, t0, abs_of_pos (by linarith : 0 < δ / 2)]
    rw [hv]
    linarith
  · intro i j k
    have hc := generic_family_chi_constant (w.continuous_sideTuple b) t0 r i j k
    change chi (w.curve (w.sideTime b t0)) i j k = chi (w.curve (w.sideTime b r)) i j k at hc
    rw [hr] at hc
    exact hc

end
end SM.WallGerm

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The flat law for the actual rooted tree coefficient at every source
root and every pair of punctured right/left representatives in the germ.
Connected-side chirotope constancy removes the local radius restriction. -/
theorem flat_right_minus_left (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) (sRight sLeft : w.Parameter)
    (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hRight : turn (w.curve sRight) j = -1) (hLeft : turn (w.curve sLeft) j = 1) :
    treeCoefficient (w.curve sRight) (w.generic_punctured sRight hRight0).1 g
        (by have := hf.1; omega) -
      treeCoefficient (w.curve sLeft) (w.generic_punctured sLeft hLeft0).1 g
        (by have := hf.1; omega) =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j g) (by have := hf.1; omega) := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.flat_right_minus_left_near j g hf
  obtain ⟨r, hr0, hrNear, hrChi⟩ := w.nearby_same_chirotope δ hδ hδr sRight hRight0
  obtain ⟨l, hl0, hlNear, hlChi⟩ := w.nearby_same_chirotope δ hδ hδr sLeft hLeft0
  have hrTurn : turn (w.curve r) j = -1 := (hrChi (j - 1) j (j + 1)).trans hRight
  have hlTurn : turn (w.curve l) j = 1 := (hlChi (j - 1) j (j + 1)).trans hLeft
  have he := hresponse r l hr0 hl0 hrTurn hlTurn hrNear hlNear
  have hrCoeff := treeCoefficient_eq_of_chi (w.generic_punctured r hr0).1
    (w.generic_punctured sRight hRight0).1 hrChi g (by have := hf.1; omega)
  have hlCoeff := treeCoefficient_eq_of_chi (w.generic_punctured l hl0).1
    (w.generic_punctured sLeft hLeft0).1 hlChi g (by have := hf.1; omega)
  rw [hrCoeff, hlCoeff] at he
  exact he

end
end SM.WallGerm



namespace SM

noncomputable section

/-- Incoming root, cut order M,B,A, with the cusp point beyond B. -/
theorem cusp_epsilons_incoming_gt_one (r : ℝ) (hr : 1 < r) :
    wallLeftEpsilon r 1 0 = 1 ∧ wallRightEpsilon r 1 0 = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (0 - r)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (0 - r)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)

/-- Incoming root, cut order M,B,A, with the cusp point before A. -/
theorem cusp_epsilons_incoming_lt_zero (r : ℝ) (hr : r < 0) :
    wallLeftEpsilon r 1 0 = 1 ∧ wallRightEpsilon r 1 0 = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - r) / (0 - r)
    exact div_pos (by linarith) (by linarith)
  · apply sign_eq_neg_one_iff.mpr
    change (0 - 1) / (0 - r) < 0
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

/-- Outgoing root, cut order B,A,M, with the cusp point beyond B. -/
theorem cusp_epsilons_outgoing_gt_one (r : ℝ) (hr : 1 < r) :
    wallLeftEpsilon 1 0 r = -1 ∧ wallRightEpsilon 1 0 r = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr
    change (0 - 1) / (r - 1) < 0
    exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (r - 1)
    exact div_pos (by linarith) (by linarith)

/-- Outgoing root, cut order B,A,M, with the cusp point before A. -/
theorem cusp_epsilons_outgoing_lt_zero (r : ℝ) (hr : r < 0) :
    wallLeftEpsilon 1 0 r = 1 ∧ wallRightEpsilon 1 0 r = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - 1) / (r - 1)
    exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 0) / (r - 1)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)

variable {n : ℕ} [NeZero n]

/-- Construct the source line coordinates from the actual cusp predicate.
The direction is B-A and the scalar is obtained from the vanishing determinant.
The exterior clause excludes the entire closed parameter interval [0,1]. -/
theorem WallGerm.cusp_exterior_affine (w : WallGerm n) (j : ZMod n)
    (hc : w.CuspAt j) :
    ∃ r : ℝ, (r < 0 ∨ 1 < r) ∧
      w.center (j + 1) - w.center (j - 1) ≠ 0 ∧
      w.center (j - 1) = w.center (j - 1) +
        (0 : ℝ) • (w.center (j + 1) - w.center (j - 1)) ∧
      w.center j = w.center (j - 1) +
        r • (w.center (j + 1) - w.center (j - 1)) ∧
      w.center (j + 1) = w.center (j - 1) +
        (1 : ℝ) • (w.center (j + 1) - w.center (j - 1)) := by
  have hi := singlePointTriple_vertices_injective hc.1 hc.2.1
  have hAB : w.center (j - 1) ≠ w.center (j + 1) :=
    fun he => prev_ne_next (by have hn := hc.1; omega) j (hi he)
  have hω : w.center (j + 1) - w.center (j - 1) ≠ 0 :=
    sub_ne_zero.mpr hAB.symm
  have hz := singlePointTriple_turn_zero hc.2.1
  have hd : det (w.center j - w.center (j - 1))
      (w.center (j + 1) - w.center (j - 1)) = 0 := sign_eq_zero_iff.mp hz
  have hd' : det (w.center (j + 1) - w.center (j - 1))
      (w.center j - w.center (j - 1)) = 0 := by
    rw [det_swap, hd, neg_zero]
  let r := planeDot (w.center (j + 1) - w.center (j - 1))
      (w.center j - w.center (j - 1)) /
    planeDot (w.center (j + 1) - w.center (j - 1))
      (w.center (j + 1) - w.center (j - 1))
  have he : w.center j - w.center (j - 1) =
      r • (w.center (j + 1) - w.center (j - 1)) := scalar_of_det_zero hω hd'
  have hm : w.center j = w.center (j - 1) +
      r • (w.center (j + 1) - w.center (j - 1)) := by
    rw [← he]
    abel
  have hr : r < 0 ∨ 1 < r := by
    by_cases hr0 : r < 0
    · exact Or.inl hr0
    · right
      exact lt_of_not_ge (fun hr1 =>
        hc.2.2.2.1 ⟨r, le_of_not_gt hr0, hr1, hm⟩)
  refine ⟨r, hr, hω, ?_, hm, ?_⟩
  · simp
  · simp

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_neg (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_neg_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    simp [criticalGapUInteger, he, show (-1 : SignType) ≠ 1 by decide]
  · rw [hl.2.2]
    simp [criticalGapVInteger, he, show (-1 : SignType) ≠ 1 by decide]

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_nonincident_signed_response (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) (hg : ¬ incident j g) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  obtain ⟨k, hk⟩ := boundaryIndex_surjective g j
  have hb := boundaryIndex_nonincident_interior g j k hk hg
  let t := consecutiveBoundaryTriple k hb.1 hb.2
  have hlabels := consecutiveBoundaryTriple_labels g j k hb.1 hb.2 hk
  have horder : CyclicTurnBoundaryOrder g j t := Or.inl hlabels
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [nonincident_flat_contracted_support g j k hb.1 hb.2 hk]
    exact hf.2.1
  obtain ⟨r, hr, hω, hA, hM, hB⟩ := w.cusp_exterior_affine j hf
  have hchange := w.flat_boundary_chi_signChanges g j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g (by have := hf.1; omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 0 r 1 hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hM)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith) (by norm_num)
  have hproper := consecutiveBoundaryTriple_proper hf.1 k hb.1 hb.2
  have hgaps := consecutiveBoundaryTriple_gaps k hb.1 hb.2
  have hfactors := integer_wall_factor_two_leaves w.center g t hZt hgaps.1 hgaps.2
    (wallLeftEpsilon 0 r 1) (wallRightEpsilon 0 r 1)
  have hcoeff := nonincident_flat_contracted_coefficient w.center g j k hb.1 hb.2 hk hg
    hf.2.1 (by have := hf.1; omega)
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_pos hproper, hfactors, one_mul, hcoeff] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ g j t horder, sub_neg_eq_add] using hr.1


variable {m : ℕ}

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_incoming_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.CuspAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 (j - 1) (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 (j - 1) (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j (j - 1)) (by omega)) := by
  let t := incomingFlatTriple (n := m + 4) (by omega)
  have hlabels := incomingFlatTriple_labels (n := m + 4) (by omega) j
  have horder : CyclicTurnBoundaryOrder (j - 1) j t := Or.inr (Or.inl hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet (j - 1)} := by
    simpa only [t, incomingFlatTriple_support, pointZeros] using hf.2.1
  obtain ⟨r, hr, hω, hA, hM, hB⟩ := w.cusp_exterior_affine j hf
  have hchange := w.flat_boundary_chi_signChanges (j - 1) j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine (j - 1) (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) r 1 0 hω
      ((congrArg w.center hlabels.1).trans hM)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by rcases hr with hr | hr <;> linarith) (by norm_num) (by rcases hr with hr | hr <;> linarith)
  have hintervals := incomingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hgap : criticalIntervalIntegerOutput w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j (j - 1)) (by omega) := incoming_flat_integer_gap w.center j hf.2.1
  have hfactor : (criticalGapUInteger w.center (j - 1) t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon r 1 0) *
      criticalGapUInteger w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon r 1 0)) + (criticalGapVInteger w.center (j - 1) t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon r 1 0) *
      criticalGapVInteger w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon r 1 0)) =
      criticalIntervalIntegerOutput w.center (j - 1) t hZt t.rightInterval t.rightInterval_excludes_span := by
    rcases hr with hr | hr
    · have hε := cusp_epsilons_incoming_lt_zero r hr
      have hfac := integer_wall_factor_left_leaf_pos_neg w.center (j - 1) t hZt hintervals.2.1 (by change 2 ≤ m + 2; omega)
      rw [hε.1, hε.2, hfac.1, hfac.2, add_zero]
    · have hε := cusp_epsilons_incoming_gt_one r hr
      have hfac := integer_wall_factor_left_leaf_pos_pos w.center (j - 1) t hZt hintervals.2.1 (by change 2 ≤ m + 2; omega)
      rw [hε.1, hε.2, hfac.1, hfac.2, zero_add]
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hfactor, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ (j - 1) j t horder, sub_neg_eq_add] using hr.1

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_outgoing_signed_response (w : WallGerm (m + 4)) (j : ZMod (m + 4))
    (hf : w.CuspAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 j (by omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 j (by omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j j) (by omega)) := by
  let t := outgoingFlatTriple (n := m + 4) (by omega)
  have hlabels := outgoingFlatTriple_labels (n := m + 4) (by omega) j
  have horder : CyclicTurnBoundaryOrder j j t := Or.inr (Or.inr hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet j} := by
    simpa only [t, outgoingFlatTriple_support, pointZeros] using hf.2.1
  obtain ⟨r, hr, hω, hA, hM, hB⟩ := w.cusp_exterior_affine j hf
  have hchange := w.flat_boundary_chi_signChanges j j t horder hf.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine j (by omega) t hZt hf.2.2.1 hchange
      (w.center (j - 1)) (w.center (j + 1) - w.center (j - 1)) 1 0 r hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hM)
      (by norm_num) (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith)
  have hintervals := outgoingFlatTriple_intervals (n := m + 4) (by omega)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval (by omega) := not_ne_iff.mpr hintervals.1
  have hgap : criticalIntervalIntegerOutput w.center j t hZt t.leftInterval t.leftInterval_excludes_span =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j j) (by omega) := outgoing_flat_integer_gap w.center j hf.2.1
  have hfactor : (criticalGapUInteger w.center j t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon 1 0 r) *
      criticalGapUInteger w.center j t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon 1 0 r)) + (criticalGapVInteger w.center j t hZt t.leftInterval t.leftInterval_excludes_span
        (wallLeftEpsilon 1 0 r) *
      criticalGapVInteger w.center j t hZt t.rightInterval t.rightInterval_excludes_span
        (wallRightEpsilon 1 0 r)) =
      criticalIntervalIntegerOutput w.center j t hZt t.leftInterval t.leftInterval_excludes_span := by
    rcases hr with hr | hr
    · have hε := cusp_epsilons_outgoing_lt_zero r hr
      have hfac := integer_wall_factor_right_leaf_pos_pos w.center j t hZt (by change 2 ≤ m + 2; omega) hintervals.2.2
      rw [hε.1, hε.2, hfac.1, hfac.2, zero_add]
    · have hε := cusp_epsilons_outgoing_gt_one r hr
      have hfac := integer_wall_factor_right_leaf_neg_pos w.center j t hZt (by change 2 ≤ m + 2; omega) hintervals.2.2
      rw [hε.1, hε.2, hfac.1, hfac.2, add_zero]
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hfactor, hgap] at hr
  refine ⟨?_, hr.2⟩
  simpa only [flat_boundary_geometric_sign _ j j t horder, sub_neg_eq_add] using hr.1

/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_incident_signed_response_all_sizes (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) (hg : incident j g) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by have := hf.1; omega⟩
  rcases hg with hg | hg
  · subst g
    exact w.cusp_incoming_signed_response j hf
  · subst g
    exact w.cusp_outgoing_signed_response j hf


/-- Cusp signed deletion response on the actual source domain. The line
coordinate is proved exterior, and all physical roots retain their exact
induced deletion labels; no flat betweenness premise is used. -/
theorem cusp_signed_response_all_roots (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  by_cases hg : incident j g
  · exact w.cusp_incident_signed_response_all_sizes j g hf hg
  · exact w.cusp_nonincident_signed_response j g hf hg

end
end SM.WallGerm





namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The source consecutive signed deletion identity uses chirotope
negative minus positive, independently of real time orientation. All roots
are retained and deletion is at the actual center. -/
theorem cusp_negative_minus_positive_near (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sNegative sPositive : w.Parameter, ∀ hNegative0 : sNegative.val ≠ 0, ∀ hPositive0 : sPositive.val ≠ 0,
        turn (w.curve sNegative) j = -1 → turn (w.curve sPositive) j = 1 →
        |sNegative.val| < δ → |sPositive.val| < δ →
        treeCoefficient (w.curve sNegative) (w.generic_punctured sNegative hNegative0).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sPositive) (w.generic_punctured sPositive hPositive0).1 g
            (by have := hf.1; omega) =
          treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega) := by
  classical
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ := w.cusp_signed_response_all_roots j g hf
  let F : w.Parameter → ℤ := fun s =>
    if hs : s.val ≠ 0 then
      treeCoefficient (w.curve s) (w.generic_punctured s hs).1 g (by have := hf.1; omega)
    else 0
  have hFresponse :
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
          (F sPlus - F sMinus = d *
            treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
              (fusionIndex j g) (by have := hf.1; omega)) := by
    intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
    simpa only [F, dif_pos (ne_of_gt hPlus), dif_pos (ne_of_lt hMinus)] using
      hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  refine ⟨δ, hδ, hrad, ?_⟩
  intro sNegative sPositive hNegative0 hPositive0 hNegative hPositive hNegativeNear hPositiveNear
  have h := w.turn_response_right_minus_left j F
    (treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
      (fusionIndex j g) (by have := hf.1; omega)) d δ hd hδ hrad hFresponse
    sNegative sPositive hNegative0 hPositive0 hNegative hPositive hNegativeNear hPositiveNear
  simpa only [F, dif_pos hNegative0, dif_pos hPositive0] using h


/-- The source consecutive signed deletion identity uses chirotope
negative minus positive, independently of real time orientation. All roots
are retained and deletion is at the actual center. -/
theorem cusp_negative_minus_positive (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.CuspAt j) (sNegative sPositive : w.Parameter)
    (hNegative0 : sNegative.val ≠ 0) (hPositive0 : sPositive.val ≠ 0)
    (hNegative : turn (w.curve sNegative) j = -1) (hPositive : turn (w.curve sPositive) j = 1) :
    treeCoefficient (w.curve sNegative) (w.generic_punctured sNegative hNegative0).1 g
        (by have := hf.1; omega) -
      treeCoefficient (w.curve sPositive) (w.generic_punctured sPositive hPositive0).1 g
        (by have := hf.1; omega) =
      treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
        (fusionIndex j g) (by have := hf.1; omega) := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.cusp_negative_minus_positive_near j g hf
  obtain ⟨r, hr0, hrNear, hrChi⟩ := w.nearby_same_chirotope δ hδ hδr sNegative hNegative0
  obtain ⟨l, hl0, hlNear, hlChi⟩ := w.nearby_same_chirotope δ hδ hδr sPositive hPositive0
  have hrTurn : turn (w.curve r) j = -1 := (hrChi (j - 1) j (j + 1)).trans hNegative
  have hlTurn : turn (w.curve l) j = 1 := (hlChi (j - 1) j (j + 1)).trans hPositive
  have he := hresponse r l hr0 hl0 hrTurn hlTurn hrNear hlNear
  have hrCoeff := treeCoefficient_eq_of_chi (w.generic_punctured r hr0).1
    (w.generic_punctured sNegative hNegative0).1 hrChi g (by have := hf.1; omega)
  have hlCoeff := treeCoefficient_eq_of_chi (w.generic_punctured l hl0).1
    (w.generic_punctured sPositive hPositive0).1 hlChi g (by have := hf.1; omega)
  rw [hrCoeff, hlCoeff] at he
  exact he


end
end SM.WallGerm

#check SM.WallGerm.cusp_negative_minus_positive_near
#print axioms SM.WallGerm.cusp_negative_minus_positive_near

#check SM.WallGerm.cusp_negative_minus_positive
#print axioms SM.WallGerm.cusp_negative_minus_positive
