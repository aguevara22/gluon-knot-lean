import SM.RelativeGeneralPosition
import SM.WeakOpen
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.LocallyConstant.Basic
import SM.TreeChamber
import SM.ContactHalfTuples
import SM.FusionIndices
import SM.NamedWallSides
import SM.UnorderedWallTriples
import Mathlib.Tactic
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

/-- The physical half-root map: the contacted root splits into the two
new child edges; every other root is retained in exactly one half. -/
def contactHalfRoots (M a g : ZMod n) :
    ZMod (firstHalfSize M a) × ZMod (secondHalfSize M a) :=
  if g = a then (-1, 0)
  else if (g - M).val < contactDistance M a then (((g - M).val : ZMod (firstHalfSize M a)), 0)
  else (-1, ((g - a).val : ZMod (secondHalfSize M a)))

theorem contactHalfRoots_base (M a : ZMod n) : contactHalfRoots M a a = (-1, 0) := by
  simp [contactHalfRoots]

theorem contactHalfRoots_first (M a : ZMod n) {i : ZMod (firstHalfSize M a)} (hi : i ≠ -1) :
    contactHalfRoots M a (firstHalfIndex M a i) = (i, 0) := by
  have hga : firstHalfIndex M a i ≠ a := by
    intro he
    exact hi (firstHalfIndex_injective M a (he.trans (firstHalfIndex_last M a).symm))
  have hf := (firstHalf_inherited_root_iff M a (firstHalfIndex M a i)).mp ⟨i, hi, rfl⟩
  have hv := cyclicRangeIndex_offset (firstHalfSize_le M a) M i
  change (firstHalfIndex M a i - M).val = i.val at hv
  rw [contactHalfRoots, if_neg hga, if_pos hf]
  simp only [hv, ZMod.natCast_zmod_val]

theorem contactHalfRoots_second (M a : ZMod n) {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    contactHalfRoots M a (secondHalfEdgeIndex M a i) = (-1, i) := by
  have hga : secondHalfEdgeIndex M a i ≠ a := by
    intro he
    exact hi (secondHalfEdgeIndex_injective M a (he.trans (secondHalfEdgeIndex_zero M a).symm))
  have hs := (secondHalf_inherited_root_iff M a (secondHalfEdgeIndex M a i)).mp ⟨i, hi, rfl⟩
  have hv := cyclicRangeIndex_offset (secondHalfSize_le M a) a i
  change (secondHalfEdgeIndex M a i - a).val = i.val at hv
  rw [contactHalfRoots, if_neg hga, if_neg (by omega)]
  simp only [hv, ZMod.natCast_zmod_val]

/-- The typed map realizes the source's three exhaustive root rows,
including an actual inherited label whenever a child retains the old root. -/
theorem contactHalfRoots_spec (M a g : ZMod n) :
    (g = a ∧ contactHalfRoots M a g = (-1, 0)) ∨
    (∃ i : ZMod (firstHalfSize M a), i ≠ -1 ∧ firstHalfIndex M a i = g ∧
      contactHalfRoots M a g = (i, 0)) ∨
    (∃ i : ZMod (secondHalfSize M a), i ≠ 0 ∧ secondHalfEdgeIndex M a i = g ∧
      contactHalfRoots M a g = (-1, i)) := by
  rcases contact_root_cases M a g with hg | ⟨i, hi, hg⟩ | ⟨i, hi, hg⟩
  · subst g
    exact Or.inl ⟨rfl, contactHalfRoots_base M a⟩
  · subst g
    exact Or.inr (Or.inl ⟨i, hi, rfl, contactHalfRoots_first M a hi⟩)
  · subst g
    exact Or.inr (Or.inr ⟨i, hi, rfl, contactHalfRoots_second M a hi⟩)

/-- Both directed endpoint pairs of the mapped child roots are the actual
source edges. Equality of vectors alone would not establish these endpoints.
The base case produces a-to-M and M-to-a+1; inherited roots keep both endpoints. -/
theorem contactHalfRoots_vertices (hn : 3 ≤ n) {M a : ZMod n} (hc : ContactSeparated M a)
    (P : LabelledTuple n) (g : ZMod n) :
    let r := contactHalfRoots M a g
    ((firstHalf P M a r.1, firstHalf P M a (r.1 + 1)) =
      if (g - M).val < contactDistance M a then (P g, P (g + 1)) else (P a, P M)) ∧
    ((secondHalf P M a r.2, secondHalf P M a (r.2 + 1)) =
      if contactDistance M a < (g - M).val then (P g, P (g + 1)) else (P M, P (a + 1))) := by
  dsimp only
  rcases contact_root_cases M a g with hg | ⟨i, hi, hg⟩ | ⟨i, hi, hg⟩
  · subst g
    rw [contactHalfRoots_base]
    simp only [Prod.fst, Prod.snd, contactDistance, Nat.lt_irrefl, ite_false,
      neg_add_cancel, zero_add, firstHalf_last, firstHalf_zero, secondHalf_zero,
      secondHalf_one hn hc, and_self]
  · subst g
    have hf := (firstHalf_inherited_root_iff M a (firstHalfIndex M a i)).mp ⟨i, hi, rfl⟩
    have hs : ¬ contactDistance M a < (firstHalfIndex M a i - M).val := by omega
    rw [contactHalfRoots_first M a hi]
    simp only [Prod.fst, Prod.snd, if_pos hf, if_neg hs, zero_add,
      secondHalf_zero, secondHalf_one hn hc, firstHalf, firstHalfIndex_next M a hi, and_self]
  · subst g
    have hs := (secondHalf_inherited_root_iff M a (secondHalfEdgeIndex M a i)).mp ⟨i, hi, rfl⟩
    have hf : ¬ (secondHalfEdgeIndex M a i - M).val < contactDistance M a := by omega
    rw [contactHalfRoots_second M a hi]
    simp only [Prod.fst, Prod.snd, if_neg hf, if_pos hs, neg_add_cancel,
      firstHalf_last, firstHalf_zero, secondHalf, secondHalfIndex_nonzero M a hi,
      secondHalfIndex_next M a hi, and_self]

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
  rw [IncreasingBoundaryTriple.expandPosition_val]
  change g + ((if (i - 1).val ≤ t.lower.val then (i - 1).val
      else (i - 1).val + t.erasedInteriorCount : ℕ) : ZMod n) + 1 =
    M + ((e i + ((g - M).val : ZMod (firstHalfSize M a))).val : ZMod n)
  rw [hlower, herase, hv, hcut]
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
  rw [IncreasingBoundaryTriple.expandPosition_val]
  change g + ((if (i - 1).val ≤ t.lower.val then (i - 1).val
      else (i - 1).val + t.erasedInteriorCount : ℕ) : ZMod n) + 1 =
    a + 1 + ((e i + ((g - a).val : ZMod (secondHalfSize M a)) - 1).val : ZMod n)
  rw [hlower, herase, hv, hearg, hcut]
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
variable {n : ℕ} [NeZero n]

/-- Every label of the restricted word is the consecutive parent label from
its starting vertex. Equality of sizes transports the complete word, including
local zero (the last vertex), without an endpoint-only inference. -/
theorem restrictedWord_reindex_start {q : ℕ} [NeZero q]
    (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
    (hsize : J.leaves + 1 = q) (u : ZMod q) :
    restrictedWordTuple P g J ((ZMod.ringEquivCongr hsize).symm u) =
      P (boundaryIndex g J.left + ((u - 1).val : ZMod n)) := by
  have hv : (((ZMod.ringEquivCongr hsize).symm u - 1)).val = (u - 1).val := by
    have he := ZMod.ringEquivCongr_val hsize ((ZMod.ringEquivCongr hsize).symm u - 1)
    simpa only [map_sub, map_one, RingEquiv.apply_symm_apply] using he.symm
  change P (g + ((J.left.val + (((ZMod.ringEquivCongr hsize).symm u - 1)).val : ℕ) : ZMod n) + 1) = _
  rw [hv, Nat.cast_add]
  apply congrArg P
  unfold boundaryIndex
  ring

/-- The gap starting at B with the second-half size is exactly the second
source half at every cyclic label, with its physical closing root zero. -/
theorem restrictedWord_eq_secondHalf (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = secondHalfSize M a)
    (hstart : boundaryIndex g J.left = a + 1) :
    (fun u : ZMod (secondHalfSize M a) =>
      restrictedWordTuple P g J ((ZMod.ringEquivCongr hsize).symm u)) =
      secondHalf P M a := by
  funext u
  rw [restrictedWord_reindex_start, hstart]
  unfold secondHalf
  rw [secondHalfIndex_range]
  rfl

/-- The gap starting at X is the complete first source half shifted by -1.
Consequently local closing root zero is the source half root -1. -/
theorem restrictedWord_eq_shift_firstHalf (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = firstHalfSize M a)
    (hstart : boundaryIndex g J.left = M) :
    (fun u : ZMod (firstHalfSize M a) =>
      restrictedWordTuple P g J ((ZMod.ringEquivCongr hsize).symm u)) =
      shift (-1) (firstHalf P M a) := by
  funext u
  rw [restrictedWord_reindex_start, hstart]
  simp only [shift, firstHalf, firstHalfIndex, cyclicRangeIndex, sub_eq_add_neg]

/-- Full tuple transport identifies the actual second-half coefficient.
G1 witnesses are explicit; no root independence is used. -/
theorem restrictedWord_secondHalf_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = secondHalfSize M a)
    (hstart : boundaryIndex g J.left = a + 1) (hJ : 2 ≤ J.leaves)
    (hP : G1 (restrictedWordTuple P g J)) (hQ : G1 (secondHalf P M a)) :
    treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega) =
      treeCoefficient (secondHalf P M a) hQ 0 (by omega) := by
  exact treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP hQ
    (restrictedWord_eq_secondHalf P g M a J hsize hstart) (by omega)

/-- The cyclic shift transports local root zero to the first-half root -1.
This is equality for a fixed physical edge, not arbitrary root invariance. -/
theorem restrictedWord_firstHalf_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = firstHalfSize M a)
    (hstart : boundaryIndex g J.left = M) (hJ : 2 ≤ J.leaves)
    (hP : G1 (restrictedWordTuple P g J)) (hQ : G1 (firstHalf P M a)) :
    treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega) =
      treeCoefficient (firstHalf P M a) hQ (-1) (by omega) := by
  have he := treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_shift_forward (-1) hQ)
    (restrictedWord_eq_shift_firstHalf P g M a J hsize hstart) (by omega)
  have hs := treeCoefficient_shift (firstHalf P M a) hQ (-1) (-1) (by omega)
  simp only [sub_self] at hs
  exact he.trans hs

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- At the contacted base root, the entire B-to-X gap is the second half.
Its arity equality and starting label are derived from the actual cut. -/
theorem contactBaseTriple_left_word (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    ∃ hsize : (contactBaseTriple M a hn hc).leftInterval.leaves + 1 = secondHalfSize M a,
      (fun u : ZMod (secondHalfSize M a) => restrictedWordTuple P a
        (contactBaseTriple M a hn hc).leftInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        secondHalf P M a := by
  have hd := contactDistance_bounds hn hc
  have hg := (contactBaseTriple_gaps M a hn hc).1
  have hs : (contactBaseTriple M a hn hc).leftInterval.leaves + 1 = secondHalfSize M a := by
    unfold secondHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_secondHalf P a M a _ hs ?_⟩
  exact (contactBaseTriple_labels M a hn hc).1

/-- At the base root, the whole X-to-A gap is the first half shifted by -1,
so its local closing edge is the physical a-to-M edge. -/
theorem contactBaseTriple_right_word (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    ∃ hsize : (contactBaseTriple M a hn hc).rightInterval.leaves + 1 = firstHalfSize M a,
      (fun u : ZMod (firstHalfSize M a) => restrictedWordTuple P a
        (contactBaseTriple M a hn hc).rightInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        shift (-1) (firstHalf P M a) := by
  have hg := (contactBaseTriple_gaps M a hn hc).2
  have hs : (contactBaseTriple M a hn hc).rightInterval.leaves + 1 = firstHalfSize M a := by
    unfold firstHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_shift_firstHalf P a M a _ hs ?_⟩
  exact (contactBaseTriple_labels M a hn hc).2.1

/-- Every root of the first inherited arc leaves exactly the same complete
B-to-X gap, including the endpoint-adjacent root at M. -/
theorem contactFirstArcTriple_right_word (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    ∃ hsize : (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves + 1 = secondHalfSize M a,
      (fun u : ZMod (secondHalfSize M a) => restrictedWordTuple P g
        (contactFirstArcTriple g M a hn hc hu).rightInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        secondHalf P M a := by
  have hd := contactDistance_bounds hn hc
  have hg := (contactFirstArcTriple_gaps g M a hn hc hu).2
  have hs : (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves + 1 = secondHalfSize M a := by
    unfold secondHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_secondHalf P g M a _ hs ?_⟩
  exact (contactFirstArcTriple_labels g M a hn hc hu).2.1

/-- Every root of the second inherited arc leaves the complete X-to-A gap,
including the endpoint-adjacent root ending at M. -/
theorem contactSecondArcTriple_left_word (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    ∃ hsize : (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves + 1 = firstHalfSize M a,
      (fun u : ZMod (firstHalfSize M a) => restrictedWordTuple P g
        (contactSecondArcTriple g M a hn hc hu).leftInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        shift (-1) (firstHalf P M a) := by
  have hg := (contactSecondArcTriple_gaps g M a hn hc hu).1
  have hs : (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves + 1 = firstHalfSize M a := by
    unfold firstHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_shift_firstHalf P g M a _ hs ?_⟩
  exact (contactSecondArcTriple_labels g M a hn hc hu).1

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem contactBaseTriple_support (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    (contactBaseTriple M a hn hc).vertexSet a = contactSupport M a := by
  have hl := contactBaseTriple_labels M a hn hc
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, contactSupport]
  ext k
  simp [or_comm, or_left_comm, or_assoc]

theorem contactFirstArcTriple_support (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).vertexSet g = contactSupport M a := by
  have hl := contactFirstArcTriple_labels g M a hn hc hu
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, contactSupport]

theorem contactSecondArcTriple_support (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).vertexSet g = contactSupport M a := by
  have hl := contactSecondArcTriple_labels g M a hn hc hu
  simp only [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet,
    Finset.image_insert, Finset.image_singleton, hl.1, hl.2.1, hl.2.2, contactSupport]
  ext k
  simp [or_comm, or_left_comm, or_assoc]

/-- At epsilon (+,+), both nonleaf E factors vanish and the V product is
the ordered product of the two actual integer B outputs. -/
theorem integer_wall_factor_two_nonleaves_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 =
      criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span *
        criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hEL := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  have hER := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · simp only [criticalGapUInteger, ite_true, hEL, hER, zero_mul]
  · simp only [criticalGapVInteger, ite_true]

/-- The base cut's B-to-X gap is the second half at its opening root zero.
All G1 and arity premises are proved from the stated contact data. -/
theorem contactBaseTriple_left_integer_gap (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P a (contactBaseTriple M a hn hc)
      (by simpa only [contactBaseTriple_support] using hz)
      (contactBaseTriple M a hn hc).leftInterval
      (contactBaseTriple M a hn hc).leftInterval_excludes_span =
      treeCoefficient (secondHalf P M a) (g1_secondHalf hn hc hz) 0
        (contactHalfSizes_bounds hn hc).2.1 := by
  let t := contactBaseTriple M a hn hc
  have hZt : pointZeroTriples P = {t.vertexSet a} := by
    simpa only [t, contactBaseTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactBaseTriple_left_word P M a hn hc
  have hhalf := (contactHalfSizes_bounds hn hc).2.1
  have hJ : 2 ≤ t.leftInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.leftInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P a t hZt t.leftInterval t.leftInterval_excludes_span
  change criticalIntervalIntegerOutput P a t hZt t.leftInterval t.leftInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  exact treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_secondHalf hn hc hz) hword (by omega)

/-- The base cut's X-to-A gap closes along A-to-X. Whole tuple transport
and cyclic covariance identify its root with first-half label -1. -/
theorem contactBaseTriple_right_integer_gap (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P a (contactBaseTriple M a hn hc)
      (by simpa only [contactBaseTriple_support] using hz)
      (contactBaseTriple M a hn hc).rightInterval
      (contactBaseTriple M a hn hc).rightInterval_excludes_span =
      treeCoefficient (firstHalf P M a) (g1_firstHalf hn hc hz) (-1)
        (contactHalfSizes_bounds hn hc).1.1 := by
  let t := contactBaseTriple M a hn hc
  have hZt : pointZeroTriples P = {t.vertexSet a} := by
    simpa only [t, contactBaseTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactBaseTriple_right_word P M a hn hc
  have hhalf := (contactHalfSizes_bounds hn hc).1.1
  have hJ : 2 ≤ t.rightInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.rightInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P a t hZt t.rightInterval t.rightInterval_excludes_span
  change criticalIntervalIntegerOutput P a t hZt t.rightInterval t.rightInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  have he := treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_shift_forward (-1) (g1_firstHalf hn hc hz)) hword (by omega)
  have hs := treeCoefficient_shift (firstHalf P M a) (g1_firstHalf hn hc hz) (-1) (-1) hhalf
  simp only [sub_self] at hs
  exact he.trans hs

/-- Every first-arc root has the same complete B-to-X integer gap output,
at second-half root zero, including the endpoint-adjacent roots. -/
theorem contactFirstArcTriple_right_integer_gap (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : (g - M).val < contactDistance M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P g (contactFirstArcTriple g M a hn hc hu)
      (by simpa only [contactFirstArcTriple_support] using hz)
      (contactFirstArcTriple g M a hn hc hu).rightInterval
      (contactFirstArcTriple g M a hn hc hu).rightInterval_excludes_span =
      treeCoefficient (secondHalf P M a) (g1_secondHalf hn hc hz) 0
        (contactHalfSizes_bounds hn hc).2.1 := by
  let t := contactFirstArcTriple g M a hn hc hu
  have hZt : pointZeroTriples P = {t.vertexSet g} := by
    simpa only [t, contactFirstArcTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactFirstArcTriple_right_word P g M a hn hc hu
  have hhalf := (contactHalfSizes_bounds hn hc).2.1
  have hJ : 2 ≤ t.rightInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.rightInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P g t hZt t.rightInterval t.rightInterval_excludes_span
  change criticalIntervalIntegerOutput P g t hZt t.rightInterval t.rightInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  exact treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_secondHalf hn hc hz) hword (by omega)

/-- Every second-arc root has the same X-to-A integer gap output at
first-half closing root -1; no caller G1 or tuple identity is needed. -/
theorem contactSecondArcTriple_left_integer_gap (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : contactDistance M a < (g - M).val)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    criticalIntervalIntegerOutput P g (contactSecondArcTriple g M a hn hc hu)
      (by simpa only [contactSecondArcTriple_support] using hz)
      (contactSecondArcTriple g M a hn hc hu).leftInterval
      (contactSecondArcTriple g M a hn hc hu).leftInterval_excludes_span =
      treeCoefficient (firstHalf P M a) (g1_firstHalf hn hc hz) (-1)
        (contactHalfSizes_bounds hn hc).1.1 := by
  let t := contactSecondArcTriple g M a hn hc hu
  have hZt : pointZeroTriples P = {t.vertexSet g} := by
    simpa only [t, contactSecondArcTriple_support] using hz
  obtain ⟨hsize, hword⟩ := contactSecondArcTriple_left_word P g M a hn hc hu
  have hhalf := (contactHalfSizes_bounds hn hc).1.1
  have hJ : 2 ≤ t.leftInterval.leaves := by
    dsimp only [t]
    omega
  have hleaf : t.leftInterval.leaves ≠ 1 := by omega
  have hP := restrictedWord_G1_off_critical P g t hZt t.leftInterval t.leftInterval_excludes_span
  change criticalIntervalIntegerOutput P g t hZt t.leftInterval t.leftInterval_excludes_span = _
  rw [criticalIntervalIntegerOutput, dif_neg hleaf]
  have he := treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_shift_forward (-1) (g1_firstHalf hn hc hz)) hword (by omega)
  have hs := treeCoefficient_shift (firstHalf P M a) (g1_firstHalf hn hc hz) (-1) (-1) hhalf
  simp only [sub_self] at hs
  exact he.trans hs

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The complete first contraction tuple and cyclic covariance identify its
coefficient at the inherited physical root; all G1 and arity facts are derived. -/
theorem contactFirstArc_contracted_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    treeCoefficient (contractedWordTuple P g (contactFirstArcTriple g M a hn hc hu))
      (contractedWord_G1 P g (contactFirstArcTriple g M a hn hc hu)
        (by rw [contactFirstArcTriple_support]; exact hz))
      0 (by rw [contactFirstArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).1.1) =
      treeCoefficient (firstHalf P M a) (g1_firstHalf hn hc hz)
        ((g - M).val : ZMod (firstHalfSize M a)) (contactHalfSizes_bounds hn hc).1.1 := by
  have he := treeCoefficient_of_reindexed_tuple_eq (contactFirstArcTriple_contractedSize g M a hn hc hu)
    (contractedWordTuple P g (contactFirstArcTriple g M a hn hc hu))
    (shift ((g - M).val : ZMod (firstHalfSize M a)) (firstHalf P M a))
    (contractedWord_G1 P g (contactFirstArcTriple g M a hn hc hu)
      (by rw [contactFirstArcTriple_support]; exact hz))
    (g1_shift_forward _ (g1_firstHalf hn hc hz))
    (contactFirstArc_contracted_tuple P g M a hn hc hu)
    (by rw [contactFirstArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).1.1)
  have hs := treeCoefficient_shift (firstHalf P M a) (g1_firstHalf hn hc hz)
    ((g - M).val : ZMod (firstHalfSize M a)) ((g - M).val : ZMod (firstHalfSize M a))
    (contactHalfSizes_bounds hn hc).1.1
  rw [sub_self] at hs
  exact he.trans hs

/-- The complete second contraction retains the original root under the
source second-half indexing, including the final edge ending at M. -/
theorem contactSecondArc_contracted_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    treeCoefficient (contractedWordTuple P g (contactSecondArcTriple g M a hn hc hu))
      (contractedWord_G1 P g (contactSecondArcTriple g M a hn hc hu)
        (by rw [contactSecondArcTriple_support]; exact hz))
      0 (by rw [contactSecondArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).2.1) =
      treeCoefficient (secondHalf P M a) (g1_secondHalf hn hc hz)
        ((g - a).val : ZMod (secondHalfSize M a)) (contactHalfSizes_bounds hn hc).2.1 := by
  have he := treeCoefficient_of_reindexed_tuple_eq (contactSecondArcTriple_contractedSize g M a hn hc hu)
    (contractedWordTuple P g (contactSecondArcTriple g M a hn hc hu))
    (shift ((g - a).val : ZMod (secondHalfSize M a)) (secondHalf P M a))
    (contractedWord_G1 P g (contactSecondArcTriple g M a hn hc hu)
      (by rw [contactSecondArcTriple_support]; exact hz))
    (g1_shift_forward _ (g1_secondHalf hn hc hz))
    (contactSecondArc_contracted_tuple P g M a hn hc hu)
    (by rw [contactSecondArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).2.1)
  have hs := treeCoefficient_shift (secondHalf P M a) (g1_secondHalf hn hc hz)
    ((g - a).val : ZMod (secondHalfSize M a)) ((g - a).val : ZMod (secondHalfSize M a))
    (contactHalfSizes_bounds hn hc).2.1
  rw [sub_self] at hs
  exact he.trans hs

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

namespace SM

noncomputable section

/-- At the contacted base edge the critical cut order is B,X,A. -/
theorem contact_epsilons_base (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 1 r 0 = 1 ∧ wallRightEpsilon 1 r 0 = 1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (r - 1) / (0 - 1)
    exact div_pos_of_neg_of_neg (by linarith) (by norm_num)
  · apply sign_eq_one_iff.mpr
    change 0 < (0 - r) / (0 - 1)
    exact div_pos_of_neg_of_neg (by linarith) (by norm_num)

/-- On the original X-to-A arc the critical cut order is A,B,X. -/
theorem contact_epsilons_first_arc (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon 0 1 r = 1 ∧ wallRightEpsilon 0 1 r = -1 := by
  constructor
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - 0) / (r - 0)
    exact div_pos (by norm_num) (by linarith)
  · apply sign_eq_neg_one_iff.mpr
    change (r - 1) / (r - 0) < 0
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- On the original B-to-X arc the critical cut order is X,A,B. -/
theorem contact_epsilons_second_arc (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    wallLeftEpsilon r 0 1 = -1 ∧ wallRightEpsilon r 0 1 = 1 := by
  constructor
  · apply sign_eq_neg_one_iff.mpr
    change (0 - r) / (1 - r) < 0
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  · apply sign_eq_one_iff.mpr
    change 0 < (1 - 0) / (1 - r)
    exact div_pos (by norm_num) (by linarith)

variable {n : ℕ} [NeZero n]

/-- The actual contact interior supplies the scalar. Central regularity,
proved from the named contact support, supplies the nonzero direction B-A.
No G1 or flat-wall premise on the center is assumed. -/
theorem WallGerm.contact_interior_affine (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      w.center (a + 1) - w.center a ≠ 0 ∧
      w.center a = w.center a + (0 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center (a + 1) = w.center a + (1 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center M = w.center a + r • (w.center (a + 1) - w.center a) := by
  have hreg := w.vertexEdge_regular hn hc
  have hω : edge w.center a ≠ 0 := (hreg a).2.1
  obtain ⟨r, hr0, hr1, hX⟩ := hc.2.2.2.1
  refine ⟨r, hr0, hr1, ?_, ?_, ?_, ?_⟩
  · simpa only [edge] using hω
  · simp
  · simp
  · simpa only [edgePoint, edge] using hX

/-- Exactly the three cyclic orders of A,B,X in an actual root word.
This predicate contains only label equalities, with no geometric premise. -/
def CyclicContactBoundaryOrder (g M a : ZMod n) (t : IncreasingBoundaryTriple n) : Prop :=
    (boundaryIndex g t.lower = a ∧ boundaryIndex g t.middle = a + 1 ∧
      boundaryIndex g t.upper = M) ∨
    (boundaryIndex g t.lower = a + 1 ∧ boundaryIndex g t.middle = M ∧
      boundaryIndex g t.upper = a) ∨
    (boundaryIndex g t.lower = M ∧ boundaryIndex g t.middle = a ∧
      boundaryIndex g t.upper = a + 1)

/-- Reversing any of the three even cyclic orders negates the same contact
chirotope. The equality holds for every tuple, including the wall center. -/
theorem contact_boundary_chi_eq_neg (P : LabelledTuple n) (g M a : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicContactBoundaryOrder g M a t) :
    chi P (boundaryIndex g t.upper) (boundaryIndex g t.middle) (boundaryIndex g t.lower) =
      -chi P a (a + 1) M := by
  rcases h with h | h | h
  · simpa only [h.1, h.2.1, h.2.2] using chi_swap_outer P a (a + 1) M
  · simpa only [h.1, h.2.1, h.2.2] using chi_swap_last P a (a + 1) M
  · simpa only [h.1, h.2.1, h.2.2] using chi_swap_first P a (a + 1) M

theorem contact_boundary_geometric_sign (P : LabelledTuple n) (g M a : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicContactBoundaryOrder g M a t) :
    geometricBoundaryArray (R := ℤ) P g t = -(chi P a (a + 1) M : ℤ) := by
  simp only [geometricBoundaryArray, contact_boundary_chi_eq_neg P g M a t h,
    Int.cast_id, SignType.coe_neg]

/-- The source contact observable's sign change gives exactly the reversed
boundary-chirotope premise of the single-triple response theorem. -/
theorem WallGerm.contact_boundary_chi_signChanges (w : WallGerm n) (g M a : ZMod n)
    (t : IncreasingBoundaryTriple n) (h : CyclicContactBoundaryOrder g M a t)
    (hcontact : w.SignChanges (fun P => (chi P a (a + 1) M : ℝ))) :
    w.SignChanges (fun P => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) := by
  have he : (fun P : LabelledTuple n => (chi P (boundaryIndex g t.upper)
      (boundaryIndex g t.middle) (boundaryIndex g t.lower) : ℝ)) =
      (fun P => -(chi P a (a + 1) M : ℝ)) := by
    funext P
    rw [contact_boundary_chi_eq_neg P g M a t h, SignType.coe_neg]
  rw [he, w.signChanges_neg]
  exact hcontact

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The base-root full-span response is the product of the two actual half
coefficients in source order. The doubled far-sign jump fixes its orientation. -/
theorem contact_base_signed_response (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 a hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 a hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            (-1) (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              0 (contactHalfSizes_bounds hn hc.1).2.1)) := by
  let t := contactBaseTriple M a hn hc.1
  have hlabels := contactBaseTriple_labels M a hn hc.1
  have horder : CyclicContactBoundaryOrder a M a t := Or.inr (Or.inl hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet a} := by
    rw [contactBaseTriple_support]
    exact hc.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hB, hX⟩ := w.contact_interior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges a M a t horder hc.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine a hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 1 r 0 hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hX)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by linarith) (by linarith) (by norm_num)
  have hε := contact_epsilons_base r hr0 hr1
  have hgaps := contactBaseTriple_gaps M a hn hc.1
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hfac := integer_wall_factor_two_nonleaves_pos_pos w.center a t hZt hL hR
  have hleft := contactBaseTriple_left_integer_gap w.center M a hn hc.1 hc.2.1
  have hright := contactBaseTriple_right_integer_gap w.center M a hn hc.1 hc.2.1
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval hn :=
    not_ne_iff.mpr (contactBaseTriple_full M a hn hc.1)
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_neg hfull, hε.1, hε.2, hfac.1, hfac.2, zero_add, hleft, hright] at hr
  refine ⟨?_, ?_⟩
  · simpa only [contact_boundary_geometric_sign _ a M a t horder, sub_neg_eq_add] using hr.1
  · simpa only [mul_comm] using hr.2

/-- On the first inherited arc the proper contraction is the complete first
half at the same physical root; the other factor is the actual second half. -/
theorem contact_first_arc_signed_response (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) (hu : (g - M).val < contactDistance M a) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            ((g - M).val : ZMod (firstHalfSize M a)) (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              0 (contactHalfSizes_bounds hn hc.1).2.1)) := by
  let t := contactFirstArcTriple g M a hn hc.1 hu
  have hlabels := contactFirstArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inl hlabels
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactFirstArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hB, hX⟩ := w.contact_interior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 0 1 r hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hX)
      (by norm_num) (by linarith) (by linarith)
  have hε := contact_epsilons_first_arc r hr0 hr1
  have hgaps := contactFirstArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hfac := integer_wall_factor_left_leaf_pos_neg w.center g t hZt hgaps.1 hR
  have hgap := contactFirstArcTriple_right_integer_gap w.center g M a hn hc.1 hu hc.2.1
  have hcoeff := contactFirstArc_contracted_coefficient w.center g M a hn hc.1 hu hc.2.1
  have hproper := contactFirstArcTriple_proper g M a hn hc.1 hu
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_pos hproper, hε.1, hε.2, hfac.1, hgap, hcoeff] at hr
  refine ⟨?_, ?_⟩
  · simpa only [contact_boundary_geometric_sign _ g M a t horder, sub_neg_eq_add] using hr.1
  · simpa only [mul_comm] using hr.2

/-- On the second inherited arc the first-half closing factor multiplies the
complete second-half contraction at the original physical root. -/
theorem contact_second_arc_signed_response (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) (hu : contactDistance M a < (g - M).val) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            (-1) (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              ((g - a).val : ZMod (secondHalfSize M a)) (contactHalfSizes_bounds hn hc.1).2.1)) := by
  let t := contactSecondArcTriple g M a hn hc.1 hu
  have hlabels := contactSecondArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inr (Or.inr hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactSecondArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr0, hr1, hω, hA, hB, hX⟩ := w.contact_interior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hrad, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) r 0 1 hω
      ((congrArg w.center hlabels.1).trans hX)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by linarith) (by norm_num) (by linarith)
  have hε := contact_epsilons_second_arc r hr0 hr1
  have hgaps := contactSecondArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hfac := integer_wall_factor_right_leaf_neg_pos w.center g t hZt hL hgaps.2
  have hgap := contactSecondArcTriple_left_integer_gap w.center g M a hn hc.1 hu hc.2.1
  have hcoeff := contactSecondArc_contracted_coefficient w.center g M a hn hc.1 hu hc.2.1
  have hproper := contactSecondArcTriple_proper g M a hn hc.1 hu
  refine ⟨d, hd, δ, hδ, hrad, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  rw [dif_pos hproper, hε.1, hε.2, hfac.1, hgap, hcoeff] at hr
  refine ⟨?_, hr.2⟩
  simpa only [contact_boundary_geometric_sign _ g M a t horder, sub_neg_eq_add] using hr.1

/-- The three source root cases exhaust every original physical edge.
No extra endpoint or root-seam exception is needed. -/
theorem contact_signed_response_all_roots (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(chi (w.curve sPlus) a (a + 1) M : ℤ) +
          (chi (w.curve sMinus) a (a + 1) M : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn =
          d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
            (contactHalfRoots M a g).1 (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              (contactHalfRoots M a g).2 (contactHalfSizes_bounds hn hc.1).2.1)) := by
  by_cases hg : g = a
  · subst g
    simpa only [contactHalfRoots_base, Prod.fst, Prod.snd] using w.contact_base_signed_response M a hn hc
  · by_cases hu : (g - M).val < contactDistance M a
    · simpa only [contactHalfRoots, if_neg hg, if_pos hu, Prod.fst, Prod.snd] using
        w.contact_first_arc_signed_response g M a hn hc hu
    · have hne : (g - M).val ≠ contactDistance M a := by
        intro he
        apply hg
        apply sub_left_injective
        exact ZMod.val_injective n he
      have hs : contactDistance M a < (g - M).val := by omega
      simpa only [contactHalfRoots, if_neg hg, if_neg hu, Prod.fst, Prod.snd] using
        w.contact_second_arc_signed_response g M a hn hc hs

end
end SM.WallGerm


namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Source thm:A-S7 for the actual two halves and prescribed physical root map.
The sign is the chirotope on the named minus side. Both side parameters are
arbitrary and independent; no local-radius or neighbor-side restriction remains. -/
theorem vertex_edge_tree_law (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.VertexEdgeAt M a) (g : ZMod n) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn -
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn =
      (w.contactSign M a : ℤ) *
        (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).1 (contactHalfSizes_bounds hn hc.1).1.1 *
        treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).2 (contactHalfSizes_bounds hn hc.1).2.1) := by
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ := w.contact_signed_response_all_roots g M a hn hc
  let q : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have hMinus : (w.sideTime false q).val < 0 := by
    change -(δ / 2) < 0
    linarith
  have hPlus : 0 < (w.sideTime true q).val := by
    change 0 < δ / 2
    linarith
  have hMinusNear : |(w.sideTime false q).val| < δ := by
    change |-(δ / 2)| < δ
    rw [abs_neg, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hPlusNear : |(w.sideTime true q).val| < δ := by
    change |δ / 2| < δ
    rw [abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hr := hresponse (w.sideTime false q) (w.sideTime true q) hMinus hPlus hMinusNear hPlusNear
  have hsign : -(chi (w.sideTuple true q).val a (a + 1) M : ℤ) +
      (chi (w.sideTuple false q).val a (a + 1) M : ℤ) = 2 * d := hr.1
  have hsigns := w.vertex_contact_signs hc q q
  rw [hsigns.2.1, hsigns.2.2, SignType.coe_neg] at hsign
  have hdcontact : d = (w.contactSign M a : ℤ) := by omega
  have hcoeff :
      treeCoefficient (w.sideTuple true q).val (w.sideTuple true q).property.1 g hn -
        treeCoefficient (w.sideTuple false q).val (w.sideTuple false q).property.1 g hn =
        d * (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).1 (contactHalfSizes_bounds hn hc.1).1.1 *
        treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
          (contactHalfRoots M a g).2 (contactHalfSizes_bounds hn hc.1).2.1) := hr.2
  have hplusCoeff := treeCoefficient_eq_of_chi (w.sideTuple true q).property.1
    (w.sideTuple true t).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple true) q t i j k) g hn
  have hminusCoeff := treeCoefficient_eq_of_chi (w.sideTuple false q).property.1
    (w.sideTuple false s).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple false) q s i j k) g hn
  rw [hplusCoeff, hminusCoeff, hdcontact] at hcoeff
  exact hcoeff

end
end SM.WallGerm


namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem integer_U_product_zero_of_left_nonleaf_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (εR : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0 := by
  have hE := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  simp only [criticalGapUInteger, ite_true, hE, zero_mul]

theorem integer_U_product_zero_of_right_nonleaf_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hR : 2 ≤ t.rightInterval.leaves) (εL : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0 := by
  have hE := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  simp only [criticalGapUInteger, ite_true, hE, mul_zero]

/-- With two nonleaf gaps, one positive epsilon suffices to annihilate the
proper-span source product, whatever the other allowed sign is. -/
theorem integer_U_product_zero_of_nonleaves_one_positive (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves)
    (εL εR : SignType) (hε : εL = 1 ∨ εR = 1) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0 := by
  rcases hε with rfl | rfl
  · exact integer_U_product_zero_of_left_nonleaf_pos P g t hZ hL εR
  · exact integer_U_product_zero_of_right_nonleaf_pos P g t hZ hR εL

/-- Opposite epsilons on two nonleaf gaps annihilate both products required
by the FULL-span response. No amplitude is canceled or assumed nonzero. -/
theorem integer_UV_products_zero_of_nonleaves_opposite (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : 2 ≤ t.rightInterval.leaves)
    (εL εR : SignType) (hε : (εL = 1 ∧ εR = -1) ∨ (εL = -1 ∧ εR = 1)) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 0) := by
  have hEL := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  have hER := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [criticalGapUInteger, criticalGapVInteger, hEL, hER,
    show (-1 : SignType) ≠ 1 by decide]

end
end SM

namespace SM

noncomputable section

/-- For the base root the critical order is B,X,A. The two exterior ranges
give the two opposite epsilon pairs, with neither epsilon zero. -/
theorem extension_epsilons_base (r : ℝ) (hr : r < 0 ∨ 1 < r) :
    (wallLeftEpsilon 1 r 0 = 1 ∧ wallRightEpsilon 1 r 0 = -1) ∨
      (wallLeftEpsilon 1 r 0 = -1 ∧ wallRightEpsilon 1 r 0 = 1) := by
  rcases hr with hr | hr
  · left
    constructor
    · apply sign_eq_one_iff.mpr
      change 0 < (r - 1) / (0 - 1)
      exact div_pos_of_neg_of_neg (by linarith) (by norm_num)
    · apply sign_eq_neg_one_iff.mpr
      change (0 - r) / (0 - 1) < 0
      exact div_neg_of_pos_of_neg (by linarith) (by norm_num)
  · right
    constructor
    · apply sign_eq_neg_one_iff.mpr
      change (r - 1) / (0 - 1) < 0
      exact div_neg_of_pos_of_neg (by linarith) (by norm_num)
    · apply sign_eq_one_iff.mpr
      change 0 < (0 - r) / (0 - 1)
      exact div_pos_of_neg_of_neg (by linarith) (by norm_num)

/-- On the original X-to-A arc the cut order is A,B,X. The nonleaf right
gap has positive epsilon for either allowed exterior coordinate range. -/
theorem extension_right_epsilon_first_arc (r : ℝ) (hr : r < 0 ∨ 1 < r) :
    wallRightEpsilon 0 1 r = 1 := by
  apply sign_eq_one_iff.mpr
  change 0 < (r - 1) / (r - 0)
  rcases hr with hr | hr
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · exact div_pos (by linarith) (by linarith)

/-- On the original B-to-X arc the cut order is X,A,B. The nonleaf left
gap has positive epsilon for either allowed exterior coordinate range. -/
theorem extension_left_epsilon_second_arc (r : ℝ) (hr : r < 0 ∨ 1 < r) :
    wallLeftEpsilon r 0 1 = 1 := by
  apply sign_eq_one_iff.mpr
  change 0 < (0 - r) / (1 - r)
  rcases hr with hr | hr
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)

variable {n : ℕ} [NeZero n]

/-- The actual extension line witness supplies the affine scalar. Closed
segment exclusion forces it outside [0,1], and central regularity supplies
the nonzero direction B-A. No interior-contact or cusp premise is used. -/
theorem WallGerm.extension_exterior_affine (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (he : w.ExtensionAt M a) :
    ∃ r : ℝ, (r < 0 ∨ 1 < r) ∧
      w.center (a + 1) - w.center a ≠ 0 ∧
      w.center a = w.center a + (0 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center (a + 1) = w.center a + (1 : ℝ) • (w.center (a + 1) - w.center a) ∧
      w.center M = w.center a + r • (w.center (a + 1) - w.center a) := by
  have hreg := w.extension_regular hn he
  have hω : edge w.center a ≠ 0 := (hreg a).2.1
  obtain ⟨r, hX⟩ := he.2.2.2.1
  have hr : r < 0 ∨ 1 < r := by
    by_cases hr0 : r < 0
    · exact Or.inl hr0
    · right
      exact lt_of_not_ge (fun hr1 =>
        he.2.2.2.2.1 ⟨r, le_of_not_gt hr0, hr1, hX⟩)
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · simpa only [edge] using hω
  · simp
  · simp
  · simpa only [edgePoint, edge] using hX

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A proved zero jump on a common local radius implies equality at every
independently chosen pair of generic germ-side points. The helper exposes
its local-response premise and transports each side's full chirotope. -/
theorem tree_sides_equal_of_local_zero (w : WallGerm n) (g : ZMod n) (hn : 3 ≤ n)
    (δ : ℝ) (hδ : 0 < δ) (hδr : δ ≤ w.radius)
    (hresponse : ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
      |sMinus.val| < δ → |sPlus.val| < δ →
      treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
        treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0)
    (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn := by
  let q : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have hMinus : (w.sideTime false q).val < 0 := by change -(δ / 2) < 0; linarith
  have hPlus : 0 < (w.sideTime true q).val := by change 0 < δ / 2; linarith
  have hMinusNear : |(w.sideTime false q).val| < δ := by
    change |-(δ / 2)| < δ
    rw [abs_neg, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hPlusNear : |(w.sideTime true q).val| < δ := by
    change |δ / 2| < δ
    rw [abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have he : treeCoefficient (w.sideTuple true q).val (w.sideTuple true q).property.1 g hn =
      treeCoefficient (w.sideTuple false q).val (w.sideTuple false q).property.1 g hn :=
    sub_eq_zero.mp (hresponse (w.sideTime false q) (w.sideTime true q) hMinus hPlus hMinusNear hPlusNear)
  have hplusCoeff := treeCoefficient_eq_of_chi (w.sideTuple true q).property.1
    (w.sideTuple true t).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple true) q t i j k) g hn
  have hminusCoeff := treeCoefficient_eq_of_chi (w.sideTuple false q).property.1
    (w.sideTuple false s).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple false) q s i j k) g hn
  rw [hplusCoeff, hminusCoeff] at he
  exact he

end
end SM.WallGerm

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- At the exterior base root both full-span products vanish: their opposite
epsilons each place a zero nonleaf unit factor in the required product. -/
theorem extension_base_tree_silent_near (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 a hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 a hn = 0 := by
  let t := contactBaseTriple M a hn hc.1
  have hlabels := contactBaseTriple_labels M a hn hc.1
  have horder : CyclicContactBoundaryOrder a M a t := Or.inr (Or.inl hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet a} := by
    rw [contactBaseTriple_support]
    exact hc.2.1
  obtain ⟨r, hr, hω, hA, hB, hX⟩ := w.extension_exterior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges a M a t horder hc.2.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine a hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 1 r 0 hω
      ((congrArg w.center hlabels.1).trans hB)
      ((congrArg w.center hlabels.2.1).trans hX)
      ((congrArg w.center hlabels.2.2).trans hA)
      (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith) (by norm_num)
  have hgaps := contactBaseTriple_gaps M a hn hc.1
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hzero := integer_UV_products_zero_of_nonleaves_opposite w.center a t hZt hL hR
    (wallLeftEpsilon 1 r 0) (wallRightEpsilon 1 r 0) (extension_epsilons_base r hr)
  have hfull : ¬ t.spanInterval ≠ fullBoundaryInterval hn :=
    not_ne_iff.mpr (contactBaseTriple_full M a hn hc.1)
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have he := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_neg hfull, hzero.1, hzero.2, add_zero, mul_zero] at he
  exact he

/-- Every first-arc exterior root has positive right epsilon and a nonleaf
right gap, so the proper-span source product vanishes in both exterior ranges. -/
theorem extension_first_arc_tree_silent_near (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (hu : (g - M).val < contactDistance M a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  let t := contactFirstArcTriple g M a hn hc.1 hu
  have hlabels := contactFirstArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inl hlabels
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactFirstArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr, hω, hA, hB, hX⟩ := w.extension_exterior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) 0 1 r hω
      ((congrArg w.center hlabels.1).trans hA)
      ((congrArg w.center hlabels.2.1).trans hB)
      ((congrArg w.center hlabels.2.2).trans hX)
      (by norm_num) (by rcases hr with hr | hr <;> linarith) (by rcases hr with hr | hr <;> linarith)
  have hgaps := contactFirstArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hR : 2 ≤ t.rightInterval.leaves := by dsimp only [t]; omega
  have hε := extension_right_epsilon_first_arc r hr
  have hzero := integer_U_product_zero_of_right_nonleaf_pos w.center g t hZt hR (wallLeftEpsilon 0 1 r)
  have hproper := contactFirstArcTriple_proper g M a hn hc.1 hu
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have he := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_pos hproper, hε, hzero, zero_mul, mul_zero] at he
  exact he

/-- Every second-arc exterior root has positive left epsilon and a nonleaf
left gap. Root endpoints are retained by the exact index-domain inequality. -/
theorem extension_second_arc_tree_silent_near (w : WallGerm n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (hu : contactDistance M a < (g - M).val) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  let t := contactSecondArcTriple g M a hn hc.1 hu
  have hlabels := contactSecondArcTriple_labels g M a hn hc.1 hu
  have horder : CyclicContactBoundaryOrder g M a t := Or.inr (Or.inr hlabels)
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [contactSecondArcTriple_support]
    exact hc.2.1
  obtain ⟨r, hr, hω, hA, hB, hX⟩ := w.extension_exterior_affine M a hn hc
  have hchange := w.contact_boundary_chi_signChanges g M a t horder hc.2.2.2.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 hchange
      (w.center a) (w.center (a + 1) - w.center a) r 0 1 hω
      ((congrArg w.center hlabels.1).trans hX)
      ((congrArg w.center hlabels.2.1).trans hA)
      ((congrArg w.center hlabels.2.2).trans hB)
      (by rcases hr with hr | hr <;> linarith) (by norm_num) (by rcases hr with hr | hr <;> linarith)
  have hgaps := contactSecondArcTriple_gaps g M a hn hc.1 hu
  have hdist := contactDistance_bounds hn hc.1
  have hL : 2 ≤ t.leftInterval.leaves := by dsimp only [t]; omega
  have hε := extension_left_epsilon_second_arc r hr
  have hzero := integer_U_product_zero_of_left_nonleaf_pos w.center g t hZt hL (wallRightEpsilon r 0 1)
  have hproper := contactSecondArcTriple_proper g M a hn hc.1 hu
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have he := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_pos hproper, hε, hzero, zero_mul, mul_zero] at he
  exact he

/-- The exterior root cases are exhaustive, including every edge incident
to a critical vertex. No consecutive cusp/flat wall is added to the domain. -/
theorem extension_tree_silent_near (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (g : ZMod n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  by_cases hg : g = a
  · subst g
    exact w.extension_base_tree_silent_near M a hn hc
  · by_cases hu : (g - M).val < contactDistance M a
    · exact w.extension_first_arc_tree_silent_near g M a hn hc hu
    · have hne : (g - M).val ≠ contactDistance M a := by
        intro he
        apply hg
        apply sub_left_injective
        exact ZMod.val_injective n he
      have hs : contactDistance M a < (g - M).val := by omega
      exact w.extension_second_arc_tree_silent_near g M a hn hc hs

/-- Source exterior-extension silence for every root and arbitrary independent
points on the complete two sides, with no remaining radius restriction. -/
theorem extension_tree_silent (w : WallGerm n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : w.ExtensionAt M a) (g : ZMod n) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.extension_tree_silent_near M a hn hc g
  exact w.tree_sides_equal_of_local_zero g hn δ hδ hδr hresponse s t

end
end SM.WallGerm






namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A singleton left gap would put two consecutive physical labels in the
critical support. No exclusion of the first boundary position is assumed. -/
theorem pureCut_left_gap_nonleaf (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : 2 ≤ t.leftInterval.leaves := by
  have hlt : t.lower.val < t.middle.val := t.lower_middle
  by_contra hsmall
  have hnext : t.middle.val = t.lower.val + 1 := by
    change ¬ 2 ≤ t.middle.val - t.lower.val at hsmall
    omega
  have hadj : boundaryIndex g t.middle = boundaryIndex g t.lower + 1 := by
    change g + (t.middle.val : ZMod n) + 1 =
      (g + (t.lower.val : ZMod n) + 1) + 1
    rw [hnext, Nat.cast_add, Nat.cast_one]
    ring
  apply h (boundaryIndex g t.lower)
  · rw [t.vertexSet_reversed g]
    simp
  · rw [← hadj, t.vertexSet_reversed g]
    simp

/-- A singleton right gap also forces consecutive physical critical labels.
The last boundary position remains available as an individual endpoint. -/
theorem pureCut_right_gap_nonleaf (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : 2 ≤ t.rightInterval.leaves := by
  have hlt : t.middle.val < t.upper.val := t.middle_upper
  by_contra hsmall
  have hnext : t.upper.val = t.middle.val + 1 := by
    change ¬ 2 ≤ t.upper.val - t.middle.val at hsmall
    omega
  have hadj : boundaryIndex g t.upper = boundaryIndex g t.middle + 1 := by
    change g + (t.upper.val : ZMod n) + 1 =
      (g + (t.middle.val : ZMod n) + 1) + 1
    rw [hnext, Nat.cast_add, Nat.cast_one]
    ring
  apply h (boundaryIndex g t.middle)
  · rw [t.vertexSet_reversed g]
    simp
  · rw [← hadj, t.vertexSet_reversed g]
    simp

/-- The source's third cyclic gap bound. Only the simultaneous extreme
positions would give a singleton wrap gap, namely the actual root g to g+1. -/
theorem pureCut_wrap_gap_nonleaf (g : ZMod n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : 2 ≤ n + t.lower.val - t.upper.val := by
  have hu : t.upper.val < n := t.upper.isLt
  have hn : 0 < n := NeZero.pos n
  by_contra hsmall
  have hlower : t.lower.val = 0 := by omega
  have hupper : t.upper.val = n - 1 := by omega
  have hsum : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by simp
      _ = (n : ZMod n) := congrArg (fun k : ℕ => (k : ZMod n)) (Nat.sub_add_cancel hn)
      _ = 0 := ZMod.natCast_self n
  have hlast : boundaryIndex g t.upper = g := by
    change g + (t.upper.val : ZMod n) + 1 = g
    rw [hupper, add_assoc, hsum, add_zero]
  have hfirst : boundaryIndex g t.lower = g + 1 := by
    simp only [boundaryIndex, hlower, Nat.cast_zero, add_zero]
  have hadj : boundaryIndex g t.upper + 1 = boundaryIndex g t.lower := by
    rw [hlast, hfirst]
  apply h (boundaryIndex g t.upper)
  · rw [t.vertexSet_reversed g]
    simp
  · rw [hadj, t.vertexSet_reversed g]
    simp

/-- A pure-cut critical span is proper in every root reading, including
readings with lower=0 or upper=n-1 separately. Only their conjunction is ruled out. -/
theorem pureCut_span_proper (g : ZMod n) (hn : 3 ≤ n) (t : IncreasingBoundaryTriple n)
    (h : NoConsecutive (t.vertexSet g)) : t.spanInterval ≠ fullBoundaryInterval hn := by
  intro he
  have hl := congrArg (fun J : BoundaryInterval n => J.left.val) he
  have hu := congrArg (fun J : BoundaryInterval n => J.right.val) he
  dsimp [IncreasingBoundaryTriple.spanInterval, fullBoundaryInterval] at hl hu
  have hwrap := pureCut_wrap_gap_nonleaf g t h
  rw [hl, hu] at hwrap
  omega

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every pure-cut root has two nonleaf gaps and a proper critical span.
One positive epsilon annihilates the source product for every line order;
no equality of the individual open sums is asserted. -/
theorem pure_cut_tree_silent_near (w : WallGerm n) (i j k : ZMod n)
    (hn : 3 ≤ n) (hc : w.PureCutAt i j k) (g : ZMod n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g hn -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g hn = 0 := by
  have hcard : ({i, j, k} : Finset (ZMod n)).card = 3 := (singlePointTriple_data hc.2.1).1
  have hn6 := noConsecutive_size hcard hc.1
  have hinj := singlePointTriple_vertices_injective (by omega : 4 ≤ n) hc.2.1
  have hsep : (({i, j, k} : Finset (ZMod n)) : Set (ZMod n)).Pairwise
      (fun a b => w.center a ≠ w.center b) := by
    intro a ha b hb hab
    exact hinj.ne hab
  obtain ⟨t, ht, huniq⟩ := w.single_triple_boundary_data g {i, j, k} hc.2.1 hsep i j k rfl hc.2.2.2
  have hZt : pointZeroTriples w.center = {t.vertexSet g} := by
    rw [ht.1]
    exact hc.2.1
  have hnc : NoConsecutive (t.vertexSet g) := by rw [ht.1]; exact hc.1
  obtain ⟨p, ω, x, y, z, hω, hx, hy, hz, hyx, hzy, hzx⟩ :=
    critical_boundary_affine_data w.center g t hZt ht.2.1.1 ht.2.1.2.1 ht.2.1.2.2
  obtain ⟨d, hd, δ, hδ, hδr, hresponse⟩ :=
    w.single_triple_integer_response_of_affine g hn t hZt hc.2.2.1 ht.2.2
      p ω x y z hω hx hy hz hyx hzy hzx
  have hL := pureCut_left_gap_nonleaf g t hnc
  have hR := pureCut_right_gap_nonleaf g t hnc
  have hproper := pureCut_span_proper g hn t hnc
  have hzero := integer_U_product_zero_of_nonleaves_one_positive w.center g t hZt hL hR
    (wallLeftEpsilon x y z) (wallRightEpsilon x y z) (wall_epsilon_positive x y z hzx)
  refine ⟨δ, hδ, hδr, ?_⟩
  intro sMinus sPlus hMinus hPlus hnearMinus hnearPlus
  have hr := (hresponse sMinus sPlus hMinus hPlus hnearMinus hnearPlus).2
  rw [dif_pos hproper, hzero, zero_mul, mul_zero] at hr
  exact hr

/-- Source pure-cut silence for every physical root and arbitrary independent
points on the two germ sides, with no remaining radius restriction. -/
theorem pure_cut_tree_silent (w : WallGerm n) (i j k : ZMod n)
    (hn : 3 ≤ n) (hc : w.PureCutAt i j k) (g : ZMod n) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
      treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn := by
  obtain ⟨δ, hδ, hδr, hresponse⟩ := w.pure_cut_tree_silent_near i j k hn hc g
  exact w.tree_sides_equal_of_local_zero g hn δ hδ hδr hresponse s t

end
end SM.WallGerm

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- At a G1 center every chirotope on either entire generic germ side agrees
with its central value. Repeated labels are handled separately, without
requiring the nongeneric wall center to be a generic tuple. -/
theorem g1_center_side_chi (w : WallGerm n) (hG1 : G1 w.center) :
    ∀ b : Bool, ∀ t : w.SideParameter, ∀ i j k : ZMod n,
      chi (w.sideTuple b t).val i j k = chi w.center i j k := by
  have hnear := w.continuous_curve.continuousAt.eventually
    (finite_nonzero_chi_persists (P := w.center))
  obtain ⟨δ, hδ, hδr, hlocal⟩ := (w.eventually_center_iff_radius _).mp hnear
  let q : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  have hq : q.val < δ := by dsimp [q]; linarith
  intro b t i j k
  by_cases hij : i = j
  · subst j
    simp
  by_cases hjk : j = k
  · subst k
    simp
  by_cases hik : i = k
  · subst k
    simp
  have habs : |(w.sideTime b q).val| = q.val := by
    cases b <;> simp [sideTime, abs_of_pos q.property.1]
  have hc := hlocal (w.sideTime b q) (by rw [habs]; exact hq) i j k (hG1 i j k hij hjk hik)
  exact (generic_family_chi_constant (w.continuous_sideTuple b) t q i j k).trans hc

/-- Source thm:A-R3E(i): every ordinary/root composition weight, every open
sum and the complete rooted output agree at a triple wall. Both side points
and the physical root are arbitrary; G1 at the center is derived. -/
theorem triple_wall_tree_data (w : WallGerm n) (e f k : ZMod n)
    (hn : 3 ≤ n) (ht : w.TripleAt e f k) (g : ZMod n) (s t : w.SideParameter) :
    TreeDataEqual (w.sideTuple true t).val (w.sideTuple false s).val
      (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 g hn := by
  have hc : G1 w.center := (w.pointZeros_empty_iff).mp ht.1
  have hchi : ∀ i j k, chi (w.sideTuple true t).val i j k =
      chi (w.sideTuple false s).val i j k := by
    intro i j k
    exact (w.g1_center_side_chi hc true t i j k).trans (w.g1_center_side_chi hc false s i j k).symm
  exact tree_data_eq_of_chi (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 hchi g hn

end
end SM.WallGerm

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Source thm:A-R3E, all clauses. At a triple wall the complete data includes
every ordinary/root composition weight, every open sum, and the rooted output.
Exterior-extension and pure-cut walls assert only equality of the complete
output. Every physical root and both independent full germ-side parameters
remain quantified; no local-radius or child-genericity premise is added. -/
theorem tree_triple_and_silent_laws (hn : 3 ≤ n) :
    (∀ (w : WallGerm n) (e f k : ZMod n), w.TripleAt e f k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        TreeDataEqual (w.sideTuple true t).val (w.sideTuple false s).val
          (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (M a : ZMod n), w.ExtensionAt M a →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (i j k : ZMod n), w.PureCutAt i j k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w e f k ht g s t
    exact w.triple_wall_tree_data e f k hn ht g s t
  · intro w M a he g s t
    exact w.extension_tree_silent M a hn he g s t
  · intro w i j k hc g s t
    exact w.pure_cut_tree_silent i j k hn hc g s t

end
end SM


namespace SM

open Set
noncomputable section
variable {X Y : Type*} [TopologicalSpace X]

/-- Pairwise constancy on the dense domain in a neighborhood of every point
constructs a unique locally constant extension. Every neighborhood premise
is explicit; this helper does not assume a silent-wall response. -/
theorem dense_local_pairs_extend (S : Set X) (hd : Dense S) (f : S → Y)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ a b : S, a.val ∈ U → b.val ∈ U → f a = f b) :
    ∃! F : X → Y, IsLocallyConstant F ∧ ∀ a : S, F a.val = f a := by
  classical
  choose U hU hx hpair using hlocal
  have hpoint : ∀ x : X, ∃ a : S, a.val ∈ U x := by
    intro x
    obtain ⟨y, hyS, hyU⟩ := hd.exists_mem_open (hU x) ⟨x, hx x⟩
    exact ⟨⟨y, hyS⟩, hyU⟩
  choose a ha using hpoint
  let F : X → Y := fun x => f (a x)
  have hvalue : ∀ x : X, ∀ b : S, b.val ∈ U x → f b = F x := by
    intro x b hb
    exact hpair x b (a x) hb (ha x)
  have hF : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_exists_open F).mpr
    intro x
    refine ⟨U x, hU x, hx x, ?_⟩
    intro y hy
    obtain ⟨z, hzS, hz⟩ := hd.exists_mem_open ((hU x).inter (hU y)) ⟨y, hy, hx y⟩
    exact (hvalue y ⟨z, hzS⟩ hz.2).symm.trans (hvalue x ⟨z, hzS⟩ hz.1)
  have hagree : ∀ b : S, F b.val = f b := fun b => (hvalue b.val b (hx b.val)).symm
  refine ⟨F, ⟨hF, hagree⟩, ?_⟩
  intro G hG
  funext x
  obtain ⟨U, hU, hxU, hGU⟩ := hG.1.exists_open x
  obtain ⟨V, hV, hxV, hFV⟩ := hF.exists_open x
  obtain ⟨z, hzS, hz⟩ := hd.exists_mem_open (hU.inter hV) ⟨x, hxU, hxV⟩
  calc
    G x = G z := (hGU z hz.1).symm
    _ = f ⟨z, hzS⟩ := hG.2 ⟨z, hzS⟩
    _ = F z := (hagree ⟨z, hzS⟩).symm
    _ = F x := hFV z hz.2

/-- On a connected parameter domain the preceding genuine extension is
constant, so all original dense-domain values agree. -/
theorem dense_local_pairs_constant [PreconnectedSpace X]
    (S : Set X) (hd : Dense S) (f : S → Y)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ a b : S, a.val ∈ U → b.val ∈ U → f a = f b) :
    ∀ a b : S, f a = f b := by
  obtain ⟨F, hF, huniq⟩ := dense_local_pairs_extend S hd f hlocal
  intro a b
  have he := hF.1.apply_eq_of_preconnectedSpace a.val b.val
  rw [hF.2 a, hF.2 b] at he
  exact he

end
end SM

namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A weakly generic center has no zero turn, whereas an actual flat wall
has its specified central turn equal to zero. -/
theorem weak_center_not_flat (w : WallGerm n) (hw : WeakGeneric w.center)
    (j : ZMod n) : ¬ w.FlatAt j := by
  intro hf
  exact hw.2.1 j (singlePointTriple_turn_zero hf.2.1)

/-- The same nonzero-turn condition excludes the actual cusp predicate,
without requiring a loop-side choice or any extra regularity hypothesis. -/
theorem weak_center_not_cusp (w : WallGerm n) (hw : WeakGeneric w.center)
    (j : ZMod n) : ¬ w.CuspAt j := by
  intro hc
  exact hw.2.1 j (singlePointTriple_turn_zero hc.2.1)

/-- The contact label is nonincident to the contacted edge. Its actual
interior point is therefore also a forbidden point on that closed segment. -/
theorem weak_center_not_vertex (w : WallGerm n) (hw : WeakGeneric w.center)
    (M a : ZMod n) : ¬ w.VertexEdgeAt M a := by
  intro hv
  have hnon : ¬ incident M a := by
    rintro (ha | ha)
    · exact hv.1.2.2.1 (by rw [ha, sub_add_cancel])
    · exact hv.1.2.1 ha.symm
  obtain ⟨r, hr0, hr1, hX⟩ := hv.2.2.2.1
  exact hw.2.2.1 M a hnon ⟨r, le_of_lt hr0, le_of_lt hr1, hX⟩

/-- The specified central concurrence supplies three distinct edge labels
and one common interior point, contradicting the actual G2 clause of WeakGeneric. -/
theorem weak_center_not_triple (w : WallGerm n) (hw : WeakGeneric w.center)
    (e f k : ZMod n) : ¬ w.TripleAt e f k := by
  intro ht
  have hm : ({e, f, k} : Finset (ZMod n)) ∈ w.concurrences := by
    rw [ht.2.1]
    simp
  have hc := (w.mem_concurrences {e, f, k}).mp hm
  have hne := Finset.card_triple_eq_three_iff.mp hc.1
  obtain ⟨x, hx⟩ := hc.2.2
  exact hw.2.2.2.2 ⟨e, f, k, x, hne.1, hne.2.2, hne.2.1,
    hx e (by simp), hx f (by simp), hx k (by simp)⟩

/-- In the continuation argument a simple event whose actual center remains
weakly generic can only be an exterior extension or pure cut. All other wall
exclusions are derived here; none is a caller-supplied premise. -/
theorem silent_of_simple_weak_center (w : WallGerm n) (hn : 3 ≤ n)
    (hs : w.Simple) (hw : WeakGeneric w.center) : w.Silent := by
  obtain ⟨kind, hk⟩ := hs
  cases kind with
  | flat =>
      obtain ⟨j, hj⟩ := hk
      exact (w.weak_center_not_flat hw j hj).elim
  | cusp =>
      obtain ⟨j, hj⟩ := hk
      exact (w.weak_center_not_cusp hw j hj).elim
  | vertex =>
      obtain ⟨M, a, hv⟩ := hk
      exact (w.weak_center_not_vertex hw M a hv).elim
  | triple =>
      obtain ⟨e, f, k, ht⟩ := hk
      exact (w.weak_center_not_triple hw e f k ht).elim
  | extension => exact Or.inl hk
  | cut => exact Or.inr hk

end
end SM.WallGerm

namespace SM

open Set
noncomputable section
variable {n : ℕ} [NeZero n]

/-- A shifted wall germ on the actual path agrees with that path at every
point in its radius, using the exact parameter identity rather than endpoints. -/
theorem WallGerm.shifted_curve_eq_path (w : WallGerm n)
    (p : unitInterval → LabelledTuple n) (t : unitInterval)
    (hcurve : ∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      w.curve s = p ⟨(t : ℝ) + s.val, hs⟩)
    (u : unitInterval) (hu : |(u : ℝ) - (t : ℝ)| < w.radius) :
    w.curve ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hu⟩ = p u := by
  obtain ⟨hs, he⟩ := hcurve ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hu⟩
  have htu : (⟨(t : ℝ) + ((u : ℝ) - (t : ℝ)), hs⟩ : unitInterval) = u := by
    apply Subtype.ext
    dsimp
    ring
  rw [htu] at he
  exact he

/-- Actual punctured-generic germs at every nongeneric path parameter ensure
density of generic parameters, including the interval endpoints. No finite
set is asserted empty, and no independent density hypothesis is required. -/
theorem generic_path_dense_of_germs (p : unitInterval → LabelledTuple n)
    (hevent : ∀ t : unitInterval, ¬ Generic (p t) → ∃ w : WallGerm n,
      ∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
        w.curve s = p ⟨(t : ℝ) + s.val, hs⟩) :
    Dense {t : unitInterval | Generic (p t)} := by
  intro t
  by_cases ht : Generic (p t)
  · exact subset_closure ht
  obtain ⟨w, hcurve⟩ := hevent t ht
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let q : ℝ := min w.radius ε / 2
  have hq0 : 0 < q := div_pos (lt_min w.radius_pos hε) (by norm_num)
  have hqr : q < w.radius := by dsimp [q]; linarith [min_le_left w.radius ε, w.radius_pos]
  have hqε : q < ε := by dsimp [q]; linarith [min_le_right w.radius ε]
  let s : w.Parameter := ⟨q, by constructor <;> linarith [w.radius_pos]⟩
  obtain ⟨hs, he⟩ := hcurve s
  let u : unitInterval := ⟨(t : ℝ) + s.val, hs⟩
  have hgu : Generic (p u) := by
    rw [← he]
    exact w.generic_punctured s (ne_of_gt hq0)
  refine ⟨u, hgu, ?_⟩
  change dist (t : ℝ) ((t : ℝ) + q) < ε
  rw [Real.dist_eq]
  have hsub : (t : ℝ) - ((t : ℝ) + q) = -q := by ring
  rw [hsub, abs_neg, abs_of_pos hq0]
  exact hqε

end
end SM

namespace SM

open Set
noncomputable section
variable {n : ℕ} [NeZero n]

/-- A compact actual path in an open set has one positive Euclidean tolerance
that keeps every uniformly close path inside that set. -/
theorem euclidean_path_open_tolerance (γ : unitInterval → LabelledTuple n)
    (hγ : Continuous γ) (S : Set (LabelledTuple n)) (hS : IsOpen S)
    (hγS : ∀ t, γ t ∈ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : unitInterval → LabelledTuple n,
      (∀ t, dist (tupleCoordinates (p t)) (tupleCoordinates (γ t)) < δ) →
      ∀ t, p t ∈ S := by
  let K := Set.range (fun t => tupleCoordinates (γ t))
  have hK : IsCompact K := isCompact_range (continuous_tupleCoordinates.comp hγ)
  have hopen : IsOpen (coordinatesTuple ⁻¹' S) := hS.preimage continuous_coordinatesTuple
  have hsub : K ⊆ coordinatesTuple ⁻¹' S := by
    rintro z ⟨t, rfl⟩
    simpa only [mem_preimage, coordinatesTuple_tupleCoordinates] using hγS t
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hopen hsub
  refine ⟨δ, hδ, ?_⟩
  intro p hclose t
  have hmem : tupleCoordinates (p t) ∈ Metric.thickening δ K :=
    Metric.mem_thickening_iff.mpr ⟨tupleCoordinates (γ t), Set.mem_range_self t, hclose t⟩
  have hz := hthick hmem
  simpa only [mem_preimage, coordinatesTuple_tupleCoordinates] using hz

/-- Relative general position inside the actual weak locus. The positive
error tolerance and all weak membership are derived from the input path;
the caller does not supply a path or event-exclusion certificate. -/
theorem weak_relative_general_position (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hw : ∀ t, WeakGeneric (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ D : RelativeGeneralPositionPath γ δ,
      ∀ t, WeakGeneric (D.path t) := by
  obtain ⟨δ, hδ, hstay⟩ := euclidean_path_open_tolerance γ hγ (weakLocus n)
    isOpen_WeakGeneric hw
  obtain ⟨D⟩ := relative_general_position hn γ hγ
    (fun t => nonzero_turns_regular (hw t).2.1) hfirst hlast δ hδ
  exact ⟨δ, hδ, D, hstay D.path D.close⟩

end
end SM

namespace SM

open Set Filter Topology
noncomputable section
variable {n : ℕ} [NeZero n]

/-- At an actual G1 tuple every chi value persists simultaneously; repeated
labels are proved zero separately, rather than included in the G1 premise. -/
theorem g1_all_chi_persists {P : LabelledTuple n} (hP : G1 P) :
    ∀ᶠ Q in 𝓝 P, ∀ i j k : ZMod n, chi Q i j k = chi P i j k := by
  filter_upwards [finite_nonzero_chi_persists (P := P)] with Q hQ
  intro i j k
  by_cases hij : i = j
  · subst j; simp
  by_cases hjk : j = k
  · subst k; simp
  by_cases hik : i = k
  · subst k; simp
  exact hQ i j k (hP i j k hij hjk hik)

/-- Generic path values have pairwise constancy in an actual open parameter
neighborhood of any G1 point, with every physical root retained. -/
theorem tree_path_pair_near_generic {X : Type*} [TopologicalSpace X]
    (p : X → LabelledTuple n) (hp : Continuous p) (x : X) (hxG : G1 (p x))
    (g : ZMod n) (hn : 3 ≤ n) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ a b : {t : X // Generic (p t)}, a.val ∈ U → b.val ∈ U →
        treeCoefficient (p a.val) a.property.1 g hn =
          treeCoefficient (p b.val) b.property.1 g hn := by
  have hnear := hp.continuousAt.eventually (g1_all_chi_persists hxG)
  obtain ⟨U, hsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, hU, hxU, ?_⟩
  intro a b ha hb
  apply treeCoefficient_eq_of_chi a.property.1 b.property.1
  intro i j k
  exact (hsub ha i j k).trans (hsub hb i j k).symm

/-- Actual generic side constancy, with the same physical root. -/
theorem WallGerm.tree_coefficient_same_side (w : WallGerm n)
    (g : ZMod n) (hn : 3 ≤ n) (b : Bool) (s t : w.SideParameter) :
    treeCoefficient (w.sideTuple b s).val (w.sideTuple b s).property.1 g hn =
      treeCoefficient (w.sideTuple b t).val (w.sideTuple b t).property.1 g hn :=
  treeCoefficient_eq_of_chi (w.sideTuple b s).property.1 (w.sideTuple b t).property.1
    (fun i j k => generic_family_chi_constant (w.continuous_sideTuple b) s t i j k) g hn

/-- A proved equality across the two full sides identifies any punctured
parameter value with the positive-side value. The cross-side premise is
explicit here and must be proved from the named wall in applications. -/
theorem WallGerm.tree_parameter_eq_positive_of_sides_equal (w : WallGerm n)
    (g : ZMod n) (hn : 3 ≤ n)
    (hsides : ∀ s t : w.SideParameter,
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
        treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn)
    (u : w.Parameter) (hu : u.val ≠ 0) (t : w.SideParameter) :
    treeCoefficient (w.curve u) (w.generic_punctured u hu).1 g hn =
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn := by
  by_cases hp : 0 < u.val
  · let q : w.SideParameter := ⟨u.val, hp, u.property.2⟩
    have he := w.tree_coefficient_same_side g hn true q t
    have htime : w.sideTime true q = u := Subtype.ext rfl
    have hval : (w.sideTuple true q).val = w.curve u := congrArg w.curve htime
    have htuple : w.sideTuple true q =
        (⟨w.curve u, w.generic_punctured u hu⟩ : GenericTuple n) := Subtype.ext hval
    have hcoeff := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple
    exact hcoeff.symm.trans he
  · have hnz : u.val < 0 := lt_of_le_of_ne (le_of_not_gt hp) hu
    let q : w.SideParameter := ⟨-u.val, by constructor <;> linarith [u.property.1]⟩
    have he := (hsides q t).symm
    have htime : w.sideTime false q = u := by
      apply Subtype.ext
      change -(-u.val) = u.val
      ring
    have hval : (w.sideTuple false q).val = w.curve u := congrArg w.curve htime
    have htuple : w.sideTuple false q =
        (⟨w.curve u, w.generic_punctured u hu⟩ : GenericTuple n) := Subtype.ext hval
    have hcoeff := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple
    exact hcoeff.symm.trans he

end
end SM

namespace SM

open Set
noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every actual silent wall has a common value at all punctured parameters.
The cross-side law is derived from the named E/C predicates here. -/
theorem WallGerm.silent_tree_parameter_value (w : WallGerm n)
    (g : ZMod n) (hn : 3 ≤ n) (hs : w.Silent)
    (u : w.Parameter) (hu : u.val ≠ 0) (t : w.SideParameter) :
    treeCoefficient (w.curve u) (w.generic_punctured u hu).1 g hn =
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn := by
  apply w.tree_parameter_eq_positive_of_sides_equal g hn ?_ u hu t
  intro a b
  rcases hs with ⟨M, e, he⟩ | ⟨i, j, k, hc⟩
  · exact w.extension_tree_silent M e hn he g a b
  · exact w.pure_cut_tree_silent i j k hn hc g a b

/-- The actual shifted silent germ gives pairwise equality of generic path
values in a full open parameter neighborhood of the event. -/
theorem tree_path_pair_near_silent_event (p : unitInterval → LabelledTuple n)
    (x : unitInterval) (w : WallGerm n) (hcenter : w.center = p x)
    (hcurve : ∀ s : w.Parameter, ∃ hs : (x : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
      w.curve s = p ⟨(x : ℝ) + s.val, hs⟩)
    (hs : w.Silent) (g : ZMod n) (hn : 3 ≤ n) :
    ∃ U : Set unitInterval, IsOpen U ∧ x ∈ U ∧
      ∀ a b : {t : unitInterval // Generic (p t)}, a.val ∈ U → b.val ∈ U →
        treeCoefficient (p a.val) a.property.1 g hn =
          treeCoefficient (p b.val) b.property.1 g hn := by
  have hxNG : ¬ Generic (p x) := by rw [← hcenter]; exact w.nongeneric_center
  have hvalue : ∀ a : {t : unitInterval // Generic (p t)}, a.val ∈ Metric.ball x w.radius →
      treeCoefficient (p a.val) a.property.1 g hn =
        treeCoefficient (w.sideTuple true w.sideBase).val
          (w.sideTuple true w.sideBase).property.1 g hn := by
    intro a ha
    have hdist : |(a.val : ℝ) - (x : ℝ)| < w.radius := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using ha
    let u : w.Parameter := ⟨(a.val : ℝ) - (x : ℝ), abs_lt.mp hdist⟩
    have hu : u.val ≠ 0 := by
      intro he
      have hax : a.val = x := Subtype.ext (sub_eq_zero.mp he)
      apply hxNG
      rw [← hax]
      exact a.property
    have he := w.silent_tree_parameter_value g hn hs u hu w.sideBase
    have hpath : w.curve u = p a.val := w.shifted_curve_eq_path p x hcurve a.val hdist
    have htuple : (⟨w.curve u, w.generic_punctured u hu⟩ : GenericTuple n) =
        ⟨p a.val, a.property⟩ := Subtype.ext hpath
    have hcoeff := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple
    exact hcoeff.symm.trans he
  refine ⟨Metric.ball x w.radius, Metric.isOpen_ball, Metric.mem_ball_self w.radius_pos, ?_⟩
  intro a b ha hb
  exact (hvalue a ha).trans (hvalue b hb).symm

/-- The generic values of an actual continuous path agree when every
nongeneric parameter has its actual shifted silent germ. Density and
local-pair constancy are proved, not supplied as abstract placeholders. -/
theorem tree_path_constant_of_silent_germs (p : unitInterval → LabelledTuple n)
    (hp : Continuous p)
    (hevent : ∀ x : unitInterval, ¬ Generic (p x) → ∃ w : WallGerm n,
      w.center = p x ∧
      (∀ s : w.Parameter, ∃ hs : (x : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
        w.curve s = p ⟨(x : ℝ) + s.val, hs⟩) ∧ w.Silent)
    (g : ZMod n) (hn : 3 ≤ n)
    (a b : {t : unitInterval // Generic (p t)}) :
    treeCoefficient (p a.val) a.property.1 g hn =
      treeCoefficient (p b.val) b.property.1 g hn := by
  let S : Set unitInterval := {t | Generic (p t)}
  let f : S → ℤ := fun t => treeCoefficient (p t.val) t.property.1 g hn
  have hd : Dense S := generic_path_dense_of_germs p (by
    intro x hx
    obtain ⟨w, hc, hcurve, hs⟩ := hevent x hx
    exact ⟨w, hcurve⟩)
  have hlocal : ∀ x : unitInterval, ∃ U : Set unitInterval, IsOpen U ∧ x ∈ U ∧
      ∀ a b : S, a.val ∈ U → b.val ∈ U → f a = f b := by
    intro x
    by_cases hx : Generic (p x)
    · exact tree_path_pair_near_generic p hp x hx.1 g hn
    · obtain ⟨w, hc, hcurve, hs⟩ := hevent x hx
      exact tree_path_pair_near_silent_event p x w hc hcurve hs g hn
  exact dense_local_pairs_constant S hd f hlocal a b

/-- Any actual weak-locus path with generic endpoints preserves the rooted
coefficient. Relative general position, weak membership and E/C classification
are all derived, with no R, silent-response or path-certificate premise. -/
theorem tree_coefficient_eq_along_weak_path (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hw : ∀ t, WeakGeneric (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1))
    (g : ZMod n) :
    treeCoefficient (γ 0) hfirst.1 g hn = treeCoefficient (γ 1) hlast.1 g hn := by
  obtain ⟨δ, hδ, D, hDw⟩ := weak_relative_general_position hn γ hγ hw hfirst hlast
  have hfirstD : Generic (D.path 0) := by rw [D.first]; exact hfirst
  have hlastD : Generic (D.path 1) := by rw [D.last]; exact hlast
  have he := tree_path_constant_of_silent_germs D.path D.continuous (by
    intro x hx
    obtain ⟨w, hc, hcurve, hs, hkind⟩ := D.event x hx
    have hw : WeakGeneric w.center := by rw [hc]; exact hDw x
    exact ⟨w, hc, hcurve, w.silent_of_simple_weak_center hn hs hw⟩)
    g hn ⟨0, hfirstD⟩ ⟨1, hlastD⟩
  have htuple0 : (⟨D.path 0, hfirstD⟩ : GenericTuple n) = ⟨γ 0, hfirst⟩ := Subtype.ext D.first
  have htuple1 : (⟨D.path 1, hlastD⟩ : GenericTuple n) = ⟨γ 1, hlast⟩ := Subtype.ext D.last
  have hc0 := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple0
  have hc1 := congrArg (fun P : GenericTuple n => treeCoefficient P.val P.property.1 g hn) htuple1
  exact hc0.symm.trans (he.trans hc1)

end
end SM

#check SM.WallGerm.silent_tree_parameter_value
#print axioms SM.WallGerm.silent_tree_parameter_value

#check SM.tree_path_pair_near_silent_event
#print axioms SM.tree_path_pair_near_silent_event

#check SM.tree_path_constant_of_silent_germs
#print axioms SM.tree_path_constant_of_silent_germs

#check SM.tree_coefficient_eq_along_weak_path
#print axioms SM.tree_coefficient_eq_along_weak_path
