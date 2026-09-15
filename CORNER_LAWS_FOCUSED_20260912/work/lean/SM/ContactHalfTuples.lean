import SM.ContactHalfSupport
import SM.ContactCenter

/-! The actual two source polygons at a central vertex-edge contact.
Their vertices are inherited with the source cyclic order and cut. -/

namespace SM

variable {n : ℕ} [NeZero n]

def firstHalf (P : LabelledTuple n) (M a : ZMod n) : LabelledTuple (firstHalfSize M a) :=
  fun i => P (firstHalfIndex M a i)

def secondHalf (P : LabelledTuple n) (M a : ZMod n) : LabelledTuple (secondHalfSize M a) :=
  fun i => P (secondHalfIndex M a i)

theorem firstHalf_zero (P : LabelledTuple n) (M a : ZMod n) : firstHalf P M a 0 = P M := by
  rw [firstHalf, firstHalfIndex_zero]

theorem firstHalf_last (P : LabelledTuple n) (M a : ZMod n) : firstHalf P M a (-1) = P a := by
  rw [firstHalf, firstHalfIndex_last]

theorem secondHalf_zero (P : LabelledTuple n) (M a : ZMod n) : secondHalf P M a 0 = P M := by
  rw [secondHalf, secondHalfIndex_zero]

theorem secondHalf_one (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    (P : LabelledTuple n) : secondHalf P M a 1 = P (a + 1) := by
  rw [secondHalf, secondHalfIndex_one hn h]

theorem secondHalf_last (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    (P : LabelledTuple n) : secondHalf P M a (-1) = P (M - 1) := by
  rw [secondHalf, secondHalfIndex_last hn h]

theorem edge_firstHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (firstHalfSize M a)} (hi : i ≠ -1) :
    edge (firstHalf P M a) i = edge P (firstHalfIndex M a i) := by
  simp only [edge, firstHalf, firstHalfIndex_next M a hi]

theorem edge_firstHalf_last (P : LabelledTuple n) (M a : ZMod n) :
    edge (firstHalf P M a) (-1) = P M - P a := by
  simp only [edge, neg_add_cancel, firstHalf_zero, firstHalf_last]

theorem edge_secondHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) :
    edge (secondHalf P M a) i = edge P (secondHalfEdgeIndex M a i) := by
  simp only [edge, secondHalf, secondHalfIndex_next M a hi, secondHalfIndex_nonzero M a hi]

theorem edge_secondHalf_zero (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    (P : LabelledTuple n) : edge (secondHalf P M a) 0 = P (a + 1) - P M := by
  simp only [edge, zero_add, secondHalf_one hn h, secondHalf_zero]

theorem g1_inherited_avoiding_point_zero {k : ℕ} {P : LabelledTuple n}
    (f : ZMod k → ZMod n) (hf : Function.Injective f) {z : Finset (ZMod n)}
    (hz : pointZeroTriples P = {z}) {missing : ZMod n} (hm : missing ∈ z)
    (hmiss : ∀ i, f i ≠ missing) : G1 (fun i => P (f i)) := by
  intro i j l hij hjl hil hc
  have hmemb : ({f i, f j, f l} : Finset (ZMod n)) ∈ pointZeroTriples P :=
    (mem_pointZeroTriples _ _).mpr ((pointZeroTriple_iff (hf.ne hij) (hf.ne hjl) (hf.ne hil)).mpr hc)
  rw [hz, Finset.mem_singleton] at hmemb
  rw [← hmemb] at hm
  rcases Finset.mem_insert.mp hm with he | hm
  · exact hmiss i he.symm
  · rcases Finset.mem_insert.mp hm with he | hm
    · exact hmiss j he.symm
    · exact hmiss l (Finset.mem_singleton.mp hm).symm

theorem g1_firstHalf (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} (hz : pointZeroTriples P = {contactSupport M a}) : G1 (firstHalf P M a) :=
  g1_inherited_avoiding_point_zero (firstHalfIndex M a) (firstHalfIndex_injective M a) hz
    (by simp [contactSupport] : a + 1 ∈ contactSupport M a) (firstHalfIndex_ne_base_successor hn h)

theorem g1_secondHalf (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} (hz : pointZeroTriples P = {contactSupport M a}) : G1 (secondHalf P M a) :=
  g1_inherited_avoiding_point_zero (secondHalfIndex M a) (secondHalfIndex_injective M a) hz
    (by simp [contactSupport] : a ∈ contactSupport M a) (secondHalfIndex_ne_base hn h)

end SM
