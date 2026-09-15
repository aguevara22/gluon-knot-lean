import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! Concrete coordinate and cyclic-quotient definitions for SM, Chapter 1.
No genericity, nonzero-edge condition, or distinguished vertex is built into
the tuple type. The source's n ≥ 3 restriction is explicit in `Polygon`.
Helpers on labelled tuples are also defined at smaller sizes. -/

namespace SM

abbrev Plane := ℝ × ℝ
abbrev LabelledTuple (n : ℕ) := ZMod n → Plane

def det (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1
def bracket (u v : Plane) : ℝ := u.2 * v.1 - u.1 * v.2

variable {n : ℕ}

/-- `shift 1` is precisely the source's sigma. -/
def shift (k : ZMod n) (P : LabelledTuple n) : LabelledTuple n :=
  fun i => P (i + k)

@[simp] theorem shift_zero (P : LabelledTuple n) : shift 0 P = P := by
  funext i
  simp [shift]

theorem shift_add (a b : ZMod n) (P : LabelledTuple n) :
    shift a (shift b P) = shift (a + b) P := by
  funext i
  simp [shift, add_assoc]

def cyclicSetoid (n : ℕ) : Setoid (LabelledTuple n) where
  r P Q := ∃ k : ZMod n, Q = shift k P
  iseqv := {
    refl := fun P => ⟨0, (shift_zero P).symm⟩
    symm := by
      rintro P Q ⟨k, rfl⟩
      refine ⟨-k, ?_⟩
      simp [shift_add]
    trans := by
      rintro P Q R ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨b + a, shift_add b a P⟩ }

/-- SM def:polygon: the cyclic orbit space, with no preferred label. -/
def Polygon (n : ℕ) (_hn : 3 ≤ n) := Quotient (cyclicSetoid n)

def edge (P : LabelledTuple n) (i : ZMod n) : Plane := P (i + 1) - P i

def edgePoint (P : LabelledTuple n) (i : ZMod n) (t : ℝ) : Plane :=
  P i + t • edge P i

def edgeSegment (P : LabelledTuple n) (i : ZMod n) : Set Plane :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = edgePoint P i t}

def edgeInterior (P : LabelledTuple n) (i : ZMod n) : Set Plane :=
  {x | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = edgePoint P i t}

def incident (vertexIndex edgeIndex : ZMod n) : Prop :=
  edgeIndex = vertexIndex - 1 ∨ edgeIndex = vertexIndex

def adjacent (i j : ZMod n) : Prop :=
  j - i = -1 ∨ j - i = 0 ∨ j - i = 1

def remote (i j : ZMod n) : Prop := ¬ adjacent i j

def remoteToVertex (i j : ZMod n) : Prop := ¬ incident i j

def remoteToVertexAndEdges (i j : ZMod n) : Prop :=
  j ≠ i - 2 ∧ j ≠ i - 1 ∧ j ≠ i ∧ j ≠ i + 1

theorem edge_shift (k : ZMod n) (P : LabelledTuple n) (i : ZMod n) :
    edge (shift k P) i = edge P (i + k) := by
  simp [edge, shift, add_assoc, add_comm, add_left_comm]

theorem edgePoint_shift (k : ZMod n) (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    edgePoint (shift k P) i t = edgePoint P (i + k) t := by
  simp [edgePoint, shift, edge_shift]

theorem edgeSegment_shift (k : ZMod n) (P : LabelledTuple n) (i : ZMod n) :
    edgeSegment (shift k P) i = edgeSegment P (i + k) := by
  simp only [edgeSegment, edgePoint_shift]

theorem sum_edges [NeZero n] (P : LabelledTuple n) :
    ∑ i : ZMod n, edge P i = 0 := by
  have hs : (∑ i : ZMod n, P (i + 1)) = ∑ i : ZMod n, P i :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) P
  simp only [edge, Finset.sum_sub_distrib, hs, sub_self]

/-- Review aggregate: binds every definition in source def:polygon to one
declaration hash. The zero edge-sum assertion is proved by `sum_edges`. -/
def polygonData (n : ℕ) (hn : 3 ≤ n) :=
  (Polygon n hn, shift (n := n), edge (n := n), edgeSegment (n := n),
    incident (n := n), adjacent (n := n), remote (n := n),
    remoteToVertex (n := n), remoteToVertexAndEdges (n := n))

end SM
