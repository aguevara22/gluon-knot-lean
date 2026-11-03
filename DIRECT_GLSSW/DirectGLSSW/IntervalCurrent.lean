import DirectGLSSW.Gates
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Concrete finite interval-current implementation

Source: `ep:Phi`, `ep:tree-recursion`. Indices are natural numbers, entries
are rational numbers, and every sum is finite. The recursive calls are
guarded by strict interval-length decrease. `CurrentFidelity` proves every
nonunary branch satisfies that guard and establishes the source array
equation and uniqueness for arbitrary size. Identification with the
original GLSSW marked-tree expansion remains a separate obligation.
-/

namespace DirectGLSSW
open scoped BigOperators

abbrev TripleArray := ℕ → ℕ → ℕ → ℚ
abbrev IntervalArray := ℕ → ℕ → ℚ

def cutVertices (i j : ℕ) (S : Finset ℕ) : List ℕ :=
  i :: S.sort (· ≤ ·) ++ [j]

def branchProduct (b : IntervalArray) (v : List ℕ) : ℚ :=
  ((v.zip v.tail).map fun (i, j) => b i j).prod

def gateProduct (D H : TripleArray) (i j : ℕ) (v : List ℕ) : ℚ :=
  ((v.zip (v.tail.zip v.tail.tail)).map fun (a, b, c) =>
    (D a b c - H i b j) / 2).prod

def cutContribution (D H : TripleArray) (b : IntervalArray)
    (i j : ℕ) (S : Finset ℕ) : ℚ :=
  gateProduct D H i j (cutVertices i j S) * branchProduct b (cutVertices i j S)

def phi (D H : TripleArray) (b : IntervalArray) (i j : ℕ) : ℚ :=
  ∑ S ∈ (Finset.Ioo i j).powerset, cutContribution D H b i j S

def nonUnary (D H : TripleArray) (b : IntervalArray) (i j : ℕ) : ℚ :=
  ∑ S ∈ (Finset.Ioo i j).powerset.erase ∅, cutContribution D H b i j S

def source (i j : ℕ) : ℚ := if j = i + 1 then 1 else 0

def ordinaryCurrent (D H : TripleArray) (i j : ℕ) : ℚ :=
  source i j - nonUnary D H
    (fun a b => if _h : b - a < j - i then ordinaryCurrent D H a b else 0) i j
termination_by j - i

/-- The marked map reverses H and retains its unary term. -/
def markedAmplitude (D H : TripleArray) (i j : ℕ) : ℚ :=
  phi D (fun a b c => -H a b c) (ordinaryCurrent D H) i j

@[simp] theorem cutContribution_empty (D H : TripleArray) (b : IntervalArray)
    (i j : ℕ) : cutContribution D H b i j ∅ = b i j := by
  simp [cutContribution, cutVertices, gateProduct, branchProduct]

/-- Exactly separates the retained unary term from all ordinary vertices. -/
theorem phi_eq_unary_add (D H : TripleArray) (b : IntervalArray) (i j : ℕ) :
    phi D H b i j = b i j + nonUnary D H b i j := by
  unfold phi nonUnary
  have h : (∅ : Finset ℕ) ∈ (Finset.Ioo i j).powerset := by simp
  rw [← Finset.add_sum_erase _ _ h]
  rw [cutContribution_empty]

/-- The ordinary one-edge current is exactly the unit source. -/
@[simp] theorem ordinaryCurrent_adjacent (D H : TripleArray) (i : ℕ) :
    ordinaryCurrent D H i (i + 1) = 1 := by
  have he : Finset.Ioo i (i + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro a ha
    simp only [Finset.mem_Ioo] at ha
    omega
  rw [ordinaryCurrent]
  simp [nonUnary, source, he]

/-- The only nonunary cut of a two-edge interval is its middle vertex. -/
theorem nonUnary_two (D H : TripleArray) (b : IntervalArray) (i : ℕ) :
    nonUnary D H b i (i + 2) =
      (D i (i + 1) (i + 2) - H i (i + 1) (i + 2)) / 2 *
        b i (i + 1) * b (i + 1) (i + 2) := by
  have he : Finset.Ioo i (i + 2) = {i + 1} := by
    ext a
    simp only [Finset.mem_Ioo, Finset.mem_singleton]
    omega
  have hp : ({i + 1} : Finset ℕ).powerset = {∅, {i + 1}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  have hps : ({∅, {i + 1}} : Finset (Finset ℕ)).erase ∅ = {{i + 1}} := by
    ext S
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, heq | heq⟩
      · exact False.elim (hn heq)
      · exact heq
    · intro heq
      subst S
      exact ⟨Finset.singleton_ne_empty _, Or.inr rfl⟩
  simp [nonUnary, he, hp, hps, cutContribution, cutVertices, gateProduct, branchProduct]
  ring

theorem ordinaryCurrent_two (D H : TripleArray) (i : ℕ) :
    ordinaryCurrent D H i (i + 2) =
      -(D i (i + 1) (i + 2) - H i (i + 1) (i + 2)) / 2 := by
  have hg : i + 2 - (i + 1) < 2 := by omega
  rw [ordinaryCurrent, nonUnary_two]
  norm_num [source, hg, Nat.add_assoc]
  ring

/-- Symbolic normalization check: the actual implemented marked current
on a triangle is its far sign, independently of all near data. -/
theorem markedAmplitude_triangle (D H : TripleArray) (i : ℕ) :
    markedAmplitude D H i (i + 2) = H i (i + 1) (i + 2) := by
  unfold markedAmplitude
  rw [phi_eq_unary_add, ordinaryCurrent_two, nonUnary_two]
  norm_num [Nat.add_assoc]
  ring

end DirectGLSSW
