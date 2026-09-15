import SM.Generic
import Mathlib.Tactic

namespace SM

variable {n : ℕ} [NeZero n]

def boundaryIndex (g : ZMod n) (k : Fin n) : ZMod n :=
  g + (k.val : ZMod n) + 1

def boundaryWord (P : LabelledTuple n) (g : ZMod n) (k : Fin n) : Plane :=
  P (boundaryIndex g k)

theorem boundaryIndex_injective (g : ZMod n) : Function.Injective (boundaryIndex g) := by
  intro i j he
  have hc : (i.val : ZMod n) = (j.val : ZMod n) :=
    add_left_cancel (add_right_cancel he)
  apply Fin.ext
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using hv

theorem boundaryWord_shift (P : LabelledTuple n) (g a : ZMod n) :
    boundaryWord (shift a P) (g - a) = boundaryWord P g := by
  funext k
  change P (g - a + (k.val : ZMod n) + 1 + a) = P (g + (k.val : ZMod n) + 1)
  congr 1
  ring

theorem boundaryWord_first (P : LabelledTuple n) (g : ZMod n) (hn : 0 < n) :
    boundaryWord P g ⟨0, hn⟩ = P (g + 1) := by
  simp [boundaryWord, boundaryIndex]

theorem boundaryWord_last (P : LabelledTuple n) (g : ZMod n) (hn : 0 < n) :
    boundaryWord P g ⟨n - 1, by omega⟩ = P g := by
  have hsum : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    calc
      ((n - 1 : ℕ) : ZMod n) + 1 = (((n - 1) + 1 : ℕ) : ZMod n) := by simp
      _ = (n : ZMod n) := congrArg (fun t : ℕ => (t : ZMod n)) (Nat.sub_add_cancel hn)
      _ = 0 := ZMod.natCast_self n
  simp [boundaryWord, boundaryIndex, add_assoc, hsum]

theorem boundaryWord_leaf_edge (P : LabelledTuple n) (g : ZMod n)
    (k : ℕ) (hk : k + 1 < n) :
    boundaryWord P g ⟨k + 1, hk⟩ - boundaryWord P g ⟨k, by omega⟩ =
      edge P (g + (k + 1 : ℕ)) := by
  simp [boundaryWord, boundaryIndex, edge, Nat.cast_add, Nat.cast_one, add_assoc]

structure BoundaryInterval (n : ℕ) where
  left : Fin n
  right : Fin n
  increasing : left < right

namespace BoundaryInterval

def leaves (I : BoundaryInterval n) : ℕ := I.right.val - I.left.val

theorem leaves_pos (I : BoundaryInterval n) : 0 < I.leaves :=
  Nat.sub_pos_of_lt I.increasing

end BoundaryInterval

structure IntervalComposition (I : BoundaryInterval n) where
  parts : ℕ
  parts_pos : 0 < parts
  cut : Fin (parts + 1) → Fin n
  strict : StrictMono cut
  first : cut 0 = I.left
  last : cut (Fin.last parts) = I.right

namespace IntervalComposition

variable {I : BoundaryInterval n}

theorem parts_lt (π : IntervalComposition I) : π.parts < n := by
  have hc := Fintype.card_le_of_injective π.cut π.strict.injective
  simp only [Fintype.card_fin] at hc
  omega

def part (π : IntervalComposition I) (k : Fin π.parts) : BoundaryInterval n where
  left := π.cut k.castSucc
  right := π.cut k.succ
  increasing := π.strict (by simp)

def single (I : BoundaryInterval n) : IntervalComposition I where
  parts := 1
  parts_pos := by decide
  cut := ![I.left, I.right]
  strict := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [I.increasing]
  first := rfl
  last := rfl

end IntervalComposition

/-- The exact representative-based root/boundary/interval/composition data;
`boundaryWord_shift` supplies descent under the source's allowed reading. -/
def rootData (n : ℕ) [NeZero n] (_hn : 3 ≤ n) :=
  (ZMod n, edge (n := n), boundaryWord (n := n), BoundaryInterval n,
    BoundaryInterval.leaves (n := n),
    (fun I : BoundaryInterval n => IntervalComposition I),
    fun (I : BoundaryInterval n) (π : IntervalComposition I) => π.part)

end SM
