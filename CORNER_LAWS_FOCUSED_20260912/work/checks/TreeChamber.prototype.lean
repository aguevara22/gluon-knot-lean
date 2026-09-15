import SM.CyclicChambers
import Mathlib.Data.Sign.Basic
import SM.Generic
import Mathlib.Tactic

/-! Development of source def:root. Work with labelled representatives and
prove the stipulated simultaneous shift of tuple and root. Composition lengths
are unbounded natural numbers in the definition; their finite bound is derived
from strict monotonicity, so no extra restriction is hidden in the domain. -/

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

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

/-- The source step function restricted to the nonzero sign arguments used by
the gates. There is deliberately no call accepting a zero argument. -/
def signTheta (s : SignType) (_hs : s ≠ 0) : ℤ := if s = 1 then 1 else 0

theorem sign_product_nonzero (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    h * d ≠ 0 ∧ -h * d ≠ 0 := by
  cases d <;> cases h <;> simp_all

def ordinaryGate (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) : ℤ :=
  (d : ℤ) * signTheta (-h * d) (sign_product_nonzero d h hd hh).2

def rootGate (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) : ℤ :=
  (d : ℤ) * signTheta (h * d) (sign_product_nonzero d h hd hh).1

theorem gate_pair_identities (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    ordinaryGate d h hd hh = ((d : ℤ) - (h : ℤ)) / 2 ∧
    rootGate d h hd hh = ((d : ℤ) + (h : ℤ)) / 2 := by
  cases d <;> cases h <;>
    first | exact (hd rfl).elim | exact (hh rfl).elim |
      norm_num [ordinaryGate, rootGate, signTheta]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

def nearSign (P : LabelledTuple n) (g : ZMod n) (k : Fin (π.parts - 1)) : SignType :=
  chi P (boundaryIndex g (π.cut ⟨k.val + 2, by have := k.isLt; omega⟩))
    (boundaryIndex g (π.cut ⟨k.val + 1, by have := k.isLt; omega⟩))
    (boundaryIndex g (π.cut ⟨k.val, by have := k.isLt; omega⟩))

def farSign (P : LabelledTuple n) (g : ZMod n) (k : Fin (π.parts - 1)) : SignType :=
  chi P (boundaryIndex g I.right)
    (boundaryIndex g (π.cut ⟨k.val + 1, by have := k.isLt; omega⟩))
    (boundaryIndex g I.left)

theorem nearSign_ne_zero {P : LabelledTuple n} (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) : π.nearSign P g k ≠ 0 := by
  have hinj := (boundaryIndex_injective g).comp π.strict.injective
  apply hP
  all_goals apply hinj.ne; intro he; have hv := congrArg Fin.val he; simp at hv

theorem farSign_ne_zero {P : LabelledTuple n} (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) : π.farSign P g k ≠ 0 := by
  have hinj := (boundaryIndex_injective g).comp π.strict.injective
  unfold farSign
  rw [← π.last, ← π.first]
  apply hP
  all_goals
    apply hinj.ne
    intro he
    have hv := congrArg Fin.val he
    have hk := k.isLt
    have hp := π.parts_pos
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega

def ordinaryWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) : ℤ :=
  ∏ k : Fin (π.parts - 1), ordinaryGate (π.nearSign P g k) (π.farSign P g k)
    (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)

def rootWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) : ℤ :=
  ∏ k : Fin (π.parts - 1), rootGate (π.nearSign P g k) (π.farSign P g k)
    (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)

theorem one_part_weights (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (hparts : π.parts = 1) : π.ordinaryWeight P hP g = 1 ∧ π.rootWeight P hP g = 1 := by
  letI : IsEmpty (Fin (π.parts - 1)) := ⟨fun k => by have := k.isLt; omega⟩
  simp [ordinaryWeight, rootWeight]

theorem binary_near_eq_far (P : LabelledTuple n) (g : ZMod n) (hparts : π.parts = 2)
    (k : Fin (π.parts - 1)) : π.nearSign P g k = π.farSign P g k := by
  have hk : k.val = 0 := by have := k.isLt; omega
  have hnext : (⟨k.val + 2, by have := k.isLt; omega⟩ : Fin (π.parts + 1)) =
      Fin.last π.parts := by apply Fin.ext; simp [hk, hparts]
  have hprev : (⟨k.val, by have := k.isLt; omega⟩ : Fin (π.parts + 1)) = 0 := by
    apply Fin.ext; exact hk
  simp only [nearSign, farSign, hnext, hprev, π.first, π.last]

theorem binary_ordinaryWeight_zero (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (hparts : π.parts = 2) : π.ordinaryWeight P hP g = 0 := by
  let k : Fin (π.parts - 1) := ⟨0, by omega⟩
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  rw [(gate_pair_identities _ _ (π.nearSign_ne_zero hP g k)
    (π.farSign_ne_zero hP g k)).1, π.binary_near_eq_far P g hparts k]
  simp

end IntervalComposition

/-- The complete gates definition on the source's G1 domain. -/
def gatesData (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :=
  fun (I : BoundaryInterval n) (π : IntervalComposition I) =>
    (π.nearSign P g, π.farSign P g, π.ordinaryWeight P hP g, π.rootWeight P hP g)

theorem nonzero_sign_cases (s : SignType) (hs : s ≠ 0) : s = 1 ∨ s = -1 := by
  cases s <;> simp_all

/-- All source lem:gates-nonzero clauses, including the four scalar sign pairs,
the nonzero domain of every step-function call, and vanishing for two parts. -/
theorem gates_nonzero (_hn : 3 ≤ n) (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      (∀ k : Fin (π.parts - 1),
        (π.nearSign P g k = 1 ∨ π.nearSign P g k = -1) ∧
        (π.farSign P g k = 1 ∨ π.farSign P g k = -1) ∧
        (π.farSign P g k * π.nearSign P g k = 1 ∨
          π.farSign P g k * π.nearSign P g k = -1) ∧
        (-π.farSign P g k * π.nearSign P g k = 1 ∨
          -π.farSign P g k * π.nearSign P g k = -1)) ∧
      (π.parts = 2 → π.ordinaryWeight P hP g = 0)) ∧
    (∀ (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0),
      ordinaryGate d h hd hh = ((d : ℤ) - (h : ℤ)) / 2 ∧
      rootGate d h hd hh = ((d : ℤ) + (h : ℤ)) / 2) := by
  refine ⟨?_, gate_pair_identities⟩
  intro I π
  refine ⟨?_, π.binary_ordinaryWeight_zero P hP g⟩
  intro k
  have hd := π.nearSign_ne_zero hP g k
  have hh := π.farSign_ne_zero hP g k
  have hp := sign_product_nonzero _ _ hd hh
  exact ⟨nonzero_sign_cases _ hd, nonzero_sign_cases _ hh,
    nonzero_sign_cases _ hp.1, nonzero_sign_cases _ hp.2⟩

end

end SM

namespace SM.IntervalComposition

variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A finite encoding of the unchanged raw source composition. The cut count
bound is proved from strict monotonicity, not inserted as a source premise. -/
def finiteCode (π : IntervalComposition I) : Σ s : Fin n, Fin (s.val + 1) → Fin n :=
  ⟨⟨π.parts, π.parts_lt⟩, π.cut⟩

theorem finiteCode_injective : Function.Injective (finiteCode (I := I)) := by
  intro π ρ he
  have hp := congrArg (fun s : Σ s : Fin n, Fin (s.val + 1) → Fin n => s.1.val) he
  cases π with
  | mk p hp0 c hc cf cl =>
    cases ρ with
    | mk q hq0 d hd df dl =>
      change p = q at hp
      subst q
      have hcd : c = d := eq_of_heq (Sigma.mk.inj he).2
      cases hcd
      rfl

instance finite : Finite (IntervalComposition I) :=
  Finite.of_injective finiteCode finiteCode_injective

noncomputable instance fintype : Fintype (IntervalComposition I) := Fintype.ofFinite _

/-- Every child of a composition with at least two parts has strictly fewer
leaves. This is the actual termination measure of the source tree recursion. -/
theorem part_leaves_lt (π : IntervalComposition I) (hp : 2 ≤ π.parts)
    (k : Fin π.parts) : (π.part k).leaves < I.leaves := by
  have hleft := π.strict.monotone (show (0 : Fin (π.parts + 1)) ≤ k.castSucc by simp)
  have hright := π.strict.monotone (show k.succ ≤ Fin.last π.parts by exact Fin.le_last _)
  rw [π.first] at hleft
  rw [π.last] at hright
  change I.left.val ≤ (π.cut k.castSucc).val at hleft
  change (π.cut k.succ).val ≤ I.right.val at hright
  change (π.cut k.succ).val - (π.cut k.castSucc).val < I.right.val - I.left.val
  by_cases hk : k.val = 0
  · have he : k.succ < Fin.last π.parts := by
      change k.val + 1 < π.parts
      omega
    have ht := π.strict he
    rw [π.last] at ht
    change (π.cut k.succ).val < I.right.val at ht
    have hc := π.strict (show k.castSucc < k.succ by simp)
    change (π.cut k.castSucc).val < (π.cut k.succ).val at hc
    omega
  · have he : (0 : Fin (π.parts + 1)) < k.castSucc := by
      change 0 < k.val
      omega
    have ht := π.strict he
    rw [π.first] at ht
    change I.left.val < (π.cut k.castSucc).val at ht
    have hc := π.strict (show k.castSucc < k.succ by simp)
    change (π.cut k.castSucc).val < (π.cut k.succ).val at hc
    omega

end SM.IntervalComposition


namespace SM

noncomputable section

universe u

variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

/-- The open source recursion with arbitrary independent ordinary weights.
The complete raw composition type is finite by the proved encoding; every
recursive call has strictly fewer leaves by the proved child-size theorem. -/
def openTreeRec (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R :=
  if I.leaves = 1 then 1 else
    -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
      ordinary I π.val * ∏ k : Fin π.val.parts, openTreeRec ordinary (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

/-- The distinguished root may have one child and carries no extra minus sign. -/
def rootedTreeRec (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R :=
  ∑ π : IntervalComposition I,
    rootWeight I π * ∏ k : Fin π.parts, openTreeRec ordinary (π.part k)

theorem openTreeRec_one (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openTreeRec ordinary I = 1 := by
  rw [openTreeRec]
  simp [hI]

theorem openTreeRec_many (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openTreeRec ordinary I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        ordinary I π.val * ∏ k : Fin π.val.parts, openTreeRec ordinary (π.val.part k) := by
  rw [openTreeRec]
  simp [show I.leaves ≠ 1 by omega]

def fullBoundaryInterval (hn : 3 ≤ n) : BoundaryInterval n where
  left := ⟨0, by omega⟩
  right := ⟨n - 1, by omega⟩
  increasing := by change 0 < n - 1; omega

def openTreeSum (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) : ℤ :=
  openTreeRec (fun _ π => π.ordinaryWeight P hP g) I

def treeCoefficient (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) : ℤ :=
  rootedTreeRec (fun _ π => π.ordinaryWeight P hP g)
    (fun _ π => π.rootWeight P hP g) (fullBoundaryInterval hn)

/-- The main text's last-edge root n is residue zero in the source label convention. -/
def mainTreeCoefficient (P : LabelledTuple n) (hP : G1 P) (hn : 3 ≤ n) : ℤ :=
  treeCoefficient P hP 0 hn

theorem openTreeSum_one (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openTreeSum P hP g I = 1 :=
  openTreeRec_one _ I hI

theorem openTreeSum_many (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openTreeSum P hP g I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        π.val.ordinaryWeight P hP g * ∏ k : Fin π.val.parts, openTreeSum P hP g (π.val.part k) :=
  openTreeRec_many _ I hI

theorem treeCoefficient_eq (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn =
      ∑ π : IntervalComposition (fullBoundaryInterval hn),
        π.rootWeight P hP g * ∏ k : Fin π.parts, openTreeSum P hP g (π.part k) := rfl

/-- Source def:treesum, including all open interval sums and the rooted output. -/
def treesumData (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :=
  (openTreeSum P hP g, treeCoefficient P hP g hn, mainTreeCoefficient P hP hn)

end

end SM

namespace SM

noncomputable section

theorem ordinaryGate_congr {d h d' h' : SignType} (ed : d = d') (eh : h = h')
    (hd : d ≠ 0) (hh : h ≠ 0) (hd' : d' ≠ 0) (hh' : h' ≠ 0) :
    ordinaryGate d h hd hh = ordinaryGate d' h' hd' hh' := by
  cases ed
  cases eh
  rfl

theorem rootGate_congr {d h d' h' : SignType} (ed : d = d') (eh : h = h')
    (hd : d ≠ 0) (hh : h ≠ 0) (hd' : d' ≠ 0) (hh' : h' ≠ 0) :
    rootGate d h hd hh = rootGate d' h' hd' hh' := by
  cases ed
  cases eh
  rfl

variable {n : ℕ} [NeZero n]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearSign_shift (P : LabelledTuple n) (g a : ZMod n) (k : Fin (π.parts - 1)) :
    π.nearSign (shift a P) (g - a) k = π.nearSign P g k := by
  unfold nearSign
  rw [chi_shift]
  congr 1 <;> unfold boundaryIndex <;> ring

theorem farSign_shift (P : LabelledTuple n) (g a : ZMod n) (k : Fin (π.parts - 1)) :
    π.farSign (shift a P) (g - a) k = π.farSign P g k := by
  unfold farSign
  rw [chi_shift]
  congr 1 <;> unfold boundaryIndex <;> ring

theorem ordinaryWeight_eq_of_signs (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q)
    (g h : ZMod n) (hd : ∀ k, π.nearSign P g k = π.nearSign Q h k)
    (hh : ∀ k, π.farSign P g k = π.farSign Q h k) :
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ h := by
  apply Finset.prod_congr rfl
  intro k _
  exact ordinaryGate_congr (hd k) (hh k) _ _ _ _

theorem rootWeight_eq_of_signs (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q)
    (g h : ZMod n) (hd : ∀ k, π.nearSign P g k = π.nearSign Q h k)
    (hh : ∀ k, π.farSign P g k = π.farSign Q h k) :
    π.rootWeight P hP g = π.rootWeight Q hQ h := by
  apply Finset.prod_congr rfl
  intro k _
  exact rootGate_congr (hd k) (hh k) _ _ _ _

theorem ordinaryWeight_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    π.ordinaryWeight (shift a P) (g1_shift_forward a hP) (g - a) =
      π.ordinaryWeight P hP g :=
  π.ordinaryWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_shift P g a) (π.farSign_shift P g a)

theorem rootWeight_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    π.rootWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.rootWeight P hP g :=
  π.rootWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_shift P g a) (π.farSign_shift P g a)

end IntervalComposition

/-- All gates descend under the exact simultaneous source relabelling of the
polygon and its physical root edge, including arbitrary cyclic shifts. -/
theorem gatesData_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    gatesData (shift a P) (g1_shift_forward a hP) (g - a) = gatesData P hP g := by
  funext I π
  have hd := funext (π.nearSign_shift P g a)
  have hh := funext (π.farSign_shift P g a)
  dsimp only [gatesData]
  rw [hd, hh, π.ordinaryWeight_shift P hP g a, π.rootWeight_shift P hP g a]

end

end SM


namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

theorem nearSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.nearSign P g k = π.nearSign Q g k := hchi _ _ _

theorem farSign_eq_of_chi {P Q : LabelledTuple n}
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (k : Fin (π.parts - 1)) :
    π.farSign P g k = π.farSign Q g k := hchi _ _ _

theorem ordinaryWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g :=
  π.ordinaryWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

theorem rootWeight_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) :
    π.rootWeight P hP g = π.rootWeight Q hQ g :=
  π.rootWeight_eq_of_signs _ _ _ _ _ _ (π.nearSign_eq_of_chi hchi g)
    (π.farSign_eq_of_chi hchi g)

end IntervalComposition

theorem openTreeSum_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (I : BoundaryInterval n) :
    openTreeSum P hP g I = openTreeSum Q hQ g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_eq_of_chi hP hQ hchi g

theorem treeCoefficient_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_eq_of_chi hP hQ hchi g
  · funext J π
    exact π.rootWeight_eq_of_chi hP hQ hchi g

theorem openTreeSum_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n)
    (I : BoundaryInterval n) :
    openTreeSum (shift a P) (g1_shift_forward a hP) (g - a) I = openTreeSum P hP g I := by
  unfold openTreeSum
  congr 1
  funext J π
  exact π.ordinaryWeight_shift P hP g a

theorem treeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (shift a P) (g1_shift_forward a hP) (g - a) hn =
      treeCoefficient P hP g hn := by
  unfold treeCoefficient
  congr 1
  · funext J π
    exact π.ordinaryWeight_shift P hP g a
  · funext J π
    exact π.rootWeight_shift P hP g a

/-- Fixed label zero on the shifted representative corresponds to label a on
the original representative. No independence of different physical roots is assumed. -/
theorem mainTreeCoefficient_shift (P : LabelledTuple n) (hP : G1 P) (a : ZMod n) (hn : 3 ≤ n) :
    mainTreeCoefficient (shift a P) (g1_shift_forward a hP) hn = treeCoefficient P hP a hn := by
  simpa only [mainTreeCoefficient, sub_self] using treeCoefficient_shift P hP a a hn

theorem treesumData_shift (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) (hn : 3 ≤ n) :
    treesumData (shift a P) (g1_shift_forward a hP) (g - a) hn =
      (openTreeSum P hP g, treeCoefficient P hP g hn, treeCoefficient P hP a hn) := by
  unfold treesumData
  rw [funext (openTreeSum_shift P hP g a), treeCoefficient_shift P hP g a hn,
    mainTreeCoefficient_shift P hP a hn]

end

end SM

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

/-- All quantities in the source chirotope-constancy clause, on G1 alone. -/
theorem tree_data_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
      π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
    (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn :=
  ⟨fun _ π => ⟨π.ordinaryWeight_eq_of_chi hP hQ hchi g,
    π.rootWeight_eq_of_chi hP hQ hchi g⟩,
    openTreeSum_eq_of_chi hP hQ hchi g, treeCoefficient_eq_of_chi hP hQ hchi g hn⟩

/-- The labelled chamber is the actual connected component of the generic locus.
Its continuous sign maps have discrete target, so they are constant on it. -/
theorem labelled_chamber_chi_constant (P Q : GenericTuple n) (hQ : Q ∈ labelledChamber P)
    (i j k : ZMod n) : chi P.val i j k = chi Q.val i j k := by
  exact isPreconnected_connectedComponent.constant
    (continuous_generic_chi i j k).continuousOn mem_connectedComponent hQ

theorem tree_data_labelled_chamber_constant (P Q : GenericTuple n)
    (hQ : Q ∈ labelledChamber P) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P.val P.property.1 g = π.ordinaryWeight Q.val Q.property.1 g ∧
      π.rootWeight P.val P.property.1 g = π.rootWeight Q.val Q.property.1 g) ∧
    (∀ I, openTreeSum P.val P.property.1 g I = openTreeSum Q.val Q.property.1 g I) ∧
    treeCoefficient P.val P.property.1 g hn = treeCoefficient Q.val Q.property.1 g hn :=
  tree_data_eq_of_chi P.property.1 Q.property.1 (labelled_chamber_chi_constant P Q hQ) g hn

/-- The path clause retains G1 only. Its asserted constant chirotope already
forces all values to agree; no further geometric condition is needed. -/
theorem tree_data_G1_path_constant {P Q : {P : LabelledTuple n // G1 P}}
    (γ : Path P Q)
    (hchi : ∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k)
    (g : ZMod n) (hn : 3 ≤ n) (s t : unitInterval) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight (γ s).val (γ s).property g =
        π.ordinaryWeight (γ t).val (γ t).property g ∧
      π.rootWeight (γ s).val (γ s).property g = π.rootWeight (γ t).val (γ t).property g) ∧
    (∀ I, openTreeSum (γ s).val (γ s).property g I =
      openTreeSum (γ t).val (γ t).property g I) ∧
    treeCoefficient (γ s).val (γ s).property g hn =
      treeCoefficient (γ t).val (γ t).property g hn :=
  tree_data_eq_of_chi (γ s).property (γ t).property (hchi s t) g hn

/-- On the actual unlabelled chamber, a label change must carry the root with it.
The proved chamber preimage theorem supplies the shift; this does not assume
independence of different physical roots. -/
theorem treeCoefficient_quotient_chamber_transport (P Q : GenericTuple n)
    (hn : 3 ≤ n) (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, Q ∈ labelledChamber (genericShift a P) ∧
      ∀ g : ZMod n, treeCoefficient Q.val Q.property.1 (g - a) hn =
        treeCoefficient P.val P.property.1 g hn := by
  have hm : Q ∈ ⋃ a : ZMod n, labelledChamber (genericShift a P) := by
    rw [← chamber_preimage_eq_cyclic_union hn P]
    exact hQ
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hm
  refine ⟨a, ha, ?_⟩
  intro g
  have he := (tree_data_labelled_chamber_constant (genericShift a P) Q ha (g - a) hn).2.2
  exact he.symm.trans (treeCoefficient_shift P.val P.property.1 g a hn)

end

end SM

#print axioms SM.tree_data_eq_of_chi
#print axioms SM.labelled_chamber_chi_constant
#print axioms SM.tree_data_labelled_chamber_constant
#print axioms SM.tree_data_G1_path_constant
#print axioms SM.treeCoefficient_quotient_chamber_transport
