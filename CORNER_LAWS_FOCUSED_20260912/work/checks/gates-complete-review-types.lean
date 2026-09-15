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

set_option pp.fullNames true
set_option pp.universes false
#check SM.IntervalComposition.finiteCode
#print axioms SM.IntervalComposition.finiteCode
#check SM.IntervalComposition.finiteCode_injective
#print axioms SM.IntervalComposition.finiteCode_injective
#check SM.IntervalComposition.finite
#print axioms SM.IntervalComposition.finite
#check SM.IntervalComposition.fintype
#print axioms SM.IntervalComposition.fintype
#check SM.IntervalComposition.part_leaves_lt
#print axioms SM.IntervalComposition.part_leaves_lt
#check SM.signTheta
#print axioms SM.signTheta
#check SM.sign_product_nonzero
#print axioms SM.sign_product_nonzero
#check SM.ordinaryGate
#print axioms SM.ordinaryGate
#check SM.rootGate
#print axioms SM.rootGate
#check SM.gate_pair_identities
#print axioms SM.gate_pair_identities
#check SM.IntervalComposition.nearSign
#print axioms SM.IntervalComposition.nearSign
#check SM.IntervalComposition.farSign
#print axioms SM.IntervalComposition.farSign
#check SM.IntervalComposition.nearSign_ne_zero
#print axioms SM.IntervalComposition.nearSign_ne_zero
#check SM.IntervalComposition.farSign_ne_zero
#print axioms SM.IntervalComposition.farSign_ne_zero
#check SM.IntervalComposition.ordinaryWeight
#print axioms SM.IntervalComposition.ordinaryWeight
#check SM.IntervalComposition.rootWeight
#print axioms SM.IntervalComposition.rootWeight
#check SM.IntervalComposition.one_part_weights
#print axioms SM.IntervalComposition.one_part_weights
#check SM.IntervalComposition.binary_near_eq_far
#print axioms SM.IntervalComposition.binary_near_eq_far
#check SM.IntervalComposition.binary_ordinaryWeight_zero
#print axioms SM.IntervalComposition.binary_ordinaryWeight_zero
#check SM.gatesData
#print axioms SM.gatesData
#check SM.nonzero_sign_cases
#print axioms SM.nonzero_sign_cases
#check SM.gates_nonzero
#print axioms SM.gates_nonzero
#check SM.ordinaryGate_congr
#print axioms SM.ordinaryGate_congr
#check SM.rootGate_congr
#print axioms SM.rootGate_congr
#check SM.IntervalComposition.nearSign_shift
#print axioms SM.IntervalComposition.nearSign_shift
#check SM.IntervalComposition.farSign_shift
#print axioms SM.IntervalComposition.farSign_shift
#check SM.IntervalComposition.ordinaryWeight_eq_of_signs
#print axioms SM.IntervalComposition.ordinaryWeight_eq_of_signs
#check SM.IntervalComposition.rootWeight_eq_of_signs
#print axioms SM.IntervalComposition.rootWeight_eq_of_signs
#check SM.IntervalComposition.ordinaryWeight_shift
#print axioms SM.IntervalComposition.ordinaryWeight_shift
#check SM.IntervalComposition.rootWeight_shift
#print axioms SM.IntervalComposition.rootWeight_shift
#check SM.gatesData_shift
#print axioms SM.gatesData_shift
#print SM.IntervalComposition
#print SM.signTheta
#print SM.IntervalComposition.nearSign
#print SM.IntervalComposition.farSign
#print SM.IntervalComposition.ordinaryWeight
#print SM.IntervalComposition.rootWeight
#print SM.gatesData

namespace FiniteAndGatesIndependentReview
open SM

-- The canonical typeclass domain is the unchanged source composition type.
theorem every_composition_enumerated {n : ℕ} [NeZero n] (I : BoundaryInterval n) :
    (∀ π : IntervalComposition I, π ∈ (Finset.univ : Finset (IntervalComposition I))) ∧
      0 < Fintype.card (IntervalComposition I) := by
  exact ⟨fun _ => Finset.mem_univ _, Fintype.card_pos_iff.mpr ⟨IntervalComposition.single I⟩⟩

-- Actual child intervals have positive and strictly smaller leaf counts.
theorem all_source_children_decrease {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (hp : 2 ≤ π.parts) :
    ∀ k : Fin π.parts, 0 < (π.part k).leaves ∧ (π.part k).leaves < I.leaves :=
  fun k => ⟨(π.part k).leaves_pos, π.part_leaves_lt hp k⟩

-- The exact source recursive-child relation is well founded under that measure.
theorem source_child_relation_wellFounded {n : ℕ} [NeZero n] :
    WellFounded (fun J I : BoundaryInterval n =>
      ∃ π : IntervalComposition I, 2 ≤ π.parts ∧ ∃ k : Fin π.parts, J = π.part k) := by
  apply (measure BoundaryInterval.leaves).wf.mono
  intro J I h
  obtain ⟨π, hp, k, rfl⟩ := h
  exact π.part_leaves_lt hp k

-- The excluded one-part case has equal measure, not a false strict decrease.
theorem singleton_measure_equal {n : ℕ} [NeZero n] (I : BoundaryInterval n) :
    ((IntervalComposition.single I).part ⟨0, (IntervalComposition.single I).parts_pos⟩).leaves = I.leaves := by
  cases I
  rfl

-- Every source interior cut1<=k<=s-1 has exactly an indexing position k-1.
theorem interior_cut_exhaustion {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (k : ℕ) (hk : 0 < k) (hks : k < π.parts) :
    ∃ j : Fin (π.parts - 1), j.val + 1 = k := by
  exact ⟨⟨k - 1, by omega⟩, by simp; omega⟩

-- The nonzero SignType step is the source Real step on every actual gate argument.
theorem real_step_interpretation (s : SignType) (hs : s ≠ 0) :
    (signTheta s hs : ℝ) = (if 0 < (s : ℝ) then 1 else 0) := by
  cases s <;> first | exact (hs rfl).elim | norm_num [signTheta]

-- Both half-formulas are exact rational/real identities, not rounded integer division.
theorem real_gate_identities (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    (ordinaryGate d h hd hh : ℝ) = ((d : ℝ) - (h : ℝ)) / 2 ∧
    (rootGate d h hd hh : ℝ) = ((d : ℝ) + (h : ℝ)) / 2 := by
  cases d <;> cases h <;>
    first | exact (hd rfl).elim | exact (hh rfl).elim |
      norm_num [ordinaryGate, rootGate, signTheta]

-- Embedding the actual complete weights gives the product of the source halves.
theorem real_weight_identities {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.ordinaryWeight P hP g : ℝ) = ∏ k : Fin (π.parts - 1),
      ((π.nearSign P g k : ℝ) - (π.farSign P g k : ℝ)) / 2 ∧
    (π.rootWeight P hP g : ℝ) = ∏ k : Fin (π.parts - 1),
      ((π.nearSign P g k : ℝ) + (π.farSign P g k : ℝ)) / 2 := by
  constructor
  · rw [IntervalComposition.ordinaryWeight, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    exact (real_gate_identities _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).1
  · rw [IntervalComposition.rootWeight, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    exact (real_gate_identities _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).2

-- Empty products and the arbitrary two-part source composition need only G1.
theorem source_small_part_cases {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.parts = 1 → π.ordinaryWeight P hP g = 1 ∧ π.rootWeight P hP g = 1) ∧
    (π.parts = 2 → π.ordinaryWeight P hP g = 0) :=
  ⟨π.one_part_weights P hP g, π.binary_ordinaryWeight_zero P hP g⟩

-- Independent check of the representative-equivalence obligation.
theorem gate_signs_shift {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (g a : ZMod n)
    (k : Fin (π.parts - 1)) :
    π.nearSign (shift a P) (g - a) k = π.nearSign P g k ∧
      π.farSign (shift a P) (g - a) k = π.farSign P g k := by
  have hb : ∀ j : Fin n, boundaryIndex (g - a) j + a = boundaryIndex g j := by
    intro j
    unfold boundaryIndex
    ring
  constructor
  · simp only [IntervalComposition.nearSign, chi_shift, hb]
  · simp only [IntervalComposition.farSign, chi_shift, hb]

-- All factors and weights preserve the pair(polygon,root), including G1 transport.
theorem gate_weights_shift {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    π.ordinaryWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.ordinaryWeight P hP g ∧
    π.rootWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.rootWeight P hP g := by
  constructor
  · unfold IntervalComposition.ordinaryWeight
    apply Finset.prod_congr rfl
    intro k _
    rcases gate_signs_shift I π P g a k with ⟨hd, hh⟩
    simp only [hd, hh]
  · unfold IntervalComposition.rootWeight
    apply Finset.prod_congr rfl
    intro k _
    rcases gate_signs_shift I π P g a k with ⟨hd, hh⟩
    simp only [hd, hh]

end FiniteAndGatesIndependentReview

#print axioms FiniteAndGatesIndependentReview.every_composition_enumerated
#print axioms FiniteAndGatesIndependentReview.all_source_children_decrease
#print axioms FiniteAndGatesIndependentReview.source_child_relation_wellFounded
#print axioms FiniteAndGatesIndependentReview.singleton_measure_equal
#print axioms FiniteAndGatesIndependentReview.interior_cut_exhaustion
#print axioms FiniteAndGatesIndependentReview.real_step_interpretation
#print axioms FiniteAndGatesIndependentReview.real_gate_identities
#print axioms FiniteAndGatesIndependentReview.real_weight_identities
#print axioms FiniteAndGatesIndependentReview.source_small_part_cases
#print axioms FiniteAndGatesIndependentReview.gate_signs_shift
#print axioms FiniteAndGatesIndependentReview.gate_weights_shift

namespace GatesEquivarianceIndependentReview
open SM

-- The source generator sigma sends the root g exactly to g-1.
theorem source_generator {n : ℕ} [NeZero n] (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    gatesData (shift 1 P) (g1_shift_forward 1 hP) (g - 1) = gatesData P hP g :=
  gatesData_shift P hP g 1

-- Any two allowed representative/root presentations give the same whole data.
-- A different proof of G1 for the shifted representative cannot change it.
theorem rooted_representative_descent {n : ℕ} [NeZero n]
    (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q) (g h a : ZMod n)
    (hQeq : Q = shift a P) (hroot : h = g - a) :
    gatesData Q hQ h = gatesData P hP g := by
  subst Q
  subst h
  exact gatesData_shift P hP g a

-- The proof-carrying nonzero interface carries no numerical proof dependence.
theorem G1_proof_independence {n : ℕ} [NeZero n] (P : LabelledTuple n)
    (hP hP' : G1 P) (g : ZMod n) : gatesData P hP g = gatesData P hP' g := rfl

end GatesEquivarianceIndependentReview

#print axioms GatesEquivarianceIndependentReview.source_generator
#print axioms GatesEquivarianceIndependentReview.rooted_representative_descent
#print axioms GatesEquivarianceIndependentReview.G1_proof_independence
