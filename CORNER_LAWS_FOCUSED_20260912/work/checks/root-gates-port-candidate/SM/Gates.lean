import SM.RootBoundary
import Mathlib.Data.Sign.Basic

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
