import SM.Polygon
import Mathlib.Data.Sign.Defs

/-! SM def:chirotope and lem:chi-basic, including all four source clauses. -/

namespace SM

variable {n : ℕ}

noncomputable def chi (P : LabelledTuple n) (i j k : ZMod n) : SignType :=
  SignType.sign (det (P j - P i) (P k - P i))

noncomputable def turn (P : LabelledTuple n) (i : ZMod n) : SignType :=
  chi P (i - 1) i (i + 1)

noncomputable def leftTurns [NeZero n] (P : LabelledTuple n) : ℕ :=
  (Finset.univ.filter (fun i => turn P i = 1)).card

/-- The three functions introduced together in def:chirotope. -/
noncomputable def chirotopeData [NeZero n] (P : LabelledTuple n) :=
  (chi P, turn P, leftTurns P)

/-- The directed-line convention in lem:chi-basic(iii). -/
def strictlyLeft (P : LabelledTuple n) (i : ZMod n) (x : Plane) : Prop :=
  0 < det (edge P i) (x - P i)

def strictlyRight (P : LabelledTuple n) (i : ZMod n) (x : Plane) : Prop :=
  det (edge P i) (x - P i) < 0

theorem det_swap (u v : Plane) : det v u = -det u v := by
  dsimp [det]
  ring

theorem area_cyclic (a b c : Plane) :
    det (c - b) (a - b) = det (b - a) (c - a) := by
  dsimp [det]
  ring

theorem chi_swap_last (P : LabelledTuple n) (i j k : ZMod n) :
    chi P i k j = -chi P i j k := by
  unfold chi
  rw [det_swap, Left.sign_neg]

theorem chi_cyclic (P : LabelledTuple n) (i j k : ZMod n) :
    chi P j k i = chi P i j k := by
  unfold chi
  rw [area_cyclic]

theorem chi_swap_first (P : LabelledTuple n) (i j k : ZMod n) :
    chi P j i k = -chi P i j k := by
  rw [← chi_cyclic P j i k, chi_swap_last, chi_cyclic]

theorem chi_swap_outer (P : LabelledTuple n) (i j k : ZMod n) :
    chi P k j i = -chi P i j k := by
  rw [chi_cyclic P i k j, chi_swap_last]

@[simp] theorem chi_repeat_first (P : LabelledTuple n) (i k : ZMod n) :
    chi P i i k = 0 := by
  simp [chi, det]

@[simp] theorem chi_repeat_last (P : LabelledTuple n) (i j : ZMod n) :
    chi P i j j = 0 := by
  simp [chi, det, mul_comm]

@[simp] theorem chi_repeat_outer (P : LabelledTuple n) (i j : ZMod n) :
    chi P i j i = 0 := by
  simp [chi, det]

theorem chi_bracket (P : LabelledTuple n) (i j k : ZMod n) :
    chi P i j k = SignType.sign (bracket (P j - P i) (P j - P k)) := by
  unfold chi
  congr 1
  dsimp [det, bracket]
  ring

theorem chi_edge (P : LabelledTuple n) (i k : ZMod n) :
    chi P i (i + 1) k = SignType.sign (det (edge P i) (P k - P i)) := rfl

theorem chi_edge_left (P : LabelledTuple n) (i k : ZMod n) :
    chi P i (i + 1) k = 1 ↔ strictlyLeft P i (P k) := by
  exact sign_eq_one_iff

theorem chi_edge_right (P : LabelledTuple n) (i k : ZMod n) :
    chi P i (i + 1) k = -1 ↔ strictlyRight P i (P k) := by
  exact sign_eq_neg_one_iff

theorem turn_det (P : LabelledTuple n) (i : ZMod n) :
    turn P i = SignType.sign (det (edge P (i - 1)) (edge P i)) := by
  unfold turn chi
  congr 1
  simp only [edge, sub_add_cancel]
  dsimp [det]
  ring

theorem turn_left (P : LabelledTuple n) (i : ZMod n) :
    turn P i = 1 ↔ 0 < det (edge P (i - 1)) (edge P i) := by
  rw [turn_det]
  exact sign_eq_one_iff

theorem chi_shift (a : ZMod n) (P : LabelledTuple n) (i j k : ZMod n) :
    chi (shift a P) i j k = chi P (i + a) (j + a) (k + a) := rfl

theorem turn_shift (a : ZMod n) (P : LabelledTuple n) (i : ZMod n) :
    turn (shift a P) i = turn P (i + a) := by
  simp [turn, chi_shift, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem leftTurns_shift [NeZero n] (a : ZMod n) (P : LabelledTuple n) :
    leftTurns (shift a P) = leftTurns P := by
  unfold leftTurns
  apply Finset.card_bij (fun i _ => i + a)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, turn_shift] using hi
  · intro i _ j _ hij
    exact add_right_cancel hij
  · intro j hj
    refine ⟨j - a, ?_, sub_add_cancel j a⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, turn_shift,
      sub_add_cancel] using hj

/-- All the assertions of SM lem:chi-basic, without genericity assumptions. -/
theorem chi_basic (P : LabelledTuple n) :
    (∀ i j k, chi P i k j = -chi P i j k) ∧
    (∀ i j k, chi P j i k = -chi P i j k) ∧
    (∀ i j k, chi P k j i = -chi P i j k) ∧
    (∀ i j k, chi P j k i = chi P i j k) ∧
    (∀ i k, chi P i i k = 0) ∧
    (∀ i j, chi P i j j = 0) ∧
    (∀ i j, chi P i j i = 0) ∧
    (∀ i j k, chi P i j k = SignType.sign (bracket (P j - P i) (P j - P k))) ∧
    (∀ i k, chi P i (i + 1) k = SignType.sign (det (edge P i) (P k - P i))) ∧
    (∀ i k, chi P i (i + 1) k = 1 ↔ strictlyLeft P i (P k)) ∧
    (∀ i k, chi P i (i + 1) k = -1 ↔ strictlyRight P i (P k)) ∧
    (∀ i, turn P i = SignType.sign (det (edge P (i - 1)) (edge P i))) ∧
    (∀ i, turn P i = 1 ↔ 0 < det (edge P (i - 1)) (edge P i)) := by
  exact ⟨chi_swap_last P, chi_swap_first P, chi_swap_outer P, chi_cyclic P,
    chi_repeat_first P, chi_repeat_last P, chi_repeat_outer P, chi_bracket P,
    chi_edge P, chi_edge_left P, chi_edge_right P, turn_det P, turn_left P⟩

end SM
