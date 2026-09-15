import SM.Chirotope
import Mathlib.Tactic.Linarith

/-! SM def:generic and the developing proof of lem:g1.
The full lem:g1 is not claimed by the initial auxiliary results here. -/

namespace SM

variable {n : ℕ}

def G1 (P : LabelledTuple n) : Prop :=
  ∀ i j k, i ≠ j → j ≠ k → i ≠ k → chi P i j k ≠ 0

def G2 (P : LabelledTuple n) : Prop :=
  ¬ ∃ (i j k : ZMod n) (x : Plane),
    i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧ x ∈ edgeInterior P k

def Generic (P : LabelledTuple n) : Prop := G1 P ∧ G2 P

theorem edgeInterior_shift (a : ZMod n) (P : LabelledTuple n) (i : ZMod n) :
    edgeInterior (shift a P) i = edgeInterior P (i + a) := by
  simp only [edgeInterior, edgePoint_shift]

theorem g1_shift_forward (a : ZMod n) {P : LabelledTuple n} (h : G1 P) :
    G1 (shift a P) := by
  intro i j k hij hjk hik
  apply h (i + a) (j + a) (k + a)
  · exact fun he => hij (add_right_cancel he)
  · exact fun he => hjk (add_right_cancel he)
  · exact fun he => hik (add_right_cancel he)

theorem g2_shift_forward (a : ZMod n) {P : LabelledTuple n} (h : G2 P) :
    G2 (shift a P) := by
  rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
  apply h
  refine ⟨i + a, j + a, k + a, x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun he => hij (add_right_cancel he)
  · exact fun he => hjk (add_right_cancel he)
  · exact fun he => hik (add_right_cancel he)
  · simpa only [edgeInterior_shift] using hi
  · simpa only [edgeInterior_shift] using hj
  · simpa only [edgeInterior_shift] using hk

theorem generic_shift (a : ZMod n) (P : LabelledTuple n) :
    Generic (shift a P) ↔ Generic P := by
  constructor
  · intro h
    have h1 := g1_shift_forward (-a) h.1
    have h2 := g2_shift_forward (-a) h.2
    simpa only [Generic, shift_add, neg_add_cancel, shift_zero] using And.intro h1 h2
  · rintro ⟨h1, h2⟩
    exact ⟨g1_shift_forward a h1, g2_shift_forward a h2⟩

theorem g1_area_ne_zero {P : LabelledTuple n} (h : G1 P)
    {i j k : ZMod n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    det (P j - P i) (P k - P i) ≠ 0 := by
  exact sign_ne_zero.mp (h i j k hij hjk hik)

theorem exists_third_index [NeZero n] (hn : 3 ≤ n) (i j : ZMod n) :
    ∃ k : ZMod n, k ≠ i ∧ k ≠ j := by
  have hc : ({i, j} : Finset (ZMod n)).card < (Finset.univ : Finset (ZMod n)).card := by
    have hpair : ({i, j} : Finset (ZMod n)).card ≤ 2 := by
      calc
        _ ≤ ({j} : Finset (ZMod n)).card + 1 := Finset.card_insert_le i {j}
        _ = 2 := by simp
    have h2 : 2 < n := by omega
    simpa only [Finset.card_univ, ZMod.card] using lt_of_le_of_lt hpair h2
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨k, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk⟩

theorem g1_vertices_injective [NeZero n] (hn : 3 ≤ n)
    {P : LabelledTuple n} (h : G1 P) : Function.Injective P := by
  intro i j heq
  by_contra hij
  obtain ⟨k, hki, hkj⟩ := exists_third_index hn i j
  have harea := g1_area_ne_zero h hij hkj.symm hki.symm
  apply harea
  simp [heq, det]

theorem g1_edge_ne_zero [NeZero n] [Nontrivial (ZMod n)] (hn : 3 ≤ n)
    {P : LabelledTuple n} (h : G1 P) (i : ZMod n) : edge P i ≠ 0 := by
  intro hz
  have heq : P (i + 1) = P i := sub_eq_zero.mp hz
  have hi := g1_vertices_injective hn h heq
  have hone : (1 : ZMod n) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using hi)
  exact one_ne_zero hone

theorem g1_turn_area [NeZero n] (hn : 3 ≤ n)
    {P : LabelledTuple n} (h : G1 P) (i : ZMod n)
    (hprev : i - 1 ≠ i) (hnext : i ≠ i + 1) (hends : i - 1 ≠ i + 1) :
    det (edge P (i - 1)) (edge P i) ≠ 0 := by
  have hsign := h (i - 1) i (i + 1) hprev hnext hends
  change turn P i ≠ 0 at hsign
  rw [turn_det] at hsign
  exact sign_ne_zero.mp hsign

theorem det_edge_line (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    det (edge P i) (edgePoint P i t - P i) = 0 := by
  dsimp [det, edgePoint]
  ring

theorem g1_vertex_off_edge_line {P : LabelledTuple n} (h : G1 P)
    (i k : ZMod n) (hedge : i ≠ i + 1) (hk0 : k ≠ i) (hk1 : k ≠ i + 1)
    (t : ℝ) : P k ≠ edgePoint P i t := by
  intro heq
  have harea := g1_area_ne_zero h hedge hk1.symm hk0.symm
  change det (edge P i) (P k - P i) ≠ 0 at harea
  rw [heq] at harea
  exact harea (det_edge_line P i t)

theorem g1_vertex_not_mem_edge {P : LabelledTuple n} (h : G1 P)
    (i k : ZMod n) (hedge : i ≠ i + 1) (hk0 : k ≠ i) (hk1 : k ≠ i + 1) :
    P k ∉ edgeSegment P i := by
  rintro ⟨t, _, _, heq⟩
  exact g1_vertex_off_edge_line h i k hedge hk0 hk1 t heq

end SM
