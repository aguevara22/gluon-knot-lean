import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

namespace SM.Carrier

/-- Two indices below the list length cross its cut at most once when added. -/
theorem mod_add_one_wrap (N p i : ℕ) (hp : p < N) (hi : i < N) :
    (i + p) % N = if i + p < N then i + p else i + p - N := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h), Nat.mod_eq_of_lt (by omega)]

/-- Translating indices around a finite circle preserves the strict arc from
index zero to index j, including the case where that arc crosses the cut. -/
theorem cyclic_mod_add_iff (N k i j : ℕ) (hi : i < N) (hj : j < N) :
    ((k % N < (i + k) % N ∧ (i + k) % N < (j + k) % N) ∨
      ((i + k) % N < (j + k) % N ∧ (j + k) % N < k % N) ∨
      ((j + k) % N < k % N ∧ k % N < (i + k) % N)) ↔
      0 < i ∧ i < j := by
  have hp : k % N < N := Nat.mod_lt k (Nat.zero_lt_of_lt hi)
  have hm (z : ℕ) (hz : z < N) : (z + k) % N = (z + k % N) % N := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hz]
  rw [hm i hi, hm j hj, mod_add_one_wrap N (k % N) i hp hi,
    mod_add_one_wrap N (k % N) j hp hj]
  split_ifs <;> omega

/-- In a sorted finite list, comparisons of rotated entries are comparisons of
their cyclic indices. The order premise comes from the actual finset sort. -/
theorem sorted_rotate_getElem_between_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (k i j : ℕ)
    (hi : i < (s.sort.rotate k).length) (hj : j < (s.sort.rotate k).length) :
    (((s.sort.rotate k)[0]'(lt_of_le_of_lt (Nat.zero_le i) hi) < (s.sort.rotate k)[i] ∧
        (s.sort.rotate k)[i] < (s.sort.rotate k)[j]) ∨
      ((s.sort.rotate k)[i] < (s.sort.rotate k)[j] ∧
        (s.sort.rotate k)[j] < (s.sort.rotate k)[0]'(lt_of_le_of_lt (Nat.zero_le i) hi)) ∨
      ((s.sort.rotate k)[j] < (s.sort.rotate k)[0]'(lt_of_le_of_lt (Nat.zero_le i) hi) ∧
        (s.sort.rotate k)[0]'(lt_of_le_of_lt (Nat.zero_le i) hi) < (s.sort.rotate k)[i])) ↔
      0 < i ∧ i < j := by
  have hi' : i < s.sort.length := by simpa only [List.length_rotate] using hi
  have hj' : j < s.sort.length := by simpa only [List.length_rotate] using hj
  simp only [List.getElem_rotate, Nat.zero_add, s.sortedLT_sort.getElem_lt_getElem_iff]
  exact cyclic_mod_add_iff s.sort.length k i j hi' hj'

/-- In a duplicate-free literal split list, membership in its first open arc
is exactly a strict index between its two endpoint indices. -/
theorem nodup_split_getElem_mem_iff {α : Type*} (a b : α) (A B : List α)
    (hN : (a :: (A ++ b :: B)).Nodup) (i : ℕ)
    (hi : i < (a :: (A ++ b :: B)).length) :
    (a :: (A ++ b :: B))[i] ∈ A ↔ 0 < i ∧ i < A.length + 1 := by
  constructor
  · intro hx
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hx
    have hjL : j + 1 < (a :: (A ++ b :: B)).length := by
      simp only [List.length_cons, List.length_append]
      omega
    have heL : (a :: (A ++ b :: B))[j + 1]'hjL = (a :: (A ++ b :: B))[i] := by
      simpa only [List.getElem_cons_succ, List.getElem_append_left hj] using he
    have hji : j + 1 = i := hN.getElem_inj_iff.mp heL
    omega
  · rintro ⟨hi0, hiA⟩
    cases i with
    | zero => omega
    | succ i =>
      have hiA' : i < A.length := by omega
      simpa only [List.getElem_cons_succ, List.getElem_append_left hiA'] using
        (List.getElem_mem hiA' : A[i] ∈ A)

/-- The first open slice of an actual rotated finset sort is exactly the
forward strict cyclic-order arc. Endpoints and wraparound are handled literally. -/
theorem sorted_rotate_split_mem_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (k : ℕ) (a b : α) (A B : List α) (x : α)
    (hr : s.sort.rotate k = a :: (A ++ b :: B)) (hx : x ∈ s) :
    x ∈ A ↔ ((a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ (b < a ∧ a < x)) := by
  have hN : (a :: (A ++ b :: B)).Nodup := by
    rw [← hr]
    exact List.nodup_rotate.mpr (Finset.sort_nodup s _)
  have hxm : x ∈ s.sort.rotate k := List.mem_rotate.mpr ((Finset.mem_sort _).mpr hx)
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxm
  have hiL : i < (a :: (A ++ b :: B)).length := by simpa only [hr] using hi
  have h0 : 0 < (s.sort.rotate k).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hj : A.length + 1 < (s.sort.rotate k).length := by
    rw [hr]
    simp only [List.length_cons, List.length_append]
    omega
  have hzero : (s.sort.rotate k)[0]'h0 = a := by
    simp only [hr, List.getElem_cons_zero]
  have hb : (s.sort.rotate k)[A.length + 1]'hj = b := by
    simp only [hr, List.getElem_cons_succ, List.getElem_append_right (Nat.le_refl A.length),
      Nat.sub_self, List.getElem_cons_zero]
  have hslice : x ∈ A ↔ 0 < i ∧ i < A.length + 1 := by
    have he : (a :: (A ++ b :: B))[i]'hiL = x := by simpa only [hr] using hix
    rw [← he]
    exact nodup_split_getElem_mem_iff a b A B hN i hiL
  have horder := sorted_rotate_getElem_between_iff s k i (A.length + 1) hi hj
  rw [hzero, hix, hb] at horder
  exact hslice.trans horder.symm

/-- The complementary literal slice is the reverse strict cyclic-order arc.
Rotating again to b reduces it to the proved forward-slice statement. -/
theorem sorted_rotate_split_reverse_mem_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (k : ℕ) (a b : α) (A B : List α) (x : α)
    (hr : s.sort.rotate k = a :: (A ++ b :: B)) (hx : x ∈ s) :
    x ∈ B ↔ ((b < x ∧ x < a) ∨ (x < a ∧ a < b) ∨ (a < b ∧ b < x)) := by
  have hr' : s.sort.rotate (k + (a :: A).length) = b :: (B ++ a :: A) := by
    rw [← List.rotate_rotate, hr]
    change (((a :: A) ++ (b :: B)).rotate (a :: A).length) = _
    rw [List.rotate_append_length_eq]
    rfl
  exact sorted_rotate_split_mem_iff s (k + (a :: A).length) b a B A x hr' hx

end SM.Carrier


#print axioms SM.Carrier.mod_add_one_wrap
#print axioms SM.Carrier.cyclic_mod_add_iff
#print axioms SM.Carrier.sorted_rotate_getElem_between_iff
#print axioms SM.Carrier.nodup_split_getElem_mem_iff
#print axioms SM.Carrier.sorted_rotate_split_mem_iff
#print axioms SM.Carrier.sorted_rotate_split_reverse_mem_iff
