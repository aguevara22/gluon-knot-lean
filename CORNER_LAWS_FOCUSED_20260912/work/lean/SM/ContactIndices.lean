import SM.TurnSupports
import Mathlib.Tactic.IntervalCases

/-! Exact cyclic index consequences of the vertex--edge separation condition.
No extra cardinality or combinatorial hypothesis is added to a named wall. -/

namespace SM

variable {n : ℕ} [NeZero n]

def ContactSeparated (M a : ZMod n) : Prop :=
  M ≠ a - 1 ∧ M ≠ a ∧ M ≠ a + 1 ∧ M ≠ a + 2

theorem contactSeparated_iff (M a : ZMod n) : ContactSeparated M a ↔
    M ∉ ({a - 1, a, a + 1, a + 2} : Finset (ZMod n)) := by
  simp only [ContactSeparated, Finset.mem_insert, Finset.mem_singleton, not_or]

def contactSupport (M a : ZMod n) : Finset (ZMod n) := {a, a + 1, M}

theorem contactSeparated_size (hn : 3 ≤ n) {M a : ZMod n}
    (h : ContactSeparated M a) : 5 ≤ n := by
  by_contra hn5
  have hsmall : n = 3 ∨ n = 4 := by omega
  have hzero : M - a ≠ 0 := sub_ne_zero.mpr h.2.1
  have hone : M - a ≠ 1 := by intro he; exact h.2.2.1 (by linear_combination he)
  have htwo : M - a ≠ 2 := by intro he; exact h.2.2.2 (by linear_combination he)
  have hneg : M - a ≠ -1 := by intro he; exact h.1 (by linear_combination he)
  rcases hsmall with rfl | rfl
  · have hv := ZMod.val_lt (M - a)
    have he := ZMod.natCast_zmod_val (M - a)
    interval_cases hval : (M - a).val <;> norm_num [hval] at he <;> aesop
  · have hv := ZMod.val_lt (M - a)
    have he := ZMod.natCast_zmod_val (M - a)
    have hthree : (3 : ZMod 4) = -1 := by decide
    interval_cases hval : (M - a).val <;> norm_num [hval, hthree] at he <;> aesop

/-- The only forward consecutive pair in a contact support is its base edge. -/
theorem contactSupport_successive (hn : 3 ≤ n) {M a i : ZMod n}
    (h : ContactSeparated M a) (hi : i ∈ contactSupport M a)
    (hj : i + 1 ∈ contactSupport M a) : i = a := by
  have hn5 := contactSeparated_size hn h
  have h1 : (1 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 1) (by omega) (by omega)
  have h2 : (2 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 2) (by omega) (by omega)
  simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl
  · rfl
  · rcases hj with he | he | he
    · exact (h2 (by linear_combination he)).elim
    · exact (h1 (by linear_combination he)).elim
    · exact (h.2.2.2 (by linear_combination -he)).elim
  · rcases hj with he | he | he
    · exact (h.1 (by linear_combination he)).elim
    · exact (h.2.1 (by linear_combination he)).elim
    · exact (h1 (by linear_combination he)).elim

theorem contactSupport_ne_turnSupport (hn : 3 ≤ n) {M a : ZMod n}
    (h : ContactSeparated M a) (i : ZMod n) : contactSupport M a ≠ turnSupport i := by
  intro he
  have hprev : i - 1 = a := contactSupport_successive hn h
    (by rw [he]; simp [turnSupport]) (by rw [he]; simp [turnSupport])
  have hself : i = a := contactSupport_successive hn h
    (by rw [he]; simp [turnSupport]) (by rw [he]; simp [turnSupport])
  have hn5 := contactSeparated_size hn h
  have h1 : (1 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 1) (by omega) (by omega)
  exact h1 (by linear_combination hself - hprev)

theorem contactSupport_vertex_edge (hn : 3 ≤ n) {M a i k : ZMod n}
    (h : ContactSeparated M a) (hki : k ≠ i) (hki1 : k ≠ i + 1)
    (he : ({i, i + 1, k} : Finset _) = contactSupport M a) : i = a ∧ k = M := by
  have hi : i = a := contactSupport_successive hn h
    (by rw [← he]; simp) (by rw [← he]; simp)
  subst i
  have hk : k ∈ contactSupport M a := by rw [← he]; simp
  simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hk
  exact ⟨rfl, hk.resolve_left hki |>.resolve_left hki1⟩

end SM
