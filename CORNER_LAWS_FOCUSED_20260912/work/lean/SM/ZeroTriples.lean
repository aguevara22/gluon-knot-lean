import SM.G1Consequences
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Aesop

/-! Actual unordered central point-zero and interior-concurrence triples.
These definitions apply to arbitrary tuples, including nongeneric centres. -/

namespace SM

variable {n : ℕ}

def PointZeroTriple (P : LabelledTuple n) (s : Finset (ZMod n)) : Prop :=
  s.card = 3 ∧ ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, chi P i j k = 0

theorem chi_zero_of_mem_triple {P : LabelledTuple n} {i j k a b c : ZMod n}
    (h : chi P i j k = 0) (ha : a ∈ ({i, j, k} : Finset (ZMod n)))
    (hb : b ∈ ({i, j, k} : Finset (ZMod n)))
    (hc : c ∈ ({i, j, k} : Finset (ZMod n))) : chi P a b c = 0 := by
  have h1 : chi P j k i = 0 := (chi_cyclic P i j k).trans h
  have h2 : chi P k i j = 0 := (chi_cyclic P j k i).trans h1
  have h3 : chi P i k j = 0 := by rw [chi_swap_last, h]; rfl
  have h4 : chi P k j i = 0 := (chi_cyclic P i k j).trans h3
  have h5 : chi P j i k = 0 := (chi_cyclic P k j i).trans h4
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> simp_all

theorem pointZeroTriple_iff {P : LabelledTuple n} {i j k : ZMod n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    PointZeroTriple P {i, j, k} ↔ chi P i j k = 0 := by
  constructor
  · intro h
    exact h.2 i (by simp) j (by simp) k (by simp)
  · intro h
    exact ⟨Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩,
      fun _ ha _ hb _ hc => chi_zero_of_mem_triple h ha hb hc⟩

noncomputable def pointZeroTriples [NeZero n] (P : LabelledTuple n) :
    Finset (Finset (ZMod n)) := by
  classical
  exact Finset.univ.powerset.filter (PointZeroTriple P)

theorem mem_pointZeroTriples [NeZero n] (P : LabelledTuple n) (s : Finset (ZMod n)) :
    s ∈ pointZeroTriples P ↔ PointZeroTriple P s := by
  simp [pointZeroTriples]

theorem pointZeroTriples_empty_iff [NeZero n] (P : LabelledTuple n) :
    pointZeroTriples P = ∅ ↔ G1 P := by
  constructor
  · intro he i j k hij hjk hik hz
    have hm := (mem_pointZeroTriples P {i, j, k}).mpr ((pointZeroTriple_iff hij hjk hik).mpr hz)
    simpa only [he, Finset.notMem_empty] using hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hp := (mem_pointZeroTriples P s).mp hs
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hp.1
    exact h i j k hij hjk hik ((pointZeroTriple_iff hij hjk hik).mp hp)

def ConcurrenceTriple (P : LabelledTuple n) (s : Finset (ZMod n)) : Prop :=
  s.card = 3 ∧ (s : Set (ZMod n)).Pairwise remote ∧
    ∃ x : Plane, ∀ i ∈ s, x ∈ edgeInterior P i

noncomputable def concurrenceTriples [NeZero n] (P : LabelledTuple n) :
    Finset (Finset (ZMod n)) := by
  classical
  exact Finset.univ.powerset.filter (ConcurrenceTriple P)

theorem mem_concurrenceTriples [NeZero n] (P : LabelledTuple n) (s : Finset (ZMod n)) :
    s ∈ concurrenceTriples P ↔ ConcurrenceTriple P s := by
  simp [concurrenceTriples]

theorem concurrenceTriple_iff {P : LabelledTuple n} {i j k : ZMod n}
    (hij : remote i j) (hjk : remote j k) (hik : remote i k) :
    ConcurrenceTriple P {i, j, k} ↔
      ∃ x : Plane, x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧ x ∈ edgeInterior P k := by
  constructor
  · rintro ⟨_, _, x, hx⟩
    exact ⟨x, hx i (by simp), hx j (by simp), hx k (by simp)⟩
  · rintro ⟨x, hi, hj, hk⟩
    have hji := remote_symm hij
    have hkj := remote_symm hjk
    have hki := remote_symm hik
    refine ⟨Finset.card_triple_eq_three_iff.mpr
      ⟨(remote_endpoints i j hij).1.symm, (remote_endpoints i k hik).1.symm,
        (remote_endpoints j k hjk).1.symm⟩, ?_, x, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> aesop
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption

end SM
