import SM.ContactCrossingTest
import SM.ContactPersistence
import SM.ContactSignPatterns
import Mathlib.Data.Finset.SymmDiff

/-! Actual crossing-set consequences of the two proved contact tests.
All predicates below concern the geometric IsCrossing relation. -/

namespace SM

open scoped symmDiff

variable {n : ℕ} [NeZero n]

def ContactTests (C P : LabelledTuple n) (M a : ZMod n) : Prop :=
  ∀ forward : Bool, IsCrossing P {a, contactLeg forward M} ↔
    chi P a (a + 1) M * chi C a (a + 1) (contactNeighbour forward M) = -1

def BigonCrossingPattern (P Q : LabelledTuple n) (M a : ZMod n) : Prop :=
  (IsCrossing P {a, M - 1} ∧ IsCrossing P {a, M} ∧
    ¬ IsCrossing Q {a, M - 1} ∧ ¬ IsCrossing Q {a, M}) ∨
  (¬ IsCrossing P {a, M - 1} ∧ ¬ IsCrossing P {a, M} ∧
    IsCrossing Q {a, M - 1} ∧ IsCrossing Q {a, M})

def SlidingCrossingPattern (P Q : LabelledTuple n) (M a : ZMod n) : Prop :=
  (IsCrossing P {a, M - 1} ∧ ¬ IsCrossing P {a, M} ∧
    ¬ IsCrossing Q {a, M - 1} ∧ IsCrossing Q {a, M}) ∨
  (¬ IsCrossing P {a, M - 1} ∧ IsCrossing P {a, M} ∧
    IsCrossing Q {a, M - 1} ∧ ¬ IsCrossing Q {a, M})

theorem contact_pairs_distinct (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) :
    ({a, M - 1} : Finset (ZMod n)) ≠ {a, M} := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro he
  have hm : M ∈ ({a, M - 1} : Finset (ZMod n)) := by rw [he]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact hsep.2.1 hm
  · exact prev_ne_self M hm.symm

theorem contact_pair_flips {C P Q : LabelledTuple n} {M a : ZMod n}
    (hP : ContactTests C P M a) (hQ : ContactTests C Q M a)
    (hsc : (chi P a (a + 1) M : ℝ) * (chi Q a (a + 1) M : ℝ) < 0)
    (hne : ∀ forward, chi C a (a + 1) (contactNeighbour forward M) ≠ 0) :
    ∀ forward, IsCrossing P {a, contactLeg forward M} ↔
      ¬ IsCrossing Q {a, contactLeg forward M} := by
  intro forward
  have hq := (not_congr (hQ forward)).symm
  exact (hP forward).trans
    ((sign_contact_complement _ _ _ hsc (hne forward)).trans hq)

theorem exclusive_of_complement {A B : Prop} (h : A ↔ ¬ B) :
    (A ∧ ¬ B) ∨ (B ∧ ¬ A) := by
  classical
  by_cases ha : A
  · exact Or.inl ⟨ha, h.mp ha⟩
  · have hb : B := by
      by_contra hn
      exact ha (h.mpr hn)
    exact Or.inr ⟨hb, ha⟩

theorem contact_symmDiff_of_flips {P Q : LabelledTuple n} {M a : ZMod n}
    (hf : ∀ forward, IsCrossing P {a, contactLeg forward M} ↔
      ¬ IsCrossing Q {a, contactLeg forward M})
    (ho : ∀ s, ¬ ContactAffected M a s → (IsCrossing P s ↔ IsCrossing Q s)) :
    crossingSet P ∆ crossingSet Q = {{a, M - 1}, {a, M}} := by
  classical
  ext s
  simp only [Finset.mem_symmDiff, mem_crossingSet, Finset.mem_insert, Finset.mem_singleton]
  by_cases ha : ContactAffected M a s
  · rcases ha with rfl | rfl
    · exact iff_of_true (exclusive_of_complement (hf false)) (Or.inl rfl)
    · exact iff_of_true (exclusive_of_complement (hf true)) (Or.inr rfl)
  · have he := ho s ha
    constructor
    · rintro (⟨hp, hnq⟩ | ⟨hq, hnp⟩)
      · exact (hnq (he.mp hp)).elim
      · exact (hnp (he.mpr hq)).elim
    · intro h
      exact (ha h).elim

theorem contact_bigon_of_tests {C P Q : LabelledTuple n} {M a : ZMod n}
    (hP : ContactTests C P M a) (hQ : ContactTests C Q M a)
    (hsc : (chi P a (a + 1) M : ℝ) * (chi Q a (a + 1) M : ℝ) < 0)
    (hne : chi C a (a + 1) (M - 1) ≠ 0)
    (he : chi C a (a + 1) (M - 1) = chi C a (a + 1) (M + 1)) :
    BigonCrossingPattern P Q M a := by
  have hp0 := hP false
  have hp1 := hP true
  have hq0 := hQ false
  have hq1 := hQ true
  simp only [contactLeg, contactNeighbour, Bool.false_eq_true, ↓reduceIte] at hp0 hp1 hq0 hq1
  simp only [BigonCrossingPattern, hp0, hp1, hq0, hq1]
  exact sign_contact_bigon _ _ _ _ hsc hne he

theorem contact_sliding_of_tests {C P Q : LabelledTuple n} {M a : ZMod n}
    (hP : ContactTests C P M a) (hQ : ContactTests C Q M a)
    (hsc : (chi P a (a + 1) M : ℝ) * (chi Q a (a + 1) M : ℝ) < 0)
    (hn0 : chi C a (a + 1) (M - 1) ≠ 0) (hn1 : chi C a (a + 1) (M + 1) ≠ 0)
    (hne : chi C a (a + 1) (M - 1) ≠ chi C a (a + 1) (M + 1)) :
    SlidingCrossingPattern P Q M a := by
  have hp0 := hP false
  have hp1 := hP true
  have hq0 := hQ false
  have hq1 := hQ true
  simp only [contactLeg, contactNeighbour, Bool.false_eq_true, ↓reduceIte] at hp0 hp1 hq0 hq1
  simp only [SlidingCrossingPattern, hp0, hp1, hq0, hq1]
  exact sign_contact_sliding _ _ _ _ hsc hn0 hn1 hne

end SM
