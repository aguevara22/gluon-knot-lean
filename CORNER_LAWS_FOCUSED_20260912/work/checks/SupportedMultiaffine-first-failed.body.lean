namespace SM

noncomputable section
variable {σ : Type*} [DecidableEq σ]

/-- A direct degree bound in the unrestricted polynomial ring: degree at most
one on S, and zero outside S. This is not a quotient or an evaluation relation. -/
def SupportedMultiaffine (p : MvPolynomial σ ℚ) (S : Finset σ) : Prop :=
  ∀ x, p.degreeOf x ≤ if x ∈ S then 1 else 0

namespace SupportedMultiaffine

theorem degree_le_one {p : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (x : σ) : p.degreeOf x ≤ 1 := by
  have h := hp x
  split_ifs at h <;> omega

theorem constant (c : ℚ) (S : Finset σ) : SupportedMultiaffine (MvPolynomial.C c) S := by
  intro x
  rw [MvPolynomial.degreeOf_C]
  exact Nat.zero_le _

theorem zero (S : Finset σ) : SupportedMultiaffine (0 : MvPolynomial σ ℚ) S := by
  simpa using constant (σ := σ) 0 S

theorem one (S : Finset σ) : SupportedMultiaffine (1 : MvPolynomial σ ℚ) S := by
  simpa using constant (σ := σ) 1 S

theorem X_singleton (x : σ) : SupportedMultiaffine (MvPolynomial.X x) {x} := by
  intro y
  simp only [MvPolynomial.degreeOf_X, Finset.mem_singleton]
  exact le_rfl

theorem mono {p : MvPolynomial σ ℚ} {S T : Finset σ}
    (hp : SupportedMultiaffine p S) (hST : S ⊆ T) : SupportedMultiaffine p T := by
  intro x
  have h := hp x
  by_cases hs : x ∈ S
  · simpa only [if_pos hs, if_pos (hST hs)] using h
  · simp only [if_neg hs] at h
    exact le_trans h (Nat.zero_le _)

theorem neg {p : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) : SupportedMultiaffine (-p) S := by
  intro x
  simpa only [MvPolynomial.degreeOf_neg] using hp x

theorem add {p q : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (hq : SupportedMultiaffine q S) :
    SupportedMultiaffine (p + q) S := by
  intro x
  exact le_trans (MvPolynomial.degreeOf_add_le x p q) (max_le (hp x) (hq x))

theorem sub {p q : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (hq : SupportedMultiaffine q S) :
    SupportedMultiaffine (p - q) S := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem constant_mul {p : MvPolynomial σ ℚ} {S : Finset σ}
    (hp : SupportedMultiaffine p S) (c : ℚ) :
    SupportedMultiaffine (MvPolynomial.C c * p) S := by
  intro x
  exact le_trans (MvPolynomial.degreeOf_C_mul_le p x c) (hp x)

/-- Distinct supports prevent adding two positive exponents of one variable. -/
theorem mul_disjoint {p q : MvPolynomial σ ℚ} {S T : Finset σ}
    (hp : SupportedMultiaffine p S) (hq : SupportedMultiaffine q T)
    (hST : Disjoint S T) : SupportedMultiaffine (p * q) (S ∪ T) := by
  intro x
  have h := MvPolynomial.degreeOf_mul_le x p q
  have hpx := hp x
  have hqx := hq x
  have hn : ¬ (x ∈ S ∧ x ∈ T) := fun hh => (Finset.disjoint_left.mp hST) hh.1 hh.2
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
    simp only [hs, ht, Finset.mem_union, or_self, if_true, if_false] at * <;> omega

/-- The finite product bound includes empty products and zero factors. -/
theorem prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → MvPolynomial σ ℚ) (S : ι → Finset σ)
    (hp : ∀ i, SupportedMultiaffine (p i) (S i))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) :
    SupportedMultiaffine (∏ i ∈ s, p i) (s.biUnion S) := by
  induction s using Finset.induction_on with
  | empty => simpa using one (σ := σ) ∅
  | @insert i s hi ih =>
      have hd : Disjoint (S i) (s.biUnion S) := by
        apply Finset.disjoint_left.mpr
        intro x hx hu
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hu
        have hij : i ≠ j := by intro h; subst j; exact hi hj
        exact (Finset.disjoint_left.mp (hS hij)) hx hxj
      simpa only [Finset.prod_insert hi, Finset.biUnion_insert] using
        (hp i).mul_disjoint ih hd

theorem sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℚ) (S : Finset σ)
    (hp : ∀ i ∈ s, SupportedMultiaffine (p i) S) :
    SupportedMultiaffine (∑ i ∈ s, p i) S := by
  intro x
  apply le_trans (MvPolynomial.degreeOf_sum_le x s p)
  exact Finset.sup_le (fun i hi => hp i hi x)

end SupportedMultiaffine
end
end SM
