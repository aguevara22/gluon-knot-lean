import SM.GenericTopology
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Baire.Lemmas

/-! Polynomial avoidance in the actual tuple space. A nonzero witness and
proved ordinary-polynomial restrictions to affine lines imply density of the
nonvanishing locus. No genericity or perturbation oracle is assumed. -/

namespace SM

open Set Topology Polynomial

variable {n : ℕ}

def tupleLine (P Q : LabelledTuple n) (t : ℝ) : LabelledTuple n :=
  fun i => P i + t • (Q i - P i)

@[simp] theorem tupleLine_zero (P Q : LabelledTuple n) : tupleLine P Q 0 = P := by
  funext i
  simp [tupleLine]

@[simp] theorem tupleLine_one (P Q : LabelledTuple n) : tupleLine P Q 1 = Q := by
  funext i
  simp [tupleLine]

theorem continuous_tupleLine (P Q : LabelledTuple n) : Continuous (tupleLine P Q) :=
  continuous_pi fun _ => continuous_const.add (continuous_id.smul continuous_const)

def PolynomialOnTupleLines (f : LabelledTuple n → ℝ) : Prop :=
  ∀ P Q, ∃ p : ℝ[X], ∀ t : ℝ, p.eval t = f (tupleLine P Q t)

theorem dense_nonzero_of_polynomial_on_lines (f : LabelledTuple n → ℝ)
    (hpoly : PolynomialOnTupleLines f) (hw : ∃ Q, f Q ≠ 0) : Dense {P | f P ≠ 0} := by
  obtain ⟨Q, hQ⟩ := hw
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨P, hP⟩ := hne
  obtain ⟨p, hp⟩ := hpoly P Q
  have hp1 : p.eval 1 = f Q := by simpa only [tupleLine_one] using hp 1
  have hpn : p ≠ 0 := by
    intro hz
    rw [hz, Polynomial.eval_zero] at hp1
    exact hQ hp1.symm
  have hd : Dense {t : ℝ | p.eval t ≠ 0} := by
    have hr := (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finite
      (Polynomial.finite_setOfPred_isRoot hpn)
    exact hr.mono (fun _ ht => ht.2)
  have ho : IsOpen ((tupleLine P Q) ⁻¹' U) := hU.preimage (continuous_tupleLine P Q)
  have hn : ((tupleLine P Q) ⁻¹' U).Nonempty :=
    ⟨0, by simpa only [Set.mem_preimage, tupleLine_zero] using hP⟩
  obtain ⟨t, ht, htU⟩ := hd.exists_mem_open ho hn
  refine ⟨tupleLine P Q t, htU, ?_⟩
  change f (tupleLine P Q t) ≠ 0
  rw [← hp t]
  exact ht

noncomputable def lineXPolynomial (P Q : LabelledTuple n) (i : ZMod n) : ℝ[X] :=
  C (P i).1 + X * C ((Q i).1 - (P i).1)

noncomputable def lineYPolynomial (P Q : LabelledTuple n) (i : ZMod n) : ℝ[X] :=
  C (P i).2 + X * C ((Q i).2 - (P i).2)

@[simp] theorem eval_lineXPolynomial (P Q : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    (lineXPolynomial P Q i).eval t = (tupleLine P Q t i).1 := by
  simp [lineXPolynomial, tupleLine]

@[simp] theorem eval_lineYPolynomial (P Q : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    (lineYPolynomial P Q i).eval t = (tupleLine P Q t i).2 := by
  simp [lineYPolynomial, tupleLine]

/-- Finite-family form used for actual geometric constraints. -/
theorem dense_finite_nonzero_family {ι : Type*} [Finite ι]
    (f : ι → LabelledTuple n → ℝ) (hc : ∀ i, Continuous (f i))
    (hp : ∀ i, PolynomialOnTupleLines (f i)) (hw : ∀ i, ∃ Q, f i Q ≠ 0) :
    Dense {P | ∀ i, f i P ≠ 0} := by
  let A : ι → Set (LabelledTuple n) := fun i => {P | f i P ≠ 0}
  have ho : ∀ i, IsOpen (A i) := fun i => isOpen_ne.preimage (hc i)
  have hd : ∀ i, Dense (A i) := fun i => dense_nonzero_of_polynomial_on_lines (f i) (hp i) (hw i)
  have hs := (Set.finite_range A).dense_sInter
    (by rintro _ ⟨i, rfl⟩; exact ho i) (by rintro _ ⟨i, rfl⟩; exact hd i)
  apply hs.mono
  intro P hP i
  exact Set.mem_sInter.mp hP (A i) (Set.mem_range_self i)

end SM
