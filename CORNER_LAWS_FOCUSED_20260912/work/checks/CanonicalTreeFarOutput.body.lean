namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] silentPolynomialTwoInvertible

theorem canonicalPolynomial_half :
    (MvPolynomial.C (1 / 2 : ℚ) : MvPolynomial (IncreasingBoundaryTriple n) ℚ) =
      ⅟ (2 : MvPolynomial (IncreasingBoundaryTriple n) ℚ) := by
  simpa only [invOf_eq_inv, one_div] using
    (ringHom_map_half (MvPolynomial.C : ℚ →+* MvPolynomial (IncreasingBoundaryTriple n) ℚ))

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- Every ordinary gate variable is specialized to its entire cut product,
not to one linear factor representing the whole composition. -/
theorem tripleOrdinaryWeight_nearFar (g : ZMod n) :
    π.tripleOrdinaryWeight g = π.nearFarWeight (formalBoundaryChi g) (formalBoundaryChi g) := by
  unfold tripleOrdinaryWeight nearFarWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [tripleOrdinaryFactor, canonicalPolynomial_half]
  exact mul_comm _ _

/-- The root weight specializes to the entire reversed-far product,
including the empty product for a unary root. -/
theorem tripleRootWeight_nearFar (g : ZMod n) :
    π.tripleRootWeight g = π.nearFarWeight (formalBoundaryChi g) (-formalBoundaryChi g) := by
  unfold tripleRootWeight nearFarWeight
  apply Finset.prod_congr rfl
  intro k _
  simp only [tripleRootFactor, canonicalPolynomial_half, Pi.neg_apply, sub_neg_eq_add]
  exact mul_comm _ _

end IntervalComposition

/-- The actual prescribed canonical physical-triple polynomial equals the
far-only output as an identity in its unrestricted rational polynomial ring. -/
theorem canonicalTreePolynomial_farOnly (g : ZMod n) (hn : 3 ≤ n) :
    canonicalTreePolynomial g hn = farOnlyOutput (formalBoundaryChi g) (fullBoundaryInterval hn) := by
  unfold canonicalTreePolynomial
  simp_rw [IntervalComposition.tripleOrdinaryWeight_nearFar,
    IntervalComposition.tripleRootWeight_nearFar]
  exact rootedTreeRec_nearFar_farOnly (formalBoundaryChi g) (formalBoundaryChi g) _

/-- Polynomial evaluation at every tuple, including simultaneous silent
zeros, equals the geometric far-only output. No step-function gate at zero
or genericity assumption enters this full polynomial identity. -/
theorem eval_canonicalTreePolynomial_farOnly (P : LabelledTuple n) (g : ZMod n)
    (hn : 3 ≤ n) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) =
      farOnlyOutput (geometricBoundaryArray (R := ℚ) P g) (fullBoundaryInterval hn) := by
  rw [canonicalTreePolynomial_farOnly]
  have h := map_farOnlyOutput (MvPolynomial.eval (canonicalTripleValue P))
    (formalBoundaryChi g) (fullBoundaryInterval hn)
  have he : (fun t => MvPolynomial.eval (canonicalTripleValue P) (formalBoundaryChi g t)) =
      geometricBoundaryArray (R := ℚ) P g := by
    funext t
    exact eval_formalBoundaryChi P g t
  rw [he] at h
  exact h

end
end SM
