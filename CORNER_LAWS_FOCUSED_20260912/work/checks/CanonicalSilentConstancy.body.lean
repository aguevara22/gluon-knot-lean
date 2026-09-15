namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] silentPolynomialTwoInvertible

/-- The residual formal boundary entries after fixing the nonzero physical
canonical variables, measured from the entire geometric constant array. -/
def canonicalSilentPerturbation (P : LabelledTuple n) (g : ZMod n) :
    TripleArray n (MvPolynomial (IncreasingBoundaryTriple n) ℚ) :=
  fun t => canonicalFreezeHom P (formalBoundaryChi g t) - geometricBoundaryArray P g t

theorem canonicalSilentPerturbation_support (P : LabelledTuple n) (g : ZMod n) :
    ∀ t, geometricBoundaryArray (R := ℚ) P g t ≠ 0 →
      canonicalSilentPerturbation P g t = 0 := by
  intro t ht
  unfold canonicalSilentPerturbation
  rw [canonicalFreezeHom_formalBoundaryChi_nonzero P g t ht, sub_self]

theorem canonicalFreezeBoundary_split (P : LabelledTuple n) (g : ZMod n) :
    (fun t => canonicalFreezeHom P (formalBoundaryChi g t)) =
      geometricBoundaryArray P g + canonicalSilentPerturbation P g := by
  funext t
  simp only [Pi.add_apply, canonicalSilentPerturbation]
  ring

/-- Formal constancy of the prescribed tree polynomial after exactly the
nonzero canonical chirotope entries are fixed. All zero variables remain
independent in the unrestricted rational polynomial ring. -/
theorem canonicalTreePolynomial_freeze_constancy (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) :
    canonicalFreezeHom P (canonicalTreePolynomial g hn) =
      MvPolynomial.C (MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn)) := by
  rw [eval_canonicalTreePolynomial_farOnly, canonicalTreePolynomial_farOnly]
  have hm := map_farOnlyOutput (canonicalFreezeHom P)
    (formalBoundaryChi g) (fullBoundaryInterval hn)
  rw [canonicalFreezeBoundary_split,
    silent_supported_output hn hP g (canonicalSilentPerturbation P g)
      (canonicalSilentPerturbation_support P g)] at hm
  have hc := map_farOnlyOutput
    (MvPolynomial.C : ℚ →+* MvPolynomial (IncreasingBoundaryTriple n) ℚ)
    (geometricBoundaryArray (R := ℚ) P g) (fullBoundaryInterval hn)
  rw [map_geometricBoundaryArray] at hc
  exact hm.trans hc.symm

/-- The formal identity also controls every rational assignment of silent
entries, including assignments that are not realizable chirotopes. -/
theorem eval_canonicalTreePolynomial_of_nonzero_agree (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (v : IncreasingBoundaryTriple n → ℚ)
    (hv : ∀ t, canonicalTripleValue P t ≠ 0 → v t = canonicalTripleValue P t) :
    MvPolynomial.eval v (canonicalTreePolynomial g hn) =
      MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) := by
  rw [← eval_canonicalFreezeHom_of_agree P v hv,
    canonicalTreePolynomial_freeze_constancy hn hP g, MvPolynomial.eval_C]

end
end SM
