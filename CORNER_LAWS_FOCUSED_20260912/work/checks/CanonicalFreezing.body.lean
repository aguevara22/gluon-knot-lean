namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Fix precisely the initially nonzero canonical physical-triple entries.
Every zero entry remains its own independent variable in the full free ring. -/
def canonicalFreezeValue (P : LabelledTuple n) (t : IncreasingBoundaryTriple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  if canonicalTripleValue P t = 0 then MvPolynomial.X t
  else MvPolynomial.C (canonicalTripleValue P t)

def canonicalFreezeHom (P : LabelledTuple n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ →+*
      MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (canonicalFreezeValue P)

theorem canonicalFreezeHom_C (P : LabelledTuple n) (a : ℚ) :
    canonicalFreezeHom P (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem canonicalFreezeHom_X_zero (P : LabelledTuple n) (t : IncreasingBoundaryTriple n)
    (ht : canonicalTripleValue P t = 0) :
    canonicalFreezeHom P (MvPolynomial.X t) = MvPolynomial.X t := by
  simp [canonicalFreezeHom, canonicalFreezeValue, ht]

theorem canonicalFreezeHom_X_nonzero (P : LabelledTuple n) (t : IncreasingBoundaryTriple n)
    (ht : canonicalTripleValue P t ≠ 0) :
    canonicalFreezeHom P (MvPolynomial.X t) = MvPolynomial.C (canonicalTripleValue P t) := by
  simp [canonicalFreezeHom, canonicalFreezeValue, ht]

/-- Any assignment agreeing on the fixed entries evaluates a polynomial and
its freezing identically. No realizability condition is imposed on v. -/
theorem eval_canonicalFreezeHom_of_agree (P : LabelledTuple n)
    (v : IncreasingBoundaryTriple n → ℚ)
    (hv : ∀ t, canonicalTripleValue P t ≠ 0 → v t = canonicalTripleValue P t)
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ) :
    MvPolynomial.eval v (canonicalFreezeHom P p) = MvPolynomial.eval v p := by
  have he : (MvPolynomial.eval v).comp (canonicalFreezeHom P) = MvPolynomial.eval v := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, canonicalFreezeHom_C]
    · intro t
      simp only [RingHom.comp_apply]
      by_cases ht : canonicalTripleValue P t = 0
      · rw [canonicalFreezeHom_X_zero P t ht]
      · rw [canonicalFreezeHom_X_nonzero P t ht,
          MvPolynomial.eval_C, MvPolynomial.eval_X, hv t ht]
  exact DFunLike.congr_fun he p

theorem eval_canonicalFreezeHom_base (P : LabelledTuple n)
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalFreezeHom P p) =
      MvPolynomial.eval (canonicalTripleValue P) p :=
  eval_canonicalFreezeHom_of_agree P _ (fun _ _ => rfl) p

/-- The exact parity and canonical label attached to a reversed boundary
triple recover its geometric sign, including zero. -/
theorem boundaryTripleData_geometric (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    (boundaryTripleData g t).2 * canonicalTripleValue P (boundaryTripleData g t).1 =
      geometricBoundaryArray (R := ℚ) P g t := by
  have h := eval_formalBoundaryChi P g t
  rw [formalBoundaryChi_eq, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
  exact h

/-- Every nonzero geometric boundary entry becomes exactly its constant
under the canonical freezing, with the reversed-order parity retained. -/
theorem canonicalFreezeHom_formalBoundaryChi_nonzero (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n)
    (ht : geometricBoundaryArray (R := ℚ) P g t ≠ 0) :
    canonicalFreezeHom P (formalBoundaryChi g t) =
      geometricBoundaryArray (R := MvPolynomial (IncreasingBoundaryTriple n) ℚ) P g t := by
  have he := boundaryTripleData_geometric P g t
  have hc : canonicalTripleValue P (boundaryTripleData g t).1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact ht he.symm
  rw [formalBoundaryChi_eq, map_mul, canonicalFreezeHom_C,
    canonicalFreezeHom_X_nonzero P _ hc, ← map_mul, he]
  exact map_intCast MvPolynomial.C _

end
end SM
