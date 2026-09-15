namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Persistence of the ordered signs implies agreement on exactly the
nonzero canonical physical-triple entries used by the polynomial. -/
theorem canonicalTripleValue_agree_of_chi (P Q : LabelledTuple n)
    (hchi : ∀ i j k : ZMod n, chi P i j k ≠ 0 → chi Q i j k = chi P i j k) :
    ∀ t, canonicalTripleValue P t ≠ 0 → canonicalTripleValue Q t = canonicalTripleValue P t := by
  intro t ht
  have hs : chi P (boundaryIndex 0 t.lower) (boundaryIndex 0 t.middle)
      (boundaryIndex 0 t.upper) ≠ 0 := by
    intro hz
    apply ht
    simp [canonicalTripleValue, hz]
  exact congrArg (fun s : SignType => ((s : ℤ) : ℚ)) (hchi _ _ _ hs)

/-- Every function satisfying the already proved continuation specification
has the polynomial value at every weak tuple. The specification mentions
only actual visible chambers and agreement with the original generic tree
coefficient; polynomial agreement is a conclusion, never an assumption. -/
theorem canonicalTreePolynomial_continuation_value (hn : 3 ≤ n) (g : ZMod n)
    (F : WeakTuple n → ℤ)
    (hF : (∀ P Q : WeakTuple n, Q ∈ labelledVisibleChamber P → F Q = F P) ∧
      (∀ Q : GenericTuple n,
        F ⟨Q.val, generic_implies_weak hn Q.property⟩ = treeCoefficient Q.val Q.property.1 g hn))
    (P : WeakTuple n) :
    (F P : ℚ) = MvPolynomial.eval (canonicalTripleValue P.val) (canonicalTreePolynomial g hn) := by
  obtain ⟨Q, hch, hchi⟩ := visible_chamber_generic_preserving_nonzero_chi hn P
  have he := eval_canonicalTreePolynomial_of_nonzero_agree hn P.property g
    (canonicalTripleValue Q.val) (canonicalTripleValue_agree_of_chi P.val Q.val hchi)
  calc
    (F P : ℚ) = (F ⟨Q.val, generic_implies_weak hn Q.property⟩ : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ)) (hF.1 P _ hch).symm
    _ = (treeCoefficient Q.val Q.property.1 g hn : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ)) (hF.2 Q)
    _ = MvPolynomial.eval (canonicalTripleValue Q.val) (canonicalTreePolynomial g hn) :=
      (eval_canonicalTreePolynomial Q.val Q.property.1 g hn).symm
    _ = MvPolynomial.eval (canonicalTripleValue P.val) (canonicalTreePolynomial g hn) := he

/-- Full source cor:polyform, together with the exact existence/uniqueness
interface identifying its continuation. At every weak tuple and each fixed
arbitrary root, the integer continuation has the prescribed polynomial
value, and freezing all nonzero canonical entries yields that constant
in the unrestricted free polynomial ring. Silent entries remain independent;
no value of a step-function gate at zero is introduced. -/
theorem polynomial_form_continuation (hn : 3 ≤ n) (g : ZMod n) :
    ∃! F : WeakTuple n → ℤ,
      ((∀ P Q : WeakTuple n, Q ∈ labelledVisibleChamber P → F Q = F P) ∧
        (∀ Q : GenericTuple n,
          F ⟨Q.val, generic_implies_weak hn Q.property⟩ = treeCoefficient Q.val Q.property.1 g hn)) ∧
      ∀ P : WeakTuple n,
        (F P : ℚ) = MvPolynomial.eval (canonicalTripleValue P.val) (canonicalTreePolynomial g hn) ∧
        canonicalFreezeHom P.val (canonicalTreePolynomial g hn) = MvPolynomial.C (F P : ℚ) := by
  obtain ⟨F, hF, huniq⟩ := A_continuation hn g
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · intro P
    have hv := canonicalTreePolynomial_continuation_value hn g F hF P
    refine ⟨hv, ?_⟩
    rw [canonicalTreePolynomial_freeze_constancy hn P.property g, ← hv]
  · intro G hG
    exact huniq G hG.1

end
end SM
