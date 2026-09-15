namespace SM

noncomputable section

universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Every coordinate of the recursive inverse commutes with a ring homomorphism:
the recursion uses only the mapped scalars, subtraction, finite sums and products. -/
theorem map_triangularInverse (f : R →+* S)
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) (I : BoundaryInterval n) :
    f (triangularInverse weight Y I) =
      triangularInverse (fun J π => f (weight J π)) (fun J => f (Y J)) I := by
  conv_lhs => rw [triangularInverse]
  conv_rhs => rw [triangularInverse]
  simp only [map_sub, map_sum, map_mul, map_prod]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact map_triangularInverse f weight Y (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

/-- The actual inverse coordinate as a polynomial in the target array entries. -/
def triangularInversePolynomial
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : MvPolynomial (BoundaryInterval n) R :=
  triangularInverse (fun J π => MvPolynomial.C (weight J π)) MvPolynomial.X I

theorem triangularInversePolynomial_eval
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : BoundaryInterval n → R) (I : BoundaryInterval n) :
    MvPolynomial.eval₂Hom (RingHom.id R) Y (triangularInversePolynomial weight I) =
      triangularInverse weight Y I := by
  simpa only [triangularInversePolynomial, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', RingHom.id_apply] using
    map_triangularInverse (MvPolynomial.eval₂Hom (RingHom.id R) Y)
      (fun J π => MvPolynomial.C (weight J π)) MvPolynomial.X I

/-- Explicit coordinate polynomials giving both inverse identities for the
source near-far transform. Factorization and geometric output are separate claims. -/
theorem nearFar_has_polynomial_inverse [Invertible (2 : R)] (D H : TripleArray n R) :
    ∃ Ψ : BoundaryInterval n → MvPolynomial (BoundaryInterval n) R,
      (∀ Y : IntervalArray n R,
        nearFarTransform D H (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = Y) ∧
      (∀ X : IntervalArray n R,
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) (nearFarTransform D H X) (Ψ I)) = X) := by
  let Ψ := triangularInversePolynomial (fun _ π => π.nearFarWeight D H)
  have he (Y : IntervalArray n R) :
      (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = nearFarInverse D H Y :=
    funext (fun I => triangularInversePolynomial_eval _ Y I)
  refine ⟨Ψ, ?_, ?_⟩
  · intro Y
    rw [he Y]
    exact nearFarTransform_inverse D H Y
  · intro X
    rw [he (nearFarTransform D H X)]
    exact nearFarInverse_transform D H X

end

end SM
