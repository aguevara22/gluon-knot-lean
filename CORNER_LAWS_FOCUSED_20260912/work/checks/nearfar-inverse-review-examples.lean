namespace NearFarInverseIndependentReview
open SM
variable {n : ℕ} [NeZero n]

-- Every source increasing natural triple in0..N is admitted without a
-- geometric restriction or a selected subset of triples.
theorem all_raw_increasing_triples (hn : 3 ≤ n) (x y z : ℕ)
    (hxy : x < y) (hyz : y < z) (hz : z ≤ n - 1) :
    ∃ t : IncreasingBoundaryTriple n,
      t.lower.val = x ∧ t.middle.val = y ∧ t.upper.val = z := by
  exact ⟨⟨⟨x, by omega⟩, ⟨y, by omega⟩, ⟨z, by omega⟩, hxy, hyz⟩, rfl, rfl, rfl⟩

theorem full_triple_domain_finite : Finite (IncreasingBoundaryTriple n) := by
  let f : IncreasingBoundaryTriple n → Fin n × Fin n × Fin n :=
    fun t => (t.lower, t.middle, t.upper)
  apply Finite.of_injective f
  rintro ⟨x,y,z,hxy,hyz⟩ ⟨a,b,c,hab,hbc⟩ he
  have hx := congrArg (fun p => p.1) he
  have hy := congrArg (fun p => p.2.1) he
  have hz := congrArg (fun p => p.2.2) he
  change x = a at hx
  change y = b at hy
  change z = c at hz
  cases hx; cases hy; cases hz
  rfl

theorem full_interval_domain_finite : Finite (BoundaryInterval n) := by
  let f : BoundaryInterval n → Fin n × Fin n := fun I => (I.left, I.right)
  apply Finite.of_injective f
  rintro ⟨x,y,hxy⟩ ⟨a,b,hab⟩ he
  have hx := congrArg (fun p => p.1) he
  have hy := congrArg (fun p => p.2) he
  change x = a at hx
  change y = b at hy
  cases hx; cases hy
  rfl

theorem unary_term_is_exact {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) (X : IntervalArray n R) (I : BoundaryInterval n) :
    (IntervalComposition.single I).nearFarWeight D H *
      ∏ k : Fin (IntervalComposition.single I).parts,
        X ((IntervalComposition.single I).part k) = X I := by
  rw [(IntervalComposition.single I).nearFarWeight_one D H rfl,
    IntervalComposition.single_product X I, one_mul]

-- Clearing the two in every factor checks the actual half convention in
-- arbitrary commutative rings with invertible two, including empty products.
theorem every_half_factor_is_exact {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) {I : BoundaryInterval n} (π : IntervalComposition I) :
    π.nearFarWeight D H * (2 : R) ^ (π.parts - 1) =
      ∏ k : Fin (π.parts - 1), (D (π.nearTriple k) - H (π.farTriple k)) := by
  have he : ∀ k : Fin (π.parts - 1),
      ((D (π.nearTriple k) - H (π.farTriple k)) * ⅟ (2 : R)) * 2 =
        D (π.nearTriple k) - H (π.farTriple k) := by
    intro k
    rw [mul_assoc, invOf_mul_self, mul_one]
  have hp := Finset.prod_congr (s₁ := Finset.univ) rfl (fun k _ => he k)
  rw [Finset.prod_mul_distrib] at hp
  simpa only [IntervalComposition.nearFarWeight, Fin.prod_const] using hp

theorem unit_array_is_leaf_indicator {R : Type*} [CommRing R]
    (I : BoundaryInterval n) :
    boundaryUnitArray (R := R) I = if I.leaves = 1 then 1 else 0 := by
  have he : I.right.val = I.left.val + 1 ↔ I.leaves = 1 := by
    have := I.increasing
    change I.right.val = I.left.val + 1 ↔ I.right.val - I.left.val = 1
    omega
  simp only [boundaryUnitArray, he]

theorem inverse_base_coordinate {R : Type*} [CommRing R]
    (weight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (Y : IntervalArray n R) (I : BoundaryInterval n) (hI : I.leaves = 1) :
    triangularInverse weight Y I = Y I := by
  letI : IsEmpty {π : IntervalComposition I // 2 ≤ π.parts} := ⟨fun π => by
    have hl := π.val.part_leaves_lt π.property ⟨0, π.val.parts_pos⟩
    have hp := (π.val.part ⟨0, π.val.parts_pos⟩).leaves_pos
    omega⟩
  rw [triangularInverse]
  simp

theorem unique_solution_for_every_target {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) (Y : IntervalArray n R) :
    ∃! X : IntervalArray n R, nearFarTransform D H X = Y := by
  refine ⟨nearFarInverse D H Y, nearFarTransform_inverse D H Y, ?_⟩
  intro X hX
  exact nearFar_solution_unique D H X Y hX

theorem inverse_is_coordinate_polynomial {R : Type*} [CommRing R] [Invertible (2 : R)]
    (D H : TripleArray n R) (Y : IntervalArray n R) (I : BoundaryInterval n) :
    MvPolynomial.eval₂Hom (RingHom.id R) Y
      (triangularInversePolynomial (fun _ π => π.nearFarWeight D H) I) =
        nearFarInverse D H Y I :=
  triangularInversePolynomial_eval _ Y I

theorem zero_triangular_weights_give_identity {R : Type*} [CommRing R]
    (Y : IntervalArray n R) : triangularInverse (fun _ _ => (0 : R)) Y = Y := by
  funext I
  rw [triangularInverse]
  simp

theorem geometric_arrays_use_same_physical_root {R : Type*} [CommRing R]
    (P : LabelledTuple n) (g a : ZMod n) :
    geometricBoundaryArray (R := R) (shift a P) (g - a) =
      geometricBoundaryArray (R := R) P g :=
  geometricBoundaryArray_shift P g a

end NearFarInverseIndependentReview
