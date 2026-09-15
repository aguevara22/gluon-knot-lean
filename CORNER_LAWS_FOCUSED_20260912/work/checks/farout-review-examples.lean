namespace FaroutIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n]

theorem all_physical_positions_once (J : BoundaryInterval n) (x : Fin n)
    (hl : J.left ≤ x) (hr : x ≤ J.right) :
    ∃! k : Fin (J.leaves + 1), J.globalPosition k = x := by
  refine ⟨J.localPosition x hl hr, J.global_localPosition x hl hr, ?_⟩
  intro k hk
  exact J.globalPosition_strict.injective (hk.trans (J.global_localPosition x hl hr).symm)

theorem translated_leaf_count (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    (J.liftInterval K).leaves = K.leaves := by
  unfold BoundaryInterval.leaves BoundaryInterval.liftInterval BoundaryInterval.globalPosition
  simp only
  omega

theorem all_physical_subintervals (J I : BoundaryInterval n)
    (hl : J.left ≤ I.left) (hr : I.right ≤ J.right) :
    ∃ K : BoundaryInterval (J.leaves + 1), J.liftInterval K = I := by
  have hli : J.left ≤ I.right := le_trans hl (le_of_lt I.increasing)
  have hri : I.left ≤ J.right := le_trans (le_of_lt I.increasing) hr
  let K : BoundaryInterval (J.leaves + 1) :=
    ⟨J.localPosition I.left hl hri, J.localPosition I.right hli hr, by
      have hi := I.increasing
      change I.left.val < I.right.val at hi
      change J.left.val ≤ I.left.val at hl
      change I.left.val - J.left.val < I.right.val - J.left.val
      omega⟩
  refine ⟨K, ?_⟩
  apply BoundaryInterval.eq_of_endpoints
  · exact J.global_localPosition I.left hl hri
  · exact J.global_localPosition I.right hli hr

theorem all_raw_parts_and_cuts (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) :
    (IntervalComposition.liftComposition J π).parts = π.parts ∧
    (∀ k : Fin (π.parts + 1),
      ((IntervalComposition.liftComposition J π).cut k).val = J.left.val + (π.cut k).val) ∧
    IntervalComposition.lowerComposition J (IntervalComposition.liftComposition J π) = π :=
  ⟨rfl, fun _ => rfl, IntervalComposition.lower_liftComposition J π⟩

theorem unary_is_preserved (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    IntervalComposition.liftComposition J (IntervalComposition.single K) =
      IntervalComposition.single (J.liftInterval K) :=
  IntervalComposition.eq_single_of_parts_eq_one _ rfl

theorem complete_composition_cardinality (J : BoundaryInterval n)
    (K : BoundaryInterval (J.leaves + 1)) :
    Fintype.card (IntervalComposition K) = Fintype.card (IntervalComposition (J.liftInterval K)) :=
  Fintype.card_congr (IntervalComposition.restrictionEquiv J K)

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem actual_child_product (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (X : IntervalArray n R) :
    (∏ k : Fin π.parts, restrictIntervalArray J X (π.part k)) =
      ∏ k : Fin (IntervalComposition.liftComposition J π).parts,
        X ((IntervalComposition.liftComposition J π).part k) := rfl

theorem all_actual_samples (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (D H : TripleArray n R) (k : Fin (π.parts - 1)) :
    restrictTripleArray J D (π.nearTriple k) =
      D ((IntervalComposition.liftComposition J π).nearTriple k) ∧
    restrictTripleArray J H (π.farTriple k) =
      H ((IntervalComposition.liftComposition J π).farTriple k) := ⟨rfl, rfl⟩

theorem local_inverse_solves_actual_restriction (J : BoundaryInterval n) (D H : TripleArray n R)
    (Y : IntervalArray n R) :
    nearFarTransform (restrictTripleArray J D) (restrictTripleArray J H)
      (restrictIntervalArray J (nearFarInverse D H Y)) = restrictIntervalArray J Y := by
  rw [nearFarTransform_restrict, nearFarTransform_inverse]

theorem restricted_c_is_actual_local_inverse (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    restrictIntervalArray J (farOnlyCoordinates (geometricBoundaryArray (R := R) P g)) =
      nearFarInverse 0 (geometricBoundaryArray (restrictedWordTuple P g J) 0) boundaryUnitArray := by
  rw [farOnlyCoordinates_restrict, ← geometricBoundaryArray_restrictedWord]
  rfl

theorem full_contiguous_word_and_directed_root (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    (∀ k : Fin (J.leaves + 1), boundaryWord (restrictedWordTuple P g J) 0 k =
      boundaryWord P g (J.globalPosition k)) ∧
    restrictedWordTuple P g J 0 = boundaryWord P g J.right ∧
    restrictedWordTuple P g J 1 = boundaryWord P g J.left ∧
    edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right :=
  ⟨restrictedWord_boundary P g J, restrictedWord_last_vertex P g J,
    restrictedWord_first_vertex P g J, restrictedWord_closing_edge P g J⟩

theorem nonleaf_has_three_vertices (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) :
    3 ≤ J.leaves + 1 := by omega

theorem local_root_without_global_G1 (hn : 3 ≤ n) (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) (hlocal : G1 (restrictedWordTuple P g J)) :
    farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
      (treeCoefficient (restrictedWordTuple P g J) hlocal 0 (by omega) : R) :=
  ((farout n R hn).2.2.2.2 P g J hJ hlocal).2

theorem aggregate_polynomials_both_directions (hn : 3 ≤ n) (D H : TripleArray n R) :
    ∃ Ψ : BoundaryInterval n → MvPolynomial (BoundaryInterval n) R,
      (∀ Y : IntervalArray n R, nearFarTransform D H
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) Y (Ψ I)) = Y) ∧
      (∀ X : IntervalArray n R,
        (fun I => MvPolynomial.eval₂Hom (RingHom.id R) (nearFarTransform D H X) (Ψ I)) = X) :=
  ((farout n R hn).1 D H).1

theorem aggregate_factorization_on_every_array (hn : 3 ≤ n)
    (D H : TripleArray n R) (X : IntervalArray n R) :
    nearFarTransform D H X = farTransform H (nearTransform D X) :=
  congrFun ((farout n R hn).1 D H).2 X

theorem aggregate_geometry_and_actual_full_root (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : G1 P) (g : ZMod n) :
    nearFarTransform (geometricBoundaryArray (R := R) P g) (geometricBoundaryArray P g)
      (fun I => (openTreeSum P hP g I : R)) = boundaryUnitArray ∧
    (treeCoefficient P hP g hn : R) =
      farOnlyOutput (geometricBoundaryArray P g) (fullBoundaryInterval hn) :=
  ⟨((farout n R hn).2.1 P hP g).1, ((farout n R hn).2.1 P hP g).2.2⟩

theorem aggregate_near_freedom_has_real_solutions (hn : 3 ≤ n) (D₁ D₂ H : TripleArray n R) :
    nearFarTransform D₁ (-H) (nearFarInverse D₁ H boundaryUnitArray) =
      nearFarTransform D₂ (-H) (nearFarInverse D₂ H boundaryUnitArray) :=
  (farout n R hn).2.2.1 D₁ D₂ H _ _ (nearFarTransform_inverse _ _ _) (nearFarTransform_inverse _ _ _)

theorem aggregate_open_leaf_and_nonleaf (hn : 3 ≤ n) (H : TripleArray n R)
    (J : BoundaryInterval n) :
    (2 ≤ J.leaves → farTransform H (farOnlyCoordinates H) J = 0) ∧
    (J.leaves = 1 → farTransform H (farOnlyCoordinates H) J = 1 ∧ farOnlyOutput H J = 1) :=
  (farout n R hn).2.2.2.1 H J

end
end FaroutIndependentReview
