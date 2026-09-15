namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every near and far gate is transported at its actual collapsed triple.
No sign-square or nonzero assumption is needed in an avoiding interval. -/
theorem nearFarWeight_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (π : IntervalComposition I) (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ) :
    π.nearFarWeight (tripleLift s D0 tD) (tripleLift s H0 tH) =
      (collapseComposition s I hI havoid π).nearFarWeight D0 H0 := by
  change (∏ k : Fin (π.parts - 1),
    (tripleLift s D0 tD (π.nearTriple k) - tripleLift s H0 tH (π.farTriple k)) * ⅟ (2 : ℚ)) =
      ∏ k : Fin (π.parts - 1),
        (D0 ((collapseComposition s I hI havoid π).nearTriple k) -
          H0 ((collapseComposition s I hI havoid π).farTriple k)) * ⅟ (2 : ℚ)
  apply Finset.prod_congr rfl
  intro k hk
  have hn := nearTriple_plain_of_avoiding s I havoid π k
  have hf := farTriple_plain_of_avoiding s I havoid π k
  rw [tripleLift_plain s D0 tD _ hn, tripleLift_plain s H0 tH _ hf,
    collapseComposition_nearTriple s I hI havoid π k hn,
    collapseComposition_farTriple s I hI havoid π k hf]

/-- The proposed ordinary array reads the exact collapsed child, including
children ending at A or starting at B. Their avoidance is derived from I. -/
theorem ordinaryLift_child_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (π : IntervalComposition I) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (k : Fin π.parts) :
    ordinaryLift s etaMinus etaPlus t b0 (π.part k) =
      b0 ((collapseComposition s I hI havoid π).part k) := by
  have hpart := composition_part_avoiding s I havoid π k
  rw [collapseComposition_part s I hI havoid π k,
    ordinaryLift_plain s etaMinus etaPlus t b0 (π.part k) hpart]

/-- Transport the complete child product without cancellation of any factor. -/
theorem ordinaryLift_children_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (π : IntervalComposition I) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    (∏ k : Fin π.parts, ordinaryLift s etaMinus etaPlus t b0 (π.part k)) =
      ∏ k : Fin (collapseComposition s I hI havoid π).parts,
        b0 ((collapseComposition s I hI havoid π).part k) := by
  change (∏ k : Fin π.parts, ordinaryLift s etaMinus etaPlus t b0 (π.part k)) =
    ∏ k : Fin π.parts, b0 ((collapseComposition s I hI havoid π).part k)
  apply Finset.prod_congr rfl
  intro k hk
  exact ordinaryLift_child_avoiding s I hI havoid π etaMinus etaPlus t b0 k

/-- The actual complete avoiding transform equals its core transform.
The reindexing is the proved composition equivalence and includes unary terms. -/
theorem nearFarTransform_ordinaryLift_avoiding (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 tD) (tripleLift s H0 tH)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      nearFarTransform D0 H0 b0 (collapseInterval s I hI) := by
  unfold nearFarTransform
  apply Fintype.sum_equiv (avoidingCompositionEquiv s I hI havoid)
  intro π
  rw [← collapseComposition_eq_avoidingCompositionEquiv s I hI havoid π,
    nearFarWeight_avoiding s I hI havoid π D0 H0 tD tH,
    ordinaryLift_children_avoiding s I hI havoid π etaMinus etaPlus t b0]

/-- With the core ordinary array defined by the actual triangular inverse,
every avoiding parent coordinate satisfies its required unit equation. -/
theorem ordinaryLift_equation_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) :
    nearFarTransform (parentNear s t) (tripleLift s H0 t)
      (ordinaryLift s etaMinus etaPlus t (nearFarInverse (coreNear s t) H0 boundaryUnitArray)) I =
      boundaryUnitArray I := by
  unfold parentNear
  rw [nearFarTransform_ordinaryLift_avoiding s I hI havoid,
    nearFarTransform_inverse, collapseInterval_unit_avoiding s I hI havoid]

/-- Negating every far datum commutes with the complete plain/exceptional lift. -/
theorem tripleLift_neg {R : Type*} [Neg R] (s : Fin n)
    (H0 : TripleArray n R) (t : Fin n → R) :
    tripleLift s (-H0) (-t) = -(tripleLift s H0 t) := by
  funext T
  change tripleLift s (-H0) (-t) T = -(tripleLift s H0 t T)
  unfold tripleLift
  split_ifs <;> rfl

/-- The root-sign transform also transports completely on an avoiding interval.
This follows from the same actual summand correspondence, not a near-array
independence assertion about individual open sums. -/
theorem rootTransform_ordinaryLift_avoiding (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 tD) (-(tripleLift s H0 tH))
      (ordinaryLift s etaMinus etaPlus t b0) I =
      nearFarTransform D0 (-H0) b0 (collapseInterval s I hI) := by
  rw [← tripleLift_neg s H0 tH]
  exact nearFarTransform_ordinaryLift_avoiding s I hI havoid D0 (-H0) tD (-tH)
    etaMinus etaPlus t b0

end
end SM.SoftDuplication
