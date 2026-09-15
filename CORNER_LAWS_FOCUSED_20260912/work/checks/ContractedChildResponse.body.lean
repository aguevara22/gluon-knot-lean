namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- Every complete contracted composition has exactly one child containing
the distinguished formal leaf. Adjacent children may share endpoints, but
cannot both contain its positive length. -/
theorem IntervalComposition.unique_contracted_leaf_child (t : IncreasingBoundaryTriple n)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) :
    ∃! k : Fin π.parts,
      (π.part k).left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ (π.part k).right := by
  obtain ⟨k, hk⟩ := containing_child_of_survivingCuts t (expandComposition t π)
    ((t.expandInterval_contains J).mpr hJ) (expandComposition_survives t π)
  have hc := (t.expandInterval_contains (π.part k)).mp hk
  exact ⟨k, hc, fun l hl => π.part_contains_unique t.contractedLeaf hl hc⟩

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- A conditional product step for the interval-length induction. The only
response premise is on containing children; off-leaf factors are the actual
inverse coordinates, whose transport is already proved. No division is used. -/
theorem expanded_child_product_response (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    {J : BoundaryInterval t.contractedSize} (π : IntervalComposition J)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) (s : R)
    (hchild : ∀ k : Fin π.parts,
      (π.part k).left ≤ t.contractedLeaf.left → t.contractedLeaf.right ≤ (π.part k).right →
      farOnlyCoordinates H₂ (t.expandInterval (π.part k)) -
        farOnlyCoordinates H₁ (t.expandInterval (π.part k)) =
        s * farOnlyCoordinates (contractedTripleArray t H₁) (π.part k)) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part k))) -
      (∏ k : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part k))) =
      s * ∏ k : Fin π.parts, farOnlyCoordinates (contractedTripleArray t H₁) (π.part k) := by
  classical
  obtain ⟨k, hk, _⟩ := π.unique_contracted_leaf_child t hJ
  have hspan : ((IntervalComposition.expandComposition t π).part k).left ≤ t.spanInterval.left ∧
      t.spanInterval.right ≤ ((IntervalComposition.expandComposition t π).part k).right :=
    (t.expandInterval_contains (π.part k)).mpr hk
  have hd := (IntervalComposition.expandComposition t π).child_product_difference t.spanInterval
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂)
    (fun K hK => farOnlyCoordinates_unchanged_off_critical H₁ H₂ t hH K hK) k hspan
  change (∏ l : Fin π.parts, farOnlyCoordinates H₂ (t.expandInterval (π.part l))) -
    (∏ l : Fin π.parts, farOnlyCoordinates H₁ (t.expandInterval (π.part l))) =
    (farOnlyCoordinates H₂ (t.expandInterval (π.part k)) -
      farOnlyCoordinates H₁ (t.expandInterval (π.part k))) *
      ∏ l ∈ Finset.univ.erase k, farOnlyCoordinates H₁ (t.expandInterval (π.part l)) at hd
  have hp : (∏ l ∈ Finset.univ.erase k, farOnlyCoordinates H₁ (t.expandInterval (π.part l))) =
      ∏ l ∈ Finset.univ.erase k, farOnlyCoordinates (contractedTripleArray t H₁) (π.part l) := by
    apply Finset.prod_congr rfl
    intro l hl
    exact farOnlyCoordinates_expanded_off_leaf t H₁ (π.part l)
      (π.other_part_excludes t.contractedLeaf k hk l (Finset.mem_erase.mp hl).1)
  rw [hchild k hk.1 hk.2, hp] at hd
  rw [hd]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun l => farOnlyCoordinates (contractedTripleArray t H₁) (π.part l)) (Finset.mem_univ k)]
  ring

/-- An original composition whose cut list does not survive has no child
containing the whole critical interval, so its entire child product agrees
on the two sides. This justifies discarding its difference, not its value. -/
theorem nonsurviving_child_product_unchanged (t : IncreasingBoundaryTriple n)
    (H₁ H₂ : TripleArray n R) (hH : ∀ u, u ≠ t → H₁ u = H₂ u)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hπ : ¬ IntervalComposition.SurvivingCuts t π) :
    (∏ k : Fin π.parts, farOnlyCoordinates H₁ (π.part k)) =
      ∏ k : Fin π.parts, farOnlyCoordinates H₂ (π.part k) := by
  apply π.child_product_unchanged t.spanInterval
    (farOnlyCoordinates H₁) (farOnlyCoordinates H₂)
    (fun K hK => farOnlyCoordinates_unchanged_off_critical H₁ H₂ t hH K hK)
  intro k hk
  exact hπ (π.survivingCuts_of_containing_child t k hk)

end
end SM
