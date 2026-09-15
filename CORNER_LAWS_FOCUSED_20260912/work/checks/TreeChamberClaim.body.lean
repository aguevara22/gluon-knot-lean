namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The exact quantities named in the chirotope-constancy proposition. -/
def TreeDataEqual (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q)
    (g : ZMod n) (hn : 3 ≤ n) : Prop :=
  (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
    π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
    π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
  (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
  treeCoefficient P hP g hn = treeCoefficient Q hQ g hn

/-- Source prop:A-chamber, with actual connected-component chambers and actual
G1 paths. Label changes in the unlabelled chamber carry the physical root,
as required by the source representative convention. -/
theorem A_chamber (hn : 3 ≤ n) :
    (∀ (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q),
      (∀ i j k, chi P i j k = chi Q i j k) →
      ∀ g, TreeDataEqual P Q hP hQ g hn) ∧
    (∀ (P Q : GenericTuple n), Q ∈ labelledChamber P →
      ∀ g, TreeDataEqual P.val Q.val P.property.1 Q.property.1 g hn) ∧
    (∀ (P Q : GenericTuple n), polygonProjection Q ∈ chamber (polygonProjection P) →
      ∃ a : ZMod n, Q ∈ labelledChamber (genericShift a P) ∧
        ∀ g : ZMod n, treeCoefficient Q.val Q.property.1 (g - a) hn =
          treeCoefficient P.val P.property.1 g hn) ∧
    (∀ (P Q : {P : LabelledTuple n // G1 P}) (γ : Path P Q),
      (∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k) →
      ∀ g (s t : unitInterval),
        TreeDataEqual (γ s).val (γ t).val (γ s).property (γ t).property g hn) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ hchi g
    exact tree_data_eq_of_chi hP hQ hchi g hn
  · intro P Q hQ g
    exact tree_data_labelled_chamber_constant P Q hQ g hn
  · intro P Q hQ
    exact treeCoefficient_quotient_chamber_transport P Q hn hQ
  · intro P Q γ hchi g s t
    exact tree_data_G1_path_constant γ hchi g hn s t

end

end SM
