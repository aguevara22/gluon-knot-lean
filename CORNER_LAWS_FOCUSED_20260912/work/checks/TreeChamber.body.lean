namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

/-- All quantities in the source chirotope-constancy clause, on G1 alone. -/
theorem tree_data_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
      π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
    (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn :=
  ⟨fun _ π => ⟨π.ordinaryWeight_eq_of_chi hP hQ hchi g,
    π.rootWeight_eq_of_chi hP hQ hchi g⟩,
    openTreeSum_eq_of_chi hP hQ hchi g, treeCoefficient_eq_of_chi hP hQ hchi g hn⟩

/-- The labelled chamber is the actual connected component of the generic locus.
Its continuous sign maps have discrete target, so they are constant on it. -/
theorem labelled_chamber_chi_constant (P Q : GenericTuple n) (hQ : Q ∈ labelledChamber P)
    (i j k : ZMod n) : chi P.val i j k = chi Q.val i j k := by
  exact isPreconnected_connectedComponent.constant
    (continuous_generic_chi i j k).continuousOn mem_connectedComponent hQ

theorem tree_data_labelled_chamber_constant (P Q : GenericTuple n)
    (hQ : Q ∈ labelledChamber P) (g : ZMod n) (hn : 3 ≤ n) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight P.val P.property.1 g = π.ordinaryWeight Q.val Q.property.1 g ∧
      π.rootWeight P.val P.property.1 g = π.rootWeight Q.val Q.property.1 g) ∧
    (∀ I, openTreeSum P.val P.property.1 g I = openTreeSum Q.val Q.property.1 g I) ∧
    treeCoefficient P.val P.property.1 g hn = treeCoefficient Q.val Q.property.1 g hn :=
  tree_data_eq_of_chi P.property.1 Q.property.1 (labelled_chamber_chi_constant P Q hQ) g hn

/-- The path clause retains G1 only. Its asserted constant chirotope already
forces all values to agree; no further geometric condition is needed. -/
theorem tree_data_G1_path_constant {P Q : {P : LabelledTuple n // G1 P}}
    (γ : Path P Q)
    (hchi : ∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k)
    (g : ZMod n) (hn : 3 ≤ n) (s t : unitInterval) :
    (∀ (I : BoundaryInterval n) (π : IntervalComposition I),
      π.ordinaryWeight (γ s).val (γ s).property g =
        π.ordinaryWeight (γ t).val (γ t).property g ∧
      π.rootWeight (γ s).val (γ s).property g = π.rootWeight (γ t).val (γ t).property g) ∧
    (∀ I, openTreeSum (γ s).val (γ s).property g I =
      openTreeSum (γ t).val (γ t).property g I) ∧
    treeCoefficient (γ s).val (γ s).property g hn =
      treeCoefficient (γ t).val (γ t).property g hn :=
  tree_data_eq_of_chi (γ s).property (γ t).property (hchi s t) g hn

/-- On the actual unlabelled chamber, a label change must carry the root with it.
The proved chamber preimage theorem supplies the shift; this does not assume
independence of different physical roots. -/
theorem treeCoefficient_quotient_chamber_transport (P Q : GenericTuple n)
    (hn : 3 ≤ n) (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, Q ∈ labelledChamber (genericShift a P) ∧
      ∀ g : ZMod n, treeCoefficient Q.val Q.property.1 (g - a) hn =
        treeCoefficient P.val P.property.1 g hn := by
  have hm : Q ∈ ⋃ a : ZMod n, labelledChamber (genericShift a P) := by
    rw [← chamber_preimage_eq_cyclic_union hn P]
    exact hQ
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hm
  refine ⟨a, ha, ?_⟩
  intro g
  have he := (tree_data_labelled_chamber_constant (genericShift a P) Q ha (g - a) hn).2.2
  exact he.symm.trans (treeCoefficient_shift P.val P.property.1 g a hn)

end

end SM
