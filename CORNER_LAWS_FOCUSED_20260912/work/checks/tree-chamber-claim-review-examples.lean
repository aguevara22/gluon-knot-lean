namespace TreeChamberClaimIndependentReview
open SM
variable {n : ℕ} [NeZero n]

theorem complete_G1_quantities (hn : 3 ≤ n) (P Q : LabelledTuple n)
    (hP : G1 P) (hQ : G1 Q) (hc : ∀ i j k, chi P i j k = chi Q i j k)
    (g : ZMod n) :
    (∀ I (π : IntervalComposition I),
      π.ordinaryWeight P hP g = π.ordinaryWeight Q hQ g ∧
      π.rootWeight P hP g = π.rootWeight Q hQ g) ∧
    (∀ I, openTreeSum P hP g I = openTreeSum Q hQ g I) ∧
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn :=
  (A_chamber hn).1 P Q hP hQ hc g

theorem actual_connected_component (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : Q ∈ connectedComponent P) (g : ZMod n) :
    TreeDataEqual P.val Q.val P.property.1 Q.property.1 g hn :=
  (A_chamber hn).2.1 P Q hQ g

theorem actual_G1_path (hn : 3 ≤ n) (P Q : {P : LabelledTuple n // G1 P})
    (γ : Path P Q)
    (hc : ∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k)
    (g : ZMod n) (s t : unitInterval) :
    TreeDataEqual (γ s).val (γ t).val (γ s).property (γ t).property g hn :=
  (A_chamber hn).2.2.2 P Q γ hc g s t

-- The quotient statement exposes an actual labelled component and a single
-- coherent cyclic relabelling of every physical root. All weights and open
-- sums transport as well; this does not choose a new arbitrary fixed root.
theorem all_quantities_under_quotient_transport (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hQ : polygonProjection Q ∈ chamber (polygonProjection P)) :
    ∃ a : ZMod n, Q ∈ connectedComponent (genericShift a P) ∧
      ∀ g : ZMod n,
        (∀ I (π : IntervalComposition I),
          π.ordinaryWeight Q.val Q.property.1 (g - a) = π.ordinaryWeight P.val P.property.1 g ∧
          π.rootWeight Q.val Q.property.1 (g - a) = π.rootWeight P.val P.property.1 g) ∧
        (∀ I, openTreeSum Q.val Q.property.1 (g - a) I = openTreeSum P.val P.property.1 g I) ∧
        treeCoefficient Q.val Q.property.1 (g - a) hn = treeCoefficient P.val P.property.1 g hn := by
  obtain ⟨a, ha, hcoef⟩ := (A_chamber hn).2.2.1 P Q hQ
  refine ⟨a, ha, ?_⟩
  intro g
  have he := (A_chamber hn).2.1 (genericShift a P) Q ha (g - a)
  refine ⟨?_, ?_, hcoef g⟩
  · intro I π
    exact ⟨(he.1 I π).1.symm.trans (π.ordinaryWeight_shift P.val P.property.1 g a),
      (he.1 I π).2.symm.trans (π.rootWeight_shift P.val P.property.1 g a)⟩
  · intro I
    exact (he.2.1 I).symm.trans (openTreeSum_shift P.val P.property.1 g a I)

end TreeChamberClaimIndependentReview
