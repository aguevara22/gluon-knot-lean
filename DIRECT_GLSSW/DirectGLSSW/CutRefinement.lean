import DirectGLSSW.CutGaps
import DirectGLSSW.CutRepresentation

/-!
# Actual refinement of finite cut sets

Source: `ep:factorization`. A family of interior cuts, one in each outer
edge, corresponds to its final cut set together with the selected outer
cuts. The maps below are union and restriction to the open gaps. This
module proves their inverse laws; no weight identity is asserted here.
-/

namespace DirectGLSSW

/-- The finite subtype of consecutive outer edges. -/
abbrev CutGap (i j : ℕ) (S : Finset ℕ) := ↥(cutEdges i j S)

/-- Retain the outer cuts and insert every cut selected inside an outer gap. -/
def gapCutsUnion {i j : ℕ} {S : Finset ℕ}
    (U : ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2) : Finset ℕ :=
  S ∪ Finset.univ.biUnion (fun e : CutGap i j S => (U e).val)

/-- Restrict a final cut set to each open outer gap. -/
def gapCutsRestrict {i j : ℕ} {S : Finset ℕ} (T : Finset ℕ)
    (e : CutGap i j S) : IntervalCutSet e.val.1 e.val.2 :=
  ⟨T ∩ Finset.Ioo e.val.1 e.val.2,
    Finset.mem_powerset.mpr Finset.inter_subset_right⟩

theorem mem_gapCutsUnion {i j : ℕ} {S : Finset ℕ}
    (U : ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2) {k : ℕ} :
    k ∈ gapCutsUnion U ↔ k ∈ S ∨ ∃ e : CutGap i j S, k ∈ (U e).val := by
  simp [gapCutsUnion]

theorem subset_gapCutsUnion {i j : ℕ} {S : Finset ℕ}
    (U : ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2) :
    S ⊆ gapCutsUnion U := Finset.subset_union_left

theorem gapCutsUnion_subset {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (U : ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2) :
    gapCutsUnion U ⊆ Finset.Ioo i j := by
  intro k hk
  rcases (mem_gapCutsUnion U).mp hk with hk | ⟨e, hk⟩
  · exact hS hk
  · have hgap := Finset.mem_powerset.mp (U e).property hk
    exact (Finset.mem_sdiff.mp (cutEdges_gap_subset hij hS e.property hgap)).1

/-- Distinct gaps contribute no cuts when restricting the union to one gap. -/
theorem gapCutsUnion_inter_gap {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (U : ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2)
    (e : CutGap i j S) :
    gapCutsUnion U ∩ Finset.Ioo e.val.1 e.val.2 = (U e).val := by
  ext k
  constructor
  · intro hk
    obtain ⟨hkU, hke⟩ := Finset.mem_inter.mp hk
    rcases (mem_gapCutsUnion U).mp hkU with hkS | ⟨f, hkf⟩
    · exact False.elim
        ((Finset.mem_sdiff.mp (cutEdges_gap_subset hij hS e.property hke)).2 hkS)
    · have hkfgap := Finset.mem_powerset.mp (U f).property hkf
      have hfe : f = e := by
        apply Subtype.ext
        by_contra hne
        exact Finset.disjoint_left.mp
          (cutEdges_gaps_pairwiseDisjoint hij hS f.property e.property hne) hkfgap hke
      subst f
      exact hkf
  · intro hk
    exact Finset.mem_inter.mpr
      ⟨(mem_gapCutsUnion U).mpr (Or.inr ⟨e, hk⟩),
        Finset.mem_powerset.mp (U e).property hk⟩

/-- Every retained final cut is either outer or in its unique open outer gap. -/
theorem gapCutsUnion_restrict {i j : ℕ} {S T : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hST : S ⊆ T) (hT : T ⊆ Finset.Ioo i j) :
    gapCutsUnion (gapCutsRestrict (i := i) (j := j) (S := S) T) = T := by
  ext k
  constructor
  · intro hk
    rcases (mem_gapCutsUnion _).mp hk with hkS | ⟨e, hke⟩
    · exact hST hkS
    · exact (Finset.mem_inter.mp hke).1
  · intro hkT
    apply (mem_gapCutsUnion _).mpr
    by_cases hkS : k ∈ S
    · exact Or.inl hkS
    · have hkgap : k ∈ (cutEdges i j S).biUnion (fun e => Finset.Ioo e.1 e.2) := by
        rw [cutEdges_biUnion_Ioo hij hS]
        exact Finset.mem_sdiff.mpr ⟨hT hkT, hkS⟩
      obtain ⟨e, he, hke⟩ := Finset.mem_biUnion.mp hkgap
      exact Or.inr ⟨⟨e, he⟩, Finset.mem_inter.mpr ⟨hkT, hke⟩⟩

/-- The final set represented by a fixed outer set and its gap cuts. -/
def gapCutsToRefinement {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (U : ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2) :
    {T : Finset ℕ // S ⊆ T ∧ T ⊆ Finset.Ioo i j} :=
  ⟨gapCutsUnion U, subset_gapCutsUnion U, gapCutsUnion_subset hij hS U⟩

/-- Recover the gap cuts by restricting the final set. -/
def refinementToGapCuts {i j : ℕ} {S : Finset ℕ}
    (T : {T : Finset ℕ // S ⊆ T ∧ T ⊆ Finset.Ioo i j}) :
    ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2 :=
  gapCutsRestrict T.val

theorem refinementToGapCuts_gapCutsToRefinement {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (U : ∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2) :
    refinementToGapCuts (gapCutsToRefinement hij hS U) = U := by
  funext e
  apply Subtype.ext
  exact gapCutsUnion_inter_gap hij hS U e

theorem gapCutsToRefinement_refinementToGapCuts {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (T : {T : Finset ℕ // S ⊆ T ∧ T ⊆ Finset.Ioo i j}) :
    gapCutsToRefinement hij hS (refinementToGapCuts T) = T := by
  apply Subtype.ext
  exact gapCutsUnion_restrict hij hS T.property.1 T.property.2

/-- For a fixed outer cut set, gapwise inner cuts are exactly final cut sets
containing the outer cuts. Both inverse laws are separate opaque theorems. -/
def gapCutsEquiv {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    (∀ e : CutGap i j S, IntervalCutSet e.val.1 e.val.2) ≃
      {T : Finset ℕ // S ⊆ T ∧ T ⊆ Finset.Ioo i j} where
  toFun := gapCutsToRefinement hij hS
  invFun := refinementToGapCuts
  left_inv := refinementToGapCuts_gapCutsToRefinement hij hS
  right_inv := gapCutsToRefinement_refinementToGapCuts hij hS

/-- Combine an outer set and its gap cuts, remembering which final cuts were outer. -/
def cutRefinementToSelected {i j : ℕ} (hij : i < j)
    (R : Σ S : IntervalCutSet i j,
      ∀ e : CutGap i j S.val, IntervalCutSet e.val.1 e.val.2) :
    Σ T : IntervalCutSet i j, ↥T.val.powerset :=
  ⟨⟨gapCutsUnion R.2, Finset.mem_powerset.mpr
      (gapCutsUnion_subset hij (Finset.mem_powerset.mp R.1.property) R.2)⟩,
    ⟨R.1.val, Finset.mem_powerset.mpr (subset_gapCutsUnion R.2)⟩⟩

/-- Read the selected subset as outer cuts, and restrict the final set to its gaps. -/
def selectedToCutRefinement {i j : ℕ}
    (R : Σ T : IntervalCutSet i j, ↥T.val.powerset) :
    Σ S : IntervalCutSet i j,
      ∀ e : CutGap i j S.val, IntervalCutSet e.val.1 e.val.2 :=
  ⟨⟨R.2.val, Finset.mem_powerset.mpr
      ((Finset.mem_powerset.mp R.2.property).trans
        (Finset.mem_powerset.mp R.1.property))⟩,
    gapCutsRestrict R.1.val⟩

theorem selectedToCutRefinement_cutRefinementToSelected {i j : ℕ}
    (hij : i < j)
    (R : Σ S : IntervalCutSet i j,
      ∀ e : CutGap i j S.val, IntervalCutSet e.val.1 e.val.2) :
    selectedToCutRefinement (cutRefinementToSelected hij R) = R := by
  rcases R with ⟨⟨S, hS⟩, U⟩
  dsimp only [selectedToCutRefinement, cutRefinementToSelected]
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  funext e
  apply Subtype.ext
  exact gapCutsUnion_inter_gap hij (Finset.mem_powerset.mp hS) U e

theorem cutRefinementToSelected_selectedToCutRefinement {i j : ℕ}
    (hij : i < j) (R : Σ T : IntervalCutSet i j, ↥T.val.powerset) :
    cutRefinementToSelected hij (selectedToCutRefinement R) = R := by
  rcases R with ⟨⟨T, hT⟩, ⟨S, hS⟩⟩
  have hST : S ⊆ T := Finset.mem_powerset.mp hS
  have hTI : T ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hT
  have hfinal := gapCutsUnion_restrict hij (hST.trans hTI) hST hTI
  dsimp only [selectedToCutRefinement, cutRefinementToSelected]
  apply Sigma.ext (Subtype.ext hfinal)
  apply (Subtype.heq_iff_coe_eq ?_).mpr
  · rfl
  intro A
  change A ∈ (gapCutsUnion (gapCutsRestrict (i := i) (j := j) (S := S) T)).powerset ↔
    A ∈ T.powerset
  rw [hfinal]

/-- Choosing outer cuts and then cuts independently in each open gap is
equivalent to a final cut set together with a selected subset of outer cuts.
Both inverse laws are separate opaque theorems. -/
def cutRefinementEquiv {i j : ℕ} (hij : i < j) :
    (Σ S : IntervalCutSet i j,
      ∀ e : CutGap i j S.val, IntervalCutSet e.val.1 e.val.2) ≃
    (Σ T : IntervalCutSet i j, ↥T.val.powerset) where
  toFun := cutRefinementToSelected hij
  invFun := selectedToCutRefinement
  left_inv := selectedToCutRefinement_cutRefinementToSelected hij
  right_inv := cutRefinementToSelected_selectedToCutRefinement hij

end DirectGLSSW
