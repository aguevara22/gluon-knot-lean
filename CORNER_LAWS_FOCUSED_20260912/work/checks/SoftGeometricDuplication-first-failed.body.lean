namespace SM

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Collapse of every actual root-relative child label, including the new label. -/
theorem softRootBoundary_collapse_index (j g : ZMod n) (p : Fin (n + 1)) :
    softCollapseIndex j (boundaryIndex (softParentEdge j g) p) =
      boundaryIndex g (SoftDuplication.collapse (softRootPosition j g) p) := by
  rcases SoftDuplication.child_exhaust (softRootPosition j g) p with rfl | ⟨k, rfl⟩
  · rw [softRootBoundary_B_index, softCollapseIndex_new, SoftDuplication.collapse_B,
      softRootPosition_index]
  · rw [softRootBoundary_old_index, softCollapseIndex_old, SoftDuplication.collapse_old]

/-- Every position other than B is the retained old occurrence of its collapse. -/
theorem softRootBoundary_old_collapse_index (j g : ZMod n) (p : Fin (n + 1))
    (hp : p ≠ SoftDuplication.B (softRootPosition j g)) :
    boundaryIndex (softParentEdge j g) p =
      softOldIndex j (boundaryIndex g (SoftDuplication.collapse (softRootPosition j g) p)) := by
  have h := softRootBoundary_old_index j g (SoftDuplication.collapse (softRootPosition j g) p)
  rw [SoftDuplication.old_collapse_of_ne_B (softRootPosition j g) p hp] at h
  exact h

/-- The exceptional sign data indexed by the actual parent boundary word. -/
def softRootFarData (P : LabelledTuple n) (j g : ZMod n) (q : Plane) (k : Fin n) : ℚ :=
  ((softFarSign P j q (boundaryIndex g k) : ℤ) : ℚ)

theorem softRootFarData_square {P : LabelledTuple n} {j : ZMod n} {q : Plane}
    (hq : SoftAdmissible P j q) (g : ZMod n) (k : Fin n)
    (hk : k ≠ softRootPosition j g) : (softRootFarData P j g q k)^2 = 1 := by
  apply SoftDuplication.sign_square
  apply softFarSign_ne_zero hq
  intro he
  exact hk (boundaryIndex_injective g (he.trans (softRootPosition_index j g).symm))

/-- Core geometric far values are signs on every increasing boundary triple. -/
theorem geometricBoundaryArray_square {P : LabelledTuple n} (hP : G1 P)
    (g : ZMod n) (T : IncreasingBoundaryTriple n) :
    (geometricBoundaryArray (R := ℚ) P g T)^2 = 1 := by
  apply SoftDuplication.sign_square
  apply hP
  · intro h
    exact (ne_of_gt T.middle_upper) (boundaryIndex_injective g h)
  · intro h
    exact (ne_of_gt T.lower_middle) (boundaryIndex_injective g h)
  · intro h
    exact (ne_of_gt (lt_trans T.lower_middle T.middle_upper)) (boundaryIndex_injective g h)

/-- The values at the actual cyclic neighboring labels give both attachments. -/
theorem softRootFarData_neighbors (P : LabelledTuple n) (j g : ZMod n) (q : Plane) :
    softRootFarData P j g q (softRootPosition (j - 1) g) =
      ((softAttachmentMinus P j q : ℤ) : ℚ) ∧
    softRootFarData P j g q (softRootPosition (j + 1) g) =
      ((softAttachmentPlus P j q : ℤ) : ℚ) := by
  simp only [softRootFarData, softRootPosition_index,
    (softFarSign_neighbors P j q).1, (softFarSign_neighbors P j q).2]
  exact ⟨rfl, rfl⟩

/-- Plain linear triples avoid precisely the two physical attachment occurrences. -/
theorem softRootBoundary_plain_avoids (j g : ZMod n)
    (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ SoftDuplication.tripleContainsBoth (softRootPosition j g) T) :
    ¬ (softOldIndex j j ∈ ({boundaryIndex (softParentEdge j g) T.upper,
        boundaryIndex (softParentEdge j g) T.middle,
        boundaryIndex (softParentEdge j g) T.lower} : Finset (ZMod (n + 1))) ∧
      softNewIndex j ∈ ({boundaryIndex (softParentEdge j g) T.upper,
        boundaryIndex (softParentEdge j g) T.middle,
        boundaryIndex (softParentEdge j g) T.lower} : Finset (ZMod (n + 1)))) := by
  rintro ⟨ha, hb⟩
  rw [← softRootBoundary_A_index j g] at ha
  rw [← softRootBoundary_B_index j g] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton,
    (boundaryIndex_injective (softParentEdge j g)).eq_iff] at ha hb
  apply hplain
  constructor
  · rcases ha with ha | ha | ha
    · exact Or.inr (Or.inr ha.symm)
    · exact Or.inr (Or.inl ha.symm)
    · exact Or.inl ha.symm
  · rcases hb with hb | hb | hb
    · exact Or.inr (Or.inr hb.symm)
    · exact Or.inr (Or.inl hb.symm)
    · exact Or.inl hb.symm

/-- Upper exceptional triples read the first proved physical exceptional sign. -/
theorem softGeometricBoundaryArray_upper (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) (T : IncreasingBoundaryTriple (n + 1))
    (hu : T.middle = SoftDuplication.A (softRootPosition j g) ∧
      T.upper = SoftDuplication.B (softRootPosition j g)) :
    geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) T =
      softRootFarData P j g q (SoftDuplication.collapse (softRootPosition j g) T.lower) := by
  have hp : T.lower ≠ SoftDuplication.B (softRootPosition j g) :=
    ne_of_lt (lt_of_lt_of_eq (lt_trans T.lower_middle T.middle_upper) hu.2)
  unfold geometricBoundaryArray softRootFarData
  rw [hu.1, hu.2, softRootBoundary_A_index, softRootBoundary_B_index,
    softRootBoundary_old_collapse_index j g T.lower hp,
    (softFarSign_exceptional P j q ε hε _).1]

/-- Lower exceptional triples read the second proved physical exceptional sign. -/
theorem softGeometricBoundaryArray_lower (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) (ε : ℝ) (hε : 0 < ε) (T : IncreasingBoundaryTriple (n + 1))
    (hl : T.lower = SoftDuplication.A (softRootPosition j g) ∧
      T.middle = SoftDuplication.B (softRootPosition j g)) :
    geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) T =
      softRootFarData P j g q (SoftDuplication.collapse (softRootPosition j g) T.upper) := by
  have hp : T.upper ≠ SoftDuplication.B (softRootPosition j g) :=
    ne_of_gt (lt_of_eq_of_lt hl.2.symm T.middle_upper)
  unfold geometricBoundaryArray softRootFarData
  rw [hl.1, hl.2, softRootBoundary_A_index, softRootBoundary_B_index,
    softRootBoundary_old_collapse_index j g T.upper hp,
    (softFarSign_exceptional P j q ε hε _).2]

/-- A proved common physical pullback specializes to every plain boundary triple. -/
theorem softGeometricBoundaryArray_plain (P : LabelledTuple n) (j g : ZMod n)
    (q : Plane) (ε : ℝ)
    (hpull : ∀ a b c : ZMod (n + 1), a ≠ b → b ≠ c → a ≠ c →
      ¬ (softOldIndex j j ∈ ({a, b, c} : Finset (ZMod (n + 1))) ∧
        softNewIndex j ∈ ({a, b, c} : Finset (ZMod (n + 1)))) →
      chi (softInsertion P j q ε) a b c =
        chi P (softCollapseIndex j a) (softCollapseIndex j b) (softCollapseIndex j c))
    (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ SoftDuplication.tripleContainsBoth (softRootPosition j g) T) :
    geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) T =
      geometricBoundaryArray (R := ℚ) P g
        (SoftDuplication.collapseTriple (softRootPosition j g) T hplain) := by
  have hab : boundaryIndex (softParentEdge j g) T.upper ≠
      boundaryIndex (softParentEdge j g) T.middle := fun h =>
    (ne_of_gt T.middle_upper) (boundaryIndex_injective _ h)
  have hbc : boundaryIndex (softParentEdge j g) T.middle ≠
      boundaryIndex (softParentEdge j g) T.lower := fun h =>
    (ne_of_gt T.lower_middle) (boundaryIndex_injective _ h)
  have hac : boundaryIndex (softParentEdge j g) T.upper ≠
      boundaryIndex (softParentEdge j g) T.lower := fun h =>
    (ne_of_gt (lt_trans T.lower_middle T.middle_upper)) (boundaryIndex_injective _ h)
  have he := hpull _ _ _ hab hbc hac (softRootBoundary_plain_avoids j g T hplain)
  simp only [softRootBoundary_collapse_index] at he
  exact congrArg (fun x : SignType => ((x : ℤ) : ℚ)) he

/-- One positive radius gives the exact formal far array for every parent root.
The array equality and sign hypotheses are derived from the actual polygon.
This is the geometric input to duplication, not its recurrence or output law. -/
theorem soft_geometric_duplication_data (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      G1 (softInsertion P j q ε) ∧ ∀ g : ZMod n,
      geometricBoundaryArray (R := ℚ) (softInsertion P j q ε) (softParentEdge j g) =
        SoftDuplication.tripleLift (softRootPosition j g) (geometricBoundaryArray P g)
          (softRootFarData P j g q) ∧
      (∀ T : IncreasingBoundaryTriple n, (geometricBoundaryArray (R := ℚ) P g T)^2 = 1) ∧
      (∀ k : Fin n, k ≠ softRootPosition j g → (softRootFarData P j g q k)^2 = 1) := by
  obtain ⟨δ, hδ, hf⟩ := soft_far_sign_family hn hP j q hq
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hG, hpull, hrest⟩ := hf ε hε hεδ
  refine ⟨hG, ?_⟩
  intro g
  refine ⟨?_, geometricBoundaryArray_square hP g, softRootFarData_square hq g⟩
  funext T
  by_cases hu : T.middle = SoftDuplication.A (softRootPosition j g) ∧
      T.upper = SoftDuplication.B (softRootPosition j g)
  · rw [SoftDuplication.tripleLift_upper _ _ _ _ hu]
    exact softGeometricBoundaryArray_upper P j g q ε hε T hu
  · by_cases hl : T.lower = SoftDuplication.A (softRootPosition j g) ∧
        T.middle = SoftDuplication.B (softRootPosition j g)
    · rw [SoftDuplication.tripleLift_lower _ _ _ _ hl]
      exact softGeometricBoundaryArray_lower P j g q ε hε T hl
    · have hplain : ¬ SoftDuplication.tripleContainsBoth (softRootPosition j g) T :=
        fun h => ((SoftDuplication.triple_contains_both_iff _ _).mp h).elim hu hl
      rw [SoftDuplication.tripleLift_plain _ _ _ _ hplain]
      exact softGeometricBoundaryArray_plain P j g q ε hpull T hplain

end
end SM
