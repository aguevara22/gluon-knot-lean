import SM.FarOnlyOutput
import SM.ConsecutiveCuts
import SM.InteriorCutIndex

namespace SM

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

namespace BoundaryCutSet
variable {I : BoundaryInterval n}

/-- Every complete cut set is one raw source composition. -/
instance fintype : Fintype (BoundaryCutSet I) :=
  Fintype.ofEquiv (IntervalComposition I) (IntervalComposition.cutSetEquiv I)

/-- Reindex an interior cut by its actual boundary position. -/
def interiorIndexEquiv (S : BoundaryCutSet I) :
    Fin (S.toComposition.parts - 1) ≃ {x : Fin n // x ∈ S.interior.val} :=
  Equiv.ofBijective (fun k => ⟨S.toComposition.interiorPosition k, by
    simpa only [S.toComposition_cutSet] using S.toComposition.interiorPosition_mem k⟩)
    ⟨by
      intro k l he
      exact S.toComposition.interiorPosition_injective (congrArg Subtype.val he), by
      intro x
      have hx : x.val ∈ S.toComposition.cutSet.interior.val := by
        simpa only [S.toComposition_cutSet] using x.property
      obtain ⟨k, hk⟩ := (S.toComposition.mem_interior_iff_exists_index x.val).mp hx
      exact ⟨k, Subtype.ext hk⟩⟩

/-- Reindex all children by the actual consecutive pairs of cuts. -/
def partIndexEquiv (S : BoundaryCutSet I) :
    Fin S.toComposition.parts ≃ {J : BoundaryInterval n // S.Consecutive J} :=
  Equiv.ofBijective (fun k => ⟨S.toComposition.part k, by
    simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive k⟩)
    ⟨by
      intro k l he
      exact S.toComposition.part_injective (congrArg Subtype.val he), by
      intro J
      have hJ : S.toComposition.cutSet.Consecutive J.val := by
        simpa only [S.toComposition_cutSet] using J.property
      obtain ⟨k, hk⟩ := S.toComposition.exists_part_of_consecutive J.val hJ
      exact ⟨k, Subtype.ext hk⟩⟩

instance consecutiveFintype (S : BoundaryCutSet I) :
    Fintype {J : BoundaryInterval n // S.Consecutive J} :=
  Fintype.ofEquiv (Fin S.toComposition.parts) S.partIndexEquiv

/-- The near triple at this actual interior cut uses its two neighboring cuts. -/
def nearAtCut (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    IncreasingBoundaryTriple n :=
  S.toComposition.nearTriple (S.interiorIndexEquiv.symm x)

/-- The far triple uses the full interval endpoints and this actual cut. -/
def farAtCut (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    IncreasingBoundaryTriple n :=
  S.toComposition.farTriple (S.interiorIndexEquiv.symm x)

theorem nearAtCut_middle (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.nearAtCut x).middle = x.val := by
  change S.toComposition.interiorPosition (S.interiorIndexEquiv.symm x) = x.val
  exact congrArg Subtype.val (S.interiorIndexEquiv.apply_symm_apply x)

theorem farAtCut_middle (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.farAtCut x).middle = x.val := by
  change S.toComposition.interiorPosition (S.interiorIndexEquiv.symm x) = x.val
  exact congrArg Subtype.val (S.interiorIndexEquiv.apply_symm_apply x)

theorem farAtCut_lower (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.farAtCut x).lower = I.left := rfl

theorem farAtCut_upper (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.farAtCut x).upper = I.right := rfl

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The complete summand, indexed by actual interior cuts and consecutive
child intervals. No nonunary restriction or nonzero factor is imposed. -/
def nearFarSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (S : BoundaryCutSet I) : R :=
  (∏ x : {x : Fin n // x ∈ S.interior.val},
    (D (S.nearAtCut x) - H (S.farAtCut x)) * ⅟ (2 : R)) *
    ∏ J : {J : BoundaryInterval n // S.Consecutive J}, X J.val

theorem nearFarSummand_toComposition (D H : TripleArray n R) (X : IntervalArray n R)
    (S : BoundaryCutSet I) :
    S.nearFarSummand D H X = S.toComposition.nearFarWeight D H *
      ∏ k : Fin S.toComposition.parts, X (S.toComposition.part k) := by
  have hg : S.toComposition.nearFarWeight D H =
      ∏ x : {x : Fin n // x ∈ S.interior.val},
        (D (S.nearAtCut x) - H (S.farAtCut x)) * ⅟ (2 : R) := by
    unfold IntervalComposition.nearFarWeight
    apply Fintype.prod_equiv S.interiorIndexEquiv
    intro k
    simp only [nearAtCut, farAtCut, Equiv.symm_apply_apply]
  have hp : (∏ k : Fin S.toComposition.parts, X (S.toComposition.part k)) =
      ∏ J : {J : BoundaryInterval n // S.Consecutive J}, X J.val :=
    Fintype.prod_equiv S.partIndexEquiv _ _ (fun _ => rfl)
  exact (congrArg₂ (fun a b : R => a * b) hg hp).symm

theorem nearFarSummand_cutSet (D H : TripleArray n R) (X : IntervalArray n R)
    (π : IntervalComposition I) :
    π.cutSet.nearFarSummand D H X = π.nearFarWeight D H *
      ∏ k : Fin π.parts, X (π.part k) := by
  rw [nearFarSummand_toComposition, IntervalComposition.cutSet_toComposition]

end BoundaryCutSet

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Reindex the complete source transform by all complete cut sets.
Every composition, including the one-part term, occurs exactly once. -/
theorem nearFarTransform_eq_cutSet_sum (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    nearFarTransform D H X I = ∑ S : BoundaryCutSet I, S.nearFarSummand D H X := by
  apply Fintype.sum_equiv (IntervalComposition.cutSetEquiv I)
  intro π
  exact (BoundaryCutSet.nearFarSummand_cutSet D H X π).symm

end
end SM

#print axioms SM.BoundaryCutSet.fintype
#print axioms SM.BoundaryCutSet.interiorIndexEquiv
#print axioms SM.BoundaryCutSet.partIndexEquiv
#print axioms SM.BoundaryCutSet.consecutiveFintype
#print axioms SM.BoundaryCutSet.nearAtCut
#print axioms SM.BoundaryCutSet.farAtCut
#print axioms SM.BoundaryCutSet.nearAtCut_middle
#print axioms SM.BoundaryCutSet.farAtCut_middle
#print axioms SM.BoundaryCutSet.farAtCut_lower
#print axioms SM.BoundaryCutSet.farAtCut_upper
#print axioms SM.BoundaryCutSet.nearFarSummand
#print axioms SM.BoundaryCutSet.nearFarSummand_toComposition
#print axioms SM.BoundaryCutSet.nearFarSummand_cutSet
#print axioms SM.nearFarTransform_eq_cutSet_sum
