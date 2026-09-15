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
      exact S.toComposition.interiorPosition_injective
        (congrArg (fun x : {x : Fin n // x ∈ S.interior.val} => x.val) he), by
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

namespace SM.BoundaryCutSet

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Two consecutive intervals with the same right endpoint have the same
left endpoint: either strict ordering would expose an intervening cut. -/
theorem consecutive_left_unique (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hr : J.right = K.right) :
    J.left = K.left := by
  rcases lt_trichotomy J.left K.left with h | h | h
  · exact False.elim (hJ.2.2 K.left hK.1 ⟨h, by rw [hr]; exact K.increasing⟩)
  · exact h
  · exact False.elim (hK.2.2 J.left hJ.1 ⟨h, by rw [← hr]; exact J.increasing⟩)

theorem consecutive_right_unique (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hl : J.left = K.left) :
    J.right = K.right := by
  rcases lt_trichotomy J.right K.right with h | h | h
  · exact False.elim (hK.2.2 J.right hJ.2.1 ⟨by rw [← hl]; exact J.increasing, h⟩)
  · exact h
  · exact False.elim (hJ.2.2 K.right hK.2.1 ⟨by rw [hl]; exact K.increasing, h⟩)

/-- The physical child interval ending at this interior cut. -/
def nearLeftInterval (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    BoundaryInterval n where
  left := (S.nearAtCut x).lower
  right := (S.nearAtCut x).middle
  increasing := (S.nearAtCut x).lower_middle

/-- The physical child interval beginning at this interior cut. -/
def nearRightInterval (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    BoundaryInterval n where
  left := (S.nearAtCut x).middle
  right := (S.nearAtCut x).upper
  increasing := (S.nearAtCut x).middle_upper

theorem nearLeftInterval_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : S.Consecutive (S.nearLeftInterval x) := by
  let k := S.interiorIndexEquiv.symm x
  let l : Fin S.toComposition.parts := ⟨k.val, by have := k.isLt; omega⟩
  have he : S.nearLeftInterval x = S.toComposition.part l := rfl
  rw [he]
  simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive l

theorem nearRightInterval_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : S.Consecutive (S.nearRightInterval x) := by
  let k := S.interiorIndexEquiv.symm x
  let l : Fin S.toComposition.parts := ⟨k.val + 1, by have := k.isLt; omega⟩
  have he : S.nearRightInterval x = S.toComposition.part l := rfl
  rw [he]
  simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive l

/-- Any geometric proof that J is the preceding consecutive child identifies
the actual near gate's lower argument. No enumeration correspondence is assumed. -/
theorem nearAtCut_lower_eq_of_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) (J : BoundaryInterval n)
    (hJ : S.Consecutive J) (hr : J.right = x.val) :
    (S.nearAtCut x).lower = J.left := by
  apply S.consecutive_left_unique (S.nearLeftInterval_consecutive x) hJ
  exact (S.nearAtCut_middle x).trans hr.symm

theorem nearAtCut_upper_eq_of_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) (J : BoundaryInterval n)
    (hJ : S.Consecutive J) (hl : J.left = x.val) :
    (S.nearAtCut x).upper = J.right := by
  apply S.consecutive_right_unique (S.nearRightInterval_consecutive x) hJ
  exact (S.nearAtCut_middle x).trans hl.symm

end
end SM.BoundaryCutSet

#print axioms SM.BoundaryCutSet.consecutive_left_unique
#print axioms SM.BoundaryCutSet.consecutive_right_unique
#print axioms SM.BoundaryCutSet.nearLeftInterval
#print axioms SM.BoundaryCutSet.nearRightInterval
#print axioms SM.BoundaryCutSet.nearLeftInterval_consecutive
#print axioms SM.BoundaryCutSet.nearRightInterval_consecutive
#print axioms SM.BoundaryCutSet.nearAtCut_lower_eq_of_consecutive
#print axioms SM.BoundaryCutSet.nearAtCut_upper_eq_of_consecutive
