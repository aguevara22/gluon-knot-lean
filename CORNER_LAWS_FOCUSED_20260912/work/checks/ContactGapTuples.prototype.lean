import SM.ContactHalfTuples
import SM.RestrictedWordRoot
import Mathlib.Tactic

namespace SM

noncomputable section
variable {n q : ℕ} [NeZero n] [NeZero q]

/-- Reindexing by a proved equality of sizes preserves G1 by equality
induction. This assumes no invariance under an arbitrary permutation. -/
theorem g1_reindex_size (h : n = q) (P : LabelledTuple n) (hP : G1 P) :
    G1 (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i)) := by
  subst q
  cases n <;> exact hP

/-- The same equality induction transports the full coefficient and its
actual root. No cyclic covariance or root independence is assumed here. -/
theorem treeCoefficient_reindex_size (h : n = q) (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i))
      (g1_reindex_size h P hP) (ZMod.ringEquivCongr h g) (by omega) = treeCoefficient P hP g hn := by
  subst q
  cases n <;> rfl

/-- A proved pointwise tuple identity after size transport identifies the
two coefficients at root zero, including their dependent G1 witnesses. -/
theorem treeCoefficient_of_reindexed_tuple_eq (h : n = q)
    (P : LabelledTuple n) (Q : LabelledTuple q) (hP : G1 P) (hQ : G1 Q)
    (he : (fun i : ZMod q => P ((ZMod.ringEquivCongr h).symm i)) = Q) (hn : 3 ≤ n) :
    treeCoefficient P hP 0 hn = treeCoefficient Q hQ 0 (by omega) := by
  subst q
  cases n
  all_goals
    have hpq : P = Q := he
    clear he
    subst Q
    rfl

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every label of the restricted word is the consecutive parent label from
its starting vertex. Equality of sizes transports the complete word, including
local zero (the last vertex), without an endpoint-only inference. -/
theorem restrictedWord_reindex_start {q : ℕ} [NeZero q]
    (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
    (hsize : J.leaves + 1 = q) (u : ZMod q) :
    restrictedWordTuple P g J ((ZMod.ringEquivCongr hsize).symm u) =
      P (boundaryIndex g J.left + ((u - 1).val : ZMod n)) := by
  have hv : (((ZMod.ringEquivCongr hsize).symm u - 1)).val = (u - 1).val := by
    have he := ZMod.ringEquivCongr_val hsize ((ZMod.ringEquivCongr hsize).symm u - 1)
    simpa only [map_sub, map_one, RingEquiv.apply_symm_apply] using he.symm
  change P (g + ((J.left.val + (((ZMod.ringEquivCongr hsize).symm u - 1)).val : ℕ) : ZMod n) + 1) = _
  rw [hv, Nat.cast_add]
  apply congrArg P
  unfold boundaryIndex
  ring

/-- The gap starting at B with the second-half size is exactly the second
source half at every cyclic label, with its physical closing root zero. -/
theorem restrictedWord_eq_secondHalf (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = secondHalfSize M a)
    (hstart : boundaryIndex g J.left = a + 1) :
    (fun u : ZMod (secondHalfSize M a) =>
      restrictedWordTuple P g J ((ZMod.ringEquivCongr hsize).symm u)) =
      secondHalf P M a := by
  funext u
  rw [restrictedWord_reindex_start, hstart]
  unfold secondHalf
  rw [secondHalfIndex_range]
  rfl

/-- The gap starting at X is the complete first source half shifted by -1.
Consequently local closing root zero is the source half root -1. -/
theorem restrictedWord_eq_shift_firstHalf (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = firstHalfSize M a)
    (hstart : boundaryIndex g J.left = M) :
    (fun u : ZMod (firstHalfSize M a) =>
      restrictedWordTuple P g J ((ZMod.ringEquivCongr hsize).symm u)) =
      shift (-1) (firstHalf P M a) := by
  funext u
  rw [restrictedWord_reindex_start, hstart]
  simp only [shift, firstHalf, firstHalfIndex, cyclicRangeIndex, sub_eq_add_neg]

/-- Full tuple transport identifies the actual second-half coefficient.
G1 witnesses are explicit; no root independence is used. -/
theorem restrictedWord_secondHalf_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = secondHalfSize M a)
    (hstart : boundaryIndex g J.left = a + 1) (hJ : 2 ≤ J.leaves)
    (hP : G1 (restrictedWordTuple P g J)) (hQ : G1 (secondHalf P M a)) :
    treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega) =
      treeCoefficient (secondHalf P M a) hQ 0 (by omega) := by
  exact treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP hQ
    (restrictedWord_eq_secondHalf P g M a J hsize hstart) (by omega)

/-- The cyclic shift transports local root zero to the first-half root -1.
This is equality for a fixed physical edge, not arbitrary root invariance. -/
theorem restrictedWord_firstHalf_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (J : BoundaryInterval n) (hsize : J.leaves + 1 = firstHalfSize M a)
    (hstart : boundaryIndex g J.left = M) (hJ : 2 ≤ J.leaves)
    (hP : G1 (restrictedWordTuple P g J)) (hQ : G1 (firstHalf P M a)) :
    treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega) =
      treeCoefficient (firstHalf P M a) hQ (-1) (by omega) := by
  have he := treeCoefficient_of_reindexed_tuple_eq hsize _ _ hP
    (g1_shift_forward (-1) hQ)
    (restrictedWord_eq_shift_firstHalf P g M a J hsize hstart) (by omega)
  have hs := treeCoefficient_shift (firstHalf P M a) hQ (-1) (-1) (by omega)
  simp only [sub_self] at hs
  exact he.trans hs

end
end SM

#check SM.restrictedWord_reindex_start
#print axioms SM.restrictedWord_reindex_start
#check SM.restrictedWord_eq_secondHalf
#print axioms SM.restrictedWord_eq_secondHalf
#check SM.restrictedWord_eq_shift_firstHalf
#print axioms SM.restrictedWord_eq_shift_firstHalf
#check SM.restrictedWord_secondHalf_coefficient
#print axioms SM.restrictedWord_secondHalf_coefficient
#check SM.restrictedWord_firstHalf_coefficient
#print axioms SM.restrictedWord_firstHalf_coefficient
