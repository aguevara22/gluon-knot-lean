import SM.ContactHalfTuples
import SM.RestrictedWordRoot
import SM.CriticalCutSplit
import Mathlib.Tactic

namespace SM.IncreasingBoundaryTriple

noncomputable section
variable {n : ℕ}

/-- Contract the entire positive-length critical arc to one leaf by deleting
exactly its strictly interior positions, retaining both endpoints. -/
def erasedInteriorCount (t : IncreasingBoundaryTriple n) : ℕ :=
  t.upper.val - t.lower.val - 1

def contractedSize (t : IncreasingBoundaryTriple n) : ℕ :=
  n - t.erasedInteriorCount

theorem erasedInteriorCount_pos (t : IncreasingBoundaryTriple n) :
    0 < t.erasedInteriorCount := by
  have hl := t.lower_middle
  have hr := t.middle_upper
  change t.lower.val < t.middle.val at hl
  change t.middle.val < t.upper.val at hr
  unfold erasedInteriorCount
  omega

/-- Both endpoints survive, even when the contracted word is one formal
leaf. No arity-three polygon amplitude is inferred from this bound. -/
theorem contractedSize_bounds (t : IncreasingBoundaryTriple n) :
    t.lower.val + 2 ≤ t.contractedSize ∧ t.contractedSize ≤ n := by
  have hu := t.upper.isLt
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold contractedSize erasedInteriorCount
  omega

def expandPosition (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) : Fin n :=
  if hk : k.val ≤ t.lower.val then
    ⟨k.val, lt_of_le_of_lt hk t.lower.isLt⟩
  else
    ⟨k.val + t.erasedInteriorCount, by
      have hb := k.isLt
      unfold contractedSize at hb
      omega⟩

theorem expandPosition_val (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    (t.expandPosition k).val =
      if k.val ≤ t.lower.val then k.val else k.val + t.erasedInteriorCount := by
  unfold expandPosition
  split_ifs <;> rfl

theorem expandPosition_strict (t : IncreasingBoundaryTriple n) : StrictMono t.expandPosition := by
  intro a b hab
  change a.val < b.val at hab
  change (t.expandPosition a).val < (t.expandPosition b).val
  rw [expandPosition_val, expandPosition_val]
  split_ifs <;> omega

theorem expandPosition_lower (t : IncreasingBoundaryTriple n) :
    t.expandPosition ⟨t.lower.val, by have := t.contractedSize_bounds; omega⟩ = t.lower := by
  apply Fin.ext
  rw [expandPosition_val]
  simp

/-- The distinguished surviving edge expands from the old first endpoint
directly to the old last endpoint, not to the old critical middle vertex. -/
theorem expandPosition_upper (t : IncreasingBoundaryTriple n) :
    t.expandPosition ⟨t.lower.val + 1, by have := t.contractedSize_bounds; omega⟩ = t.upper := by
  apply Fin.ext
  rw [expandPosition_val]
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  simp only [show ¬ t.lower.val + 1 ≤ t.lower.val by omega, ite_false]
  unfold erasedInteriorCount
  omega

theorem expandPosition_survives (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    t.expandPosition k ≤ t.lower ∨ t.upper ≤ t.expandPosition k := by
  change (t.expandPosition k).val ≤ t.lower.val ∨ t.upper.val ≤ (t.expandPosition k).val
  rw [expandPosition_val]
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold erasedInteriorCount
  split_ifs <;> omega

/-- Translate back only surviving positions. The range condition excludes
every deleted interior position explicitly. -/
def contractPosition (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ≤ t.lower ∨ t.upper ≤ x) : Fin t.contractedSize :=
  ⟨if x.val ≤ t.lower.val then x.val else x.val - t.erasedInteriorCount, by
    have hb := t.contractedSize_bounds
    have hxn := x.isLt
    change x.val ≤ t.lower.val ∨ t.upper.val ≤ x.val at hx
    have hl := lt_trans t.lower_middle t.middle_upper
    change t.lower.val < t.upper.val at hl
    unfold contractedSize erasedInteriorCount at *
    split_ifs <;> omega⟩

theorem expand_contractPosition (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ≤ t.lower ∨ t.upper ≤ x) : t.expandPosition (t.contractPosition x hx) = x := by
  apply Fin.ext
  rw [expandPosition_val]
  simp only [contractPosition]
  change x.val ≤ t.lower.val ∨ t.upper.val ≤ x.val at hx
  have hl := lt_trans t.lower_middle t.middle_upper
  change t.lower.val < t.upper.val at hl
  unfold erasedInteriorCount
  split_ifs <;> omega

theorem contract_expandPosition (t : IncreasingBoundaryTriple n) (k : Fin t.contractedSize) :
    t.contractPosition (t.expandPosition k) (t.expandPosition_survives k) = k := by
  apply Fin.ext
  change (if (t.expandPosition k).val ≤ t.lower.val then (t.expandPosition k).val
    else (t.expandPosition k).val - t.erasedInteriorCount) = k.val
  rw [expandPosition_val]
  split_ifs <;> omega

/-- A bijection onto every surviving boundary position, in the original
linear reading. It deletes exactly the open critical arc. -/
def survivingPositionEquiv (t : IncreasingBoundaryTriple n) :
    Fin t.contractedSize ≃ {x : Fin n // x ≤ t.lower ∨ t.upper ≤ x} where
  toFun k := ⟨t.expandPosition k, t.expandPosition_survives k⟩
  invFun x := t.contractPosition x.val x.property
  left_inv := t.contract_expandPosition
  right_inv x := Subtype.ext (t.expand_contractPosition x.val x.property)

end
end SM.IncreasingBoundaryTriple

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Root a cuts the cyclic contact order at B: B,X,A. -/
def contactBaseTriple (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    IncreasingBoundaryTriple n where
  lower := ⟨0, by omega⟩
  middle := ⟨n - contactDistance M a - 1, by
    have hd := contactDistance_bounds hn hc
    omega⟩
  upper := ⟨n - 1, by omega⟩
  lower_middle := by
    change 0 < n - contactDistance M a - 1
    have hd := contactDistance_bounds hn hc
    omega
  middle_upper := by
    change n - contactDistance M a - 1 < n - 1
    have hd := contactDistance_bounds hn hc
    omega

/-- A root on the original X-to-A arc cuts the critical labels as A,B,X.
The representative u includes zero, hence the edge starting at X. -/
def contactFirstArcTriple (g M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : (g - M).val < contactDistance M a) : IncreasingBoundaryTriple n where
  lower := ⟨contactDistance M a - (g - M).val - 1, by
    have hd := contactDistance_bounds hn hc
    omega⟩
  middle := ⟨contactDistance M a - (g - M).val, by
    have hd := contactDistance_bounds hn hc
    omega⟩
  upper := ⟨n - (g - M).val - 1, by omega⟩
  lower_middle := by
    change contactDistance M a - (g - M).val - 1 < contactDistance M a - (g - M).val
    omega
  middle_upper := by
    change contactDistance M a - (g - M).val < n - (g - M).val - 1
    have hd := contactDistance_bounds hn hc
    omega

/-- A root on the original B-to-X arc cuts the critical labels as X,A,B.
The final representative n-1 includes the edge ending at X. -/
def contactSecondArcTriple (g M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a)
    (hu : contactDistance M a < (g - M).val) : IncreasingBoundaryTriple n where
  lower := ⟨n - (g - M).val - 1, by omega⟩
  middle := ⟨n - (g - M).val + contactDistance M a - 1, by
    have huN : (g - M).val < n := ZMod.val_lt _
    omega⟩
  upper := ⟨n - (g - M).val + contactDistance M a, by
    have huN : (g - M).val < n := ZMod.val_lt _
    omega⟩
  lower_middle := by
    change n - (g - M).val - 1 < n - (g - M).val + contactDistance M a - 1
    have hd := contactDistance_bounds hn hc
    have huN : (g - M).val < n := ZMod.val_lt _
    omega
  middle_upper := by
    change n - (g - M).val + contactDistance M a - 1 < n - (g - M).val + contactDistance M a
    have huN : (g - M).val < n := ZMod.val_lt _
    omega

theorem contactBaseTriple_labels (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    boundaryIndex a (contactBaseTriple M a hn hc).lower = a + 1 ∧
      boundaryIndex a (contactBaseTriple M a hn hc).middle = M ∧
      boundaryIndex a (contactBaseTriple M a hn hc).upper = a := by
  have hd := contactDistance_bounds hn hc
  refine ⟨?_, ?_, ?_⟩
  · change a + ((0 : ℕ) : ZMod n) + 1 = a + 1
    simp
  · change a + ((n - contactDistance M a - 1 : ℕ) : ZMod n) + 1 = M
    rw [Nat.cast_sub (by omega : 1 ≤ n - contactDistance M a),
      Nat.cast_sub (by omega : contactDistance M a ≤ n), Nat.cast_one,
      ZMod.natCast_self, contactDistance_cast]
    ring
  · change a + ((n - 1 : ℕ) : ZMod n) + 1 = a
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, ZMod.natCast_self]
    ring

theorem contactFirstArcTriple_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    boundaryIndex g (contactFirstArcTriple g M a hn hc hu).lower = a ∧
      boundaryIndex g (contactFirstArcTriple g M a hn hc hu).middle = a + 1 ∧
      boundaryIndex g (contactFirstArcTriple g M a hn hc hu).upper = M := by
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hdZ := contactDistance_cast M a
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  refine ⟨?_, ?_, ?_⟩
  · change g + ((contactDistance M a - (g - M).val - 1 : ℕ) : ZMod n) + 1 = a
    rw [Nat.cast_sub (by omega : 1 ≤ contactDistance M a - (g - M).val),
      Nat.cast_sub (by omega : (g - M).val ≤ contactDistance M a), Nat.cast_one, hdZ, huZ]
    ring
  · change g + ((contactDistance M a - (g - M).val : ℕ) : ZMod n) + 1 = a + 1
    rw [Nat.cast_sub (by omega : (g - M).val ≤ contactDistance M a), hdZ, huZ]
    ring
  · change g + ((n - (g - M).val - 1 : ℕ) : ZMod n) + 1 = M
    rw [Nat.cast_sub (by omega : 1 ≤ n - (g - M).val),
      Nat.cast_sub (by omega : (g - M).val ≤ n), Nat.cast_one, ZMod.natCast_self, huZ]
    ring

theorem contactSecondArcTriple_labels (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    boundaryIndex g (contactSecondArcTriple g M a hn hc hu).lower = M ∧
      boundaryIndex g (contactSecondArcTriple g M a hn hc hu).middle = a ∧
      boundaryIndex g (contactSecondArcTriple g M a hn hc hu).upper = a + 1 := by
  have huN : (g - M).val < n := ZMod.val_lt _
  have hdZ := contactDistance_cast M a
  have huZ : ((g - M).val : ZMod n) = g - M := ZMod.natCast_zmod_val _
  refine ⟨?_, ?_, ?_⟩
  · change g + ((n - (g - M).val - 1 : ℕ) : ZMod n) + 1 = M
    rw [Nat.cast_sub (by omega : 1 ≤ n - (g - M).val),
      Nat.cast_sub (by omega : (g - M).val ≤ n), Nat.cast_one, ZMod.natCast_self, huZ]
    ring
  · change g + ((n - (g - M).val + contactDistance M a - 1 : ℕ) : ZMod n) + 1 = a
    rw [Nat.cast_sub (by omega : 1 ≤ n - (g - M).val + contactDistance M a),
      Nat.cast_add, Nat.cast_sub (by omega : (g - M).val ≤ n), Nat.cast_one,
      ZMod.natCast_self, hdZ, huZ]
    ring
  · change g + ((n - (g - M).val + contactDistance M a : ℕ) : ZMod n) + 1 = a + 1
    rw [Nat.cast_add, Nat.cast_sub (by omega : (g - M).val ≤ n),
      ZMod.natCast_self, hdZ, huZ]
    ring

theorem contactBaseTriple_gaps (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    (contactBaseTriple M a hn hc).leftInterval.leaves = n - contactDistance M a - 1 ∧
      (contactBaseTriple M a hn hc).rightInterval.leaves = contactDistance M a := by
  have hd := contactDistance_bounds hn hc
  dsimp [contactBaseTriple, IncreasingBoundaryTriple.leftInterval,
    IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem contactFirstArcTriple_gaps (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).leftInterval.leaves = 1 ∧
      (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves = n - contactDistance M a - 1 := by
  have hd := contactDistance_bounds hn hc
  dsimp [contactFirstArcTriple, IncreasingBoundaryTriple.leftInterval,
    IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem contactSecondArcTriple_gaps (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves = contactDistance M a ∧
      (contactSecondArcTriple g M a hn hc hu).rightInterval.leaves = 1 := by
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  dsimp [contactSecondArcTriple, IncreasingBoundaryTriple.leftInterval,
    IncreasingBoundaryTriple.rightInterval, BoundaryInterval.leaves]
  omega

theorem contactBaseTriple_full (M a : ZMod n) (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    (contactBaseTriple M a hn hc).spanInterval = fullBoundaryInterval hn := rfl

theorem contactFirstArcTriple_proper (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).spanInterval ≠ fullBoundaryInterval hn := by
  intro he
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hl := congrArg (fun J : BoundaryInterval n => J.left.val) he
  have hr := congrArg (fun J : BoundaryInterval n => J.right.val) he
  dsimp [IncreasingBoundaryTriple.spanInterval, contactFirstArcTriple, fullBoundaryInterval] at hl hr
  omega

theorem contactSecondArcTriple_proper (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).spanInterval ≠ fullBoundaryInterval hn := by
  intro he
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  have hl := congrArg (fun J : BoundaryInterval n => J.left.val) he
  have hr := congrArg (fun J : BoundaryInterval n => J.right.val) he
  dsimp [IncreasingBoundaryTriple.spanInterval, contactSecondArcTriple, fullBoundaryInterval] at hl hr
  omega

/-- Only arity is identified here; no tuple equality is inferred from it. -/
theorem contactFirstArcTriple_contractedSize (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    (contactFirstArcTriple g M a hn hc hu).contractedSize = firstHalfSize M a := by
  have hd := contactDistance_bounds hn hc
  dsimp [IncreasingBoundaryTriple.contractedSize, IncreasingBoundaryTriple.erasedInteriorCount,
    contactFirstArcTriple, firstHalfSize]
  omega

/-- Only arity is identified here; the whole contracted tuple needs its own proof. -/
theorem contactSecondArcTriple_contractedSize (g M a : ZMod n) (hn : 3 ≤ n)
    (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    (contactSecondArcTriple g M a hn hc hu).contractedSize = secondHalfSize M a := by
  have hd := contactDistance_bounds hn hc
  have huN : (g - M).val < n := ZMod.val_lt _
  dsimp [IncreasingBoundaryTriple.contractedSize, IncreasingBoundaryTriple.erasedInteriorCount,
    contactSecondArcTriple, secondHalfSize]
  omega

end
end SM

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

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- At the contacted base root, the entire B-to-X gap is the second half.
Its arity equality and starting label are derived from the actual cut. -/
theorem contactBaseTriple_left_word (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    ∃ hsize : (contactBaseTriple M a hn hc).leftInterval.leaves + 1 = secondHalfSize M a,
      (fun u : ZMod (secondHalfSize M a) => restrictedWordTuple P a
        (contactBaseTriple M a hn hc).leftInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        secondHalf P M a := by
  have hd := contactDistance_bounds hn hc
  have hg := (contactBaseTriple_gaps M a hn hc).1
  have hs : (contactBaseTriple M a hn hc).leftInterval.leaves + 1 = secondHalfSize M a := by
    unfold secondHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_secondHalf P a M a _ hs ?_⟩
  exact (contactBaseTriple_labels M a hn hc).1

/-- At the base root, the whole X-to-A gap is the first half shifted by -1,
so its local closing edge is the physical a-to-M edge. -/
theorem contactBaseTriple_right_word (P : LabelledTuple n) (M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) :
    ∃ hsize : (contactBaseTriple M a hn hc).rightInterval.leaves + 1 = firstHalfSize M a,
      (fun u : ZMod (firstHalfSize M a) => restrictedWordTuple P a
        (contactBaseTriple M a hn hc).rightInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        shift (-1) (firstHalf P M a) := by
  have hg := (contactBaseTriple_gaps M a hn hc).2
  have hs : (contactBaseTriple M a hn hc).rightInterval.leaves + 1 = firstHalfSize M a := by
    unfold firstHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_shift_firstHalf P a M a _ hs ?_⟩
  exact (contactBaseTriple_labels M a hn hc).2.1

/-- Every root of the first inherited arc leaves exactly the same complete
B-to-X gap, including the endpoint-adjacent root at M. -/
theorem contactFirstArcTriple_right_word (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a) :
    ∃ hsize : (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves + 1 = secondHalfSize M a,
      (fun u : ZMod (secondHalfSize M a) => restrictedWordTuple P g
        (contactFirstArcTriple g M a hn hc hu).rightInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        secondHalf P M a := by
  have hd := contactDistance_bounds hn hc
  have hg := (contactFirstArcTriple_gaps g M a hn hc hu).2
  have hs : (contactFirstArcTriple g M a hn hc hu).rightInterval.leaves + 1 = secondHalfSize M a := by
    unfold secondHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_secondHalf P g M a _ hs ?_⟩
  exact (contactFirstArcTriple_labels g M a hn hc hu).2.1

/-- Every root of the second inherited arc leaves the complete X-to-A gap,
including the endpoint-adjacent root ending at M. -/
theorem contactSecondArcTriple_left_word (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val) :
    ∃ hsize : (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves + 1 = firstHalfSize M a,
      (fun u : ZMod (firstHalfSize M a) => restrictedWordTuple P g
        (contactSecondArcTriple g M a hn hc hu).leftInterval ((ZMod.ringEquivCongr hsize).symm u)) =
        shift (-1) (firstHalf P M a) := by
  have hg := (contactSecondArcTriple_gaps g M a hn hc hu).1
  have hs : (contactSecondArcTriple g M a hn hc hu).leftInterval.leaves + 1 = firstHalfSize M a := by
    unfold firstHalfSize
    omega
  refine ⟨hs, restrictedWord_eq_shift_firstHalf P g M a _ hs ?_⟩
  exact (contactSecondArcTriple_labels g M a hn hc hu).1

end
end SM

#check SM.contactBaseTriple_left_word
#print axioms SM.contactBaseTriple_left_word
#check SM.contactBaseTriple_right_word
#print axioms SM.contactBaseTriple_right_word
#check SM.contactFirstArcTriple_right_word
#print axioms SM.contactFirstArcTriple_right_word
#check SM.contactSecondArcTriple_left_word
#print axioms SM.contactSecondArcTriple_left_word
