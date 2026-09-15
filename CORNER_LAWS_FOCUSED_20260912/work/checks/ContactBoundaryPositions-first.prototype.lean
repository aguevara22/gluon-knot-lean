import SM.ContactHalfSizes
import SM.NearFar
import SM.CriticalCutSplit
import SM.TreeCoefficient
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
  · change a + (0 : ZMod n) + 1 = a + 1
    ring
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

#check SM.contactBaseTriple
#print axioms SM.contactBaseTriple
#check SM.contactFirstArcTriple
#print axioms SM.contactFirstArcTriple
#check SM.contactSecondArcTriple
#print axioms SM.contactSecondArcTriple
#check SM.contactBaseTriple_labels
#print axioms SM.contactBaseTriple_labels
#check SM.contactFirstArcTriple_labels
#print axioms SM.contactFirstArcTriple_labels
#check SM.contactSecondArcTriple_labels
#print axioms SM.contactSecondArcTriple_labels
#check SM.contactBaseTriple_gaps
#print axioms SM.contactBaseTriple_gaps
#check SM.contactFirstArcTriple_gaps
#print axioms SM.contactFirstArcTriple_gaps
#check SM.contactSecondArcTriple_gaps
#print axioms SM.contactSecondArcTriple_gaps
#check SM.contactBaseTriple_full
#print axioms SM.contactBaseTriple_full
#check SM.contactFirstArcTriple_proper
#print axioms SM.contactFirstArcTriple_proper
#check SM.contactSecondArcTriple_proper
#print axioms SM.contactSecondArcTriple_proper
#check SM.contactFirstArcTriple_contractedSize
#print axioms SM.contactFirstArcTriple_contractedSize
#check SM.contactSecondArcTriple_contractedSize
#print axioms SM.contactSecondArcTriple_contractedSize
