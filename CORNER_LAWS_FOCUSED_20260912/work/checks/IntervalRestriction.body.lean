namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace BoundaryInterval

/-- Translate a local position of the contiguous word J into its physical
position in the original boundary word. No intermediate position is omitted. -/
def globalPosition (J : BoundaryInterval n) (k : Fin (J.leaves + 1)) : Fin n :=
  ⟨J.left.val + k.val, by
    have hk := k.isLt
    have hr := J.right.isLt
    have hj := J.increasing
    unfold leaves at hk
    change J.left.val < J.right.val at hj
    omega⟩

theorem globalPosition_strict (J : BoundaryInterval n) : StrictMono J.globalPosition := by
  intro a b hab
  change J.left.val + a.val < J.left.val + b.val
  exact Nat.add_lt_add_left hab _

theorem globalPosition_bounds (J : BoundaryInterval n) (k : Fin (J.leaves + 1)) :
    J.left ≤ J.globalPosition k ∧ J.globalPosition k ≤ J.right := by
  have hk := k.isLt
  have hj := J.increasing
  unfold leaves at hk
  change J.left.val < J.right.val at hj
  change J.left.val ≤ J.left.val + k.val ∧ J.left.val + k.val ≤ J.right.val
  omega

/-- Subtract J's left position from a physical position known to lie in J. -/
def localPosition (J : BoundaryInterval n) (x : Fin n) (hl : J.left ≤ x) (hr : x ≤ J.right) :
    Fin (J.leaves + 1) :=
  ⟨x.val - J.left.val, by
    unfold leaves
    change J.left.val ≤ x.val at hl
    change x.val ≤ J.right.val at hr
    omega⟩

theorem global_localPosition (J : BoundaryInterval n) (x : Fin n)
    (hl : J.left ≤ x) (hr : x ≤ J.right) : J.globalPosition (J.localPosition x hl hr) = x := by
  apply Fin.ext
  change J.left.val + (x.val - J.left.val) = x.val
  change J.left.val ≤ x.val at hl
  omega

theorem local_globalPosition (J : BoundaryInterval n) (k : Fin (J.leaves + 1)) :
    J.localPosition (J.globalPosition k) (J.globalPosition_bounds k).1
      (J.globalPosition_bounds k).2 = k := by
  apply Fin.ext
  change J.left.val + k.val - J.left.val = k.val
  omega

/-- Translate an arbitrary subinterval of the local word to the same physical
subinterval in the original word. -/
def liftInterval (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) : BoundaryInterval n where
  left := J.globalPosition K.left
  right := J.globalPosition K.right
  increasing := J.globalPosition_strict K.increasing

def liftTriple (J : BoundaryInterval n) (t : IncreasingBoundaryTriple (J.leaves + 1)) :
    IncreasingBoundaryTriple n where
  lower := J.globalPosition t.lower
  middle := J.globalPosition t.middle
  upper := J.globalPosition t.upper
  lower_middle := J.globalPosition_strict t.lower_middle
  middle_upper := J.globalPosition_strict t.middle_upper

end BoundaryInterval

namespace IntervalComposition

theorem eq_of_parts_cut {I : BoundaryInterval n} {π ρ : IntervalComposition I}
    (hp : π.parts = ρ.parts) (hc : HEq π.cut ρ.cut) : π = ρ := by
  cases π
  cases ρ
  cases hp
  cases hc
  rfl

theorem cut_bounds {I : BoundaryInterval n} (π : IntervalComposition I) (k : Fin (π.parts + 1)) :
    I.left ≤ π.cut k ∧ π.cut k ≤ I.right := by
  constructor
  · rw [← π.first]
    exact π.strict.monotone (Fin.zero_le k)
  · rw [← π.last]
    exact π.strict.monotone (Fin.le_last k)

/-- Preserve every part and cut index while translating all physical positions. -/
def liftComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) : IntervalComposition (J.liftInterval K) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => J.globalPosition (π.cut k)
  strict := J.globalPosition_strict.comp π.strict
  first := congrArg J.globalPosition π.first
  last := congrArg J.globalPosition π.last

/-- Every composition of a translated subinterval has all of its cuts in J,
so translation back is defined on the complete raw composition domain. -/
def lowerComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition (J.liftInterval K)) : IntervalComposition K where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => J.localPosition (π.cut k)
    (le_trans (J.globalPosition_bounds K.left).1 (π.cut_bounds k).1)
    (le_trans (π.cut_bounds k).2 (J.globalPosition_bounds K.right).2)
  strict := by
    intro a b hab
    have hs := π.strict hab
    have ha := (π.cut_bounds a).1
    have hb := (π.cut_bounds b).1
    change (π.cut a).val < (π.cut b).val at hs
    change J.left.val + K.left.val ≤ (π.cut a).val at ha
    change J.left.val + K.left.val ≤ (π.cut b).val at hb
    change (π.cut a).val - J.left.val < (π.cut b).val - J.left.val
    omega
  first := by
    apply Fin.ext
    have h := congrArg Fin.val π.first
    change (π.cut 0).val = J.left.val + K.left.val at h
    change (π.cut 0).val - J.left.val = K.left.val
    omega
  last := by
    apply Fin.ext
    have h := congrArg Fin.val π.last
    change (π.cut (Fin.last π.parts)).val = J.left.val + K.right.val at h
    change (π.cut (Fin.last π.parts)).val - J.left.val = K.right.val
    omega

theorem lower_liftComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) : lowerComposition J (liftComposition J π) = π := by
  apply eq_of_parts_cut (π := lowerComposition J (liftComposition J π)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact J.local_globalPosition (π.cut k)

theorem lift_lowerComposition (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition (J.liftInterval K)) : liftComposition J (lowerComposition J π) = π := by
  apply eq_of_parts_cut (π := liftComposition J (lowerComposition J π)) (ρ := π) rfl
  apply heq_of_eq
  funext k
  exact J.global_localPosition (π.cut k)
    (le_trans (J.globalPosition_bounds K.left).1 (π.cut_bounds k).1)
    (le_trans (π.cut_bounds k).2 (J.globalPosition_bounds K.right).2)

def restrictionEquiv (J : BoundaryInterval n) (K : BoundaryInterval (J.leaves + 1)) :
    IntervalComposition K ≃ IntervalComposition (J.liftInterval K) where
  toFun := liftComposition J
  invFun := lowerComposition J
  left_inv := lower_liftComposition J
  right_inv := lift_lowerComposition J

theorem liftComposition_part (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (k : Fin π.parts) :
    (liftComposition J π).part k = J.liftInterval (π.part k) := rfl

theorem liftComposition_nearTriple (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (k : Fin (π.parts - 1)) :
    (liftComposition J π).nearTriple k = J.liftTriple (π.nearTriple k) := rfl

theorem liftComposition_farTriple (J : BoundaryInterval n) {K : BoundaryInterval (J.leaves + 1)}
    (π : IntervalComposition K) (k : Fin (π.parts - 1)) :
    (liftComposition J π).farTriple k = J.liftTriple (π.farTriple k) := rfl

end IntervalComposition

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

def restrictTripleArray (J : BoundaryInterval n) (D : TripleArray n R) : TripleArray (J.leaves + 1) R :=
  fun t => D (J.liftTriple t)

def restrictIntervalArray (J : BoundaryInterval n) (X : IntervalArray n R) : IntervalArray (J.leaves + 1) R :=
  fun K => X (J.liftInterval K)

/-- Restriction commutes with every full coordinate equation because its
raw compositions, exact triples and child intervals correspond bijectively. -/
theorem nearFarTransform_restrict (J : BoundaryInterval n) (D H : TripleArray n R)
    (X : IntervalArray n R) :
    nearFarTransform (restrictTripleArray J D) (restrictTripleArray J H) (restrictIntervalArray J X) =
      restrictIntervalArray J (nearFarTransform D H X) := by
  funext K
  unfold nearFarTransform restrictIntervalArray
  exact Fintype.sum_equiv (IntervalComposition.restrictionEquiv J K) _ _ (fun _ => rfl)

/-- The unique triangular inverse therefore restricts to the unique inverse
constructed directly on the shorter word. -/
theorem nearFarInverse_restrict (J : BoundaryInterval n) (D H : TripleArray n R)
    (Y : IntervalArray n R) :
    restrictIntervalArray J (nearFarInverse D H Y) =
      nearFarInverse (restrictTripleArray J D) (restrictTripleArray J H) (restrictIntervalArray J Y) := by
  apply nearFar_solution_unique
  rw [nearFarTransform_restrict, nearFarTransform_inverse]

theorem boundaryUnitArray_restrict (J : BoundaryInterval n) :
    restrictIntervalArray J (boundaryUnitArray (R := R)) = boundaryUnitArray := by
  funext K
  have he : (J.liftInterval K).right.val = (J.liftInterval K).left.val + 1 ↔
      K.right.val = K.left.val + 1 := by
    change J.left.val + K.right.val = J.left.val + K.left.val + 1 ↔ _
    omega
  simp only [restrictIntervalArray, boundaryUnitArray, he]

theorem farOnlyCoordinates_restrict (J : BoundaryInterval n) (H : TripleArray n R) :
    restrictIntervalArray J (farOnlyCoordinates H) = farOnlyCoordinates (restrictTripleArray J H) := by
  unfold farOnlyCoordinates
  rw [nearFarInverse_restrict, boundaryUnitArray_restrict]
  rfl

theorem farOnlyOutput_restrict (J : BoundaryInterval n) (H : TripleArray n R) :
    restrictIntervalArray J (farOnlyOutput H) = farOnlyOutput (restrictTripleArray J H) := by
  change restrictIntervalArray J (nearFarTransform 0 (-H) (farOnlyCoordinates H)) =
    nearFarTransform 0 (-restrictTripleArray J H) (farOnlyCoordinates (restrictTripleArray J H))
  rw [← nearFarTransform_restrict, farOnlyCoordinates_restrict]
  rfl

end
end SM
