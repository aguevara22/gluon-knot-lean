import DirectGLSSW.GeneralPhiInverse
import DirectGLSSW.CurrentFidelity

/-!
# Finite interval inverse and locality

The inverse is unique using equations only on a bounded positive interval
window. Its finite restriction depends only on target values on that window.
-/

namespace DirectGLSSW
open scoped BigOperators

private theorem nonUnary_congr_on_interval (D H : TripleArray) {X Y : IntervalArray}
    {i j : ℕ} (hij : i < j)
    (hXY : ∀ a b, i ≤ a → a < b → b ≤ j → b - a < j - i → X a b = Y a b) :
    nonUnary D H X i j = nonUnary D H Y i j := by
  unfold nonUnary
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hS
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hsubset : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hsub
  unfold cutContribution
  congr 1
  unfold branchProduct
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨a, b⟩ hab
  have hb := cutVertices_branch_bounds hij hsubset hnonempty hab
  exact hXY a b hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

private theorem phi_congr_on_interval (D H : TripleArray) {X Y : IntervalArray}
    {L U : ℕ} (hXY : ∀ a b, L ≤ a → a < b → b ≤ U → X a b = Y a b) :
    ∀ i j, L ≤ i → i < j → j ≤ U → phi D H X i j = phi D H Y i j := by
  intro i j hLi hij hUj
  rw [phi_eq_unary_add, phi_eq_unary_add]
  congr 1
  · exact hXY i j hLi hij hUj
  · apply nonUnary_congr_on_interval D H hij
    intro a b hia hab hb hlt
    exact hXY a b (le_trans hLi hia) hab (le_trans hb hUj)

/-- Any two solutions that agree with the target on a finite positive
interval window agree there with the generalized inverse. -/
theorem inverseCurrent_unique_on_interval (D H : TripleArray) (Y X : IntervalArray)
    (L U : ℕ)
    (hX : ∀ i j, L ≤ i → i < j → j ≤ U → phi D H X i j = Y i j) :
    ∀ i j, L ≤ i → i < j → j ≤ U → X i j = inverseCurrent D H Y i j := by
  intro i j hLi hij hUj
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      have hshort : nonUnary D H X i j =
          nonUnary D H (inverseCurrent D H Y) i j := by
        apply nonUnary_congr_on_interval D H hij
        intro a b hia hab hb hlt
        exact ih (b - a) (by omega) a b (le_trans hLi hia) hab (le_trans hb hUj) rfl
      have hsource : X i j + nonUnary D H X i j = Y i j := by
        rw [← phi_eq_unary_add]
        exact hX i j hLi hij hUj
      have hvalue : X i j = Y i j - nonUnary D H (inverseCurrent D H Y) i j := by
        rw [← hshort]
        exact (eq_sub_iff_add_eq).mpr hsource
      rw [hvalue, inverseCurrent_recurrence D H Y hij]

/-- Values of the finite inverse depend only on target entries in the window. -/
theorem inverseCurrent_congr_on_interval (D H : TripleArray) (Y Z : IntervalArray)
    (L U : ℕ)
    (hYZ : ∀ i j, L ≤ i → i < j → j ≤ U → Y i j = Z i j) :
    ∀ i j, L ≤ i → i < j → j ≤ U →
      inverseCurrent D H Y i j = inverseCurrent D H Z i j := by
  intro i j hLi hij hUj
  apply (inverseCurrent_unique_on_interval D H Y (inverseCurrent D H Z) L U _
    i j hLi hij hUj).symm
  intro a b ha hab hb
  calc
    phi D H (inverseCurrent D H Z) a b = Z a b := inverseCurrent_phi D H Z a b
    _ = Y a b := (hYZ a b ha hab hb).symm

/-- The finite carrier of positive intervals with left endpoint at least `L`
and right endpoint at most `U`. -/
abbrev FiniteIntervalPair (L U : ℕ) :=
  {p : Fin (U + 1) × Fin (U + 1) // L ≤ p.1.val ∧ p.1.val < p.2.val}

/-- A rational value at each interval in the finite carrier. -/
abbrev FiniteIntervalValues (L U : ℕ) := FiniteIntervalPair L U → ℚ

/-- Extend finite interval values by zero outside the carrier. -/
def finiteIntervalExtension (L U : ℕ) (X : FiniteIntervalValues L U) : IntervalArray :=
  fun i j => if h : L ≤ i ∧ i < j ∧ j ≤ U then
    X ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), ⟨h.1, h.2.1⟩⟩ else 0

private theorem finiteIntervalExtension_apply (L U : ℕ) (X : FiniteIntervalValues L U)
    (p : FiniteIntervalPair L U) :
    finiteIntervalExtension L U X p.val.1.val p.val.2.val = X p := by
  unfold finiteIntervalExtension
  have h : L ≤ p.val.1.val ∧ p.val.1.val < p.val.2.val ∧ p.val.2.val ≤ U := by
    exact ⟨p.property.1, p.property.2, by omega⟩
  rw [dif_pos h]

/-- Phi restricted to finite positive interval pairs, using zero extension. -/
def finitePhi (D H : TripleArray) (L U : ℕ) :
    FiniteIntervalValues L U → FiniteIntervalValues L U :=
  fun X p => phi D H (finiteIntervalExtension L U X) p.val.1.val p.val.2.val

/-- Every finite target array has exactly one finite preimage under Phi. -/
theorem finitePhi_bijective (D H : TripleArray) (L U : ℕ) :
    Function.Bijective (finitePhi D H L U) := by
  constructor
  · intro X Z hXZ
    funext p
    let Y := finitePhi D H L U X
    have hX : ∀ i j, L ≤ i → i < j → j ≤ U →
        phi D H (finiteIntervalExtension L U X) i j = finiteIntervalExtension L U Y i j := by
      intro i j hLi hij hUj
      let q : FiniteIntervalPair L U :=
        ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), ⟨hLi, hij⟩⟩
      calc
        phi D H (finiteIntervalExtension L U X) i j = finitePhi D H L U X q := rfl
        _ = Y q := rfl
        _ = finiteIntervalExtension L U Y i j := (finiteIntervalExtension_apply L U Y q).symm
    have hZ : ∀ i j, L ≤ i → i < j → j ≤ U →
        phi D H (finiteIntervalExtension L U Z) i j = finiteIntervalExtension L U Y i j := by
      intro i j hLi hij hUj
      let q : FiniteIntervalPair L U :=
        ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), ⟨hLi, hij⟩⟩
      calc
        phi D H (finiteIntervalExtension L U Z) i j = finitePhi D H L U Z q := rfl
        _ = finitePhi D H L U X q := (congrFun hXZ q).symm
        _ = Y q := rfl
        _ = finiteIntervalExtension L U Y i j := (finiteIntervalExtension_apply L U Y q).symm
    have hx := inverseCurrent_unique_on_interval D H (finiteIntervalExtension L U Y) (finiteIntervalExtension L U X) L U hX
    have hz := inverseCurrent_unique_on_interval D H (finiteIntervalExtension L U Y) (finiteIntervalExtension L U Z) L U hZ
    calc
      X p = finiteIntervalExtension L U X p.val.1.val p.val.2.val :=
        (finiteIntervalExtension_apply L U X p).symm
      _ = inverseCurrent D H (finiteIntervalExtension L U Y) p.val.1.val p.val.2.val := hx _ _ p.property.1 p.property.2 (by omega)
      _ = finiteIntervalExtension L U Z p.val.1.val p.val.2.val := (hz _ _ p.property.1 p.property.2 (by omega)).symm
      _ = Z p := finiteIntervalExtension_apply L U Z p
  · intro Y
    let Ytotal := finiteIntervalExtension L U Y
    let X : FiniteIntervalValues L U := fun p => inverseCurrent D H Ytotal p.val.1.val p.val.2.val
    refine ⟨X, ?_⟩
    funext p
    have hExt : ∀ i j, L ≤ i → i < j → j ≤ U →
        finiteIntervalExtension L U X i j = inverseCurrent D H Ytotal i j := by
      intro i j hLi hij hUj
      let q : FiniteIntervalPair L U :=
        ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), ⟨hLi, hij⟩⟩
      calc
        finiteIntervalExtension L U X i j = X q := finiteIntervalExtension_apply L U X q
        _ = inverseCurrent D H Ytotal i j := rfl
    calc
      phi D H (finiteIntervalExtension L U X) p.val.1.val p.val.2.val =
          phi D H (inverseCurrent D H Ytotal) p.val.1.val p.val.2.val :=
        phi_congr_on_interval D H hExt _ _ p.property.1 p.property.2 (by omega)
      _ = Ytotal p.val.1.val p.val.2.val :=
        inverseCurrent_phi D H Ytotal p.val.1.val p.val.2.val
      _ = Y p := finiteIntervalExtension_apply L U Y p

/-- Each finite target has a unique solution on the finite positive-pair
carrier; values outside that carrier are deliberately unobserved. -/
theorem existsUnique_finitePhi_preimage (D H : TripleArray) (L U : ℕ)
    (Y : FiniteIntervalValues L U) :
    ∃! X : FiniteIntervalValues L U, finitePhi D H L U X = Y := by
  rcases (finitePhi_bijective D H L U).2 Y with ⟨X, hX⟩
  refine ⟨X, hX, ?_⟩
  intro Z hZ
  exact (finitePhi_bijective D H L U).1 (hZ.trans hX.symm)

/-- The original ordinary current is uniquely determined by equations only
on the finite source interval. -/
theorem ordinaryCurrent_unique_on_interval (D H : TripleArray) (X : IntervalArray)
    (L U : ℕ)
    (hX : ∀ i j, L ≤ i → i < j → j ≤ U → phi D H X i j = source i j) :
    ∀ i j, L ≤ i → i < j → j ≤ U → X i j = ordinaryCurrent D H i j := by
  intro i j hLi hij hUj
  have hOrd : ∀ a b, L ≤ a → a < b → b ≤ U →
      phi D H (ordinaryCurrent D H) a b = source a b := by
    intro a b _ hab _
    exact ordinaryCurrent_phi D H hab
  calc
    X i j = inverseCurrent D H source i j :=
      inverseCurrent_unique_on_interval D H source X L U hX i j hLi hij hUj
    _ = ordinaryCurrent D H i j :=
      (inverseCurrent_unique_on_interval D H source (ordinaryCurrent D H) L U hOrd i j hLi hij hUj).symm


end DirectGLSSW
