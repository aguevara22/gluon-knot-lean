import SM.FiniteCompositions

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IntervalComposition
variable {I : BoundaryInterval n}

/-- A one-part composition has only its two fixed endpoints. -/
theorem eq_single_of_parts_eq_one (π : IntervalComposition I) (hparts : π.parts = 1) :
    π = single I := by
  cases π with
  | mk parts hp cut hstrict hfirst hlast =>
    change parts = 1 at hparts
    subst parts
    have hc : cut = ![I.left, I.right] := by
      funext k
      fin_cases k
      · exact hfirst
      · exact hlast
    subst cut
    rfl

theorem parts_eq_one_iff_eq_single (π : IntervalComposition I) :
    π.parts = 1 ↔ π = single I :=
  ⟨π.eq_single_of_parts_eq_one, fun h => by rw [h]; rfl⟩

/-- The sole part of the unary composition is exactly the original interval. -/
theorem single_part (I : BoundaryInterval n) (k : Fin (single I).parts) :
    (single I).part k = I := by
  change Fin 1 at k
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  rfl

theorem single_product {R : Type*} [CommMonoid R]
    (X : BoundaryInterval n → R) (I : BoundaryInterval n) :
    (∏ k : Fin (single I).parts, X ((single I).part k)) = X I := by
  simp only [single_part]
  exact Fin.prod_univ_one (fun _ => X I)

/-- Every nonunary composition has at least two parts; its underlying cuts
are unchanged by this equivalence. -/
def nonSingleEquiv (I : BoundaryInterval n) :
    {π : IntervalComposition I // π ≠ single I} ≃
      {π : IntervalComposition I // 2 ≤ π.parts} :=
  Equiv.subtypeEquivRight (fun π => by
    constructor
    · intro h
      have hn : π.parts ≠ 1 := fun hp => h (π.eq_single_of_parts_eq_one hp)
      have := π.parts_pos
      omega
    · intro h he
      have hp : π.parts = 1 := π.parts_eq_one_iff_eq_single.mpr he
      omega)

end IntervalComposition

end

end SM
