import CompatiblePairOriginalSupportReindex

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW ActiveArc Primitive Cursor Split SingletonWords
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- If a summand vanishes on original supports incompatible with the selected
cut, its sum over every cut-avoiding support is exactly the child×parent sum
obtained from the actual compatible decomposition. -/
theorem unselected_support_sum_eq_compatible_pair_sum
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : ClosedAuxiliary q hR)
    (g : Primitive.Support q hR → ℚ)
    (hzero : ∀ U : Primitive.Support q hR, c ∉ U.val →
      ¬ Nonalternation.Nonalternating q hR (insert c U.val) → g U = 0) :
    (∑ U : {U : Primitive.Support q hR // c ∉ U.val}, g U.val) =
    ∑ S : GeometricSmoothingWeights.SeparatingSupport
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux),
      ∑ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
        g ((originalCompatiblePairEquiv q hR c hc hcut (S,T)).val) := by
  classical
  let All := {U : Primitive.Support q hR // c ∉ U.val}
  let Good := {U : Primitive.Support q hR // c ∉ U.val ∧
    Nonalternation.Nonalternating q hR (insert c U.val)}
  let Bad := {U : Primitive.Support q hR // c ∉ U.val ∧
    ¬ Nonalternation.Nonalternating q hR (insert c U.val)}
  let toFun : All → Good ⊕ Bad := fun U =>
    if h : Nonalternation.Nonalternating q hR (insert c U.val.val) then
      Sum.inl ⟨U.val, U.property, h⟩
    else
      Sum.inr ⟨U.val, U.property, h⟩
  let invFun : Good ⊕ Bad → All := fun x =>
    match x with
    | Sum.inl U => ⟨U.val, U.property.1⟩
    | Sum.inr U => ⟨U.val, U.property.1⟩
  have leftInv : Function.LeftInverse invFun toFun := by
    intro U
    apply Subtype.ext
    by_cases h : Nonalternation.Nonalternating q hR (insert c U.val.val)
    · simp [toFun, invFun, h]
    · simp [toFun, invFun, h]
  have rightInv : Function.RightInverse invFun toFun := by
    intro x
    cases x with
    | inl U => simp [toFun, invFun, U.property.2]
    | inr U => simp [toFun, invFun, U.property.2]
  let partition : All ≃ Good ⊕ Bad :=
    { toFun := toFun, invFun := invFun, left_inv := leftInv, right_inv := rightInv }
  let term : Good ⊕ Bad → ℚ := Sum.elim (fun U => g U.val) (fun U => g U.val)
  have hpartition :
      (∑ U : All, g U.val) = (∑ U : Good, g U.val) + (∑ U : Bad, g U.val) := by
    calc
      (∑ U : All, g U.val) = ∑ X : Good ⊕ Bad, term X := by
        apply Fintype.sum_equiv partition
        intro U
        by_cases h : Nonalternation.Nonalternating q hR (insert c U.val.val)
        · simp [partition, toFun, term, h]
        · simp [partition, toFun, term, h]
      _ = (∑ U : Good, g U.val) + (∑ U : Bad, g U.val) := by
        simp [term, Fintype.sum_sum_type]
  have hbad : (∑ U : Bad, g U.val) = 0 := by
    apply Finset.sum_eq_zero
    intro U hU
    exact hzero U.val U.property.1 U.property.2
  let pairEquiv := originalCompatiblePairEquiv q hR c hc hcut
  let pairTerm := fun p => g (pairEquiv p).val
  have hgood :
      (∑ U : Good, g U.val) =
      ∑ S : GeometricSmoothingWeights.SeparatingSupport
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux),
        ∑ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
          pairTerm (S,T) := by
    have hreindex := compatible_pair_sum_reindex_original q hR c hc hcut hAux pairTerm
    calc
      (∑ U : Good, g U.val) =
          ∑ U : Good, pairTerm (pairEquiv.symm U) := by
        apply Finset.sum_congr rfl
        intro U hU
        simp only [pairTerm, pairEquiv, Equiv.apply_symm_apply]
      _ = _ := hreindex.symm
  rw [hpartition, hbad, add_zero, hgood]


end DirectGLSSW.ActiveArc.CompatibleWords
