import CompatiblePairWeightedSum

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW ActiveArc Primitive Cursor Split SingletonWords
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal original support after adjoining the selected cut is identified
with the existing finset target, while retaining its actual `Primitive.Support`
structure. -/
def originalCompatibleSupportEquiv
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    {W : Finset (Crossing q) // c ∉ W ∧
      Nonalternation.Nonalternating q hR (insert c W)} ≃
    {U : Primitive.Support q hR // c ∉ U.val ∧
      Nonalternation.Nonalternating q hR (insert c U.val)} := by
  classical
  let P := {W : Finset (Crossing q) // c ∉ W ∧
    Nonalternation.Nonalternating q hR (insert c W)}
  let Q := {U : Primitive.Support q hR // c ∉ U.val ∧
    Nonalternation.Nonalternating q hR (insert c U.val)}
  let toQ : P → Q := fun W =>
    ⟨⟨W.val, (nonalternating_insert_iff q hR c W.val W.property.1).mp W.property.2 |>.1⟩,
      W.property.1, W.property.2⟩
  let toP : Q → P := fun U => ⟨U.val.val, U.property.1, U.property.2⟩
  refine ⟨toQ, toP, ?_, ?_⟩
  · intro W
    apply Subtype.ext
    rfl
  · intro U
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The existing first-cut decomposition is an equivalence with actual
original compatible unselected supports. -/
def originalCompatiblePairEquiv
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    ({S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
        PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S} ×
     {T : Finset (Crossing (parent q c hcut)) //
        Nonalternation.Nonalternating (parent q c hcut)
          (regular_parent q hR c hcut) T}) ≃
    {U : Primitive.Support q hR // c ∉ U.val ∧
      Nonalternation.Nonalternating q hR (insert c U.val)} := by
  exact (nonalternatingSelectionEquiv q hR c hc hcut).trans
    (originalCompatibleSupportEquiv q hR c hc hcut)

/-- Reindex any summand over the independent child and parent selections by
the actual original support left unselected after adding the cut. -/
theorem compatible_pair_sum_reindex_original
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : ClosedAuxiliary q hR) {R : Type} [AddCommMonoid R]
    (f : ({S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
        PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S} ×
       {T : Finset (Crossing (parent q c hcut)) //
        Nonalternation.Nonalternating (parent q c hcut)
          (regular_parent q hR c hcut) T}) → R) :
    (∑ S : GeometricSmoothingWeights.SeparatingSupport
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux),
      ∑ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
        f (S,T)) =
    ∑ U : {U : Primitive.Support q hR // c ∉ U.val ∧
      Nonalternation.Nonalternating q hR (insert c U.val)},
      f ((originalCompatiblePairEquiv q hR c hc hcut).symm U) := by
  classical
  let SType := GeometricSmoothingWeights.SeparatingSupport
    (child q hR c hc.1 hcut)
    (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
  letI : Fintype SType := GeometricSmoothingSumTransport.separatingSupportFintype
    (child q hR c hc.1 hcut)
    (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
  let TType := Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)
  let e := originalCompatiblePairEquiv q hR c hc hcut
  change (∑ S : SType, ∑ T : TType, f (S,T)) =
    ∑ U, f (e.symm U)
  calc
    (∑ S : SType, ∑ T : TType, f (S,T)) =
        ∑ p : SType × TType, f p := by
          rw [Fintype.sum_prod_type]
    _ = ∑ U : {U : Primitive.Support q hR // c ∉ U.val ∧
        Nonalternation.Nonalternating q hR (insert c U.val)}, f (e.symm U) := by
          apply Fintype.sum_equiv e
          intro p
          simp only [Equiv.symm_apply_apply]

/-- The exponent in the pair sum is exactly the cardinality exponent of its
reindexed original support. -/
theorem original_compatible_support_card
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
        PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S})
    (T : {T : Finset (Crossing (parent q c hcut)) //
        Nonalternation.Nonalternating (parent q c hcut)
          (regular_parent q hR c hcut) T}) :
    ((originalCompatiblePairEquiv q hR c hc hcut (S,T)).val.val).card =
      S.val.card + T.val.card := by
  change (nonalternatingSelectionEquiv q hR c hc hcut (S,T)).val.card = _
  exact nonalternatingSelectionEquiv_card q hR c hc hcut S T

/-- The signed weight in the pair sum is exactly the signed cardinality of its
literal original-support image. -/
theorem original_compatible_support_sign
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
        PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S})
    (T : {T : Finset (Crossing (parent q c hcut)) //
        Nonalternation.Nonalternating (parent q c hcut)
          (regular_parent q hR c hcut) T}) :
    (-1 : ℚ)^(((originalCompatiblePairEquiv q hR c hc hcut (S,T)).val.val).card) =
      (-1 : ℚ)^(S.val.card + T.val.card) := by
  rw [original_compatible_support_card]

/-- Failure of the inserted-set nonalternation condition is exactly an
incompatible original member, once the original support is known to be
nonalternating and the cut is absent. -/
theorem not_insert_nonalternating_iff_exists_incompatible
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (U : Primitive.Support q hR) (hcmem : c ∉ U.val) :
    ¬ Nonalternation.Nonalternating q hR (insert c U.val) ↔
      ∃ d ∈ U.val, ¬ Compatible q hR c d := by
  constructor
  · intro hbad
    by_contra hnone
    push_neg at hnone
    have hgood := (nonalternating_insert_iff q hR c U.val hcmem).mpr
      ⟨U.property, hnone⟩
    exact hbad hgood
  · rintro ⟨d, hd, hcompat⟩ hgood
    exact hcompat (((nonalternating_insert_iff q hR c U.val hcmem).mp hgood).2 d hd)







end DirectGLSSW.ActiveArc.CompatibleWords
