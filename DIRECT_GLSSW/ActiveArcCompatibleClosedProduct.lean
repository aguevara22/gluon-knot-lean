import ActiveArcChildClosedAmplitude
import ActiveArcParentClosedProduct

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact reindexing of the source's erased-open-component product. -/
theorem closedWeight_product_erase_eq_subtype
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (hAux : Primitive.ClosedAuxiliary q hR) (U : Primitive.Support q hR) :
    (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val), Primitive.closedWeight q hR hAux U D)=
      ∏ D : {D : Primitive.Components q hR U // D≠openComponent q hR.noTriple U.val},
        Primitive.closedWeight q hR hAux U D.val := by
  exact Finset.prod_subtype _ (by intro D;simp) _

variable (hRI : GLSSWRootIndependence)
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (hAux : Primitive.ClosedAuxiliary q hR)
variable (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
  PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S})
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))

include hRI

/-- The exact original closed interval factor equals the actual child
component-amplitude product, through the proved actual component bijection. -/
theorem childClosedInterval_closedWeight_product :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    (∏ D : {D : {D : Primitive.Components q hR U // D≠openComponent q hR.noTriple U.val} //
        (Nonalternation.eventEnumeration q hR).symm
          (closedRoot q hR.noTriple U.val D.val D.property)∈intervalSide (leftRank q hR c) (rightRank q hR c)},
      Primitive.closedWeight q hR hAux U D.val.val)=
      GeometricSmoothingWeights.componentAmplitudeProduct (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S.val
        (child_auxiliaryGenericity q hR c hc hcut hAux) S.property := by
  let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let E := childClosedIntervalEquiv q hR c hc hcut S.val T.val hAux
  let f := fun D : {D : {D : Primitive.Components q hR U // D≠openComponent q hR.noTriple U.val} //
    (Nonalternation.eventEnumeration q hR).symm
      (closedRoot q hR.noTriple U.val D.val D.property)∈intervalSide (leftRank q hR c) (rightRank q hR c)} =>
    Primitive.closedWeight q hR hAux U D.val.val
  calc
    (∏ D, f D) = ∏ C, f (E C) :=
      (Fintype.prod_equiv E (fun C => f (E C)) f (by intro C;rfl)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro C _
      exact childComponentMap_closedWeight hRI q hR c hc hcut hAux S T C

/-- Full actual closed-product factorization for a compatible selected cut.
The original closed components partition by the singleton interval and its
complement. RI enters only through the derived closed amplitude equalities. -/
theorem compatible_closedWeight_product :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val), Primitive.closedWeight q hR hAux U D)=
      GeometricSmoothingWeights.componentAmplitudeProduct (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux) S.val
        (child_auxiliaryGenericity q hR c hc hcut hAux) S.property *
      (∏ C ∈ Finset.univ.erase (openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val),
        Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
          (parent_closedAuxiliary q hR c hc hcut hAux) T C) := by
  let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let Closed := {D : Primitive.Components q hR U // D≠openComponent q hR.noTriple U.val}
  let I := fun D : Closed => (Nonalternation.eventEnumeration q hR).symm
    (closedRoot q hR.noTriple U.val D.val D.property)∈intervalSide (leftRank q hR c) (rightRank q hR c)
  let f := fun D : Closed => Primitive.closedWeight q hR hAux U D.val
  have hsplit := Fintype.prod_subtype_mul_prod_subtype I f
  have hchild := childClosedInterval_closedWeight_product hRI q hR c hc hcut hAux S T
  have hparent := parentClosedComplement_closedWeight_product hRI q hR c hc hcut hAux S T
  change (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val), Primitive.closedWeight q hR hAux U D)=_
  rw [closedWeight_product_erase_eq_subtype q hR hAux U,
    closedWeight_product_erase_eq_subtype (parent q c hcut) (regular_parent q hR c hcut)
      (parent_closedAuxiliary q hR c hc hcut hAux) T]
  have hp : (∏ i : {D : Closed // ¬I D}, f i.val)=
      ∏ C : {C : Primitive.Components (parent q c hcut) (regular_parent q hR c hcut) T //
        C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val},
        Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
          (parent_closedAuxiliary q hR c hc hcut hAux) T C.val := by
    have he : (∏ i : {D : Closed // ¬I D}, f i.val)=
        (∏ i : {D : Closed // (Nonalternation.eventEnumeration q hR).symm
          (closedRoot q hR.noTriple U.val D.val D.property)∈complementSide (leftRank q hR c) (rightRank q hR c)},
          f i.val) := by
      apply Finset.prod_congr
      · ext i;simp
      · intro i _;rfl
    exact he.trans hparent
  exact hsplit.symm.trans (congrArg₂ (fun x y : ℚ => x*y) hchild hp)

end DirectGLSSW.ActiveArc.CompatibleWords
