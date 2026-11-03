import ActiveArcBeforeFirstComponents
import ActiveArcSelectedCutSum
import ActiveArcTinyParentEndpoint

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open Cursor Split SingletonWords Primitive
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual moving selected-cut contribution factors with fixed physical
child and parent. The only changing point on the RHS is the prefixed mark. -/
theorem gammaM_selectedCut_before_first
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR) (hRI : GLSSWRootIndependence)
    (t : ℝ) (ht0 : 0≤t) (htc : t<leftParameter q c) :
    let qm := moveStart q t
    let hm := before_first_regular q hR c hc t ht0 htc
    let C := crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t htc c)
    let hAm := BeforeFirst.closedAuxiliary q hR c hc t ht0 htc hAux
    (∑ U : {U : Primitive.Support qm hm // C ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent qm hm U.val *
          ∏ D ∈ Finset.univ.erase (openComponent qm hm.noTriple U.val.val),
            Primitive.closedWeight qm hm hAm U.val D)) =
      -(GeometricSmoothingWeights.separatingSmoothingSum
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
        (child_auxiliaryGenericity q hR c hc hcut hAux)) *
      (∑ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
        (-1 : ℚ)^T.val.card *
          (OpenMarkedCurrent.entry
            (polygonSignArray (fun k => if k=0 then moveStart q t 0 else
              rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
                (regular_parent q hR c hcut) T)
                (RetainedWords.openLast (parent q c hcut)
                  (regular_parent q hR c hcut) T.val) (k-1)))
            0 (RetainedWords.openCount (parent q c hcut) (regular_parent q hR c hcut) T.val) *
            ∏ D ∈ Finset.univ.erase
              (openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T.val),
              Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
                (parent_closedAuxiliary q hR c hc hcut hAux) T D)) := by
  let qm := moveStart q t
  let hm := before_first_regular q hR c hc t ht0 htc
  let C := crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
    c (survives_before_first q c hc t htc c)
  let hAm := BeforeFirst.closedAuxiliary q hR c hc t ht0 htc hAux
  have hcm : FirstCrossing qm C := before_first_isFirst q hR c hc t ht0 htc
  have hfactor := gammaM_selectedCut_factorization qm hm C hcm hcut hAm hRI
  have hp := before_first_parent q hR c hc t ht0 htc hcut
  have hchild := before_first_child q hR c hc t ht0 htc hcut
  dsimp only [qm,hm,C] at hfactor
  simp only [hchild] at hfactor
  refine hfactor.trans ?_
  congr 1
  let F := fun (p : Fin (b+2) → PlanarPoint ℝ) (hP : Regular p)
      (hA : Primitive.ClosedAuxiliary p hP) =>
    ∑ T : Primitive.Support p hP, (-1 : ℚ)^T.val.card *
      (OpenMarkedCurrent.entry (polygonSignArray (fun k => if k=0 then moveStart q t 0 else
        rootedPolygonWord (Primitive.OpenVertex p hP T)
          (RetainedWords.openLast p hP T.val) (k-1))) 0 (RetainedWords.openCount p hP T.val) *
        ∏ D ∈ Finset.univ.erase (openComponent p hP.noTriple T.val),
          Primitive.closedWeight p hP hA T D)
  have hF (p₁ p₂ : Fin (b+2) → PlanarPoint ℝ) (h₁ : Regular p₁) (h₂ : Regular p₂)
      (A₁ : Primitive.ClosedAuxiliary p₁ h₁) (A₂ : Primitive.ClosedAuxiliary p₂ h₂)
      (h : p₁=p₂) : F p₁ h₁ A₁ = F p₂ h₂ A₂ := by
    subst p₂
    rfl
  change F _ _ _ = F _ _ _
  exact hF _ _ _ _ _ _ hp

end DirectGLSSW.ActiveArc.CompatibleWords
