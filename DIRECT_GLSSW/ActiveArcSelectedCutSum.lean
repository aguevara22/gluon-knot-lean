import ActiveArcParentOpenCurrent
import ActiveArcCompatibleClosedProduct

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits SingletonWords Split Cursor
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private def selectedCutEraseEquiv
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q)
    : {U : Primitive.Support q hR // c ∈ U.val} ≃
      {V : Finset (Crossing q) // c ∉ V ∧
        Nonalternation.Nonalternating q hR (insert c V)} where
  toFun U := ⟨U.val.val.erase c, by
    constructor
    · simp
    · rw [Finset.insert_erase U.property]
      exact U.val.property⟩
  invFun V := ⟨⟨insert c V.val, V.property.2⟩, Finset.mem_insert_self _ _⟩
  left_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.insert_erase U.property
  right_inv V := by
    apply Subtype.ext
    exact Finset.erase_insert V.property.1

private def selectedCutSupportEquiv
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val = a) :
    {U : Primitive.Support q hR // c ∈ U.val} ≃
      ({S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
        PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S} ×
       Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)) :=
  (selectedCutEraseEquiv q hR c).trans
    (nonalternatingSelectionEquiv q hR c hc hcut).symm

theorem gammaM_selectedCut_factorization
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val = a)
    (hAux : Primitive.ClosedAuxiliary q hR) (hRI : GLSSWRootIndependence) :
    (∑ U : {U : Primitive.Support q hR // c ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent q hR U.val *
          ∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val.val),
            Primitive.closedWeight q hR hAux U.val D)) =
    -(GeometricSmoothingWeights.separatingSmoothingSum
        (child q hR c hc.1 hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
        (child_auxiliaryGenericity q hR c hc hcut hAux)) *
      (∑ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
        (-1 : ℚ)^T.val.card *
          (OpenMarkedCurrent.entry
              (polygonSignArray (fun k =>
                if k = 0 then q ⟨0, by omega⟩
                else rootedPolygonWord
                  (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T)
                  (RetainedWords.openLast (parent q c hcut)
                    (regular_parent q hR c hcut) T.val) (k-1)))
              0 (RetainedWords.openCount (parent q c hcut)
                (regular_parent q hR c hcut) T.val) *
            ∏ D ∈ Finset.univ.erase
                (openComponent (parent q c hcut)
                  (regular_parent q hR c hcut).noTriple T.val),
              Primitive.closedWeight (parent q c hcut) (regular_parent q hR c hcut)
                (parent_closedAuxiliary q hR c hc hcut hAux) T D)) := by
  classical
  let C := child q hR c hc.1 hcut
  let hC := child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux
  let hCA := child_auxiliaryGenericity q hR c hc hcut hAux
  let P := parent q c hcut
  let hP := regular_parent q hR c hcut
  let hPA := parent_closedAuxiliary q hR c hc hcut hAux
  let E := selectedCutSupportEquiv q hR c hc hcut
  let F : {S : Finset (PolygonCrossing C) //
      PolygonNonalternation.polygonNonalternating C (child_noTriple q hR c hc.1 hcut) S} → ℚ := fun S =>
    (-1 : ℚ)^S.val.card * GeometricSmoothingWeights.componentAmplitudeProduct
      C hC S.val hCA S.property
  let G : Primitive.Support P hP → ℚ := fun T =>
    (-1 : ℚ)^T.val.card *
      (OpenMarkedCurrent.entry
          (polygonSignArray (fun k =>
            if k = 0 then q ⟨0, by omega⟩
            else rootedPolygonWord (Primitive.OpenVertex P hP T)
              (RetainedWords.openLast P hP T.val) (k-1)))
          0 (RetainedWords.openCount P hP T.val) *
        ∏ D ∈ Finset.univ.erase (openComponent P hP.noTriple T.val),
          Primitive.closedWeight P hP hPA T D)
  have hsum :
      (∑ U : {U : Primitive.Support q hR // c ∈ U.val},
        (-1 : ℚ)^U.val.val.card *
          (Primitive.openCurrent q hR U.val *
            ∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val.val),
              Primitive.closedWeight q hR hAux U.val D)) =
      ∑ p : ({S : Finset (PolygonCrossing C) //
          PolygonNonalternation.polygonNonalternating C
            (child_noTriple q hR c hc.1 hcut) S} × Primitive.Support P hP),
        -(F p.1 * G p.2) := by
    apply Fintype.sum_equiv E
    intro U
    let p := E U
    let V := nonalternatingSelectionEquiv q hR c hc hcut p
    let W : Primitive.Support q hR := ⟨insert c V.val, V.property.2⟩
    have hV : V.val = U.val.val.erase c := by
      have h := Equiv.apply_symm_apply (nonalternatingSelectionEquiv q hR c hc hcut)
        ((selectedCutEraseEquiv q hR c) U)
      exact congrArg Subtype.val h
    have hW : W.val = U.val.val := by
      dsimp [W]
      rw [hV]
      exact Finset.insert_erase U.property
    have hWsup : W = U.val := Subtype.ext hW
    have hcardV : V.val.card = p.1.val.card + p.2.val.card :=
      nonalternatingSelectionEquiv_card q hR c hc hcut p.1 p.2
    have hcard : U.val.val.card = p.1.val.card + p.2.val.card + 1 := by
      rw [← hW]
      rw [Finset.card_insert_of_not_mem V.property.1, hcardV]
    have hopen := parent_openCurrent_eq_prefixedParentWord q hR c hc hcut p.1 p.2
    have hprod := compatible_closedWeight_product hRI q hR c hc hcut hAux p.1 p.2
    have hopenW : Primitive.openCurrent q hR W =
        OpenMarkedCurrent.entry
          (polygonSignArray (fun k =>
            if k = 0 then q ⟨0, by omega⟩
            else rootedPolygonWord (Primitive.OpenVertex P hP p.2)
              (RetainedWords.openLast P hP p.2.val) (k-1)))
          0 (RetainedWords.openCount P hP p.2.val) := by
      simpa [W, V] using hopen
    have hprodW :
        (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple W.val),
          Primitive.closedWeight q hR hAux W D) =
          GeometricSmoothingWeights.componentAmplitudeProduct C hC p.1.val hCA p.1.property *
            (∏ D ∈ Finset.univ.erase (openComponent P hP.noTriple p.2.val),
              Primitive.closedWeight P hP hPA p.2 D) := by
      simpa [W, V] using hprod
    rw [hcard, ← hWsup, hopenW, hprodW]
    dsimp [F, G]
    rw [pow_add, pow_add]
    norm_num [pow_one]
    ring
  rw [hsum, Fintype.sum_prod_type]
  rw [GeometricSmoothingWeights.separatingSmoothingSum]
  dsimp [F, G, C, hC, hCA, P, hP, hPA]
  symm
  calc
    -(∑ S : {S : Finset (PolygonCrossing C) //
        PolygonNonalternation.polygonNonalternating C (child_noTriple q hR c hc.1 hcut) S}, F S) *
      (∑ T : Primitive.Support P hP, G T) =
        -((∑ S : {S : Finset (PolygonCrossing C) //
            PolygonNonalternation.polygonNonalternating C (child_noTriple q hR c hc.1 hcut) S}, F S) *
          (∑ T : Primitive.Support P hP, G T)) := by ring
    _ = -(∑ S : {S : Finset (PolygonCrossing C) //
          PolygonNonalternation.polygonNonalternating C (child_noTriple q hR c hc.1 hcut) S},
          ∑ T : Primitive.Support P hP, F S * G T) := by
      rw [Finset.sum_mul_sum]
    _ = ∑ S : {S : Finset (PolygonCrossing C) //
          PolygonNonalternation.polygonNonalternating C (child_noTriple q hR c hc.1 hcut) S},
          ∑ T : Primitive.Support P hP, -(F S * G T) := by
      simp

end DirectGLSSW.ActiveArc.CompatibleWords
