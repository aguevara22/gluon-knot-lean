import SharpDaughterSignedIsoLocality
import SharpDaughterRotationLocality
import OriginalLeftTurnLocality
import UniformDaughterSupportLocality
import DirectGLSSW.HOMFLY.HOMFLYSkeinEvaluator
import DirectGLSSW.RealPolygons

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open DirectGLSSW DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients DirectGLSSW.TruncationDirection Filter Topology

namespace DirectGLSSW.CornerStateSumLocality

/-- The literal integer corner state sum from the frozen joint identity. -/
def cornerStateSum (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) : ℤ := by
  let ell : ℕ := (Finset.univ.filter (fun i : Fin n =>
    0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
      (cyclicTangent q i))).card
  let Supports := {S : Finset (PolygonCrossing q) //
    PolygonNonalternation.polygonNonalternating q hq.g2 S ∧
    ∀ C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S),
      ∃ root : PolygonEvent q,
        DaughterFirstReturn.retainedCorner q S root ∧
        PermutationOrbits.componentOf (smoothingDartPermutation q hq.g2 S) root = C ∧
        ((∀ i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)),
          0 < planarDet
            (DaughterFirstReturn.daughterSideVector q hq.g2 S root
              ((cyclicSuccessorPerm (Fintype.card
                (DaughterFirstReturn.CornerCoord q hq.g2 S root)))⁻¹ i))
            (DaughterFirstReturn.daughterSideVector q hq.g2 S root i)) ∨
         (∀ i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)),
          planarDet
            (DaughterFirstReturn.daughterSideVector q hq.g2 S root
              ((cyclicSuccessorPerm (Fintype.card
                (DaughterFirstReturn.CornerCoord q hq.g2 S root)))⁻¹ i))
            (DaughterFirstReturn.daughterSideVector q hq.g2 S root i) < 0))}
  letI : Fintype Supports := Fintype.ofFinite Supports
  exact (((-1 : ℤ) ^ ell *
    ∑ S : Supports,
      letI : Fintype (PermutationOrbits.Component
        (smoothingDartPermutation q hq.g2 S.val)) :=
          PermutationOrbits.componentFintype (smoothingDartPermutation q hq.g2 S.val)
      (-1 : ℤ) ^ S.val.card *
        ∏ C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S.val),
          coeff
            (H (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1)
              (SharpDaughter.arc_count_pos q hq S.val C S.property.1))
            (1 - (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1).nCrossing -
              |SharpDaughterRotation.sharpDaughterRotationInteger
                q hq S.val C S.property.1|) 0 : ℤ))

private abbrev CornerSupports {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) :=
  {S : Finset (PolygonCrossing q) //
    UniformDaughterSupportLocality.uniformDaughterSupport q hq S}

private theorem cornerCoefficient_transport
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : ∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
      SignedDiagramIso D E → H D hD = H E hE)
    (D D' : PLLinkDiagram) (hD : 0 < D.nArc) (hD' : 0 < D'.nArc)
    (I : SignedDiagramIso D D') (r r' : ℤ) (hr : r = r') :
    coeff (H D' hD') (1 - D'.nCrossing - |r'|) 0 =
      coeff (H D hD) (1 - D.nCrossing - |r|) 0 := by
  have hcross : D.nCrossing = D'.nCrossing := by
    simpa using (Fintype.card_congr I.crossingEquiv)
  have hpoly := hH D D' hD hD' I
  rw [← hpoly]
  congr 1
  rw [← hcross, ← hr]

private theorem cornerStateSum_transport
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : ∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
      SignedDiagramIso D E → H D hD = H E hE)
    {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (E : PolygonCrossing q ≃ PolygonCrossing q')
    (hlabels : ∀ c, (E c).val = c.val)
    (horder : ∀ x y : PolygonEvent q,
      (letI := polygonEventOrder q hq.g2; x < y) ↔
        (letI := polygonEventOrder q' hq'.g2;
          DirectGLSSW.LocalCrossingTransport.polygonEventMapEquiv E x < DirectGLSSW.LocalCrossingTransport.polygonEventMapEquiv E y))
    (hell : (Finset.univ.filter (fun i : Fin n =>
        0 < planarDet (cyclicTangent q' ((cyclicSuccessorPerm n)⁻¹ i))
          (cyclicTangent q' i))).card =
      (Finset.univ.filter (fun i : Fin n =>
        0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
          (cyclicTangent q i))).card)
    (hrotation : ∀ (S : Finset (PolygonCrossing q))
      (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
      (C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S)),
      SharpDaughterRotation.sharpDaughterRotationInteger q hq S C hNA =
        SharpDaughterRotation.sharpDaughterRotationInteger q' hq' (S.map E.toEmbedding)
          (LocalSupportConjugacy.smoothingComponentMapEquiv q q' hq hq' E
            hlabels horder S C)
          ((LocalSupportConjugacy.polygonNonalternating_map_iff
            q q' hq hq' E hlabels horder S).mp hNA))
    (hsupport : ∀ S : Finset (PolygonCrossing q),
      UniformDaughterSupportLocality.uniformDaughterSupport q hq S ↔
        UniformDaughterSupportLocality.uniformDaughterSupport q' hq'
          (S.map E.toEmbedding))
    (hisos : ∀ (S : Finset (PolygonCrossing q))
      (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
      (C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S)),
      Nonempty (SignedDiagramIso
        (SharpDaughter.sharpDaughterDiagram q hq S C hNA)
        (SharpDaughter.sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
          (LocalSupportConjugacy.smoothingComponentMapEquiv q q' hq hq' E
            hlabels horder S C)
          ((LocalSupportConjugacy.polygonNonalternating_map_iff
            q q' hq hq' E hlabels horder S).mp hNA)))) :
    cornerStateSum H q' hq' = cornerStateSum H q hq := by
  classical
  let e : CornerSupports q hq ≃ CornerSupports q' hq' :=
    E.finsetCongr.subtypeEquiv hsupport
  letI : Fintype (CornerSupports q hq) := Fintype.ofFinite _
  letI : Fintype (CornerSupports q' hq') := Fintype.ofFinite _
  unfold cornerStateSum
  dsimp only
  rw [hell]
  congr 1
  calc
    (∑ S : {S : Finset (PolygonCrossing q') //
        UniformDaughterSupportLocality.uniformDaughterSupport q' hq' S},
      (-1 : ℤ) ^ S.val.card *
        ∏ C : PermutationOrbits.Component (smoothingDartPermutation q' hq'.g2 S.val),
          coeff (H (SharpDaughter.sharpDaughterDiagram q' hq' S.val C S.property.1)
            (SharpDaughter.arc_count_pos q' hq' S.val C S.property.1))
            (1 - (SharpDaughter.sharpDaughterDiagram q' hq' S.val C S.property.1).nCrossing -
              |SharpDaughterRotation.sharpDaughterRotationInteger q' hq' S.val C S.property.1|) 0) =
      ∑ S : CornerSupports q hq,
        (-1 : ℤ) ^ (e S).val.card *
          ∏ C' : PermutationOrbits.Component
              (smoothingDartPermutation q' hq'.g2 (e S).val),
            coeff (H (SharpDaughter.sharpDaughterDiagram q' hq' (e S).val C' (e S).property.1)
              (SharpDaughter.arc_count_pos q' hq' (e S).val C' (e S).property.1))
              (1 - (SharpDaughter.sharpDaughterDiagram q' hq' (e S).val C' (e S).property.1).nCrossing -
                |SharpDaughterRotation.sharpDaughterRotationInteger q' hq' (e S).val C' (e S).property.1|) 0 := by
        exact (Fintype.sum_equiv e
          (fun S => (-1 : ℤ) ^ (e S).val.card *
            ∏ C' : PermutationOrbits.Component
                (smoothingDartPermutation q' hq'.g2 (e S).val),
              coeff (H (SharpDaughter.sharpDaughterDiagram q' hq' (e S).val C' (e S).property.1)
                (SharpDaughter.arc_count_pos q' hq' (e S).val C' (e S).property.1))
                (1 - (SharpDaughter.sharpDaughterDiagram q' hq' (e S).val C' (e S).property.1).nCrossing -
                  |SharpDaughterRotation.sharpDaughterRotationInteger q' hq' (e S).val C' (e S).property.1|) 0)
          (fun T => (-1 : ℤ) ^ T.val.card *
            ∏ C' : PermutationOrbits.Component
                (smoothingDartPermutation q' hq'.g2 T.val),
              coeff (H (SharpDaughter.sharpDaughterDiagram q' hq' T.val C' T.property.1)
                (SharpDaughter.arc_count_pos q' hq' T.val C' T.property.1))
                (1 - (SharpDaughter.sharpDaughterDiagram q' hq' T.val C' T.property.1).nCrossing -
                  |SharpDaughterRotation.sharpDaughterRotationInteger q' hq' T.val C' T.property.1|) 0)
          (by intro S; rfl)).symm
    _ = ∑ S : CornerSupports q hq,
        (-1 : ℤ) ^ S.val.card *
          ∏ C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S.val),
            coeff (H (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1)
              (SharpDaughter.arc_count_pos q hq S.val C S.property.1))
              (1 - (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1).nCrossing -
                |SharpDaughterRotation.sharpDaughterRotationInteger q hq S.val C S.property.1|) 0 := by
      apply Finset.sum_congr rfl
      intro S _
      have hmap : (e S).val = S.val.map E.toEmbedding := rfl
      have hcard : (e S).val.card = S.val.card := by rw [hmap, Finset.card_map]
      rw [hcard]
      let CE := LocalSupportConjugacy.smoothingComponentMapEquiv q q' hq hq' E
        hlabels horder S.val
      have hprod :
          (∏ C' : PermutationOrbits.Component
              (smoothingDartPermutation q' hq'.g2 (e S).val),
            coeff (H (SharpDaughter.sharpDaughterDiagram q' hq' (e S).val C' (e S).property.1)
              (SharpDaughter.arc_count_pos q' hq' (e S).val C' (e S).property.1))
              (1 - (SharpDaughter.sharpDaughterDiagram q' hq' (e S).val C' (e S).property.1).nCrossing -
                |SharpDaughterRotation.sharpDaughterRotationInteger q' hq' (e S).val C' (e S).property.1|) 0) =
          ∏ C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S.val),
            coeff (H (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1)
              (SharpDaughter.arc_count_pos q hq S.val C S.property.1))
              (1 - (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1).nCrossing -
                |SharpDaughterRotation.sharpDaughterRotationInteger q hq S.val C S.property.1|) 0 := by
        calc
          _ = ∏ C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S.val),
              coeff (H (SharpDaughter.sharpDaughterDiagram q' hq' (S.val.map E.toEmbedding)
                (CE C) ((LocalSupportConjugacy.polygonNonalternating_map_iff
                  q q' hq hq' E hlabels horder S.val).mp S.property.1))
                (SharpDaughter.arc_count_pos q' hq' (S.val.map E.toEmbedding)
                  (CE C) ((LocalSupportConjugacy.polygonNonalternating_map_iff
                    q q' hq hq' E hlabels horder S.val).mp S.property.1)))
                (1 - (SharpDaughter.sharpDaughterDiagram q' hq' (S.val.map E.toEmbedding)
                  (CE C) ((LocalSupportConjugacy.polygonNonalternating_map_iff
                    q q' hq hq' E hlabels horder S.val).mp S.property.1)).nCrossing -
                  |SharpDaughterRotation.sharpDaughterRotationInteger q' hq' (S.val.map E.toEmbedding)
                    (CE C) ((LocalSupportConjugacy.polygonNonalternating_map_iff
                      q q' hq hq' E hlabels horder S.val).mp S.property.1)|) 0 := by
                symm
                apply Fintype.prod_equiv CE
                intro C
                rfl
          _ = _ := by
            apply Finset.prod_congr rfl
            intro C _
            let C' := CE C
            let hNA' := (LocalSupportConjugacy.polygonNonalternating_map_iff
              q q' hq hq' E hlabels horder S.val).mp S.property.1
            let D := SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1
            let D' := SharpDaughter.sharpDaughterDiagram q' hq' (S.val.map E.toEmbedding) C' hNA'
            have hcoeff := cornerCoefficient_transport H hH D D'
              (SharpDaughter.arc_count_pos q hq S.val C S.property.1)
              (SharpDaughter.arc_count_pos q' hq' (S.val.map E.toEmbedding) C' hNA')
              (Classical.choice (hisos S.val S.property.1 C))
              (SharpDaughterRotation.sharpDaughterRotationInteger q hq S.val C S.property.1)
              (SharpDaughterRotation.sharpDaughterRotationInteger q' hq'
                (S.val.map E.toEmbedding) C' hNA')
              (hrotation S.val S.property.1 C)
            simpa [D, D', C', hNA'] using hcoeff
      change (-1 : ℤ) ^ S.val.card * _ = _
      rw [hprod]

/-- Expanding the definition reproduces the frozen literal expression exactly. -/
theorem cornerStateSum_eq_literal
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    let ell : ℕ := (Finset.univ.filter (fun i : Fin n =>
      0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
        (cyclicTangent q i))).card
    let Supports := {S : Finset (PolygonCrossing q) //
      PolygonNonalternation.polygonNonalternating q hq.g2 S ∧
      ∀ C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S),
        ∃ root : PolygonEvent q,
          DaughterFirstReturn.retainedCorner q S root ∧
          PermutationOrbits.componentOf (smoothingDartPermutation q hq.g2 S) root = C ∧
          ((∀ i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)),
            0 < planarDet
              (DaughterFirstReturn.daughterSideVector q hq.g2 S root
                ((cyclicSuccessorPerm (Fintype.card
                  (DaughterFirstReturn.CornerCoord q hq.g2 S root)))⁻¹ i))
              (DaughterFirstReturn.daughterSideVector q hq.g2 S root i)) ∨
           (∀ i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)),
            planarDet
              (DaughterFirstReturn.daughterSideVector q hq.g2 S root
                ((cyclicSuccessorPerm (Fintype.card
                  (DaughterFirstReturn.CornerCoord q hq.g2 S root)))⁻¹ i))
              (DaughterFirstReturn.daughterSideVector q hq.g2 S root i) < 0))}
    letI : Fintype Supports := Fintype.ofFinite Supports
    cornerStateSum H q hq =
      (((-1 : ℤ) ^ ell *
        ∑ S : Supports,
          letI : Fintype (PermutationOrbits.Component
            (smoothingDartPermutation q hq.g2 S.val)) :=
              PermutationOrbits.componentFintype (smoothingDartPermutation q hq.g2 S.val)
          (-1 : ℤ) ^ S.val.card *
            ∏ C : PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S.val),
              coeff
                (H (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1)
                  (SharpDaughter.arc_count_pos q hq S.val C S.property.1))
                (1 - (SharpDaughter.sharpDaughterDiagram q hq S.val C S.property.1).nCrossing -
                  |SharpDaughterRotation.sharpDaughterRotationInteger
                    q hq S.val C S.property.1|) 0 : ℤ)) := by
  rfl


/-- Actual local constancy: the nearby generic witness and all reindexing data
are produced internally from full-parent locality. -/
theorem eventually_cornerStateSum_eq
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : ∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
      SignedDiagramIso D E → H D hD = H E hE)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∃ hq' : CyclicGeneric q',
      cornerStateSum H q' hq' = cornerStateSum H q hq := by
  filter_upwards [
    SharpDaughterSignedIsoLocality.eventually_sharpDaughter_signedDiagramIso q hq,
    UniformDaughterSupportLocality.eventually_uniformDaughterSupport_map_iff q hq,
    SharpDaughterRotationLocality.eventually_all_sharpDaughterRotationIntegers q hq,
    OriginalLeftTurnLocality.eventually_literal_leftTurnCount_eq q hq]
    with q' hiso hsupport hrotation hell
  obtain ⟨hq', E, hlabels, horder, hisos⟩ := hiso
  exact ⟨hq', cornerStateSum_transport H hH q q' hq hq' E hlabels horder hell
    (hrotation hq' E hlabels horder)
    (hsupport hq' E hlabels horder)
    (fun S hNA C => hisos S C hNA)⟩

end DirectGLSSW.CornerStateSumLocality

