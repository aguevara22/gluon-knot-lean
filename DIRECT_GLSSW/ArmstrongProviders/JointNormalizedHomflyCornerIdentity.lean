import WorkingReconstruction
import JointCandidateAssembly

set_option autoImplicit false
open scoped BigOperators Classical
open DirectGLSSW DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients

theorem ArmstrongProviders.jointNormalizedHomflyCornerIdentity :
∃ H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
  IsNormalizedDescendingSkeinEvaluator H ∧
  (∀ K : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff,
    IsNormalizedDescendingSkeinEvaluator K → K = H) ∧
  (∀ (D : PLLinkDiagram) (hD : 0 < D.nArc) (T : BasedTraversal D),
    H D hD = descendingLaurentEvaluator D T) ∧
  (∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
    SignedDiagramIso D E → H D hD = H E hE) ∧
  (∀ (D E : PLLinkDiagram) (hD : 0 < D.nArc) (hE : 0 < E.nArc),
    SignedRegularDeletion D E → H D hD = H E hE) ∧
  (GLSSWRootIndependence →
    ∀ {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q),
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
    polygonAmplitude q hq =
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
                    q hq S.val C S.property.1|) 0 : ℤ) : ℚ))
 := by
  exact DirectGLSSW.JointAssembly.joint_of_candidate_corner_identity
    DirectGLSSW.SourceWorkingReconstruction.candidate_corner_identity_via_working_domain
