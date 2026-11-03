import SharpDaughterSignedIsoOfOrientation
import CrossingOrientationLocality

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughterSignedIsoLocality
open DirectGLSSW PermutationOrbits PolygonDrawingBridge
open DirectGLSSW.TruncationDirection DirectGLSSW.LocalCrossingTransport
open DirectGLSSW.HOMFLY.SharpDaughter Filter Topology

/-- On the full parent G1/G2 domain, one neighborhood identifies the actual
signed diagrams of every support/component. Ordered crossing orientation is
derived locally in the proof, rather than assumed in this statement. -/
theorem eventually_sharpDaughter_signedDiagramIso {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ q' in 𝓝 q, ∃ hq' : CyclicGeneric q',
      ∃ E : PolygonCrossing q ≃ PolygonCrossing q',
      ∃ hlabels : ∀ c, (E c).val = c.val,
      ∃ horder : ∀ x y : PolygonEvent q,
        ((polygonEventOrder q hq.g2).lt x y ↔
          (polygonEventOrder q' hq'.g2).lt
            (polygonEventMapEquiv E x) (polygonEventMapEquiv E y)),
      ∀ (S : Finset (PolygonCrossing q)) (C : Component (P q hq S))
        (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S),
      Nonempty (SignedDiagramIso (sharpDaughterDiagram q hq S C hNA)
        (sharpDaughterDiagram q' hq' (S.map E.toEmbedding)
          (LocalSupportConjugacy.smoothingComponentMapEquiv
            q q' hq hq' E hlabels horder S C)
          ((LocalSupportConjugacy.polygonNonalternating_map_iff
            q q' hq hq' E hlabels horder S).mp hNA))) := by
  filter_upwards [CrossingOrientationLocality.eventually_configuration_oriented_event_order q hq]
    with q' hnear
  obtain ⟨hq', E, hlabels, horder, hpos⟩ := hnear
  refine ⟨hq', E, hlabels, horder, ?_⟩
  intro S C hNA
  exact ⟨SharpDaughterSignedIsoOfOrientation.sharpDaughter_signedDiagramIso_of_crossing_orientation
    q q' hq hq' E hlabels horder S C hNA hpos⟩

end DirectGLSSW.HOMFLY.SharpDaughterSignedIsoLocality
