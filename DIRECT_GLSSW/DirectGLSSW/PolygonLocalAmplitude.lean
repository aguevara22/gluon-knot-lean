import DirectGLSSW.PolygonLocalMotion
import DirectGLSSW.PolygonSignExtensionality

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW

theorem exists_local_polygonAmplitude_stability {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v : Fin n, Continuous (fun t : ℝ => Q t v))
    (h0 : CyclicGeneric (Q 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ ht : CyclicGeneric (Q t),
        polygonAmplitude (Q t) ht = polygonAmplitude (Q 0) h0 := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_local_cyclicGeneric_and_orderedSign_stability Q hQ h0
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  obtain ⟨htgeneric, hsign⟩ := hlocal t ht
  refine ⟨htgeneric, ?_⟩
  apply DirectGLSSW.polygonAmplitude_eq_of_oriented_triple_signs (Q t) (Q 0)
    htgeneric h0
  intro i k j hik hkj hij
  exact hsign i k j hik hkj hij

end DirectGLSSW.ShortEdgeGenericity
