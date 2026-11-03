import ActiveArcExposedInitialization
import OpenCurrentWordCongruence

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive GeometricSmoothingWeights

/-- Opening the literal cut arc at its terminal index reads exactly the
original complementary physical word, on the full index range used by M. -/
theorem cutArc_open_word
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
    (k : ℕ) (hk : k<n+2) :
    rootedPolygonWord (cutArc q e) (Fin.last (n+1)) k=rootedPolygonWord q e k := by
  have hi : cyclicVertexIndex (Fin.last (n+1)) k=(⟨k,hk⟩ : Fin (n+2)) := by
    apply Fin.ext
    rw [cyclicVertexIndex_val _ hk]
    simp only [Fin.val_last]
    split_ifs <;> omega
  change cutArc q e (cyclicVertexIndex (Fin.last (n+1)) k)=_
  rw [hi]
  rfl

/-- The actual source open current on the cut arc agrees with the exposed
polygon amplitude. This is M at the literal arc, not a smoothing summand. -/
theorem cutArc_openCurrent_eq_amplitude
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
    (hq : CyclicGeneric q) (he : LeftExposed q e) (hRI : GLSSWRootIndependence) :
    openedEdgeCurrent (cutArc q e) (Fin.last (n+1))=polygonAmplitude q hq := by
  have hw : openedEdgeCurrent (cutArc q e) (Fin.last (n+1))=openedEdgeCurrent q e := by
    unfold openedEdgeCurrent
    apply openMarkedCurrent_entry_congr_of_word_eq _ _ (by omega)
    intro k hk
    exact cutArc_open_word q e k (by omega)
  exact hw.trans (openedEdgeCurrent_eq_amplitude q hq e he hRI)

/-- Both source exposed-initialization conclusions on the same actual cut arc:
M equals A and the full physical GammaM equals the full separating sum. -/
theorem actual_exposed_initialization
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
    (hq : CyclicGeneric q) (he : LeftExposed q e)
    (hAux : auxiliaryGenericity q hq) (hRI : GLSSWRootIndependence) :
    openedEdgeCurrent (cutArc q e) (Fin.last (n+1))=polygonAmplitude q hq ∧
    Primitive.GammaM (cutArc q e) (cutArc_regular q e hq)
      (closedAuxiliary_of_parent q e hq he hAux)=separatingSmoothingSum q hq hAux :=
  ⟨cutArc_openCurrent_eq_amplitude q e hq he hRI,
    GammaM_eq_separatingSmoothingSum q e hq he hAux hRI⟩




end DirectGLSSW.ActiveArc.ExposedChart
