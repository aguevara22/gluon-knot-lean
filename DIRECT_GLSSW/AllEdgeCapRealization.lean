import ParentCapRealization
import InteriorEdgeEvents
import DirectGLSSW.EdgeAffineNormalization

set_option autoImplicit false
namespace DirectGLSSW.AllEdgeCapRealization
open EdgeAffineNormalization ExtendedReturnArcGeometry InteriorEdgeEvents
open OriginalSecantProperness OriginalOuterProperness ParentCapRealization
noncomputable section

theorem secant_normalize (u v : PlanarPoint ℝ) (p : Fin 6 → PlanarPoint ℝ) :
    secantNumerator (fun i => normalize u v (p i)) =
      (normSq u v)^2 * secantNumerator p := by
  dsimp [secantNumerator, normalize, normSq, planarDet]
  ring

theorem outer_normalize (u v : PlanarPoint ℝ) (p : Fin 4 → PlanarPoint ℝ) :
    outerNumerator (fun i => normalize u v (p i)) =
      normSq u v * outerNumerator p := by
  dsimp [outerNumerator, normalize, normSq, planarDet]
  ring

theorem every_edge_realization {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (h6 : ∀ l : Fin 6 → Fin n, Function.Injective l → secantNumerator (q ∘ l) ≠ 0)
    (h4 : ∀ l : Fin 4 → Fin n, Function.Injective l → outerNumerator (q ∘ l) ≠ 0)
    (e : Fin n) :
    let P := normalizedPolygon q e ∘ cyclicVertexEquiv e
    let hn := hq.size_ge_three
    ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hn P ∧
      Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hn P ε))
        ↑(CapCriticalTimes.criticalPairs (extendedArc hn P ε) n) ∧
      ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (GlobalCapEntry.lineCapCore
            (CapCrossingEvent.horizontalMove (extendedArc hn P ε) (t+s)) a b) := by
  dsimp only
  let P := normalizedPolygon q e ∘ cyclicVertexEquiv e
  have hP : CyclicGeneric P := opened_generic _ (normalizedPolygon_generic q hq e) e
  obtain ⟨hv,hu,hl⟩ := normalizedPolygon_leftward q hq e
  have hU : (P (zeroIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,opened_zero] using hu
  have hV : (P (lastIndex hq.size_ge_three)).2 = 0 := by
    simpa only [P,opened_last] using hv
  have hL : (P (zeroIndex hq.size_ge_three)).1 < (P (lastIndex hq.size_ge_three)).1 := by
    simpa only [P,opened_zero,opened_last] using hl
  have hnz : normSq (q (cyclicSuccessor e)) (q e) ≠ 0 :=
    ne_of_gt (normSq_pos _ _ (chosen_endpoints_ne q hq e))
  apply exists_extension_and_punctured_caps hq.size_ge_three P hP hU hV hL
  · intro l hi
    change secantNumerator (fun i => normalize (q (cyclicSuccessor e)) (q e)
      (q (cyclicVertexEquiv e (l i)))) ≠ 0
    rw [secant_normalize]
    exact mul_ne_zero (pow_ne_zero 2 hnz) (h6 (cyclicVertexEquiv e ∘ l)
      ((cyclicVertexEquiv e).injective.comp hi))
  · intro l hi
    change outerNumerator (fun i => normalize (q (cyclicSuccessor e)) (q e)
      (q (cyclicVertexEquiv e (l i)))) ≠ 0
    rw [outer_normalize]
    exact mul_ne_zero hnz (h4 (cyclicVertexEquiv e ∘ l)
      ((cyclicVertexEquiv e).injective.comp hi))

/-- A single nearby actual parent has generic daughters and permissible cap
extensions for every original edge; auxiliary choices are existential per edge. -/
theorem exists_near_all_edge_realizations {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (U : Set (Fin n → PlanarPoint ℝ))
    (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ r ∈ U, ∃ hr : CyclicGeneric r,
      GeometricSmoothingWeights.auxiliaryGenericity r hr ∧
      ∀ e : Fin n,
      let P := normalizedPolygon r e ∘ cyclicVertexEquiv e
      let hn := hr.size_ge_three
      ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hn P ∧
        Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hn P ε))
          ↑(CapCriticalTimes.criticalPairs (extendedArc hn P ε) n) ∧
        ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
          ∀ a b : Fin n, a.val < b.val →
            CyclicGeneric (GlobalCapEntry.lineCapCore
              (CapCrossingEvent.horizontalMove (extendedArc hn P ε) (t+s)) a b) := by
  obtain ⟨r,hrU,hr,haux,h6,h4⟩ := exists_joint_parent_daughters q hq U hU hqU
  exact ⟨r,hrU,hr,haux,every_edge_realization r hr h6 h4⟩





end
end DirectGLSSW.AllEdgeCapRealization
