import DirectGLSSW.CapPairwiseContribution
import DirectGLSSW.CapContributionExpansion
import DirectGLSSW.CapMatrixAssembly
import DirectGLSSW.CapEventInterpretation

set_option autoImplicit false

namespace DirectGLSSW.ConcreteCapMatrix
open DirectGLSSW CapCriticalTimes CapCriticalEventGeometry CapCrossingEvent
open GlobalCapEntry OrderedCapEvents CapGlobalTelescope CapPairwiseContribution
open CapContributionExpansion CapEventInterpretation
open scoped BigOperators


private theorem ordered_pairwise_contribution
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (hlocalCaps : ∀ t, t ∈ criticalTimes q n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b))
    (c d : EventIndex q n) (hcd : c < d) :
    (eventSign q n c + eventSign q n d) * eventPairing q n c d +
      ∑ t ∈ (criticalTimes q n).filter
        (fun t => eventTime q n c < t ∧ t < eventTime q n d),
        ∑ i : Fin n, ∑ j : Fin n,
          eventRow q n c i * contributionAt q n t i j * eventColumn q n d j = 0 := by
  classical
  have hc := eventPair_bounds q n c
  have hd := eventPair_bounds q n d
  have hcroot : criticalRoot q ((eventPair q n c).1, (eventPair q n c).1 + 1) =
      eventTime q n c := by
    simpa only [← hc.2.2.1] using (eventPair_spec q n c).2
  have hdroot : criticalRoot q ((eventPair q n d).1, (eventPair q n d).1 + 1) =
      eventTime q n d := by
    simpa only [← hd.2.2.1] using (eventPair_spec q n d).2
  have hsK : planarDet (q (eventPair q n c).1 - q ((eventPair q n c).1 + 1)) (1, 0) ≠ 0 := by
    simpa only [← hc.2.2.1] using hc.2.2.2.2
  have hsL : planarDet (q (eventPair q n d).1 - q ((eventPair q n d).1 + 1)) (1, 0) ≠ 0 := by
    simpa only [← hd.2.2.1] using hd.2.2.2.2
  have htc : (q (eventPair q n c).1).2 / (q ((eventPair q n c).1 + 1)).2 < 0 := by
    simpa only [← hc.2.2.1] using hc.2.2.2.1
  have htd : (q (eventPair q n d).1).2 / (q ((eventPair q n d).1 + 1)).2 < 0 := by
    simpa only [← hd.2.2.1] using hd.2.2.2.1
  have hrootorder : criticalRoot q ((eventPair q n c).1, (eventPair q n c).1 + 1) <
      criticalRoot q ((eventPair q n d).1, (eventPair q n d).1 + 1) := by
    rw [hcroot, hdroot]
    exact eventTime_strictMono q n hcd
  have hroots' : ∀ p r, p ∈ criticalPairs q n → r ∈ criticalPairs q n →
      criticalRoot q p = criticalRoot q r → p = r := by
    intro p r hp hr he
    exact hroots hp hr he
  have h := actual_pairwise_contribution_identity hRI q n
    (eventPair q n c).1 (eventPair q n d).1 hzero hoff hdistinct hpositive hroots'
    hc.1 hc.2.1 hd.1 hd.2.1 hsK hsL htc htd hrootorder hlocalCaps
  dsimp only at h
  rw [hcroot, hdroot] at h
  simpa only [eventSign, eventPairing, eventRow, eventColumn, ← hc.2.2.1, ← hd.2.2.1] using h


theorem ordered_pairwise_cap
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (hlocalCaps : ∀ t, t ∈ criticalTimes q n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b))
    (c d : EventIndex q n) (hcd : c < d) :
    (eventSign q n c + eventSign q n d) * eventPairing q n c d +
      2 * ∑ e ∈ Finset.univ.filter (fun e => c < e ∧ e < d),
        eventSign q n e * eventPairing q n c e * eventPairing q n e d = 0 := by
  have h := ordered_pairwise_contribution hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps c d hcd
  rw [ordered_actual_sandwich_reindex q n hroots c d] at h
  exact h


theorem actual_cap_matrix_identity
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (hlocalCaps : ∀ t, t ∈ criticalTimes q n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b))
    : eventSignMatrix q n * eventMatrix q n + eventMatrix q n * eventSignMatrix q n +
      (eventMatrix q n * eventSignMatrix q n * eventMatrix q n +
       eventMatrix q n * eventSignMatrix q n * eventMatrix q n) = 0 := by
  have hentry : ∀ c d : EventIndex q n, c.val < d.val →
      (eventSign q n c + eventSign q n d) * eventPairing q n c d +
        2 * ∑ e ∈ Finset.univ.filter (fun e : EventIndex q n => c.val < e.val ∧ e.val < d.val),
          eventSign q n e * eventPairing q n c e * eventPairing q n e d = 0 := by
    intro c d hcd
    exact ordered_pairwise_cap hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps c d hcd
  exact capMatrixRelationOfUpperEntries (eventSign q n) (eventPairing q n) hentry


theorem actual_cap_finiteInverse_identity
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (hlocalCaps : ∀ t, t ∈ criticalTimes q n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b))
    : finiteInverse (eventMatrix q n) (actualTimes q n).card * eventSignMatrix q n +
      eventSignMatrix q n * finiteInverse (eventMatrix q n) (actualTimes q n).card =
      eventSignMatrix q n + eventSignMatrix q n := by
  obtain ⟨hl, hr⟩ := strictUpper_finiteInverse (eventMatrix q n) (eventMatrix_strictUpper q n)
  exact cap_inverse_identity (eventMatrix q n) (eventSignMatrix q n)
    (finiteInverse (eventMatrix q n) (actualTimes q n).card)
    (actual_cap_matrix_identity hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps) hl hr


theorem actual_equal_sign_inverse_zero
    (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2 = 0)
    (hoff : ∀ a, 0 < a → a ≤ n → (q a).2 ≠ 0)
    (hdistinct : ∀ a b, 0 < a → a ≤ n → 0 < b → b ≤ n → a ≠ b → q a ≠ q b)
    (hpositive : ∀ i a b, 0 < i → i < a → a < b → b ≤ n → polygonHDet q i a b ≠ 0)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (hlocalCaps : ∀ t, t ∈ criticalTimes q n →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin n, a.val < b.val →
          CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b))
    (c d : EventIndex q n) (hne : c ≠ d) (hs : eventSign q n c = eventSign q n d) :
    finiteInverse (eventMatrix q n) (actualTimes q n).card c d = 0 := by
  have h := actual_cap_finiteInverse_identity hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps
  have he := congrFun (congrFun h c) d
  simp only [eventSignMatrix, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.diagonal_apply_ne _ hne, add_zero] at he
  rw [hs, eventSign_eq_directionValue q n d] at he
  cases hdir : eventDirection q n d <;> simp only [hdir, Sign.value] at he <;> linarith







end DirectGLSSW.ConcreteCapMatrix
