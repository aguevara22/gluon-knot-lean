import DirectGLSSW.ConcreteCapMatrix
import DirectGLSSW.CapEventInterpretation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceCapMatrix
open DirectGLSSW OrderedCapEvents CapCriticalTimes CapCriticalEventGeometry
open ConcreteCapMatrix CapEventInterpretation GlobalCapEntry CapCrossingEvent

/-- The source isolated-event condition makes the event pair selected at its
actual horizontal coordinate unique; no choice-tie remains in `eventPair`. -/
theorem eventPair_unique_at_time
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hroots : Set.InjOn (criticalRoot q) ↑(criticalPairs q n))
    (c : EventIndex q n) (p : ℕ × ℕ)
    (hp : p ∈ actualPairs q n)
    (ht : criticalRoot q p = eventTime q n c) :
    eventPair q n c = p := by
  have hpc : eventPair q n c ∈ criticalPairs q n :=
    eventPair_criticalPairs_mem q n c
  have hpp : p ∈ criticalPairs q n := by
    exact (Finset.mem_filter.mp hp).1
  exact hroots hpc hpp ((eventPair_spec q n c).2.trans ht.symm)

/-- The literal ordered line-cap matrix has the source pairwise relation,
exact matrix relation, its finite two-sided inverse, the K relation, and
same-direction off-diagonal cancellation. All event data are read from the
actual line crossing and all local cap genericity is explicit. -/
theorem actual_line_cap_package
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
          CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b)) :
    let X := eventMatrix q n
    let S := eventSignMatrix q n
    let K := finiteInverse X (actualTimes q n).card
    (∀ c d : EventIndex q n, c < d →
      (eventSign q n c + eventSign q n d) * eventPairing q n c d +
        2 * ∑ e ∈ Finset.univ.filter (fun e => c < e ∧ e < d),
          eventSign q n e * eventPairing q n c e * eventPairing q n e d = 0) ∧
    (S * X + X * S + (X * S * X + X * S * X) = 0) ∧
    (K * (1 + X) = 1 ∧ (1 + X) * K = 1) ∧
    (K * S + S * K = S + S) ∧
    (∀ c d : EventIndex q n, c ≠ d → eventSign q n c = eventSign q n d → K c d = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c d hcd
    exact ordered_pairwise_cap hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps c d hcd
  · exact actual_cap_matrix_identity hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps
  · exact strictUpper_finiteInverse (eventMatrix q n) (eventMatrix_strictUpper q n)
  · exact actual_cap_finiteInverse_identity hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps
  · intro c d hne hs
    exact actual_equal_sign_inverse_zero hRI q n hzero hoff hdistinct hpositive hroots hlocalCaps c d hne hs

end DirectGLSSW.SourceCapMatrix


