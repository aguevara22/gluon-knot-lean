import DirectGLSSW.ShortEdgeGenericityRadius
import DirectGLSSW.ShortEdgeZeroGeometry
import DirectGLSSW.ShortEdgeGenericInsertion
import DirectGLSSW.ShortEdgeCyclicAdapter

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW.ShortEdgeCyclicAdapter

theorem exists_insertCyclicAfter_movingCore_G2_radius
    {n : ℕ} (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ x : Fin n, Continuous (fun τ : ℝ => Q τ x))
    (h0 : CyclicGeneric (Q 0)) (a : Fin n) (v : PlanarPoint ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      cyclicNoncollinear (insertCyclicAfter (Q ε) a ε v) →
      cyclicNoTripleIntersections (insertCyclicAfter (Q ε) a ε v)
  := by
  let parent : ℝ → Fin (n + 1) → PlanarPoint ℝ :=
    fun ε => insertCyclicAfter (Q ε) a ε v
  have hparent : ∀ i : Fin (n + 1), Continuous (fun ε : ℝ => parent ε i) := by
    intro i
    by_cases hle : i.val ≤ a.val
    · have hi : i.val < n := by have := a.isLt; omega
      simpa [parent, insertCyclicAfter, hle] using hQ ⟨i.val, hi⟩
    · by_cases hmid : i.val = a.val + 1
      · simp only [parent, insertCyclicAfter, dif_neg hle, dif_pos hmid]
        have hfst : Continuous (fun ε : ℝ => (Q ε a).1) :=
          continuous_fst.comp (hQ a)
        have hsnd : Continuous (fun ε : ℝ => (Q ε a).2) :=
          continuous_snd.comp (hQ a)
        exact (hfst.add (continuous_id.mul continuous_const)).prodMk
          (hsnd.add (continuous_id.mul continuous_const))
      · have hi : i.val - 1 < n := by have := i.isLt; have := a.isLt; omega
        simpa [parent, insertCyclicAfter, hle, hmid] using hQ ⟨i.val - 1, hi⟩
  have hzero : ∀ e f g : Fin (n + 1), SeparatedTriple e f g →
      ¬ ∃ x : PlanarPoint ℝ,
        edgeClosed (parent 0) e x ∧ edgeClosed (parent 0) f x ∧
          edgeClosed (parent 0) g x := by
    intro e f g hsep
    simpa [parent] using
      insert_zero_no_three_separated (Q 0) h0 a v e f g hsep
  have hn : 3 ≤ n + 1 := by have := h0.size_ge_three; omega
  obtain ⟨δ, hδ, hsmall⟩ := exists_cyclicG2_radius hn parent hparent hzero
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ hG1
  exact hsmall ε hε hεδ hG1

end DirectGLSSW.ShortEdgeGenericity
