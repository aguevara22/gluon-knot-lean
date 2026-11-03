import DirectGLSSW.ShortEdgeContinuity
import DirectGLSSW.ShortEdgeSeparated
import DirectGLSSW.ShortEdgeCyclicGeometry
import DirectGLSSW.ShortEdgeSignStability

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW.ShortEdgeCyclicAdapter

theorem exists_cyclicG2_radius {n : ℕ} (hn : 3 ≤ n)
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ v : Fin n, Continuous (fun ε => Q ε v))
    (hzero : ∀ e f g : Fin n, SeparatedTriple e f g →
      ¬ ∃ x : PlanarPoint ℝ,
        edgeClosed (Q 0) e x ∧ edgeClosed (Q 0) f x ∧ edgeClosed (Q 0) g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      cyclicNoncollinear (Q ε) → cyclicNoTripleIntersections (Q ε) := by
  classical
  let P : (Fin n × Fin n × Fin n) → ℝ → Prop := fun t ε =>
    SeparatedTriple t.1 t.2.1 t.2.2 →
      ¬ ∃ x : PlanarPoint ℝ,
        edgeClosed (Q ε) t.1 x ∧ edgeClosed (Q ε) t.2.1 x ∧
          edgeClosed (Q ε) t.2.2 x
  have hlocal : ∀ t, t ∈ (Finset.univ : Finset (Fin n × Fin n × Fin n)) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → P t ε := by
    intro t _
    by_cases ht : SeparatedTriple t.1 t.2.1 t.2.2
    · obtain ⟨δ, hδ, hgood⟩ := exists_no_three_closed_radius Q t.1 t.2.1 t.2.2 hQ
        (hzero t.1 t.2.1 t.2.2 ht)
      refine ⟨δ, hδ, ?_⟩
      intro ε hε hεδ _
      exact hgood ε (by simpa [abs_of_pos hε] using hεδ)
    · exact ⟨1, by norm_num, fun _ _ _ h => False.elim (ht h)⟩
  obtain ⟨δ, hδ, hgood⟩ :=
    ShortEdgeSignStability.exists_finset_common_radius Finset.univ P hlocal
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ hG1 e f g x hef hfg heg hbad
  rcases hbad with ⟨he, hf, hg⟩
  have hnonadj : ∀ i j : Fin n,
      edgeInterior (Q ε) i x → edgeInterior (Q ε) j x → cyclicSuccessor i ≠ j := by
    intro i j hi hj hij
    subst j
    exact cyclic_adjacent_interiors_disjoint hn (Q ε) hG1 i x hi hj
  have hsep : SeparatedTriple e f g :=
    ⟨hef, hfg, heg, hnonadj e f he hf, hnonadj f e hf he,
      hnonadj f g hf hg, hnonadj g f hg hf, hnonadj e g he hg,
      hnonadj g e hg he⟩
  have hclosed : ∀ i : Fin n, edgeInterior (Q ε) i x → edgeClosed (Q ε) i x := by
    intro i hi
    obtain ⟨t, ht0, ht1, hxt⟩ := hi
    exact ⟨t, le_of_lt ht0, le_of_lt ht1, hxt⟩
  exact hgood ε hε hεδ (e, f, g) (Finset.mem_univ _) hsep
    ⟨x, hclosed e he, hclosed f hf, hclosed g hg⟩

theorem continuous_insertCyclicAfter {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a : Fin n) (v : PlanarPoint ℝ)
    (i : Fin (n + 1)) : Continuous (fun ε : ℝ => insertCyclicAfter q a ε v i) := by
  by_cases hle : i.val ≤ a.val
  · simpa [insertCyclicAfter, hle] using
      (continuous_const : Continuous (fun _ : ℝ => q ⟨i.val, lt_of_le_of_lt hle a.isLt⟩))
  · by_cases hmid : i.val = a.val + 1
    · simp only [insertCyclicAfter, dif_neg hle, dif_pos hmid]
      exact (continuous_const.add (continuous_id.mul continuous_const)).prodMk
        (continuous_const.add (continuous_id.mul continuous_const))
    · simpa [insertCyclicAfter, hle, hmid] using
        (continuous_const : Continuous (fun _ : ℝ =>
          q ⟨i.val - 1, by have := i.isLt; have := a.isLt; omega⟩))

end DirectGLSSW.ShortEdgeGenericity
