import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.ShortEdgeSignRealization
import DirectGLSSW.ShortEdgeAttachmentFactor
import DirectGLSSW.NearData

namespace DirectGLSSW.ShortEdgeSignStability

/-- The source short-edge stability package with only the hypotheses used by
its proof: core genericity, an admissible insertion direction, and `a ≤ N`.
The bounds making `a` an interior index are not needed for far signs or for
the packaged near-edge identities. -/
theorem source_exists_shortEdge_sign_stability
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (haN : a ≤ N)
    (hcore : CoreHGeneric q N) (hdir : DirectionGeneric q N a v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ShortEdgeStability q N a v ε haN hcore hdir := by
  obtain ⟨δ, hδ, hfarData⟩ := exists_uniform_far_sign_radius q N a v haN hcore
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hfarData := hfarData ε hε hεδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k j hik hkj hj
    by_cases hfar : ShortEdgeCutFibers.avoidsInsertedPair a i k j
    · exact (hfarData i k j ⟨hik, hkj, hj, hfar⟩).1
    · have hboth :
          (i = a ∨ k = a ∨ j = a) ∧ (i = a + 1 ∨ k = a + 1 ∨ j = a + 1) := by
        apply not_not.mp
        simpa [ShortEdgeCutFibers.avoidsInsertedPair,
          ShortEdgeCutFibers.containsIndex] using hfar
      rcases hboth with ⟨hA, hB⟩
      have hpair :
          (i < a ∧ k = a ∧ j = a + 1) ∨
          (i = a ∧ k = a + 1 ∧ a + 1 < j) := by
        rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
          simp_all <;> omega
      rcases hpair with ⟨hleft, hk, hj'⟩ | ⟨hi', hk', hright⟩
      · subst k; subst j
        rw [polygonHDet_insertedPair_left q a ε v i hleft]
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (ne_of_gt hε)
        · exact hdir i (by omega) (by omega)
      · subst i; subst k
        have hidx : j = (j - 1) + 1 := by omega
        rw [hidx, polygonHDet_insertedPair_right q a ε v (j - 1) (by omega)]
        have hy : j - 1 ≤ N := by omega
        apply mul_ne_zero
        · exact neg_ne_zero.mpr (ne_of_gt hε)
        · exact hdir (j - 1) hy (by omega)
  · intro i k j hik hkj hj hfar
    have hData := hfarData i k j ⟨hik, hkj, hj, hfar⟩
    have ho := collapseAfter_triple_order_bounded a i k j N haN hik hkj hj hfar
    have hCore := hcore _ _ _ ho.1 ho.2.1 ho.2.2
    have hNew : polygonHDet (insertAfter q a ε v) i k j ≠ 0 := hData.1
    by_cases hneg : polygonHDet q (ShortEdgeCutFibers.collapseAfter a i)
        (ShortEdgeCutFibers.collapseAfter a k) (ShortEdgeCutFibers.collapseAfter a j) < 0
    · have hnewneg := hData.2.mpr hneg
      simp [polygonHSign, nonzeroScalarSign, hneg, hnewneg]
    · have hcorepos : 0 < polygonHDet q (ShortEdgeCutFibers.collapseAfter a i)
          (ShortEdgeCutFibers.collapseAfter a k) (ShortEdgeCutFibers.collapseAfter a j) :=
        lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hCore)
      have hnot : ¬ polygonHDet (insertAfter q a ε v) i k j < 0 :=
        mt hData.2.mp hneg
      have hnewpos : 0 < polygonHDet (insertAfter q a ε v) i k j :=
        lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hNew)
      simp [polygonHSign, nonzeroScalarSign, hneg, hnewpos.not_lt]
  · exact polygonHDet_insertedPair_left q a ε v
  · exact fun y hy hyN => polygonHDet_insertedPair_right q a ε v y hy

/-- One uniform short-edge radius gives the far-sign theorem, the actual
inserted sign-array realization, and the literal near-array choices. The
geometric sign array `H1` remains distinct from the gauge data `D0`/`D1`;
near-data independence is stated separately in the final field. -/
theorem source_shortEdge_far_sign_stability
    (q : ℕ → PlanarPoint ℝ) (N a : ℕ) (v : PlanarPoint ℝ)
    (haN : a ≤ N)
    (hcore : CoreHGeneric q N) (hdir : DirectionGeneric q N a v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ShortEdgeStability q N a v ε haN hcore hdir ∧
      (∀ i k j, i < k → k < j → j ≤ N + 1 →
        ShortEdgeWeighted.H1 a
          (ShortEdgeSignRealization.shortSign q a v)
          (ShortEdgeSignRealization.coreHSign q) i k j =
        polygonSignArray (insertAfter q a ε v) i k j) ∧
      (∀ i j, ShortEdgeWeighted.D0 a
          (ShortEdgeSignRealization.shortSign q a v)
          (ShortEdgeWeighted.H0 (ShortEdgeSignRealization.coreHSign q)) i a j =
        (ShortEdgeSignRealization.shortSign q a v i).value) ∧
      (∀ x, x < a → ShortEdgeWeighted.D1 a
          (ShortEdgeSignRealization.shortSign q a v)
          (ShortEdgeWeighted.H0 (ShortEdgeSignRealization.coreHSign q)) x a (a + 1) =
        (ShortEdgeSignRealization.shortSign q a v x).value) ∧
      (∀ y, a < y → ShortEdgeWeighted.D1 a
          (ShortEdgeSignRealization.shortSign q a v)
          (ShortEdgeWeighted.H0 (ShortEdgeSignRealization.coreHSign q)) a (a + 1) (y + 1) =
        (ShortEdgeSignRealization.shortSign q a v y).value) ∧
      (∀ x, x ≤ N → x ≠ a →
        (ShortEdgeSignRealization.shortSign q a v x).value =
          scalarSignValue (-ε * planarDet v (q x - q a))) ∧
      (∀ x, planarDet (q a - insertAfter q a ε v (a + 1))
          (q x - insertAfter q a ε v (a + 1)) =
        -ε * planarDet v (q x - q a)) ∧
      (∀ D₁ D₂ H i j, i < j →
        markedAmplitude D₁ H i j = markedAmplitude D₂ H i j) := by
  obtain ⟨δ, hδ, hstable⟩ := source_exists_shortEdge_sign_stability
    q N a v haN hcore hdir
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hst := hstable ε hε hεδ
  refine ⟨hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k j hik hkj hj
    exact ShortEdgeSignRealization.H1_eq_inserted_polygonSignArray
      q N a v ε hε haN hcore hdir hst i k j hik hkj hj
  · intro i j
    simp [ShortEdgeWeighted.D0]
  · intro x hxa
    simp [ShortEdgeWeighted.D1, ShortEdgeCutFibers.collapseAfter, hxa.le]
  · intro y hay
    have hy : ¬ y + 1 ≤ a := by omega
    simp [ShortEdgeWeighted.D1, ShortEdgeCutFibers.collapseAfter, hy]
  · intro x hx hxa
    exact ShortEdgeSignRealization.shortSign_value_eq_scaled_det
      q N a v ε hε hdir x hx hxa
  · intro x
    exact ShortEdgeGenericity.inserted_short_det q a x ε v
  · exact fun D₁ D₂ H i j hij => markedAmplitude_near_independent D₁ D₂ H hij

end DirectGLSSW.ShortEdgeSignStability
