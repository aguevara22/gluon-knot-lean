import DirectGLSSW.HorizontalCapPolygon
import DirectGLSSW.EndpointGenericStability

set_option autoImplicit false

namespace DirectGLSSW.HorizontalShortEdge

theorem horizontalComplementWord_zero_eq_core {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ)
    (hzero : (q ⟨0, by omega⟩).2 = 0)
    (k : ℕ) (hk : k < n + 1) :
    horizontalComplementWord q 0 k = q ⟨k, hk⟩ := by
  by_cases hkzero : k = 0
  · subst k
    apply Prod.ext
    · simp [horizontalComplementWord]
    · simpa [horizontalComplementWord] using hzero.symm
  · simp [horizontalComplementWord, hkzero, hk]

theorem horizontalComplementWord_height {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ) (epsilon : ℝ) (k : ℕ) :
    (horizontalComplementWord q epsilon k).2 = (horizontalComplementWord q 0 k).2 := by
  unfold horizontalComplementWord
  split_ifs <;> rfl

theorem horizontalComplementWord_eq_moveEndpoint {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ) (epsilon : ℝ) :
    horizontalComplementWord q epsilon =
      EndpointEventGeometry.moveEndpoint (horizontalComplementWord q 0) (-1, 0) epsilon := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [horizontalComplementWord, EndpointEventGeometry.moveEndpoint, sub_eq_add_neg]
  · simp [horizontalComplementWord, EndpointEventGeometry.moveEndpoint, hk]

theorem horizontalComplementWord_core_generic {n : ℕ}
    (q : Fin (n + 1) → PlanarPoint ℝ) (hq : cyclicNoncollinear q)
    (hzero : (q ⟨0, by omega⟩).2 = 0) :
    ShortEdgeSignStability.CoreHGeneric (horizontalComplementWord q 0) n := by
  intro i k j hik hkj hjn
  unfold polygonHDet
  rw [horizontalComplementWord_zero_eq_core q hzero i (by omega),
    horizontalComplementWord_zero_eq_core q hzero k (by omega),
    horizontalComplementWord_zero_eq_core q hzero j (by omega)]
  apply hq ⟨i, by omega⟩ ⟨k, by omega⟩ ⟨j, by omega⟩
  · intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_mk] at this
    omega
  · intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_mk] at this
    omega
  · intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_mk] at this
    omega






end DirectGLSSW.HorizontalShortEdge
