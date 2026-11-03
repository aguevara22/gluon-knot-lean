import UncutDaughterTurns

set_option autoImplicit false
namespace DirectGLSSW.PolygonUniformity
noncomputable section

/-- The signed turn at vertex e: incoming edge followed by outgoing edge. -/
def turnDet {n : ℕ} (P : Fin n → PlanarPoint ℝ) (e : Fin n) : ℝ :=
  planarDet (cyclicTangent P ((cyclicSuccessorPerm n).symm e)) (cyclicTangent P e)

/-- Source uniformity: every turn is left, or every turn is right. -/
def PolygonUniform {n : ℕ} (P : Fin n → PlanarPoint ℝ) : Prop :=
  (∀ e, 0 < turnDet P e) ∨ (∀ e, turnDet P e < 0)

theorem turnDet_ne_zero {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (e : Fin n) : turnDet P e ≠ 0 := by
  have hs : cyclicSuccessor ((cyclicSuccessorPerm n).symm e) = e :=
    Equiv.apply_symm_apply (cyclicSuccessorPerm n) e
  simpa only [hs,turnDet] using
    cyclic_turn_det_ne_zero hP.size_ge_three P hP.g1 ((cyclicSuccessorPerm n).symm e)

theorem turnDet_successor {n : ℕ} (P : Fin n → PlanarPoint ℝ) (e : Fin n) :
    turnDet P (cyclicSuccessor e) = planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) := by
  unfold turnDet
  have hs : (cyclicSuccessorPerm n).symm (cyclicSuccessor e) = e :=
    Equiv.symm_apply_apply (cyclicSuccessorPerm n) e
  rw [hs]

theorem turnDet_penultimate {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (e : Fin n) :
    turnDet P e = planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) := by
  have hs : (cyclicSuccessorPerm n).symm e = cyclicVertexIndex e (n-2) := by
    apply (cyclicSuccessorPerm n).injective
    exact (Equiv.apply_symm_apply (cyclicSuccessorPerm n) e).trans
      (NormalizedEdgeTurns.penultimate_precedes_edge hn e).symm
  rw [turnDet,hs]

theorem all_of_successor_closed {n : ℕ} (R : Fin n → Prop)
    (hstep : ∀ e, R e → R (cyclicSuccessor e)) (z : Fin n) (hz : R z) : ∀ e, R e := by
  have hi : ∀ k : ℕ, R ((cyclicSuccessorPerm n ^ k) z) := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,cyclicSuccessorPerm_apply]
      exact hstep _ ih
  intro e
  obtain ⟨k,hk⟩ := (cyclicSuccessorPerm_oneTraversal z).surjective e
  rw [← hk]
  exact hi _

theorem exists_opposite_adjacent_turns_of_not_uniform {n : ℕ}
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P) (hnu : ¬ PolygonUniform P) :
    ∃ e, turnDet P (cyclicSuccessor e) * turnDet P e < 0 := by
  classical
  by_contra hno
  push_neg at hno
  have hpos : ∀ e, 0 < turnDet P e → 0 < turnDet P (cyclicSuccessor e) := by
    intro e he
    rcases lt_or_gt_of_ne (turnDet_ne_zero P hP (cyclicSuccessor e)) with h | h
    · exact False.elim ((not_lt_of_ge (hno e)) (mul_neg_of_neg_of_pos h he))
    · exact h
  have hneg : ∀ e, turnDet P e < 0 → turnDet P (cyclicSuccessor e) < 0 := by
    intro e he
    rcases lt_or_gt_of_ne (turnDet_ne_zero P hP (cyclicSuccessor e)) with h | h
    · exact h
    · exact False.elim ((not_lt_of_ge (hno e)) (mul_neg_of_pos_of_neg h he))
  let z : Fin n := ⟨0,by have := hP.size_ge_three; omega⟩
  apply hnu
  rcases lt_or_gt_of_ne (turnDet_ne_zero P hP z) with hz | hz
  · exact Or.inr (all_of_successor_closed _ hneg z hz)
  · exact Or.inl (all_of_successor_closed _ hpos z hz)

theorem exists_opposite_edge_of_not_uniform {n : ℕ}
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P) (hnu : ¬ PolygonUniform P) :
    ∃ e, planarDet (cyclicTangent P e) (cyclicTangent P (cyclicSuccessor e)) *
      planarDet (cyclicTangent P (cyclicVertexIndex e (n-2))) (cyclicTangent P e) < 0 := by
  obtain ⟨e,he⟩ := exists_opposite_adjacent_turns_of_not_uniform P hP hnu
  rw [turnDet_successor,turnDet_penultimate hP.size_ge_three] at he
  exact ⟨e,he⟩









end
end DirectGLSSW.PolygonUniformity
