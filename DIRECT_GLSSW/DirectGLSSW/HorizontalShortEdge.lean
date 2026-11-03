import DirectGLSSW.ShortEdgeInsertionFull

namespace DirectGLSSW.HorizontalShortEdge

open DirectGLSSW.ShortEdgeCyclicAdapter DirectGLSSW.ShortEdgeGenericity

theorem scalarSignValue_positive_mul (epsilon x : ℝ) (hepsilon : 0 < epsilon) :
    scalarSignValue (epsilon * x) = scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hm : epsilon * x < 0 := mul_neg_of_pos_of_neg hepsilon hx
    simp [scalarSignValue, ne_of_lt hx, ne_of_lt hm, hx, hm]
  · subst x
    simp [scalarSignValue]
  · have hm : 0 < epsilon * x := mul_pos hepsilon hx
    simp [scalarSignValue, ne_of_gt hx, ne_of_gt hm, not_lt_of_ge hx.le,
      not_lt_of_ge hm.le]

theorem horizontal_attachmentFactor (A P C : PlanarPoint ℝ) (hA : A.2 = 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    attachmentFactor A (A.1 - epsilon, 0) P C =
      (scalarSignValue P.2 + scalarSignValue C.2) / 2 := by
  have hdet (X : PlanarPoint ℝ) :
      planarDet (A - (A.1 - epsilon, 0)) (X - (A.1 - epsilon, 0)) =
        epsilon * X.2 := by
    simp [planarDet, hA]
  unfold attachmentFactor
  rw [hdet P, hdet C, scalarSignValue_positive_mul epsilon P.2 hepsilon,
    scalarSignValue_positive_mul epsilon C.2 hepsilon]

theorem exists_horizontal_shortEdge_insertion (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (ha : (q a).2 = 0)
    (hothers : ∀ x : Fin n, x ≠ a → (q x).2 ≠ 0)
    (P : Fin n) (hP : cyclicSuccessor P = a) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < delta →
      ∃ hp : CyclicGeneric (insertCyclicAfter q a epsilon (-1, 0)),
        polygonAmplitude (insertCyclicAfter q a epsilon (-1, 0)) hp =
          ((scalarSignValue (q P).2 + scalarSignValue (q (cyclicSuccessor a)).2) / 2) *
            polygonAmplitude q hq := by
  have havoid : ∀ x : Fin n, x ≠ a →
      planarDet ((-1, 0) : PlanarPoint ℝ) (q x - q a) ≠ 0 := by
    intro x hx
    simpa [planarDet, ha] using neg_ne_zero.mpr (hothers x hx)
  obtain ⟨delta, hdelta, hsmall⟩ :=
    exists_shortEdge_insertion hRI q hq a (-1, 0) havoid P hP
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon hepsilon hlt
  obtain ⟨hp, hvalue⟩ := hsmall epsilon hepsilon hlt
  refine ⟨hp, ?_⟩
  have hnew : insertCyclicAfter q a epsilon (-1, 0) ⟨a.val + 1, by omega⟩ =
      ((q a).1 - epsilon, 0) := by
    simp [insertCyclicAfter, ha, sub_eq_add_neg]
  rw [hnew, horizontal_attachmentFactor (q a) (q P) (q (cyclicSuccessor a))
    ha epsilon hepsilon] at hvalue
  exact hvalue





end DirectGLSSW.HorizontalShortEdge
