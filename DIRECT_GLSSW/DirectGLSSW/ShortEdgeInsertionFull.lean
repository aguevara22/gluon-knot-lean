import DirectGLSSW.ShortEdgeInteriorInsertion
import DirectGLSSW.ShortEdgeInsertionRotation
import DirectGLSSW.ShortEdgeDirectionExistence

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeInsertionRotation

theorem exists_shortEdge_insertion (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (v : PlanarPoint ℝ)
    (havoid : ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0)
    (P : Fin n) (hP : cyclicSuccessor P = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hp : CyclicGeneric (insertCyclicAfter q a ε v),
        polygonAmplitude (insertCyclicAfter q a ε v) hp =
          attachmentFactor (q a)
            (insertCyclicAfter q a ε v ⟨a.val + 1, by omega⟩)
            (q P) (q (cyclicSuccessor a)) * polygonAmplitude q hq := by
  classical
  have hn := hq.size_ge_three
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let two : Fin n := ⟨2, by omega⟩
  let ρC := cyclicVertexEquiv (coreRootBefore hn a)
  let ρP := cyclicVertexEquiv (parentRootBefore hn a)
  let qR : Fin n → PlanarPoint ℝ := q ∘ ρC
  have hρC : ∀ e, ρC (cyclicSuccessor e) = cyclicSuccessor (ρC e) :=
    cyclicVertexEquiv_commutes_successor (coreRootBefore hn a)
  have hρP : ∀ e, ρP (cyclicSuccessor e) = cyclicSuccessor (ρP e) :=
    cyclicVertexEquiv_commutes_successor (parentRootBefore hn a)
  have hρPi : ∀ e, ρP.symm (cyclicSuccessor e) = cyclicSuccessor (ρP.symm e) := by
    intro e
    apply ρP.injective
    rw [ρP.apply_symm_apply, hρP, ρP.apply_symm_apply]
  have hindexA : ρC one = a := coreRootBefore_index1 hn a
  have hsucc0 : cyclicSuccessor zero = one := by
    apply Fin.ext
    change (0 + 1 + 0) % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hsucc1 : cyclicSuccessor one = two := by
    apply Fin.ext
    change (1 + 1 + 0) % n = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hindexP : ρC zero = P := by
    apply (cyclicSuccessor_bijective (n := n)).injective
    rw [← hρC, hsucc0, hindexA, hP]
  have hindexC : ρC two = cyclicSuccessor a := by
    rw [← hsucc1, hρC, hindexA]
  have hA : qR one = q a := congrArg q hindexA
  have hPrev : qR zero = q P := congrArg q hindexP
  have hNext : qR two = q (cyclicSuccessor a) := congrArg q hindexC
  have hqR : CyclicGeneric qR := cyclicGeneric_relabel q ρC hρC hq
  have havoidR : ∀ x : Fin n, x ≠ one → planarDet v (qR x - qR one) ≠ 0 := by
    intro x hx
    change planarDet v (q (ρC x) - q (ρC one)) ≠ 0
    rw [hindexA]
    apply havoid
    intro heq
    exact hx (ρC.injective (heq.trans hindexA.symm))
  have hdirR := ShortEdgeDirectionExistence.directionGeneric_lastRoot_of_pointwise_avoidance
    (by omega : 0 < n) qR one v havoidR
  obtain ⟨δ, hδ, hgood⟩ := ShortEdgePolygonAmplitude.exists_polygonAmplitude_insert_eq
    hRI hn qR hqR one v (by simp [one]) (by simp [one]; omega) hdirR
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hpR, hAmpR⟩ := hgood ε hε hεδ
  let parent := insertCyclicAfter q a ε v
  let parentR := insertCyclicAfter qR one ε v
  have hInsert : parent ∘ ρP = parentR := by
    funext i
    exact insertCyclicAfter_rotated hn q a ε v i
  have hpRot : CyclicGeneric (parent ∘ ρP) := by
    rw [hInsert]
    exact hpR
  have hinverse : (parent ∘ ρP) ∘ ρP.symm = parent := by
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have hp : CyclicGeneric parent := by
    have h := cyclicGeneric_relabel (parent ∘ ρP) ρP.symm hρPi hpRot
    rw [hinverse] at h
    exact h
  have hparentAmp : polygonAmplitude parentR hpR = polygonAmplitude parent hp := by
    have h := polygonAmplitude_relabel hRI hp ρP hρP
    simpa only [hInsert] using h
  have hcoreAmp : polygonAmplitude qR hqR = polygonAmplitude q hq :=
    polygonAmplitude_relabel hRI hq ρC hρC
  have hindexB : ρP (⟨2, by omega⟩ : Fin (n + 1)) =
      ⟨a.val + 1, by omega⟩ := parentRootBefore_index2 hn a
  have hB : parentR ⟨2, by omega⟩ = parent ⟨a.val + 1, by omega⟩ := by
    have h := congrFun hInsert (⟨2, by omega⟩ : Fin (n + 1))
    simpa only [Function.comp_apply, hindexB] using h.symm
  have hformula : polygonAmplitude parentR hpR =
      attachmentFactor (qR one) (parentR ⟨2, by omega⟩)
        (qR zero) (qR two) * polygonAmplitude qR hqR := by
    simpa only [one] using hAmpR
  rw [hparentAmp, hcoreAmp, hA, hPrev, hNext, hB] at hformula
  exact ⟨hp, hformula⟩

end DirectGLSSW.ShortEdgeGenericity
