import DirectGLSSW.MovingCoreInteriorInsertion
import DirectGLSSW.ShortEdgeInsertionRotation
import DirectGLSSW.ShortEdgeDirectionExistence

open DirectGLSSW.ShortEdgeInsertionRotation

namespace DirectGLSSW.ShortEdgeGenericity
open DirectGLSSW.ShortEdgeCyclicAdapter

theorem exists_movingCore_shortEdge_insertion
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ x : Fin n, Continuous (fun ε : ℝ => Q ε x))
    (h0 : CyclicGeneric (Q 0)) (a : Fin n) (v : PlanarPoint ℝ)
    (havoid0 : ∀ x : Fin n, x ≠ a → planarDet v (Q 0 x - Q 0 a) ≠ 0)
    (P : Fin n) (hP : cyclicSuccessor P = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hp : CyclicGeneric (insertCyclicAfter (Q ε) a ε v),
        polygonAmplitude (insertCyclicAfter (Q ε) a ε v) hp =
          attachmentFactor (Q ε a)
            (insertCyclicAfter (Q ε) a ε v ⟨a.val + 1, by omega⟩)
            (Q ε P) (Q ε (cyclicSuccessor a)) * polygonAmplitude (Q 0) h0
  := by
  classical
  have hn := h0.size_ge_three
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let two : Fin n := ⟨2, by omega⟩
  let ρC := cyclicVertexEquiv (coreRootBefore hn a)
  let ρP := cyclicVertexEquiv (parentRootBefore hn a)
  let qR : ℝ → Fin n → PlanarPoint ℝ := fun ε => Q ε ∘ ρC
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
  have hA : ∀ ε : ℝ, qR ε one = Q ε a := by
    intro ε
    exact congrArg (Q ε) hindexA
  have hPrev : ∀ ε : ℝ, qR ε zero = Q ε P := by
    intro ε
    exact congrArg (Q ε) hindexP
  have hNext : ∀ ε : ℝ, qR ε two = Q ε (cyclicSuccessor a) := by
    intro ε
    exact congrArg (Q ε) hindexC
  have hqR : CyclicGeneric (qR 0) := by
    dsimp [qR]
    exact cyclicGeneric_relabel (Q 0) ρC hρC h0
  have hQ_R : ∀ x : Fin n, Continuous (fun ε : ℝ => qR ε x) := by
    intro x
    simpa [qR, Function.comp_apply] using hQ (ρC x)
  have havoidR : ∀ x : Fin n, x ≠ one →
      planarDet v (qR 0 x - qR 0 one) ≠ 0 := by
    intro x hx
    change planarDet v (Q 0 (ρC x) - Q 0 (ρC one)) ≠ 0
    rw [hindexA]
    apply havoid0
    intro heq
    exact hx (ρC.injective (heq.trans hindexA.symm))
  have hdirR := ShortEdgeDirectionExistence.directionGeneric_lastRoot_of_pointwise_avoidance
    (by omega : 0 < n) (qR 0) one v havoidR
  obtain ⟨δ, hδ, hgood⟩ :=
    DirectGLSSW.ShortEdgePolygonAmplitude.exists_movingCore_interior_polygonAmplitude_insert_eq
      hRI qR hQ_R hqR one v (by simp [one]) (by simp [one]; omega) havoidR
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hpR, hAmpR⟩ := hgood ε hε hεδ
  let parent : Fin (n + 1) → PlanarPoint ℝ := insertCyclicAfter (Q ε) a ε v
  let parentR : Fin (n + 1) → PlanarPoint ℝ := insertCyclicAfter (qR ε) one ε v
  have hInsert : parent ∘ ρP = parentR := by
    funext i
    exact insertCyclicAfter_rotated hn (Q ε) a ε v i
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
  have hcoreAmp : polygonAmplitude (qR 0) hqR = polygonAmplitude (Q 0) h0 := by
    dsimp [qR]
    exact polygonAmplitude_relabel hRI h0 ρC hρC
  have hindexB : ρP (⟨2, by omega⟩ : Fin (n + 1)) =
      ⟨a.val + 1, by omega⟩ := parentRootBefore_index2 hn a
  have hB : parentR ⟨2, by omega⟩ = parent ⟨a.val + 1, by omega⟩ := by
    have h := congrFun hInsert (⟨2, by omega⟩ : Fin (n + 1))
    simpa only [Function.comp_apply, hindexB] using h.symm
  have hformula : polygonAmplitude parentR hpR =
      attachmentFactor (qR ε one) (parentR ⟨2, by omega⟩)
        (qR ε zero) (qR ε two) * polygonAmplitude (qR 0) hqR := by
    simpa only [one, zero, two] using hAmpR
  rw [hparentAmp, hcoreAmp, hA ε, hPrev ε, hNext ε, hB] at hformula
  exact ⟨hp, hformula⟩

end DirectGLSSW.ShortEdgeGenericity
