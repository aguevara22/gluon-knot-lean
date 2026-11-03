import SourceCyclicShortEdgeCurrentTable
import DirectGLSSW.ShortEdgeInsertionFull
import DirectGLSSW.ShortEdgeInteriorInsertion

namespace DirectGLSSW.ShortEdgeCurrentGeometry

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeInsertionRotation
open DirectGLSSW.ShortEdgeSignRealization
open DirectGLSSW.ShortEdgeSignStability
open DirectGLSSW.ShortEdgeGenericity
open DirectGLSSW.ShortEdgeWeighted

/-- The source attachment multiplier in the literal cyclic rooting that puts
A at index 1 and its predecessor at index 0. -/
noncomputable def sourceCyclicShortEdgeKappa {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (v : PlanarPoint ℝ) : ℚ :=
  kappa 1 (by have hn := hq.size_ge_three; omega)
    (shortSign (sourceCoreWordBefore hq.size_ge_three q a) 1 v)

/-- The opened-word κ is the half-sum of the two actual attachment-turn signs
at the predecessor and successor of A. -/
theorem sourceCyclicShortEdgeKappa_eq_attachmentFactor {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (a P : Fin n)
    (hP : cyclicSuccessor P = a) (v : PlanarPoint ℝ)
    (havoid : ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    sourceCyclicShortEdgeKappa q hq a v =
      attachmentFactor (q a)
        (insertCyclicAfter q a ε v ⟨a.val + 1, by have := a.isLt; omega⟩)
        (q P) (q (cyclicSuccessor a)) := by
  classical
  have hn : 3 ≤ n := hq.size_ge_three
  let r : Fin n := coreRootBefore hn a
  let ρC : Fin n ≃ Fin n := cyclicVertexEquiv r
  let ρP : Fin (n + 1) ≃ Fin (n + 1) := cyclicVertexEquiv (parentRootBefore hn a)
  let qR : Fin n → PlanarPoint ℝ := q ∘ ρC
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let two : Fin n := ⟨2, by omega⟩
  let twoP : Fin (n + 1) := ⟨2, by omega⟩
  have hρC : ∀ e, ρC (cyclicSuccessor e) = cyclicSuccessor (ρC e) :=
    cyclicVertexEquiv_commutes_successor r
  have hρA : ρC one = a := by
    change cyclicVertexIndex r 1 = a
    exact coreRootBefore_index1 hn a
  have hsucc0 : cyclicSuccessor zero = one := by
    apply Fin.ext
    change (0 + 1 + 0) % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hsucc1 : cyclicSuccessor one = two := by
    apply Fin.ext
    change (1 + 1 + 0) % n = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hρP : ρP twoP = ⟨a.val + 1, by omega⟩ := by
    change cyclicVertexIndex (parentRootBefore hn a) 2 = _
    exact parentRootBefore_index2 hn a
  have hindexP : ρC zero = P := by
    apply (cyclicSuccessor_bijective (n := n)).injective
    rw [← hρC, hsucc0, hρA, hP]
  have hindexC : ρC two = cyclicSuccessor a := by
    calc
      ρC two = ρC (cyclicSuccessor one) := by rw [hsucc1]
      _ = cyclicSuccessor (ρC one) := hρC one
      _ = cyclicSuccessor a := by rw [hρA]
  have hA : qR one = q a := congrArg q hρA
  have hPrev : qR zero = q P := congrArg q hindexP
  have hNext : qR two = q (cyclicSuccessor a) := congrArg q hindexC
  have hB : insertCyclicAfter qR one ε v twoP =
      insertCyclicAfter q a ε v ⟨a.val + 1, by have := a.isLt; omega⟩ := by
    have h := insertCyclicAfter_rotated hn q a ε v twoP
    rw [hρP] at h
    exact h.symm
  have havoidR : ∀ x : Fin n, x ≠ one → planarDet v (qR x - qR one) ≠ 0 := by
    intro x hx
    change planarDet v (q (ρC x) - q (ρC one)) ≠ 0
    rw [hρA]
    apply havoid
    intro hxa
    exact hx (ρC.injective (hxa.trans hρA.symm))
  have hdirRoot :=
    ShortEdgeDirectionExistence.directionGeneric_lastRoot_of_pointwise_avoidance
      (by omega : 0 < n) qR one v havoidR
  have hdirR : DirectionGeneric
      (ShortEdgePolygonAmplitude.coreWord qR (by omega)) (n - 1) 1 v := by
    simpa [ShortEdgePolygonAmplitude.coreWord] using hdirRoot
  have hword : sourceCoreWordBefore hn q a =
      ShortEdgePolygonAmplitude.coreWord qR (by omega) := by
    funext k
    exact sourceCoreWordBefore_eq_lastRoot_relabel hn q a k
  have hκ : sourceCyclicShortEdgeKappa q hq a v =
      kappa 1 (by omega)
        (shortSign (ShortEdgePolygonAmplitude.coreWord qR (by omega)) 1 v) := by
    unfold sourceCyclicShortEdgeKappa
    rw [hword]
  have hone : 0 < 1 := by omega
  have honeN : 1 < n - 1 := by omega
  have hk := ShortEdgePolygonAmplitude.kappa_eq_cyclicAttachmentFactor
    qR one v ε hε hone honeN hdirR
  have hk' : kappa 1 (by omega)
        (shortSign (ShortEdgePolygonAmplitude.coreWord qR (by omega)) 1 v) =
      attachmentFactor (qR one) (insertCyclicAfter qR one ε v twoP)
        (qR zero) (qR two) := by
    simpa [zero, one, two, twoP] using hk
  rw [← hκ, hA, hB, hPrev, hNext] at hk'
  exact hk'

/-- Explicit determinant form of the source's t(P), t(C) half-sum. -/
theorem sourceCyclicShortEdgeKappa_eq_det_half_sum {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (a P : Fin n)
    (hP : cyclicSuccessor P = a) (v : PlanarPoint ℝ)
    (havoid : ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    sourceCyclicShortEdgeKappa q hq a v =
      (scalarSignValue
          (planarDet (q a - insertCyclicAfter q a ε v
            ⟨a.val + 1, by have := a.isLt; omega⟩)
            (q P - insertCyclicAfter q a ε v
              ⟨a.val + 1, by have := a.isLt; omega⟩)) +
        scalarSignValue
          (planarDet (q a - insertCyclicAfter q a ε v
            ⟨a.val + 1, by have := a.isLt; omega⟩)
            (q (cyclicSuccessor a) - insertCyclicAfter q a ε v
              ⟨a.val + 1, by have := a.isLt; omega⟩))) / 2 := by
  rw [sourceCyclicShortEdgeKappa_eq_attachmentFactor q hq a P hP v havoid ε hε]
  rfl

/-- The actual generic cyclic short-edge insertion obeys the source
amplitude-duplication identity for every sufficiently small positive length.
The multiplier is the literal rooted source short sign at the designated
vertex; root rotation imposes no restriction on its original cyclic label. -/
theorem source_exists_shortEdge_actual_amplitude_duplication
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (v : PlanarPoint ℝ)
    (havoid : ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hp : CyclicGeneric (insertCyclicAfter q a ε v),
        polygonAmplitude (insertCyclicAfter q a ε v) hp =
          sourceCyclicShortEdgeKappa q hq a v * polygonAmplitude q hq := by
  classical
  have hn : 3 ≤ n := hq.size_ge_three
  obtain ⟨P, hP⟩ := (cyclicSuccessor_bijective (n := n)).2 a
  obtain ⟨δ, hδ, hgood⟩ := ShortEdgeGenericity.exists_shortEdge_insertion
    hRI q hq a v havoid P hP
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hp, hformula⟩ := hgood ε hε hεδ
  have hfactor := sourceCyclicShortEdgeKappa_eq_attachmentFactor
    q hq a P hP v havoid ε hε
  rw [← hfactor] at hformula
  exact ⟨hp, hformula⟩

end DirectGLSSW.ShortEdgeCurrentGeometry
