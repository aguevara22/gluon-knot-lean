import DirectGLSSW.ShortEdgeGenericInsertion
import DirectGLSSW.ShortEdgeAttachmentFactor
import DirectGLSSW.PolygonAmplitude

namespace DirectGLSSW.ShortEdgePolygonAmplitude

open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeSignStability
open DirectGLSSW.ShortEdgeSignRealization
open DirectGLSSW.ShortEdgeGenericity

theorem kappa_eq_cyclicAttachmentFactor
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a : Fin n) (v : PlanarPoint ℝ) (ε : ℝ)
    (hε : 0 < ε) (ha : 0 < a.val) (haN : a.val < n - 1)
    (hdir : DirectionGeneric (coreWord q (by omega)) (n - 1) a.val v) :
    ShortEdgeWeighted.kappa a.val (by omega)
      (ShortEdgeSignRealization.shortSign (coreWord q (by omega)) a.val v) =
      attachmentFactor (q a)
        (insertCyclicAfter q a ε v ⟨a.val + 1, by omega⟩)
        (q ⟨a.val - 1, by omega⟩) (q ⟨a.val + 1, by omega⟩) := by
  let w : ℕ → PlanarPoint ℝ := coreWord q (by omega)
  have hdir' : DirectionGeneric w (n - 1) a.val v := hdir
  have hk := ShortEdgeGenericity.kappa_eq_attachmentFactor w (n - 1) a.val v ε hε ha
    haN hdir'
  have hwa : w a.val = q a := by
    exact coreLastRootWord_eval (by have := a.isLt; omega) q a.val a.isLt
  have hwp : w (a.val - 1) = q ⟨a.val - 1, by omega⟩ := by
    exact coreLastRootWord_eval (by have := a.isLt; omega) q (a.val - 1) (by omega)
  have hws : w (a.val + 1) = q ⟨a.val + 1, by omega⟩ := by
    exact coreLastRootWord_eval (by have := a.isLt; omega) q (a.val + 1) (by omega)
  have hnew : ShortEdgeSignStability.insertAfter w a.val ε v (a.val + 1) =
      insertCyclicAfter q a ε v ⟨a.val + 1, by omega⟩ := by
    simp [ShortEdgeSignStability.insertAfter, insertCyclicAfter, hwa]
  simpa [w, hwa, hwp, hws, hnew] using hk

theorem exists_polygonAmplitude_insert_eq
    (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (a : Fin n) (v : PlanarPoint ℝ)
    (ha : 0 < a.val) (haN : a.val < n - 1)
    (hdir : DirectionGeneric (coreWord q (by omega)) (n - 1) a.val v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hp : CyclicGeneric (insertCyclicAfter q a ε v),
        polygonAmplitude (insertCyclicAfter q a ε v) hp =
          attachmentFactor (q a)
            (insertCyclicAfter q a ε v ⟨a.val + 1, by omega⟩)
            (q ⟨a.val - 1, by omega⟩) (q ⟨a.val + 1, by omega⟩) *
          polygonAmplitude q hq := by
  let hc := coreHGeneric_of_cyclicNoncollinear hn q hq.g1
  have hdirRoot : DirectionGeneric
      (fun k => rootedPolygonWord q (lastCoreRoot (by omega : 0 < n)) k)
      (n - 1) a.val v := by
    simpa [coreWord] using hdir
  obtain ⟨δ, hδ, hsmall⟩ :=
    DirectGLSSW.ShortEdgeGenericity.exists_insertCyclicAfter_generic_and_sign_stability
      q hq a v ha haN hdirRoot
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hp, hstRoot⟩ := hsmall ε hε hεδ
  have hst : ShortEdgeStability (coreWord q (by omega)) (n - 1) a.val v ε
      (by omega) hc hdir := by
    simpa [coreWord, hc] using hstRoot
  have hparentG2 : cyclicNoTripleIntersections (insertCyclicAfter q a ε v) := hp.g2
  have hpoly := polygonAmplitude_insert_eq hRI hn q hq a ε v hε hc hdir hst
    ha haN hparentG2
  let hpCanonical : CyclicGeneric (insertCyclicAfter q a ε v) :=
    ⟨by have := hq.size_ge_three; omega,
      ShortEdgeCyclicG1.inserted_cyclicNoncollinear_of_openStability
        hn q a ε v hc hdir hst,
      hparentG2⟩
  have hproof : hpCanonical = hp := Subsingleton.elim _ _
  change polygonAmplitude (insertCyclicAfter q a ε v) hpCanonical = _ at hpoly
  rw [hproof] at hpoly
  rw [kappa_eq_cyclicAttachmentFactor q a v ε hε ha haN hdir] at hpoly
  exact ⟨hp, hpoly⟩

end DirectGLSSW.ShortEdgePolygonAmplitude
