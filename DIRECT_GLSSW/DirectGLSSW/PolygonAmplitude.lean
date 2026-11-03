import DirectGLSSW.RealPolygons
import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.ShortEdgeCyclicAdapter
import DirectGLSSW.ShortEdgeWeighted
import DirectGLSSW.ShortEdgeCurrentTable
import DirectGLSSW.ShortEdgeBoundedCongruence
import DirectGLSSW.ShortEdgeSignRealization
import DirectGLSSW.ShortEdgeCyclicG1
import DirectGLSSW.RootedAmplitude

namespace DirectGLSSW.ShortEdgePolygonAmplitude

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeSignRealization
open DirectGLSSW.ShortEdgeWeighted

/-- Under explicit core and parent genericity, root independence transfers the
rooted short-edge formula to the canonical polygon amplitudes. -/
theorem polygonAmplitude_insert_eq
    (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ)
    (hε : 0 < ε)
    (hcore : ShortEdgeSignStability.CoreHGeneric (coreWord q (by omega)) (n - 1))
    (hdir : ShortEdgeSignStability.DirectionGeneric (coreWord q (by omega)) (n - 1) a.val v)
    (hst : ShortEdgeSignStability.ShortEdgeStability
      (coreWord q (by omega)) (n - 1) a.val v ε (by omega) hcore hdir)
    (ha : 0 < a.val) (ha' : a.val < n - 1)
    (hparentG2 : cyclicNoTripleIntersections (insertCyclicAfter q a ε v)) :
    polygonAmplitude (insertCyclicAfter q a ε v)
      (⟨by omega,
        ShortEdgeCyclicG1.inserted_cyclicNoncollinear_of_openStability
          hn q a ε v hcore hdir hst,
        hparentG2⟩ : CyclicGeneric (insertCyclicAfter q a ε v)) =
      kappa a.val (by omega) (shortSign (coreWord q (by omega)) a.val v) *
        polygonAmplitude q hq := by
  rw [polygonAmplitude_eq_rootedSpinorAmplitude hRI _ _ (lastParentRoot n),
      polygonAmplitude_eq_rootedSpinorAmplitude hRI q hq
        (lastCoreRoot (by omega : 0 < n))]
  exact rootedLast_amplitude_eq hn q hq.g1 a ε v hε hcore hdir hst ha ha'

end DirectGLSSW.ShortEdgePolygonAmplitude
