import DirectGLSSW.RealPolygons
import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.ShortEdgeCyclicAdapter
import DirectGLSSW.ShortEdgeWeighted
import DirectGLSSW.ShortEdgeCurrentTable
import DirectGLSSW.ShortEdgeBoundedCongruence
import DirectGLSSW.ShortEdgeSignRealization
import DirectGLSSW.ShortEdgeCyclicG1

namespace DirectGLSSW.ShortEdgePolygonAmplitude

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeSignRealization
open DirectGLSSW.ShortEdgeWeighted

def coreWord {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hn : 0 < n) : ℕ → PlanarPoint ℝ :=
  fun k => rootedPolygonWord q (lastCoreRoot hn) k

def parentWord {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ) : ℕ → PlanarPoint ℝ :=
  fun k => rootedPolygonWord (insertCyclicAfter q a ε v) (lastParentRoot n) k

/-- Rooted-last amplitude formula, including the source normalization κ. -/
theorem rootedLast_amplitude_eq
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : cyclicNoncollinear q) (a : Fin n) (ε : ℝ) (v : PlanarPoint ℝ)
    (hε : 0 < ε)
    (hcore : ShortEdgeSignStability.CoreHGeneric (coreWord q (by omega)) (n - 1))
    (hdir : ShortEdgeSignStability.DirectionGeneric (coreWord q (by omega)) (n - 1) a.val v)
    (hst : ShortEdgeSignStability.ShortEdgeStability
      (coreWord q (by omega)) (n - 1) a.val v ε (by omega) hcore hdir)
    (ha : 0 < a.val) (ha' : a.val < n - 1) :
    rootedSpinorAmplitude (insertCyclicAfter q a ε v) (lastParentRoot n) =
      kappa a.val (by omega) (shortSign (coreWord q (by omega)) a.val v) *
        rootedSpinorAmplitude q (lastCoreRoot (by omega : 0 < n)) := by
  let w := coreWord q (by omega)
  let t := shortSign w a.val v
  let H := coreHSign w
  let parentSign := polygonSignArray (parentWord q a ε v)
  have hparentG1 : cyclicNoncollinear (insertCyclicAfter q a ε v) :=
    ShortEdgeCyclicG1.inserted_cyclicNoncollinear_of_openStability
      hn q a ε v hcore hdir hst
  have hparentMarked :
      rootedSpinorAmplitude (insertCyclicAfter q a ε v) (lastParentRoot n) =
        markedAmplitude parentSign parentSign 0 n := by
    rw [rootedSpinorAmplitude_eq_markedTreeSum (by omega)
      (insertCyclicAfter q a ε v) hparentG1 (lastParentRoot n)]
    rw [markedTreeSum_eq_markedAmplitude _ _ (by omega)]
    rfl
  have hcoreMarked :
      rootedSpinorAmplitude q (lastCoreRoot (by omega : 0 < n)) =
        markedAmplitude (polygonSignArray w) (polygonSignArray w) 0 (n - 1) := by
    rw [rootedSpinorAmplitude_eq_markedTreeSum hn q hq
      (lastCoreRoot (by omega : 0 < n))]
    rw [markedTreeSum_eq_markedAmplitude _ _ (by omega)]
    rfl
  have hCoreSigns : ∀ i k j, 0 ≤ i → i < k → k < j → j ≤ n - 1 →
      ShortEdgeWeighted.H0 H i k j = polygonSignArray w i k j := by
    intro i k j hi hik hkj hj
    exact coreHSign_value_eq_polygonSignArray w (n - 1) hcore i k j hik hkj hj
  have hparentWord : ∀ k, k ≤ n → parentWord q a ε v k =
      ShortEdgeSignStability.insertAfter w a.val ε v k := by
    intro k hk
    exact insertedLastRootWord_eq_openInsertAfter (by omega) q a ε v k hk
  have hParentSigns : ∀ i k j, 0 ≤ i → i < k → k < j → j ≤ n →
      parentSign i k j = ShortEdgeWeighted.H1 a.val t H i k j := by
    intro i k j hi hik hkj hj
    change scalarSignValue (polygonHDet (parentWord q a ε v) i k j) = _
    unfold polygonHDet
    rw [hparentWord i (by omega), hparentWord k (by omega), hparentWord j (by omega)]
    exact (H1_eq_inserted_polygonSignArray w (n - 1) a.val v ε hε (by omega)
      hcore hdir hst i k j hik hkj (by omega)).symm
  have hTable := ShortEdgeWeighted.CurrentTableImpl.shortEdge_markedAmplitude_near_free a.val 0 n ha (by omega)
    (by omega) t parentSign (polygonSignArray w) H
  calc
    rootedSpinorAmplitude (insertCyclicAfter q a ε v) (lastParentRoot n) =
        markedAmplitude parentSign parentSign 0 n := hparentMarked
    _ = markedAmplitude parentSign (ShortEdgeWeighted.H1 a.val t H) 0 n :=
      markedAmplitude_congr_interval parentSign parentSign parentSign
        (ShortEdgeWeighted.H1 a.val t H) (by omega) (by
          intro i k j hi hik hkj hj
          exact hParentSigns i k j (by omega) hik hkj (by omega))
    _ = kappa a.val (by omega) t *
        markedAmplitude (polygonSignArray w) (ShortEdgeWeighted.H0 H) 0
          (collapseAfter a.val n) := hTable
    _ = kappa a.val (by omega) t *
        markedAmplitude (polygonSignArray w) (polygonSignArray w) 0 (n - 1) := by
          have hcongr := markedAmplitude_congr_interval
            (polygonSignArray w) (polygonSignArray w) (ShortEdgeWeighted.H0 H)
            (polygonSignArray w) (i := 0) (j := n - 1) (by omega) (by
              intro i k j hi hik hkj hj
              simpa [ShortEdgeWeighted.H0] using
                hCoreSigns i k j hi hik hkj (by omega))
          have hcollapse : collapseAfter a.val n = n - 1 :=
            ShortEdgeCutFibers.collapseAfter_eq_sub_one_of_lt a.val n (by omega)
          rw [hcollapse]
          exact congrArg (fun x : ℚ => kappa a.val (by omega) t * x) hcongr
    _ = kappa a.val (by omega) t *
        rootedSpinorAmplitude q (lastCoreRoot (by omega : 0 < n)) := by
          rw [hcoreMarked]


end DirectGLSSW.ShortEdgePolygonAmplitude
