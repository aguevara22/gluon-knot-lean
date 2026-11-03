import DirectGLSSW.TruncationPointGeometry
import DirectGLSSW.TruncationEdgeLift
import DirectGLSSW.RealPolygons
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace DirectGLSSW.TruncationPointListAdapter

open TruncationDirection TruncationEdgeLift

theorem cyclicGeneric_of_pointList_eq {n m : ℕ}
    (q : Fin n → PlanarPoint ℝ) (r : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (h : List.ofFn q = List.ofFn r) : CyclicGeneric r := by
  have hnm : n = m := by simpa using congrArg List.length h
  subst m
  have hqr : q = r := List.ofFn_injective h
  simpa only [hqr] using hq

theorem polygonAmplitude_eq_of_pointList_eq {n m : ℕ}
    (q : Fin n → PlanarPoint ℝ) (r : Fin m → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hr : CyclicGeneric r)
    (h : List.ofFn q = List.ofFn r) : polygonAmplitude q hq = polygonAmplitude r hr := by
  have hnm : n = m := by simpa using congrArg List.length h
  subst m
  have hqr : q = r := List.ofFn_injective h
  subst r
  rfl

theorem pointList_truncate_zero {n : ℕ} (q : Fin (n + 1) → PlanarPoint ℝ)
    (p : Fin (n + 1)) (scale ε : ℝ) :
    List.ofFn (truncateCyclicCorner q 0 p scale ε) =
      (q 0 + ε • (q p - q 0)) ::
      (q 0 + (ε * scale) • (q (cyclicSuccessor 0) - q 0)) ::
      (List.ofFn q).tail := by
  let Q := truncateCyclicCorner q 0 p scale ε
  have hB : Q 0 = q 0 + ε • (q p - q 0) :=
    truncateCyclicCorner_anchor q 0 p scale ε
  have hC : Q (Fin.succ (0 : Fin (n + 1))) =
      q 0 + (ε * scale) • (q (cyclicSuccessor 0) - q 0) :=
    truncateCyclicCorner_new q 0 p scale ε
  have ht (i : Fin n) : Q i.succ.succ = q i.succ := by
    have hindex : edgeLift (0 : Fin (n + 1)) i.succ = i.succ.succ := by
      apply Fin.ext
      simp [edgeLift]
    rw [← hindex]
    change truncateCyclicCorner q 0 p scale ε (edgeLift 0 i.succ) = _
    rw [truncateCyclicCorner_of_collapse_ne q 0 p scale ε (edgeLift 0 i.succ)
      (by rw [collapseFin_edgeLift]; exact Fin.succ_ne_zero i)]
    rw [collapseFin_edgeLift]
  change List.ofFn Q = _
  rw [List.ofFn_succ, List.ofFn_succ, hB, hC]
  congr 2
  rw [List.ofFn_succ]
  simp only [List.tail_cons]
  exact congrArg List.ofFn (funext ht)

end DirectGLSSW.TruncationPointListAdapter
