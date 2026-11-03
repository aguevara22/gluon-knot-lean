import DirectGLSSW.PolygonLocalMotion
import DirectGLSSW.PolygonCrossings
import Mathlib.Tactic.FieldSimp

namespace DirectGLSSW.LocalCrossingTransport
open DirectGLSSW

/-- Actual transverse carrier parameter on the first directed segment. -/
noncomputable def leftParameter (a b c d : PlanarPoint ℝ) : ℝ :=
  planarDet (c-a) (d-c) / planarDet (b-a) (d-c)

noncomputable def rightParameter (a b c d : PlanarPoint ℝ) : ℝ :=
  planarDet (c-a) (b-a) / planarDet (b-a) (d-c)

theorem carrier_parameter_equation (a b c d : PlanarPoint ℝ)
    (hD : planarDet (b-a) (d-c) ≠ 0) :
    affinePoint a b (leftParameter a b c d) =
      affinePoint c d (rightParameter a b c d) := by
  ext <;> dsimp [affinePoint, leftParameter, rightParameter, planarDet] at * <;>
    field_simp <;> ring

theorem leftParameter_eq (a b c d : PlanarPoint ℝ) (s u : ℝ)
    (hD : planarDet (b-a) (d-c) ≠ 0)
    (hx : affinePoint a b s = affinePoint c d u) :
    leftParameter a b c d = s :=
  (affinePoint_intersection_parameters_unique a b c d
    (leftParameter a b c d) (rightParameter a b c d) s u hD
    (carrier_parameter_equation a b c d hD) hx).1

theorem rightParameter_eq (a b c d : PlanarPoint ℝ) (s u : ℝ)
    (hD : planarDet (b-a) (d-c) ≠ 0)
    (hx : affinePoint a b s = affinePoint c d u) :
    rightParameter a b c d = u :=
  (affinePoint_intersection_parameters_unique a b c d
    (leftParameter a b c d) (rightParameter a b c d) s u hD
    (carrier_parameter_equation a b c d hD) hx).2

theorem leftParameter_continuousAt (a b c d : ℝ → PlanarPoint ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (hD : planarDet (b 0-a 0) (d 0-c 0) ≠ 0) :
    ContinuousAt (fun t => leftParameter (a t) (b t) (c t) (d t)) 0 := by
  unfold leftParameter
  apply ContinuousAt.div
  · dsimp [planarDet]; fun_prop
  · dsimp [planarDet]; fun_prop
  · exact hD

theorem rightParameter_continuousAt (a b c d : ℝ → PlanarPoint ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (hD : planarDet (b 0-a 0) (d 0-c 0) ≠ 0) :
    ContinuousAt (fun t => rightParameter (a t) (b t) (c t) (d t)) 0 := by
  unfold rightParameter
  apply ContinuousAt.div
  · dsimp [planarDet]; fun_prop
  · dsimp [planarDet]; fun_prop
  · exact hD






end DirectGLSSW.LocalCrossingTransport
