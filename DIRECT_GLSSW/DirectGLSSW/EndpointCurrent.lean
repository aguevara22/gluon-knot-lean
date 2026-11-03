import DirectGLSSW.EndpointDirectSource
import DirectGLSSW.SpinorVertices

set_option autoImplicit false

namespace DirectGLSSW.EndpointCurrent
open DirectGLSSW

/-- The moving point replaces the initial position of the endpoint word. -/
def endpointFar (a : ℕ) (H : TripleArray) : TripleArray :=
  fun x y z => if x = a then H 0 y z else H x y z

/-- Row a is the word p,q_(a+1),...,q_(i+1); entries below the diagonal vanish. -/
noncomputable def endpointCurrent (d : ℕ → ℚ) (H : TripleArray) (a i : ℕ) : ℚ :=
  if a ≤ i then ordinaryCurrent (fun _ l _ => d l) (endpointFar a H) a (i + 1) else 0

def endpointWord {K : Type*} (q : ℕ → PlanarPoint K) (a x : ℕ) : PlanarPoint K :=
  if x = a then q 0 else q x

theorem ordinaryCurrent_endpointFar_core (d : ℕ → ℚ) (H : TripleArray)
    {a x y : ℕ} (hax : a < x) (hxy : x < y) :
    ordinaryCurrent (fun _ l _ => d l) (endpointFar a H) x y =
      ordinaryCurrent (fun _ l _ => d l) H x y := by
  apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hxy
  intro l m n hxl _ _ _
  have hla : l ≠ a := by omega
  simp [endpointFar, hla]

theorem endpointCurrent_diagonal (d : ℕ → ℚ) (H : TripleArray) (a : ℕ) :
    endpointCurrent d H a a = 1 := by
  simp [endpointCurrent]

theorem endpointCurrent_below (d : ℕ → ℚ) (H : TripleArray)
    {a i : ℕ} (hi : i < a) : endpointCurrent d H a i = 0 := by
  simp [endpointCurrent, Nat.not_le.mpr hi]

theorem endpointFar_polygonSignArray_congr {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q : ℕ → PlanarPoint K) {a x y z : ℕ} (hax : a ≤ x) (hxy : x < y) (hyz : y < z) :
    polygonSignArray (endpointWord q a) x y z = endpointFar a (polygonSignArray q) x y z := by
  have hya : y ≠ a := by omega
  have hza : z ≠ a := by omega
  by_cases hxa : x = a
  · simp [polygonSignArray, polygonHDet, endpointWord, endpointFar, hxa, hya, hza]
  · simp [polygonSignArray, polygonHDet, endpointWord, endpointFar, hxa, hya, hza]

theorem endpointCurrent_polygon_eq {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q : ℕ → PlanarPoint K) (d : ℕ → ℚ) {a i : ℕ} (hai : a ≤ i) :
    endpointCurrent d (polygonSignArray q) a i =
      ordinaryCurrent (fun _ l _ => d l) (polygonSignArray (endpointWord q a)) a (i+1) := by
  rw [endpointCurrent, if_pos hai]
  apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
  intro x y z hax hxy hyz _
  exact (endpointFar_polygonSignArray_congr q hax hxy hyz).symm







end DirectGLSSW.EndpointCurrent
