import SmoothingTurning
import TriangleOriginBalance

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Signed coordinate for the literal incoming/outgoing affine arc pieces.
The outgoing speed is derived from D's actual through-strand geometry. -/
noncomputable def crossingStarCoordinate (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (t : ℝ) : ℝ :=
  if t ≤ 0 then t else t / outgoingTangentScale D c i

/-- Actual local displacement from the crossing center: t=-1 is the incoming
arc's source, t=0 the crossing, and t=1 the outgoing arc's target. -/
noncomputable def crossingStarOffset (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (t : ℝ) : ℂ :=
  if t ≤ 0 then (t : ℂ) * arcVector D (D.incoming c i)
  else (t : ℂ) * arcVector D (D.outgoing c (D.through c i))

noncomputable def crossingStarCoordinateInverse (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (x : ℝ) : ℝ :=
  if x ≤ 0 then x else outgoingTangentScale D c i * x

/-- Literal local branch point on the two actual incident arcs. -/
noncomputable def crossingStarPoint (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (t : ℝ) : PlanarPoint ℝ :=
  if t ≤ 0 then
    affinePoint (D.vertexPoint (D.arcSource (D.incoming c i)))
      (D.vertexPoint (D.crossingVertex c)) (1 + t)
  else affinePoint (D.vertexPoint (D.crossingVertex c))
    (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i)))) t

theorem crossingStarPoint_eq_offset (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (t : ℝ) :
    crossingStarPoint D c i t = D.vertexPoint (D.crossingVertex c) +
      Complex.equivRealProd (crossingStarOffset D c i t) := by
  by_cases ht : t ≤ 0
  · apply Prod.ext <;>
      simp [crossingStarPoint, crossingStarOffset, ht, arcVector,
        D.incoming_target, Complex.equivRealProd_apply, affinePoint] <;> ring
  · apply Prod.ext <;>
      simp [crossingStarPoint, crossingStarOffset, ht, arcVector,
        D.outgoing_source, Complex.equivRealProd_apply, affinePoint] <;> ring

theorem crossingStarOffset_eq_coordinate (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (t : ℝ) :
    crossingStarOffset D c i t =
      (crossingStarCoordinate D c i t : ℂ) * crossingVector D c i := by
  have hα : (outgoingTangentScale D c i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (outgoingTangentScale_pos D c i))
  by_cases ht : t ≤ 0
  · simp [crossingStarOffset, crossingStarCoordinate, ht, arcVector_incoming]
  · simp only [crossingStarOffset, crossingStarCoordinate, if_neg ht, Complex.ofReal_div]
    rw [crossingVector_through_scale]
    field_simp [hα] <;> ring

theorem crossingStarCoordinate_eq_zero_iff (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (t : ℝ) : crossingStarCoordinate D c i t = 0 ↔ t = 0 := by
  have hα := ne_of_gt (outgoingTangentScale_pos D c i)
  by_cases ht : t ≤ 0 <;> simp [crossingStarCoordinate, ht, hα]

theorem crossingStarCoordinate_strictMono (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) : StrictMono (crossingStarCoordinate D c i) := by
  intro a b hab
  have hα := outgoingTangentScale_pos D c i
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · simpa [crossingStarCoordinate, ha, hb] using hab
    · have hpos : 0 < b / outgoingTangentScale D c i := div_pos (lt_of_not_ge hb) hα
      simp only [crossingStarCoordinate, if_pos ha, if_neg hb]
      exact lt_of_le_of_lt ha hpos
  · have hb : ¬ b ≤ 0 := by linarith
    simp only [crossingStarCoordinate, if_neg ha, if_neg hb]
    exact div_lt_div_of_pos_right hab hα

theorem crossingStarCoordinate_inverse (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (x : ℝ) :
    crossingStarCoordinate D c i (crossingStarCoordinateInverse D c i x) = x := by
  have hα := outgoingTangentScale_pos D c i
  by_cases hx : x ≤ 0
  · simp [crossingStarCoordinateInverse, crossingStarCoordinate, hx]
  · have hpos : 0 < outgoingTangentScale D c i * x := mul_pos hα (lt_of_not_ge hx)
    simp [crossingStarCoordinateInverse, crossingStarCoordinate, hx, not_le.mpr hpos,
      ne_of_gt hα]

theorem crossingStarCoordinateInverse_coordinate (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (t : ℝ) :
    crossingStarCoordinateInverse D c i (crossingStarCoordinate D c i t) = t := by
  apply (crossingStarCoordinate_strictMono D c i).injective
  exact crossingStarCoordinate_inverse D c i _

/-- Literal ordered secant displacement in the local two-branch star. -/
noncomputable def crossingStarSecant (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (s t : ℝ) : ℂ := crossingStarOffset D c 1 t - crossingStarOffset D c 0 s

theorem crossingStarSecant_coordinates (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (s t : ℝ) : crossingStarSecant D c s t =
      -(crossingStarCoordinate D c 0 s : ℂ) * crossingVector D c 0 +
      (crossingStarCoordinate D c 1 t : ℂ) * crossingVector D c 1 := by
  rw [crossingStarSecant, crossingStarOffset_eq_coordinate, crossingStarOffset_eq_coordinate]
  ring

theorem crossingStar_actual_det_ne_zero (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    complexDet (crossingVector D c 0) (crossingVector D c 1) ≠ 0 := by
  exact D.crossing_transverse c

/-- Actual transverse linear secant in the derived signed coordinates. -/
noncomputable def crossingStarLinear (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y : ℝ) : ℂ := -(x : ℂ) * crossingVector D c 0 + (y : ℂ) * crossingVector D c 1

theorem crossingStarLinear_det_coordinates (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y : ℝ) :
    complexDet (crossingVector D c 0) (crossingStarLinear D c x y) =
      y * complexDet (crossingVector D c 0) (crossingVector D c 1) ∧
    complexDet (crossingVector D c 1) (crossingStarLinear D c x y) =
      x * complexDet (crossingVector D c 0) (crossingVector D c 1) := by
  constructor <;> simp [crossingStarLinear, complexDet] <;> ring

theorem crossingStarLinear_eq_zero_iff (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x y : ℝ) : crossingStarLinear D c x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hz
    obtain ⟨hy, hx⟩ := crossingStarLinear_det_coordinates D c x y
    rw [hz] at hx hy
    simp only [complexDet, Complex.zero_re, Complex.zero_im, mul_zero, sub_self] at hx hy
    exact ⟨(mul_eq_zero.mp hx.symm).resolve_right (crossingStar_actual_det_ne_zero D c),
      (mul_eq_zero.mp hy.symm).resolve_right (crossingStar_actual_det_ne_zero D c)⟩
  · rintro ⟨rfl, rfl⟩
    simp [crossingStarLinear]

theorem crossingStarSecant_eq_zero_iff (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (s t : ℝ) : crossingStarSecant D c s t = 0 ↔ s = 0 ∧ t = 0 := by
  rw [crossingStarSecant_coordinates]
  change crossingStarLinear D c (crossingStarCoordinate D c 0 s)
    (crossingStarCoordinate D c 1 t) = 0 ↔ _
  rw [crossingStarLinear_eq_zero_iff, crossingStarCoordinate_eq_zero_iff,
    crossingStarCoordinate_eq_zero_iff]

end DirectGLSSW.HOMFLY.PrincipalTurning















