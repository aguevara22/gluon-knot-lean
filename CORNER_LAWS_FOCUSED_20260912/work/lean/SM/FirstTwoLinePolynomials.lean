import SM.LinePolynomials
import SM.PolynomialLinearCore

/-! The exact cross-product coefficients of two line rows in independent
tail/direction coordinates. The polynomial ring still contains every vertex
coordinate. A concrete specialization proves the needed nondivisibility. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ}

/-- Before the shear the head variables represent the independent direction. -/
def freeLineConstant (e : ZMod n) : CoordinatePolynomial n :=
  coordinateX e * coordinateY (e + 1) - coordinateY e * coordinateX (e + 1)

def freeLinePairA (e f : ZMod n) : CoordinatePolynomial n :=
  coordinateX (e + 1) * freeLineConstant f - freeLineConstant e * coordinateX (f + 1)

def freeLinePairB (e f : ZMod n) : CoordinatePolynomial n :=
  coordinateY (e + 1) * freeLineConstant f - freeLineConstant e * coordinateY (f + 1)

def freeLinePairC (e f : ZMod n) : CoordinatePolynomial n :=
  coordinateX (e + 1) * coordinateY (f + 1) - coordinateY (e + 1) * coordinateX (f + 1)

theorem freeLinePairC_irreducible (e f : ZMod n) (hr : remote e f) :
    Irreducible (freeLinePairC e f) := by
  have hef : e + 1 ≠ f + 1 := (remote_endpoints e f hr).2.2.2.symm
  exact determinantPolynomial_irreducible (e + 1, 0) (f + 1, 1) (e + 1, 1) (f + 1, 0)
    (by simp) (by simp) (by simpa using hef) (by simpa using hef.symm) (by simp)

def parallelLineCoefficientWitness (e f : ZMod n) : LabelledTuple n := fun a =>
  if a = f then (0, 1) else if a = e + 1 ∨ a = f + 1 then (1, 0) else (0, 0)

theorem parallelLineCoefficientWitness_values [Nontrivial (ZMod n)]
    (e f : ZMod n) (hr : remote e f) :
    parallelLineCoefficientWitness e f e = (0, 0) ∧
    parallelLineCoefficientWitness e f f = (0, 1) ∧
    parallelLineCoefficientWitness e f (e + 1) = (1, 0) ∧
    parallelLineCoefficientWitness e f (f + 1) = (1, 0) := by
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints e f hr
  simp [parallelLineCoefficientWitness, hfe.symm, hfe1.symm, hf1e.symm,
    (next_ne_self e).symm, next_ne_self f]

theorem freeLinePair_parallel_values [Nontrivial (ZMod n)]
    (e f : ZMod n) (hr : remote e f) :
    eval (scalarCoordinates (parallelLineCoefficientWitness e f)) (freeLinePairC e f) = 0 ∧
    eval (scalarCoordinates (parallelLineCoefficientWitness e f)) (freeLinePairA e f) = -1 := by
  obtain ⟨he, hf, he1, hf1⟩ := parallelLineCoefficientWitness_values e f hr
  simp [freeLinePairC, freeLinePairA, freeLineConstant, he, hf, he1, hf1]

theorem freeLinePairC_not_dvd_A [Nontrivial (ZMod n)]
    (e f : ZMod n) (hr : remote e f) : ¬ freeLinePairC e f ∣ freeLinePairA e f := by
  obtain ⟨hC, hA⟩ := freeLinePair_parallel_values e f hr
  rintro ⟨p, hp⟩
  have h := congrArg (eval (scalarCoordinates (parallelLineCoefficientWitness e f))) hp
  rw [map_mul, hC, hA, zero_mul] at h
  norm_num at h

theorem freeLinePairCA_relprime [Nontrivial (ZMod n)]
    (e f : ZMod n) (hr : remote e f) : IsRelPrime (freeLinePairC e f) (freeLinePairA e f) :=
  (freeLinePairC_irreducible e f hr).isRelPrime_iff_not_dvd.mpr (freeLinePairC_not_dvd_A e f hr)

theorem coordinateX_avoids_vertex (z : ScalarCoordinate n) (e : ZMod n) (h : z.1 ≠ e) :
    z ∉ (coordinateX e).vars := by
  simp [coordinateX, Prod.ext_iff, h]

theorem coordinateY_avoids_vertex (z : ScalarCoordinate n) (e : ZMod n) (h : z.1 ≠ e) :
    z ∉ (coordinateY e).vars := by
  simp [coordinateY, Prod.ext_iff, h]

theorem freeLineConstant_avoids (z : ScalarCoordinate n) (e : ZMod n)
    (he : z.1 ≠ e) (he1 : z.1 ≠ e + 1) : z ∉ (freeLineConstant e).vars :=
  polynomial_not_mem_sub
    (polynomial_not_mem_mul (coordinateX_avoids_vertex z e he) (coordinateY_avoids_vertex z _ he1))
    (polynomial_not_mem_mul (coordinateY_avoids_vertex z e he) (coordinateX_avoids_vertex z _ he1))

theorem freeLinePair_avoids (z : ScalarCoordinate n) (e f : ZMod n)
    (he : z.1 ≠ e) (he1 : z.1 ≠ e + 1) (hf : z.1 ≠ f) (hf1 : z.1 ≠ f + 1) :
    z ∉ (freeLinePairA e f).vars ∧ z ∉ (freeLinePairB e f).vars ∧
      z ∉ (freeLinePairC e f).vars := by
  have hLe := freeLineConstant_avoids z e he he1
  have hLf := freeLineConstant_avoids z f hf hf1
  have hXe := coordinateX_avoids_vertex z (e + 1) he1
  have hXf := coordinateX_avoids_vertex z (f + 1) hf1
  have hYe := coordinateY_avoids_vertex z (e + 1) he1
  have hYf := coordinateY_avoids_vertex z (f + 1) hf1
  exact ⟨polynomial_not_mem_sub (polynomial_not_mem_mul hXe hLf) (polynomial_not_mem_mul hLe hXf),
    polynomial_not_mem_sub (polynomial_not_mem_mul hYe hLf) (polynomial_not_mem_mul hLe hYf),
    polynomial_not_mem_sub (polynomial_not_mem_mul hXe hYf) (polynomial_not_mem_mul hYe hXf)⟩

end

end SM
