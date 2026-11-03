import DirectGLSSW.RealPolygons
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace DirectGLSSW.AuxiliaryCarrierChart
open DirectGLSSW

abbrev CarrierLine := PlanarPoint ℝ × ℝ

def lineValue (L : CarrierLine) (x : PlanarPoint ℝ) : ℝ :=
  planarDet L.1 x + L.2

def lineDenominator (L M : CarrierLine) : ℝ := planarDet L.1 M.1

noncomputable def lineIntersection (L M : CarrierLine) : PlanarPoint ℝ :=
  ((M.2 * L.1.1 - L.2 * M.1.1) / lineDenominator L M,
   (M.2 * L.1.2 - L.2 * M.1.2) / lineDenominator L M)

theorem lineValue_intersection_left (L M : CarrierLine)
    (h : lineDenominator L M ≠ 0) :
    lineValue L (lineIntersection L M)=0 := by
  simp only [lineValue, lineIntersection, lineDenominator, planarDet] at h ⊢
  field_simp [h] <;> ring

theorem lineValue_intersection_right (L M : CarrierLine)
    (h : lineDenominator L M ≠ 0) :
    lineValue M (lineIntersection L M)=0 := by
  simp only [lineValue, lineIntersection, lineDenominator, planarDet] at h ⊢
  field_simp [h] <;> ring

theorem lineIntersection_unique (L M : CarrierLine) (x : PlanarPoint ℝ)
    (h : lineDenominator L M ≠ 0)
    (hxL : lineValue L x=0) (hxM : lineValue M x=0) :
    x=lineIntersection L M := by
  have hxnum : lineDenominator L M * x.1 = M.2 * L.1.1 - L.2 * M.1.1 := by
    calc
      lineDenominator L M * x.1 = M.1.1 * lineValue L x - L.1.1 * lineValue M x +
          (M.2 * L.1.1 - L.2 * M.1.1) := by
        simp only [lineValue, lineDenominator, planarDet]
        ring
      _ = M.2 * L.1.1 - L.2 * M.1.1 := by rw [hxL, hxM]; ring
  have hynum : lineDenominator L M * x.2 = M.2 * L.1.2 - L.2 * M.1.2 := by
    calc
      lineDenominator L M * x.2 = M.1.2 * lineValue L x - L.1.2 * lineValue M x +
          (M.2 * L.1.2 - L.2 * M.1.2) := by
        simp only [lineValue, lineDenominator, planarDet]
        ring
      _ = M.2 * L.1.2 - L.2 * M.1.2 := by rw [hxL, hxM]; ring
  apply Prod.ext
  · change x.1=(M.2*L.1.1-L.2*M.1.1)/lineDenominator L M
    rw [eq_div_iff h]
    simpa only [mul_comm] using hxnum
  · change x.2=(M.2*L.1.2-L.2*M.1.2)/lineDenominator L M
    rw [eq_div_iff h]
    simpa only [mul_comm] using hynum

end DirectGLSSW.AuxiliaryCarrierChart




