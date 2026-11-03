import ActiveArcOpenSideGeometry
import LocalCarrierLineAlgebra
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords AuxiliaryCarrierChart
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Coordinates of a genuine directed physical edge line. -/
def physicalLine (e : Fin (n+1)) : CarrierLine :=
  (q e.succ-q e.castSucc, -planarDet (q e.succ-q e.castSucc) (q e.castSucc))

theorem physicalLine_affine_value (e : Fin (n+1)) (t : ℝ) :
    lineValue (physicalLine q e) (affinePoint (q e.castSucc) (q e.succ) t)=0 := by
  simp only [lineValue,physicalLine,affinePoint,planarDet,Prod.fst_sub,Prod.snd_sub]
  ring

/-- Source vertex G1 makes any two intersecting, distinct physical carrier lines transverse. -/
theorem physicalLine_denominator_ne (hG1 : cyclicNoncollinear q)
    (e f : Fin (n+1)) (hef : e≠f) (s t : ℝ)
    (h : affinePoint (q e.castSucc) (q e.succ) s = affinePoint (q f.castSucc) (q f.succ) t) :
    lineDenominator (physicalLine q e) (physicalLine q f)≠0 := by
  change planarDet (q e.succ-q e.castSucc) (q f.succ-q f.castSucc)≠0
  by_cases hfe : f.castSucc=e.succ
  · have hidx := congrArg Fin.val hfe
    have hd := hG1 f.succ e.castSucc e.succ
      (by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_succ,Fin.coe_castSucc] at *; omega)
      (by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_succ,Fin.coe_castSucc] at *; omega)
      (by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_succ,Fin.coe_castSucc] at *; omega)
    intro hz
    apply hd
    rw [hfe] at hz
    have heq : planarDet (q e.castSucc-q e.succ) (q f.succ-q e.succ) =
        -planarDet (q e.succ-q e.castSucc) (q f.succ-q e.succ) := by
      simp only [planarDet,Prod.fst_sub,Prod.snd_sub]; ring
    rw [heq,hz,neg_zero]
  · exact fun hz => hG1 f.castSucc e.succ e.castSucc hfe
      (by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_succ,Fin.coe_castSucc] at this; omega)
      (fun hh => hef (Fin.ext (congrArg Fin.val hh).symm))
      (affinePoint_parallel_collinear _ _ _ _ s t h hz)

/-- A coordinate line through the terminal endpoint, perpendicular to the last physical edge. -/
def terminalLine : CarrierLine :=
  let v := q ⟨n+1,by omega⟩ - q ⟨n,by omega⟩
  ((-v.2,v.1),-planarDet (-v.2,v.1) (q ⟨n+1,by omega⟩))

theorem terminalLine_value : lineValue (terminalLine q) (q ⟨n+1,by omega⟩)=0 := by
  simp [terminalLine,lineValue]

theorem terminalLine_denominator_ne (hR : Regular q) :
    lineDenominator (physicalLine q ⟨n,by omega⟩) (terminalLine q)≠0 := by
  have hv := hR.edge_nonzero ⟨n,by omega⟩
  change q ⟨n+1,by omega⟩-q ⟨n,by omega⟩≠0 at hv
  change planarDet (q ⟨n+1,by omega⟩-q ⟨n,by omega⟩)
    (-((q ⟨n+1,by omega⟩-q ⟨n,by omega⟩).2),(q ⟨n+1,by omega⟩-q ⟨n,by omega⟩).1)≠0
  intro hz
  simp only [planarDet] at hz
  have hx : (q ⟨n+1,by omega⟩-q ⟨n,by omega⟩).1=0 := by nlinarith [sq_nonneg (q ⟨n+1,by omega⟩-q ⟨n,by omega⟩).1,sq_nonneg (q ⟨n+1,by omega⟩-q ⟨n,by omega⟩).2]
  have hy : (q ⟨n+1,by omega⟩-q ⟨n,by omega⟩).2=0 := by nlinarith [sq_nonneg (q ⟨n+1,by omega⟩-q ⟨n,by omega⟩).2]
  exact hv (Prod.ext hx hy)

end DirectGLSSW.ActiveArc.OpenCarrier
