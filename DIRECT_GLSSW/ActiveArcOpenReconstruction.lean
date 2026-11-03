import ActiveArcOpenLineGeometry
import LocalCarrierContinuity

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc AuxiliaryCarrierChart
open scoped Topology
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- A fixed coordinate line through the initial endpoint, transverse to edge zero.
It is used only to reconstruct the endpoint, never as an arc edge. -/
def initialLine : CarrierLine :=
  let v := q 1-q 0
  ((-v.2,v.1),-planarDet (-v.2,v.1) (q 0))

def openChartLines : Fin (n+1) ⊕ Unit → CarrierLine :=
  Sum.elim (physicalLine q) (fun _ => terminalLine q)

theorem initialLine_value : lineValue (initialLine q) (q 0)=0 := by
  simp [initialLine,lineValue]

theorem initialLine_denominator_ne (hR : Regular q) :
    lineDenominator (initialLine q) (physicalLine q 0) ≠ 0 := by
  have hv := hR.edge_nonzero 0
  change q 1-q 0≠0 at hv
  change planarDet (-((q 1-q 0).2),(q 1-q 0).1) (q 1-q 0)≠0
  intro hz
  simp only [planarDet] at hz
  have hx : (q 1-q 0).1=0 := by
    nlinarith [sq_nonneg (q 1-q 0).1,sq_nonneg (q 1-q 0).2]
  have hy : (q 1-q 0).2=0 := by
    nlinarith [sq_nonneg (q 1-q 0).1,sq_nonneg (q 1-q 0).2]
  exact hv (Prod.ext hx hy)

/-- Reconstruction from physical lines and one terminal coordinate line.
The initial transverse line is held fixed throughout this chart. -/
def reconstructOpen (L : Fin (n+1) ⊕ Unit → CarrierLine)
    (i : Fin (n+2)) : PlanarPoint ℝ :=
  if h0 : i.val=0 then lineIntersection (initialLine q) (L (Sum.inl 0)) else
  if ht : i.val=n+1 then
    lineIntersection (L (Sum.inl ⟨n,by omega⟩)) (L (Sum.inr ())) else
    lineIntersection (L (Sum.inl ⟨i.val-1,by have := i.isLt; omega⟩))
      (L (Sum.inl ⟨i.val,by have := i.isLt; omega⟩))

theorem adjacent_denominator_ne (hG1 : cyclicNoncollinear q)
    (i : Fin (n+2)) (h0 : i.val≠0) (ht : i.val≠n+1) :
    lineDenominator
      (physicalLine q ⟨i.val-1,by have := i.isLt; omega⟩)
      (physicalLine q ⟨i.val,by have := i.isLt; omega⟩) ≠ 0 := by
  let e : Fin (n+1) := ⟨i.val-1,by have := i.isLt; omega⟩
  let f : Fin (n+1) := ⟨i.val,by have := i.isLt; omega⟩
  have he : e.succ=i := Fin.ext (by dsimp [e]; omega)
  have hf : f.castSucc=i := Fin.ext rfl
  exact physicalLine_denominator_ne q hG1 e f
    (by intro h; have := congrArg Fin.val h; dsimp [e,f] at this; omega)
    1 0 (by rw [affinePoint_one,affinePoint_zero,he,hf])

theorem reconstructOpen_recovery (hR : Regular q) (hG1 : cyclicNoncollinear q) :
    reconstructOpen q (openChartLines q)=q := by
  funext i
  by_cases h0 : i.val=0
  · have hi : i=0 := Fin.ext h0
    subst i
    simp only [reconstructOpen,Fin.val_zero,dif_pos rfl,openChartLines,Sum.elim_inl]
    apply (lineIntersection_unique _ _ _ (initialLine_denominator_ne q hR)
      (initialLine_value q) _).symm
    simpa only [affinePoint_zero] using physicalLine_affine_value q 0 0
  · by_cases ht : i.val=n+1
    · have hi : i=⟨n+1,by omega⟩ := Fin.ext ht
      rw [reconstructOpen,dif_neg h0,dif_pos ht]
      change lineIntersection (physicalLine q ⟨n,by omega⟩) (terminalLine q)=q i
      apply (lineIntersection_unique _ _ _ (terminalLine_denominator_ne q hR) _ _).symm
      · simpa only [affinePoint_one,hi] using physicalLine_affine_value q ⟨n,by omega⟩ 1
      · simpa only [hi] using terminalLine_value q
    · rw [reconstructOpen,dif_neg h0,dif_neg ht]
      let e : Fin (n+1) := ⟨i.val-1,by have := i.isLt; omega⟩
      let f : Fin (n+1) := ⟨i.val,by have := i.isLt; omega⟩
      change lineIntersection (physicalLine q e) (physicalLine q f)=q i
      apply (lineIntersection_unique _ _ _ (adjacent_denominator_ne q hG1 i h0 ht) _ _).symm
      · have he : e.succ=i := Fin.ext (by dsimp [e]; omega)
        simpa only [affinePoint_one,he] using physicalLine_affine_value q e 1
      · simpa only [affinePoint_zero] using physicalLine_affine_value q f 0

theorem reconstructOpen_continuousAt (hR : Regular q) (hG1 : cyclicNoncollinear q) :
    ContinuousAt (reconstructOpen q) (openChartLines q) := by
  apply continuousAt_pi.2
  intro i
  by_cases h0 : i.val=0
  · simp only [reconstructOpen,dif_pos h0]
    let P := fun L : Fin (n+1) ⊕ Unit → CarrierLine => (initialLine q,L (Sum.inl 0))
    have hp : ContinuousAt P (openChartLines q) :=
      continuousAt_const.prodMk (continuous_apply (π := fun _ : Fin (n+1) ⊕ Unit => CarrierLine) (Sum.inl 0)).continuousAt
    exact ContinuousAt.comp' (f := P) (x := openChartLines q)
      (lineIntersection_continuousAt _ _ (initialLine_denominator_ne q hR)) hp
  · by_cases ht : i.val=n+1
    · simp only [reconstructOpen,dif_neg h0,dif_pos ht]
      let P := fun L : Fin (n+1) ⊕ Unit → CarrierLine =>
        (L (Sum.inl ⟨n,by omega⟩),L (Sum.inr ()))
      have hp : ContinuousAt P (openChartLines q) :=
        (continuous_apply (π := fun _ : Fin (n+1) ⊕ Unit => CarrierLine) (Sum.inl ⟨n,by omega⟩)).continuousAt.prodMk
          (continuous_apply (π := fun _ : Fin (n+1) ⊕ Unit => CarrierLine) (Sum.inr ())).continuousAt
      exact ContinuousAt.comp' (f := P) (x := openChartLines q)
        (lineIntersection_continuousAt _ _ (terminalLine_denominator_ne q hR)) hp
    · simp only [reconstructOpen,dif_neg h0,dif_neg ht]
      let P := fun L : Fin (n+1) ⊕ Unit → CarrierLine =>
        (L (Sum.inl ⟨i.val-1,by have := i.isLt; omega⟩),
         L (Sum.inl ⟨i.val,by have := i.isLt; omega⟩))
      have hp : ContinuousAt P (openChartLines q) :=
        (continuous_apply (π := fun _ : Fin (n+1) ⊕ Unit => CarrierLine) (Sum.inl ⟨i.val-1,by have := i.isLt; omega⟩)).continuousAt.prodMk
          (continuous_apply (π := fun _ : Fin (n+1) ⊕ Unit => CarrierLine) (Sum.inl ⟨i.val,by have := i.isLt; omega⟩)).continuousAt
      exact ContinuousAt.comp' (f := P) (x := openChartLines q)
        (lineIntersection_continuousAt _ _ (adjacent_denominator_ne q hG1 i h0 ht)) hp



end DirectGLSSW.ActiveArc.OpenCarrier
