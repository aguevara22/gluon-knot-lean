import LocalCarrierPolygonRecovery
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions

set_option autoImplicit false
namespace DirectGLSSW.AuxiliaryCarrierChart
open DirectGLSSW

open scoped Topology

theorem lineIntersection_continuousAt (L M : CarrierLine)
    (h : lineDenominator L M ≠ 0) :
    ContinuousAt (fun p : CarrierLine × CarrierLine => lineIntersection p.1 p.2) (L,M) := by
  have hden : ContinuousAt (fun p : CarrierLine × CarrierLine => lineDenominator p.1 p.2) (L,M) := by
    unfold lineDenominator planarDet
    exact (((continuous_fst.fst.fst).mul continuous_snd.fst.snd).sub
      ((continuous_fst.fst.snd).mul continuous_snd.fst.fst)).continuousAt
  have hnumx : ContinuousAt
      (fun p : CarrierLine × CarrierLine => p.2.2*p.1.1.1-p.1.2*p.2.1.1) (L,M) := by
    exact (((continuous_snd.snd).mul continuous_fst.fst.fst).sub
      ((continuous_fst.snd).mul continuous_snd.fst.fst)).continuousAt
  have hnumy : ContinuousAt
      (fun p : CarrierLine × CarrierLine => p.2.2*p.1.1.2-p.1.2*p.2.1.2) (L,M) := by
    exact (((continuous_snd.snd).mul continuous_fst.fst.snd).sub
      ((continuous_fst.snd).mul continuous_snd.fst.snd)).continuousAt
  have hx := hnumx.div hden h
  have hy := hnumy.div hden h
  change ContinuousAt (fun p : CarrierLine × CarrierLine =>
    ((p.2.2*p.1.1.1-p.1.2*p.2.1.1)/lineDenominator p.1 p.2,
     (p.2.2*p.1.1.2-p.1.2*p.2.1.2)/lineDenominator p.1 p.2)) (L,M)
  exact ContinuousAt.prodMk hx hy

theorem reconstructPolygon_continuousAt {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ContinuousAt (fun L : Fin n → CarrierLine => reconstructPolygon L)
      (polygonCarrierCoordinates q) := by
  apply continuousAt_pi.2
  intro i
  let p := (cyclicSuccessorPerm n)⁻¹ i
  have hp : ContinuousAt (fun L : Fin n → CarrierLine => (L p,L i))
      (polygonCarrierCoordinates q) := by
    exact ContinuousAt.prodMk
      (continuous_apply (π := fun _ : Fin n => CarrierLine) p).continuousAt
      (continuous_apply (π := fun _ : Fin n => CarrierLine) i).continuousAt
  have hc := lineIntersection_continuousAt
    (polygonCarrierCoordinates q p) (polygonCarrierCoordinates q i)
    (polygonCarrierDenominator_ne_zero q hq i)
  exact ContinuousAt.comp' (f := fun L : Fin n → CarrierLine => (L p, L i))
    (x := polygonCarrierCoordinates q) hc hp

end DirectGLSSW.AuxiliaryCarrierChart



